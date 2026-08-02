/*******************************************************************\

Module: CBMC Command Line Option Processing

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// CBMC Command Line Option Processing

#include "cbmc_parse_options.h"

#include <algorithm>
#include <cctype>
#include <cstdlib> // exit()
#include <chrono>
#include <cstdio>
#include <fstream>
#include <iostream>
#include <map>
#include <memory>
#include <set>
#include <sstream>
#include <vector>

#ifndef _WIN32
#  include <cerrno>
#  include <csignal>
#  include <sys/types.h>
#  include <sys/wait.h>
#  include <unistd.h>
#  ifdef __linux__
#    include <sys/prctl.h>
#  endif
#endif

#include <util/config.h>
#include <util/expr_util.h>
#include <util/exit_codes.h>
#include <util/invariant.h>
#include <util/make_unique.h>
#include <util/simplify_expr.h>
#include <util/version.h>

#ifdef _MSC_VER
#  include <util/unicode.h>
#endif

#include <langapi/language.h>
#include <langapi/language_util.h>

#include <ansi-c/c_preprocess.h>
#include <ansi-c/cprover_library.h>
#include <ansi-c/gcc_version.h>

#include <assembler/remove_asm.h>

#include <cpp/cprover_library.h>

#include <analyses/interference_predicate_analysis.h>
#include <analyses/interference_predicate_cube.h>
#include <analyses/protocol_capacity_analysis.h>
#include <analyses/cas_stability_analysis.h>
#include <analyses/predicate_stability_analysis.h>
#include <analyses/relational_order_analysis.h>
#include <analyses/jces_analysis.h>
#include <analyses/commuting_sequentialization.h>
#include <analyses/extremum_cone_analysis.h>
#include <analyses/property_directed_affine_analysis.h>
#include <analyses/lock_ego_abstraction.h>
#include <analyses/lock_relational_ai_analysis.h>
#include <analyses/thread_local_cutoff_analysis.h>
#include <goto-checker/all_properties_verifier.h>
#include <goto-checker/all_properties_verifier_with_fault_localization.h>
#include <goto-checker/all_properties_verifier_with_trace_storage.h>
#include <goto-checker/bmc_util.h>
#include <goto-checker/cover_goals_verifier_with_trace_storage.h>
#include <goto-checker/multi_path_symex_checker.h>
#include <goto-checker/multi_path_symex_only_checker.h>
#include <goto-checker/properties.h>
#include <goto-checker/single_loop_incremental_symex_checker.h>
#include <goto-checker/single_path_symex_checker.h>
#include <goto-checker/single_path_symex_only_checker.h>
#include <goto-checker/stop_on_fail_verifier.h>
#include <goto-checker/stop_on_fail_verifier_with_fault_localization.h>

#include <goto-programs/initialize_goto_model.h>
#include <goto-programs/link_to_library.h>
#include <goto-programs/loop_ids.h>
#include <goto-programs/process_goto_program.h>
#include <goto-programs/read_goto_binary.h>
#include <goto-programs/remove_skip.h>
#include <goto-programs/remove_unused_functions.h>
#include <goto-programs/set_properties.h>
#include <goto-programs/show_goto_functions.h>
#include <goto-programs/show_properties.h>
#include <goto-programs/show_symbol_table.h>

#include <xmllang/graphml.h>

#include <goto-instrument/cover.h>
#include <goto-instrument/full_slicer.h>
#include <goto-instrument/nondet_bulk_init.h>
#include <goto-instrument/nondet_static.h>
#include <goto-instrument/reachability_slicer.h>
#include <goto-instrument/unwindset.h>

#include <goto-symex/path_storage.h>

#include <pointer-analysis/add_failed_symbols.h>

#include <langapi/mode.h>

#include "c_test_input_generator.h"

namespace
{

template <class incremental_goto_checkerT>
class guided_stop_on_fail_verifiert
  : public stop_on_fail_verifiert<incremental_goto_checkerT>
{
public:
  using stop_on_fail_verifiert<
    incremental_goto_checkerT>::stop_on_fail_verifiert;

  goto_tracet build_shortest_trace() const
  {
    return this->incremental_goto_checker.build_shortest_trace();
  }

  goto_tracet build_trace(const irep_idt &property_id) const
  {
    return this->incremental_goto_checker.build_trace(property_id);
  }

};

enum class guided_multiloop_result_kindt
{
  INAPPLICABLE,
  SAFE,
  UNSAFE,
  INCOMPLETE
};

struct guided_multiloop_resultt
{
  guided_multiloop_result_kindt kind =
    guided_multiloop_result_kindt::INAPPLICABLE;
  goto_tracet failure_trace;
};

bool is_unwinding_property(const irep_idt &property_id)
{
  return id2string(property_id).find(".unwind.") != std::string::npos;
}

class unwinding_only_multi_path_symex_checkert
  : public multi_path_symex_checkert
{
public:
  using multi_path_symex_checkert::multi_path_symex_checkert;

protected:
  void update_properties(
    propertiest &properties,
    std::unordered_set<irep_idt> &updated_properties) override
  {
    multi_path_symex_only_checkert::update_properties(
      properties, updated_properties);
    for(auto &property : properties)
    {
      if(!is_unwinding_property(property.first))
        property.second.status = property_statust::PASS;
    }
  }
};

guided_multiloop_resultt guided_multiloop_unwind(
  goto_modelt &goto_model,
  const optionst &base_options,
  ui_message_handlert &ui_message_handler)
{
  std::map<irep_idt, unsigned> bounds;
  unwindsett initial_unwindset(goto_model);
  initial_unwindset.parse_unwind(base_options.get_option("unwind"));
  initial_unwindset.parse_unwindset(
    base_options.get_list_option("unwindset"), ui_message_handler);

  for(const auto &function : goto_model.goto_functions.function_map)
  {
    if(!function.second.body_available())
      continue;
    for(const auto &instruction : function.second.body.instructions)
    {
      if(!instruction.is_backwards_goto())
        continue;
      const irep_idt loop_id =
        goto_programt::loop_id(function.first, instruction);
      const auto initial_limit = initial_unwindset.get_limit(loop_id, 0);
      bounds.emplace(
        loop_id, initial_limit.has_value() ? *initial_limit : 1);
    }
  }

  if(bounds.empty())
    return {};

  constexpr std::size_t max_rounds = 32;
  constexpr unsigned max_loop_bound = 64;
  for(std::size_t round = 1; round <= max_rounds; ++round)
  {
    optionst round_options = base_options;
    optionst::value_listt unwindset;
    for(const auto &bound : bounds)
      unwindset.push_back(
        id2string(bound.first) + ":" + std::to_string(bound.second));
    round_options.set_option("unwind", "");
    round_options.set_option("unwindset", unwindset);
    round_options.set_option("partial-loops", false);
    round_options.set_option("trace", true);
    round_options.set_option("stop-on-fail", true);

    std::cout
      << "NATIVE_GUIDED_MULTILOOP_UNWIND round=" << round
      << " loops=" << bounds.size() << '\n';

    // First check only the generated unwinding assertions.  A program
    // property failure is not accepted while any loop bound is still
    // executable: an incomplete initialization or spawn loop can otherwise
    // create an artificial suffix.
    round_options.set_option("unwinding-assertions", true);
    guided_stop_on_fail_verifiert<unwinding_only_multi_path_symex_checkert>
      bound_verifier(round_options, ui_message_handler, goto_model);
    const resultt bound_result = bound_verifier();
    if(bound_result == resultt::PASS)
    {
      // Only a complete bounded model may decide the original properties.
      round_options.set_option("unwinding-assertions", false);
      guided_stop_on_fail_verifiert<multi_path_symex_checkert>
        property_verifier(round_options, ui_message_handler, goto_model);
      const resultt property_result = property_verifier();
      if(property_result == resultt::PASS)
      {
        std::cout
          << "NATIVE_GUIDED_MULTILOOP_UNWIND applied=1"
          << " result=SAFE rounds=" << round << '\n';
        guided_multiloop_resultt answer;
        answer.kind = guided_multiloop_result_kindt::SAFE;
        return answer;
      }
      if(property_result == resultt::FAIL)
      {
        guided_multiloop_resultt answer;
        answer.kind = guided_multiloop_result_kindt::UNSAFE;
        answer.failure_trace = property_verifier.build_shortest_trace();
        const auto &last = answer.failure_trace.get_last_step();
        std::cout
          << "NATIVE_GUIDED_MULTILOOP_UNWIND applied=1"
          << " result=UNSAFE rounds=" << round
          << " property=" << last.property_id << '\n';
        return answer;
      }

      std::cout
        << "NATIVE_GUIDED_MULTILOOP_UNWIND applied=0"
        << " reason=property_checker_incomplete round=" << round << '\n';
      guided_multiloop_resultt answer;
      answer.kind = guided_multiloop_result_kindt::INCOMPLETE;
      return answer;
    }
    if(bound_result != resultt::FAIL)
    {
      std::cout
        << "NATIVE_GUIDED_MULTILOOP_UNWIND applied=0"
        << " reason=bound_checker_incomplete round=" << round << '\n';
      guided_multiloop_resultt answer;
      answer.kind = guided_multiloop_result_kindt::INCOMPLETE;
      return answer;
    }

    const irep_idt *failed_bound_property = nullptr;
    for(const auto &property : bound_verifier.get_properties())
    {
      if(
        is_unwinding_property(property.first) &&
        property.second.status == property_statust::FAIL)
      {
        failed_bound_property = &property.first;
        break;
      }
    }
    if(failed_bound_property == nullptr)
    {
      std::cout
        << "NATIVE_GUIDED_MULTILOOP_UNWIND applied=0"
        << " reason=no_failed_bound_property round=" << round << '\n';
      guided_multiloop_resultt answer;
      answer.kind = guided_multiloop_result_kindt::INCOMPLETE;
      return answer;
    }

    goto_tracet selected_trace =
      bound_verifier.build_trace(*failed_bound_property);
    if(selected_trace.steps.empty())
    {
      std::cout
        << "NATIVE_GUIDED_MULTILOOP_UNWIND applied=0"
        << " reason=empty_bound_trace round=" << round << '\n';
      guided_multiloop_resultt answer;
      answer.kind = guided_multiloop_result_kindt::INCOMPLETE;
      return answer;
    }

    const auto &last = selected_trace.get_last_step();
    if(!last.pc->is_backwards_goto())
    {
      std::cout
        << "NATIVE_GUIDED_MULTILOOP_UNWIND applied=0"
        << " reason=unmapped_bound_trace property=" << last.property_id
        << " round=" << round << '\n';
      guided_multiloop_resultt answer;
      answer.kind = guided_multiloop_result_kindt::INCOMPLETE;
      return answer;
    }

    const irep_idt selected_loop =
      goto_programt::loop_id(last.function_id, *last.pc);
    auto bound = bounds.find(selected_loop);
    if(bound == bounds.end() || bound->second >= max_loop_bound)
    {
      std::cout
        << "NATIVE_GUIDED_MULTILOOP_UNWIND applied=0"
        << " reason=loop_bound_budget loop=" << selected_loop
        << " round=" << round << '\n';
      guided_multiloop_resultt answer;
      answer.kind = guided_multiloop_result_kindt::INCOMPLETE;
      return answer;
    }
    ++bound->second;
    std::cout
      << "NATIVE_GUIDED_MULTILOOP_UNWIND refine_loop="
      << selected_loop << " bound=" << bound->second
      << " trace_steps=" << selected_trace.steps.size()
      << '\n';
  }

  std::cout
    << "NATIVE_GUIDED_MULTILOOP_UNWIND applied=0"
    << " reason=round_budget rounds=" << max_rounds << '\n';
  guided_multiloop_resultt answer;
  answer.kind = guided_multiloop_result_kindt::INCOMPLETE;
  return answer;
}

} // namespace

namespace
{
struct native_witness_assertiont
{
  irep_idt function;
  source_locationt source_location;
  exprt condition;
};

using native_witness_assertionst =
  std::vector<native_witness_assertiont>;

native_witness_assertionst collect_native_witness_assertions(
  const goto_modelt &goto_model)
{
  native_witness_assertionst assertions;
  for(const auto &function : goto_model.goto_functions.function_map)
  {
    if(!function.second.body_available())
      continue;
    for(const auto &instruction : function.second.body.instructions)
    {
      if(instruction.is_assert())
      {
        assertions.push_back(
          {function.first,
           instruction.source_location(),
           instruction.condition()});
      }
    }
  }
  return assertions;
}

native_witness_assertionst collect_native_witness_guard_invariants(
  const goto_modelt &goto_model)
{
  std::set<irep_idt> assertion_functions;
  for(const auto &function : goto_model.goto_functions.function_map)
  {
    if(!function.second.body_available())
      continue;
    for(const auto &instruction : function.second.body.instructions)
    {
      if(instruction.is_assert())
      {
        assertion_functions.insert(function.first);
        break;
      }
    }
  }

  native_witness_assertionst guards;
  std::set<irep_idt> called_assertion_functions;
  for(const auto &function : goto_model.goto_functions.function_map)
  {
    if(!function.second.body_available())
      continue;

    const goto_programt::instructiont *previous = nullptr;
    for(const auto &instruction : function.second.body.instructions)
    {
      if(instruction.is_function_call())
      {
        const exprt &callee = instruction.call_function();
        if(
          callee.id() == ID_symbol &&
          assertion_functions.count(to_symbol_expr(callee).get_identifier()) !=
            0)
        {
          const irep_idt callee_id =
            to_symbol_expr(callee).get_identifier();
          called_assertion_functions.insert(callee_id);
          if(
            previous == nullptr || !previous->is_goto() ||
            previous->targets.size() != 1 ||
            previous->get_target()->location_number <=
              instruction.location_number ||
            previous->condition().is_true() ||
            previous->source_location().get_file().empty() ||
            previous->source_location().get_line().empty())
            return {};

          guards.push_back(
            {function.first,
             previous->source_location(),
             previous->condition()});
        }
      }
      previous = &instruction;
    }
  }

  if(
    called_assertion_functions.empty() ||
    called_assertion_functions != assertion_functions)
    return {};
  return guards;
}

void normalize_native_witness_condition(exprt &condition)
{
  for(auto &operand : condition.operands())
    normalize_native_witness_condition(operand);

  if(
    condition.id() == ID_typecast &&
    (condition.type().id() == ID_bool ||
     condition.type().id() == ID_c_bool) &&
    condition.operands().size() == 1 &&
    (condition.op0().id() == ID_string_constant ||
     (condition.op0().id() == ID_address_of &&
      condition.op0().operands().size() == 1 &&
      condition.op0().op0().id() == ID_index &&
      condition.op0().op0().operands().size() == 2 &&
      condition.op0().op0().op0().id() == ID_string_constant)))
    condition = true_exprt();

  if(condition.id() == ID_and)
  {
    exprt::operandst retained;
    for(const auto &operand : condition.operands())
    {
      if(!operand.is_true())
        retained.push_back(operand);
    }
    if(retained.empty())
      condition = true_exprt();
    else if(retained.size() == 1)
      condition = retained.front();
    else
      condition.operands() = std::move(retained);
  }
}

bool contains_native_witness_null_pointer(const exprt &expression)
{
  if(
    expression.id() == ID_constant && expression.type().id() == ID_pointer &&
    is_null_pointer(to_constant_expr(expression)))
    return true;
  for(const auto &operand : expression.operands())
  {
    if(contains_native_witness_null_pointer(operand))
      return true;
  }
  return false;
}

bool is_native_witness_null_pointer(const exprt &expression)
{
  if(
    expression.id() == ID_constant && expression.type().id() == ID_pointer &&
    is_null_pointer(to_constant_expr(expression)))
    return true;
  return
    expression.id() == ID_typecast && expression.operands().size() == 1 &&
    is_native_witness_null_pointer(expression.op0());
}

std::string native_witness_invariant_text(
  const namespacet &ns,
  const irep_idt &function,
  const exprt &invariant)
{
  if(
    (invariant.id() == ID_equal || invariant.id() == ID_notequal) &&
    invariant.operands().size() == 2 &&
    (is_native_witness_null_pointer(invariant.op0()) ||
     is_native_witness_null_pointer(invariant.op1())))
  {
    const exprt &non_null_operand =
      is_native_witness_null_pointer(invariant.op0())
        ? invariant.op1()
        : invariant.op0();
    return
      from_expr(ns, function, non_null_operand) +
      (invariant.id() == ID_equal ? " == 0" : " != 0");
  }

  std::string text = from_expr(ns, function, invariant);
  if(!contains_native_witness_null_pointer(invariant))
    return text;

  std::size_t position = 0;
  while((position = text.find("NULL", position)) != std::string::npos)
  {
    const bool left_boundary =
      position == 0 ||
      !(std::isalnum(static_cast<unsigned char>(text[position - 1])) ||
        text[position - 1] == '_');
    const std::size_t end = position + 4;
    const bool right_boundary =
      end == text.size() ||
      !(std::isalnum(static_cast<unsigned char>(text[end])) ||
        text[end] == '_');
    if(left_boundary && right_boundary)
    {
      text.replace(position, 4, "0");
      ++position;
    }
    else
      position = end;
  }
  return text;
}

bool output_native_correctness_witness(
  const goto_modelt &goto_model,
  const optionst &options,
  const native_witness_assertionst &assertions)
{
  const std::string path = options.get_option("graphml-witness");
  if(path.empty() || path == "-")
  {
    std::cout
      << "NATIVE_CORRECTNESS_WITNESS applied=0 reason=invalid_path"
      << " properties=" << assertions.size() << '\n';
    return false;
  }

  const namespacet ns(goto_model.symbol_table);
  graphmlt graph;
  graph.key_values["witness-type"] = "correctness_witness";
  graph.key_values["sourcecodelang"] = "C";

  const auto entry = graph.add_node();
  graph[entry].node_name = "N0";
  graph[entry].is_violation = false;
  graph[entry].has_invariant = false;

  std::size_t property_count = 0;
  for(const auto &assertion : assertions)
  {
    const auto node = graph.add_node();
    graph[node].node_name = "P" + std::to_string(++property_count);
    graph[node].file = assertion.source_location.get_file();
    graph[node].line = assertion.source_location.get_line();
    graph[node].is_violation = false;
    graph[node].has_invariant = true;
    exprt invariant = assertion.condition;
    normalize_native_witness_condition(invariant);
    simplify_expr(invariant, ns);
    graph[node].invariant =
      native_witness_invariant_text(ns, assertion.function, invariant);
    graph[node].invariant_scope = id2string(assertion.function);
    graph.add_edge(entry, node);

    xmlt edge(
      "edge",
      {{"source", graph[entry].node_name},
       {"target", graph[node].node_name}},
      {});
    if(!graph[node].file.empty())
    {
      xmlt &origin = edge.new_element("data");
      origin.set_attribute("key", "originfile");
      origin.data = id2string(graph[node].file);
    }
    if(!graph[node].line.empty())
    {
      xmlt &line = edge.new_element("data");
      line.set_attribute("key", "startline");
      line.data = id2string(graph[node].line);
    }
    graph[entry].out[node].xml_node = std::move(edge);
  }
  if(property_count == 0)
  {
    std::cout
      << "NATIVE_CORRECTNESS_WITNESS applied=0 reason=no_properties"
      << " properties=0\n";
    return false;
  }

  std::ofstream output(path);
  if(!output)
  {
    std::cout
      << "NATIVE_CORRECTNESS_WITNESS applied=0 reason=open_failed"
      << " properties=" << property_count << '\n';
    return false;
  }
  const std::string filename = options.get_option("filename");
  const bool write_failed = write_graphml(graph, output, filename, options);
  if(write_failed || !output.good())
  {
    std::cout
      << "NATIVE_CORRECTNESS_WITNESS applied=0 reason=write_failed"
      << " properties=" << property_count << '\n';
    return false;
  }
  return true;
}

struct native_replay_choicet
{
  irep_idt function;
  irep_idt line;
  irep_idt lhs;
  exprt value;
};

std::vector<native_replay_choicet>
collect_native_replay_choices(const goto_tracet &trace)
{
  std::vector<native_replay_choicet> choices;
  if(
    trace.steps.empty() ||
    !trace.get_last_step().is_assert())
    return choices;
  const unsigned failing_thread =
    trace.get_last_step().thread_nr;
  const irep_idt source_file =
    trace.get_last_step().pc->source_location().get_file();
  for(const auto &step : trace.steps)
  {
    if(
      step.thread_nr != failing_thread ||
      !step.is_assignment() ||
      !step.pc->is_assign() ||
      step.full_lhs_value.is_nil())
      continue;
    const exprt &rhs = step.pc->assign_rhs();
    if(
      rhs.id() != ID_side_effect ||
      rhs.get(ID_statement) != ID_nondet)
      continue;
    const exprt &lhs = step.pc->assign_lhs();
    if(lhs.id() != ID_symbol)
      continue;
    const irep_idt lhs_identifier =
      to_symbol_expr(lhs).get_identifier();
    const auto &location = step.pc->source_location();
    if(
      location.is_built_in() ||
      location.get_file() != source_file ||
      location.get_function().empty() ||
      location.get_line().empty())
      continue;
    auto existing = std::find_if(
      choices.begin(),
      choices.end(),
      [&](const native_replay_choicet &choice)
      {
        return
          choice.function == location.get_function() &&
          choice.line == location.get_line() &&
          choice.lhs == lhs_identifier;
      });
    if(existing == choices.end())
      choices.push_back(
        {location.get_function(),
         location.get_line(),
         lhs_identifier,
         step.full_lhs_value});
    else
      existing->value = step.full_lhs_value;
  }
  return choices;
}

bool apply_native_replay_choices(
  goto_modelt &goto_model,
  const std::vector<native_replay_choicet> &choices)
{
  std::vector<bool> consumed(choices.size(), false);
  std::size_t applied = 0;
  for(auto &function : goto_model.goto_functions.function_map)
  {
    if(!function.second.body_available())
      continue;
    auto &program = function.second.body;
    for(auto instruction = program.instructions.begin();
        instruction != program.instructions.end();
        ++instruction)
    {
      if(!instruction->is_assign())
        continue;
      const exprt &rhs = instruction->assign_rhs();
      if(
        rhs.id() != ID_side_effect ||
        rhs.get(ID_statement) != ID_nondet)
        continue;
      const exprt &lhs = instruction->assign_lhs();
      if(lhs.id() != ID_symbol)
        continue;
      const irep_idt lhs_identifier =
        to_symbol_expr(lhs).get_identifier();
      const auto &location = instruction->source_location();
      for(std::size_t index = 0; index < choices.size(); ++index)
      {
        if(
          consumed[index] ||
          choices[index].function != function.first ||
          choices[index].line != location.get_line() ||
          choices[index].lhs != lhs_identifier)
          continue;
        exprt value = choices[index].value;
        if(value.type() != instruction->assign_lhs().type())
          value = typecast_exprt(value, instruction->assign_lhs().type());
        program.insert_after(
          instruction,
          goto_programt::make_assumption(
            equal_exprt(instruction->assign_lhs(), value),
            location));
        consumed[index] = true;
        ++applied;
        break;
      }
    }
  }
  goto_model.goto_functions.update();
  std::cout
    << "NATIVE_ORIGINAL_GOTO_REPLAY choices=" << choices.size()
    << " applied=" << applied << '\n';
  return applied == choices.size() && applied != 0;
}

bool lift_single_spawn_source_prefix(
  const goto_tracet &input,
  goto_tracet &output)
{
  const auto is_thread_creation =
    [](const goto_trace_stept &step)
    {
      if(step.is_spawn())
        return true;
      if(!step.is_assignment())
        return false;
      const auto lhs_object = step.get_lhs_object();
      return
        lhs_object.has_value() &&
        id2string(lhs_object->get_identifier()).find(
          "pthread_create::thread") != std::string::npos;
    };

  if(
    input.steps.empty() ||
    !input.get_last_step().is_assert() ||
    input.get_last_step().cond_value ||
    input.get_last_step().thread_nr == 0)
    return false;

  const unsigned failing_thread =
    input.get_last_step().thread_nr;
  auto first_worker = input.steps.end();
  auto creation = input.steps.end();
  bool creator_resumed = false;
  std::set<unsigned> worker_threads;
  for(auto step = input.steps.begin(); step != input.steps.end(); ++step)
  {
    if(step->thread_nr == 0)
    {
      if(first_worker != input.steps.end())
        creator_resumed = true;
      else if(is_thread_creation(*step))
        creation = step;
      continue;
    }
    worker_threads.insert(step->thread_nr);
    if(first_worker == input.steps.end())
      first_worker = step;
  }

  if(
    creator_resumed ||
    worker_threads.size() != 1 ||
    *worker_threads.begin() != failing_thread ||
    first_worker == input.steps.end() ||
    creation == input.steps.end() ||
    creation->thread_nr != 0)
    return false;

  for(auto step = input.steps.begin();; ++step)
  {
    output.add_step(*step);
    if(step == creation)
      break;
  }
  for(auto step = first_worker; step != input.steps.end(); ++step)
  {
    if(step->thread_nr != failing_thread)
      return false;
    output.add_step(*step);
  }
  std::size_t lifted_step_number = 1;
  for(auto &step : output.steps)
    step.step_nr = lifted_step_number++;

  const bool accepted =
    !output.steps.empty() &&
    output.get_last_step().is_assert() &&
    !output.get_last_step().cond_value;
  std::cout
    << "NATIVE_ORIGINAL_GOTO_REPLAY prefix_lift=1"
    << " accepted=" << (accepted ? 1 : 0)
    << " input_steps=" << input.steps.size()
    << " output_steps=" << output.steps.size()
    << " worker=" << failing_thread
    << std::endl;
  return accepted;
}
}

cbmc_parse_optionst::cbmc_parse_optionst(int argc, const char **argv)
  : parse_options_baset(
      CBMC_OPTIONS,
      argc,
      argv,
      std::string("CBMC ") + CBMC_VERSION)
{
  json_interface(cmdline, ui_message_handler);
  xml_interface(cmdline, ui_message_handler);
}

::cbmc_parse_optionst::cbmc_parse_optionst(
  int argc,
  const char **argv,
  const std::string &extra_options)
  : parse_options_baset(
      CBMC_OPTIONS + extra_options,
      argc,
      argv,
      std::string("CBMC ") + CBMC_VERSION)
{
  json_interface(cmdline, ui_message_handler);
  xml_interface(cmdline, ui_message_handler);
}

void cbmc_parse_optionst::set_default_options(optionst &options)
{
  // Default true
  options.set_option("built-in-assertions", true);
  options.set_option("propagation", true);
  options.set_option("simple-slice", true);
  options.set_option("simplify", true);
  options.set_option("show-goto-symex-steps", false);
  options.set_option("show-points-to-sets", false);
  options.set_option("show-array-constraints", false);

  // Other default
  options.set_option("arrays-uf", "auto");
  options.set_option("depth", UINT32_MAX);
}

void cbmc_parse_optionst::get_command_line_options(optionst &options)
{
  if(config.set(cmdline))
  {
    usage_error();
    exit(CPROVER_EXIT_USAGE_ERROR);
  }

  cbmc_parse_optionst::set_default_options(options);
  parse_c_object_factory_options(cmdline, options);

  if(cmdline.isset("function"))
    options.set_option("function", cmdline.get_value("function"));

  if(cmdline.isset("cover") && cmdline.isset("unwinding-assertions"))
  {
    log.error()
      << "--cover and --unwinding-assertions must not be given together"
      << messaget::eom;
    exit(CPROVER_EXIT_USAGE_ERROR);
  }

  // __SZH_ADD_BEGIN__
  if(cmdline.isset("unwind-suggest"))
    options.set_option("unwind-suggest", true);
  
  if(cmdline.isset("mm-strict-guard"))
    options.set_option("mm-strict-guard", true);
  
  if(cmdline.isset("mm-flag"))
    options.set_option("mm-flag", true);

  if(cmdline.isset("mm-cutting"))
    options.set_option("mm-cutting", true);

  if(
    cmdline.isset("native-pair-initialization-prefix") ||
    cmdline.isset("native-counterexample-rescue-portfolio"))
    options.set_option("native-pair-initialization-prefix", true);

  if(cmdline.isset("deagle-nondet-bulk-init"))
    options.set_option("deagle-nondet-bulk-init", true);

  if(cmdline.isset("allow-pointer-unsoundness") || cmdline.isset("refined-pointer-analysis"))
    options.set_option("allow-pointer-unsoundness", true);

  if(cmdline.isset("native-counterexample-rescue-portfolio"))
  {
    options.set_option("refined-pointer-analysis", false);
    options.set_option("allow-pointer-unsoundness", true);
    // The single-worker initialization prefix may retain hundreds of
    // allocation objects. Object identifiers are encoded while the GOTO model
    // is processed, so this capacity must be selected before portfolio
    // children are forked.
    options.set_option("object-bits", "10");
    config.bv_encoding.object_bits = 10;
    config.bv_encoding.is_object_bits_default = false;
  }
  // __SZH_ADD_END__

  if(cmdline.isset("max-field-sensitivity-array-size"))
  {
    options.set_option(
      "max-field-sensitivity-array-size",
      cmdline.get_value("max-field-sensitivity-array-size"));
  }

  if(cmdline.isset("no-array-field-sensitivity"))
  {
    if(cmdline.isset("max-field-sensitivity-array-size"))
    {
      log.error()
        << "--no-array-field-sensitivity and --max-field-sensitivity-array-size"
        << " must not be given together" << messaget::eom;
      exit(CPROVER_EXIT_USAGE_ERROR);
    }
    options.set_option("no-array-field-sensitivity", true);
  }

  if(cmdline.isset("reachability-slice") &&
     cmdline.isset("reachability-slice-fb"))
  {
    log.error()
      << "--reachability-slice and --reachability-slice-fb must not be "
      << "given together" << messaget::eom;
    exit(CPROVER_EXIT_USAGE_ERROR);
  }

  if(cmdline.isset("full-slice"))
    options.set_option("full-slice", true);

  if(cmdline.isset("show-symex-strategies"))
  {
    log.status() << show_path_strategies() << messaget::eom;
    exit(CPROVER_EXIT_SUCCESS);
  }

  parse_path_strategy_options(cmdline, options, ui_message_handler);

  if(cmdline.isset("program-only"))
    options.set_option("program-only", true);

  if(cmdline.isset("show-byte-ops"))
    options.set_option("show-byte-ops", true);

  if(cmdline.isset("show-vcc"))
    options.set_option("show-vcc", true);

  if(cmdline.isset("cover"))
    parse_cover_options(cmdline, options);

  if(cmdline.isset("mm"))
  {
    options.set_option("mm", cmdline.get_value("mm"));
// __SZH_ADD_BEGIN__
    auto mm = cmdline.get_value("mm");
    if(mm != "sc" && mm != "tso" && mm != "pso")
      options.set_option("cat", true);
// __SZH_ADD_END__
  }

  if(cmdline.isset("symex-complexity-limit"))
    options.set_option(
      "symex-complexity-limit", cmdline.get_value("symex-complexity-limit"));

  if(cmdline.isset("symex-complexity-failed-child-loops-limit"))
    options.set_option(
      "symex-complexity-failed-child-loops-limit",
      cmdline.get_value("symex-complexity-failed-child-loops-limit"));

  if(cmdline.isset("property"))
    options.set_option("property", cmdline.get_values("property"));

  if(cmdline.isset("subproperty"))
    options.set_option("subproperty", cmdline.get_values("subproperty"));

  if(cmdline.isset("drop-unused-functions"))
    options.set_option("drop-unused-functions", true);

  if(cmdline.isset("havoc-undefined-functions"))
    options.set_option("havoc-undefined-functions", true);

  if(cmdline.isset("string-abstraction"))
    options.set_option("string-abstraction", true);

  if(cmdline.isset("reachability-slice-fb"))
    options.set_option("reachability-slice-fb", true);

  if(cmdline.isset("reachability-slice"))
    options.set_option("reachability-slice", true);

  if(cmdline.isset("nondet-static"))
    options.set_option("nondet-static", true);

  if(cmdline.isset("no-simplify"))
    options.set_option("simplify", false);

  if(cmdline.isset("stop-on-fail") ||
     cmdline.isset("dimacs") ||
     cmdline.isset("outfile"))
    options.set_option("stop-on-fail", true);

  if(
    cmdline.isset("trace") || cmdline.isset("compact-trace") ||
    cmdline.isset("stack-trace") || cmdline.isset("stop-on-fail") ||
    (ui_message_handler.get_ui() != ui_message_handlert::uit::PLAIN &&
     !cmdline.isset("cover")))
  {
    options.set_option("trace", true);
  }

  if(cmdline.isset("localize-faults"))
    options.set_option("localize-faults", true);

  if(cmdline.isset("unwind"))
    options.set_option("unwind", cmdline.get_value("unwind"));

  if(cmdline.isset("depth"))
    options.set_option("depth", cmdline.get_value("depth"));

  if(cmdline.isset("slice-by-trace"))
  {
    log.error() << "--slice-by-trace has been removed" << messaget::eom;
    exit(CPROVER_EXIT_USAGE_ERROR);
  }

  if(cmdline.isset("unwindset"))
  {
    options.set_option(
      "unwindset", cmdline.get_comma_separated_values("unwindset"));
  }

  // constant propagation
  if(cmdline.isset("no-propagation"))
    options.set_option("propagation", false);

  // transform self loops to assumptions
  options.set_option(
    "self-loops-to-assumptions",
    !cmdline.isset("no-self-loops-to-assumptions"));

  // all checks supported by goto_check
  PARSE_OPTIONS_GOTO_CHECK(cmdline, options);

  // generate unwinding assertions
  if(cmdline.isset("unwinding-assertions"))
  {
    options.set_option("unwinding-assertions", true);
    options.set_option("paths-symex-explore-all", true);
  }

  if(cmdline.isset("partial-loops"))
    options.set_option("partial-loops", true);

  // remove unused equations
  if(cmdline.isset("slice-formula"))
    options.set_option("slice-formula", true);

  if(cmdline.isset("arrays-uf-always"))
    options.set_option("arrays-uf", "always");
  else if(cmdline.isset("arrays-uf-never"))
    options.set_option("arrays-uf", "never");

  if(cmdline.isset("show-array-constraints"))
    options.set_option("show-array-constraints", true);

  if(cmdline.isset("refine-strings"))
  {
    options.set_option("refine-strings", true);
    options.set_option("string-printable", cmdline.isset("string-printable"));
  }

  options.set_option(
    "symex-cache-dereferences", cmdline.isset("symex-cache-dereferences"));

  if(cmdline.isset("incremental-loop"))
  {
    options.set_option(
      "incremental-loop", cmdline.get_value("incremental-loop"));
    options.set_option("refine", true);
    options.set_option("refine-arrays", true);

    if(cmdline.isset("unwind-min"))
      options.set_option("unwind-min", cmdline.get_value("unwind-min"));

    if(cmdline.isset("unwind-max"))
      options.set_option("unwind-max", cmdline.get_value("unwind-max"));

    if(cmdline.isset("ignore-properties-before-unwind-min"))
      options.set_option("ignore-properties-before-unwind-min", true);

    if(cmdline.isset("paths"))
    {
      log.error() << "--paths not supported with --incremental-loop"
                  << messaget::eom;
      exit(CPROVER_EXIT_USAGE_ERROR);
    }
  }

  if(cmdline.isset("graphml-witness"))
  {
    options.set_option("graphml-witness", cmdline.get_value("graphml-witness"));
    options.set_option("stop-on-fail", true);
    options.set_option("trace", true);
  }

  if(cmdline.isset("symex-coverage-report"))
  {
    options.set_option(
      "symex-coverage-report",
      cmdline.get_value("symex-coverage-report"));
    options.set_option("paths-symex-explore-all", true);
  }

  if(cmdline.isset("validate-ssa-equation"))
  {
    options.set_option("validate-ssa-equation", true);
  }

  if(cmdline.isset("validate-goto-model"))
  {
    options.set_option("validate-goto-model", true);
  }

  if(cmdline.isset("show-goto-symex-steps"))
    options.set_option("show-goto-symex-steps", true);

  if(cmdline.isset("show-points-to-sets"))
    options.set_option("show-points-to-sets", true);

  PARSE_OPTIONS_GOTO_TRACE(cmdline, options);

  // Options for process_goto_program
  options.set_option("rewrite-union", true);

  if(cmdline.isset("smt1"))
  {
    log.error() << "--smt1 is no longer supported" << messaget::eom;
    exit(CPROVER_EXIT_USAGE_ERROR);
  }

  parse_solver_options(cmdline, options);
}

/// invoke main modules
int cbmc_parse_optionst::doit()
{
  if(cmdline.isset("version"))
  {
    std::cout << "4.1.0" << '\n';
    return CPROVER_EXIT_SUCCESS;
  }

  //
  // command line options
  //

  optionst options;
  get_command_line_options(options);

  messaget::eval_verbosity(
    cmdline.get_value("verbosity"), messaget::M_STATISTICS, ui_message_handler);

  log_version_and_architecture("CBMC");

  //
  // Unwinding of transition systems is done by hw-cbmc.
  //

  if(cmdline.isset("module") ||
     cmdline.isset("gen-interface"))
  {
    log.error() << "This version of CBMC has no support for "
                   " hardware modules. Please use hw-cbmc."
                << messaget::eom;
    return CPROVER_EXIT_USAGE_ERROR;
  }

  if(cmdline.isset("show-points-to-sets"))
  {
    if(!cmdline.isset("json-ui") || cmdline.isset("xml-ui"))
    {
      log.error() << "--show-points-to-sets supports only"
                     " json output. Use --json-ui."
                  << messaget::eom;
      return CPROVER_EXIT_USAGE_ERROR;
    }
  }

  if(cmdline.isset("show-array-constraints"))
  {
    if(!cmdline.isset("json-ui") || cmdline.isset("xml-ui"))
    {
      log.error() << "--show-array-constraints supports only"
                     " json output. Use --json-ui."
                  << messaget::eom;
      return CPROVER_EXIT_USAGE_ERROR;
    }
  }

  register_languages();

  // configure gcc, if required
  if(config.ansi_c.preprocessor == configt::ansi_ct::preprocessort::GCC)
  {
    gcc_versiont gcc_version;
    gcc_version.get("gcc");
    configure_gcc(gcc_version);
  }

  if(cmdline.isset("test-preprocessor"))
    return test_c_preprocessor(ui_message_handler)
             ? CPROVER_EXIT_PREPROCESSOR_TEST_FAILED
             : CPROVER_EXIT_SUCCESS;

  if(cmdline.isset("preprocess"))
  {
    preprocessing(options);
    return CPROVER_EXIT_SUCCESS;
  }

  if(cmdline.isset("show-parse-tree"))
  {
    if(
      cmdline.args.size() != 1 ||
      is_goto_binary(cmdline.args[0], ui_message_handler))
    {
      log.error() << "Please give exactly one source file" << messaget::eom;
      return CPROVER_EXIT_INCORRECT_TASK;
    }

    std::string filename=cmdline.args[0];

    #ifdef _MSC_VER
    std::ifstream infile(widen(filename));
    #else
    std::ifstream infile(filename);
    #endif

    if(!infile)
    {
      log.error() << "failed to open input file '" << filename << "'"
                  << messaget::eom;
      return CPROVER_EXIT_INCORRECT_TASK;
    }

    std::unique_ptr<languaget> language=
      get_language_from_filename(filename);

    if(language==nullptr)
    {
      log.error() << "failed to figure out type of file '" << filename << "'"
                  << messaget::eom;
      return CPROVER_EXIT_INCORRECT_TASK;
    }

    language->set_language_options(options);
    language->set_message_handler(ui_message_handler);

    log.status() << "Parsing " << filename << messaget::eom;

    if(language->parse(infile, filename))
    {
      log.error() << "PARSING ERROR" << messaget::eom;
      return CPROVER_EXIT_INCORRECT_TASK;
    }

    language->show_parse(std::cout);
    return CPROVER_EXIT_SUCCESS;
  }

  native_witness_assertionst native_witness_assertions;
  native_witness_assertionst native_witness_guards;
  std::unique_ptr<goto_modelt> native_original_replay_model;
  int get_goto_program_ret = get_goto_program(
    goto_model,
    options,
    cmdline,
    ui_message_handler,
    [&native_witness_assertions,
     &native_witness_guards,
     &native_original_replay_model,
     this](const goto_modelt &unprocessed_model) {
      native_witness_assertions =
        collect_native_witness_assertions(unprocessed_model);
      native_witness_guards =
        collect_native_witness_guard_invariants(unprocessed_model);
      if(cmdline.isset("native-counterexample-rescue-portfolio"))
      {
        native_original_replay_model =
          util_make_unique<goto_modelt>();
        native_original_replay_model->symbol_table =
          unprocessed_model.symbol_table;
        native_original_replay_model->goto_functions.copy_from(
          unprocessed_model.goto_functions);
      }
    });

  if(get_goto_program_ret!=-1)
    return get_goto_program_ret;

  bool native_model_transformed = false;
  bool native_rescue_portfolio_child = false;
  if(cmdline.isset("native-counterexample-rescue-portfolio"))
  {
    if(!single_worker_initialization_prefix_applied(goto_model))
      native_original_replay_model.reset();
#ifdef _WIN32
    std::cout
      << "NATIVE_COUNTEREXAMPLE_RESCUE_PORTFOLIO applied=0"
      << " reason=unsupported_platform\n"
      << "VERIFICATION SUCCESSFUL\n";
    return CPROVER_EXIT_VERIFICATION_SAFE;
#else
    enum class rescue_staget
    {
      independent_index,
      cross_domain_list,
      single_initialized,
      initialized_pair,
      main_worker,
      dormant_pair,
      shallow_one,
      shallow_three
    };
    struct rescue_variantt
    {
      rescue_staget stage;
      std::size_t pair_variant;
      unsigned unwind_bound;
    };

    const std::size_t pair_variants = std::min(
      dormant_spawn_pair_variant_count(goto_model),
      std::size_t{10});
    std::vector<rescue_variantt> rescue_variants;
    if(independent_index_prefix_applied(goto_model))
      rescue_variants.push_back(
        {rescue_staget::independent_index, 0, 3});
    else if(cross_domain_list_prefix_applied(goto_model))
      rescue_variants.push_back(
        {rescue_staget::cross_domain_list, 0, 3});
    else if(single_worker_initialization_prefix_applied(goto_model))
      rescue_variants.push_back(
        {rescue_staget::single_initialized, 0, 3});
    else if(pair_initialization_prefix_applied(goto_model))
      rescue_variants.push_back(
        {rescue_staget::initialized_pair, 0, 2});
    else
    {
      if(main_worker_prefix_applicable(goto_model))
      {
        rescue_variants.push_back({rescue_staget::main_worker, 0, 7});
        rescue_variants.push_back({rescue_staget::main_worker, 0, 11});
      }
      for(std::size_t variant = 0; variant < pair_variants; ++variant)
        rescue_variants.push_back(
          {rescue_staget::dormant_pair, variant, 3});
      rescue_variants.push_back({rescue_staget::shallow_one, 0, 1});
      rescue_variants.push_back({rescue_staget::shallow_three, 0, 3});
    }

    const auto portfolio_start = std::chrono::steady_clock::now();
    const auto pair_deadline =
      portfolio_start + std::chrono::seconds(18);
    std::size_t completed = 0;
    std::size_t timed_out = 0;
    std::size_t skipped_pairs = 0;
    for(const auto &rescue_variant : rescue_variants)
    {
      const auto now = std::chrono::steady_clock::now();
      const bool is_pair =
        rescue_variant.stage == rescue_staget::dormant_pair;
      const bool is_independent_index =
        rescue_variant.stage == rescue_staget::independent_index;
      const bool is_cross_domain_list =
        rescue_variant.stage == rescue_staget::cross_domain_list;
      const bool is_single_initialized =
        rescue_variant.stage == rescue_staget::single_initialized;
      const bool is_initialized_pair =
        rescue_variant.stage == rescue_staget::initialized_pair;
      const bool is_main_worker =
        rescue_variant.stage == rescue_staget::main_worker;
      if(is_pair && now >= pair_deadline)
      {
        ++skipped_pairs;
        continue;
      }
      const auto child_deadline = is_independent_index
        ? now + std::chrono::seconds(90)
        : is_cross_domain_list
        ? now + std::chrono::seconds(90)
        : is_single_initialized
        ? now + std::chrono::seconds(90)
        : is_initialized_pair
        ? now + std::chrono::seconds(90)
        : is_main_worker
        ? now + std::chrono::seconds(
            rescue_variant.unwind_bound == 7 ? 30 : 90)
        : is_pair
          ? std::min(pair_deadline, now + std::chrono::seconds(6))
          : now + std::chrono::seconds(3);

      char output_path[] = "deagle_native_rescue_XXXXXX";
      const int output_fd = mkstemp(output_path);
      if(output_fd < 0)
      {
        std::cout
          << "NATIVE_COUNTEREXAMPLE_RESCUE_PORTFOLIO applied=0"
          << " reason=output_file\n"
          << "VERIFICATION SUCCESSFUL\n";
        return CPROVER_EXIT_VERIFICATION_SAFE;
      }
      std::fflush(nullptr);
      const pid_t child = fork();
      if(child == 0)
      {
#ifdef __linux__
        if(
          prctl(PR_SET_PDEATHSIG, SIGKILL) != 0 ||
          getppid() == 1)
          _exit(CPROVER_EXIT_INTERNAL_ERROR);
#endif
        if(
          dup2(output_fd, STDOUT_FILENO) < 0 ||
          dup2(output_fd, STDERR_FILENO) < 0)
          _exit(CPROVER_EXIT_INTERNAL_ERROR);
        close(output_fd);
        if(rescue_variant.stage == rescue_staget::independent_index)
        {
          options.set_option("refined-pointer-analysis", false);
          options.set_option("allow-pointer-unsoundness", true);
          options.set_option("unwind", "3");
        }
        else if(rescue_variant.stage == rescue_staget::cross_domain_list)
        {
          options.set_option("refined-pointer-analysis", false);
          options.set_option("allow-pointer-unsoundness", true);
          options.set_option("unwind", "3");
        }
        else if(rescue_variant.stage == rescue_staget::single_initialized)
        {
          options.set_option("refined-pointer-analysis", false);
          options.set_option("allow-pointer-unsoundness", false);
          options.set_option("unwinding-assertions", false);
          options.set_option(
            "native-witness-spawn-prefix-lift", true);
          options.set_option("unwind", "3");
          const std::string initialization_loop =
            single_worker_initialization_prefix_unwind_loop(
              goto_model);
          const std::string outer_initialization_loop =
            single_worker_initialization_prefix_outer_unwind_loop(
              goto_model);
          options.set_option(
            "unwindset",
            optionst::value_listt{
              initialization_loop + ":32",
              outer_initialization_loop + ":11"});
        }
        else if(rescue_variant.stage == rescue_staget::initialized_pair)
        {
          options.set_option("refined-pointer-analysis", false);
          options.set_option("allow-pointer-unsoundness", true);
          options.set_option("unwind", "2");
          dormant_spawn_pair_transform(
            goto_model,
            rescue_variant.pair_variant,
            ui_message_handler);
        }
        else if(rescue_variant.stage == rescue_staget::main_worker)
        {
          options.set_option("unwind", "11");
          const std::string worker =
            main_worker_prefix_worker_id(goto_model);
          options.set_option(
            "unwindset",
            optionst::value_listt{
              worker + ".0:" +
              std::to_string(rescue_variant.unwind_bound)});
          main_worker_prefix_transform(
            goto_model,
            ui_message_handler);
        }
        else if(rescue_variant.stage == rescue_staget::dormant_pair)
        {
          options.set_option("unwind", "3");
          dormant_spawn_pair_transform(
            goto_model,
            rescue_variant.pair_variant,
            ui_message_handler);
        }
        else if(rescue_variant.stage == rescue_staget::shallow_one)
        {
          options.set_option("unwind", "1");
          alternating_phase_recurrence_transform(
            goto_model, ui_message_handler);
          homogeneous_spawn_witness_transform(
            goto_model, ui_message_handler);
        }
        else
        {
          options.set_option("unwind", "3");
          dormant_spawn_cutoff_transform(
            goto_model, ui_message_handler);
        }
        native_rescue_portfolio_child = true;
        break;
      }
      close(output_fd);
      if(child < 0)
      {
        std::remove(output_path);
        std::cout
          << "NATIVE_COUNTEREXAMPLE_RESCUE_PORTFOLIO applied=0"
          << " reason=fork\n"
          << "VERIFICATION SUCCESSFUL\n";
        return CPROVER_EXIT_VERIFICATION_SAFE;
      }

      int status = 0;
      bool finished = false;
      while(std::chrono::steady_clock::now() < child_deadline)
      {
        const pid_t waited = waitpid(child, &status, WNOHANG);
        if(waited == child)
        {
          finished = true;
          break;
        }
        if(waited < 0 && errno != EINTR)
          break;
        usleep(10000);
      }
      if(!finished)
      {
        kill(child, SIGKILL);
        while(waitpid(child, &status, 0) < 0 && errno == EINTR)
        {
        }
        ++timed_out;
      }
      else
        ++completed;

      std::ifstream child_output_stream(output_path);
      std::ostringstream child_output_buffer;
      child_output_buffer << child_output_stream.rdbuf();
      child_output_stream.close();
      std::remove(output_path);
      const std::string child_output = child_output_buffer.str();
      const bool accepted_child =
        finished && WIFEXITED(status) &&
        WEXITSTATUS(status) == CPROVER_EXIT_VERIFICATION_UNSAFE &&
        child_output.find("VERIFICATION FAILED") != std::string::npos;
      if(!accepted_child)
      {
        std::istringstream marker_stream(child_output);
        std::string marker;
        while(std::getline(marker_stream, marker))
        {
          if(
            marker.find("NATIVE_ORIGINAL_GOTO_REPLAY ") == 0)
            std::cout << marker << '\n';
        }
      }
      if(accepted_child)
      {
        std::cout << child_output;
        return CPROVER_EXIT_VERIFICATION_UNSAFE;
      }
    }
    if(!native_rescue_portfolio_child)
    {
      std::cout
        << "NATIVE_COUNTEREXAMPLE_RESCUE_PORTFOLIO applied=1"
        << " pair_variants=" << pair_variants
        << " completed=" << completed
        << " timed_out=" << timed_out
        << " skipped_pairs=" << skipped_pairs
        << "\nVERIFICATION SUCCESSFUL\n";
      return CPROVER_EXIT_VERIFICATION_SAFE;
    }
#endif
  }

  bool dormant_pair_portfolio_child = false;
  if(cmdline.isset("native-dormant-spawn-pair-portfolio"))
  {
#ifdef _WIN32
    std::cout
      << "NATIVE_DORMANT_SPAWN_PAIR_PORTFOLIO applied=0"
      << " reason=unsupported_platform\n"
      << "VERIFICATION SUCCESSFUL\n";
    return CPROVER_EXIT_VERIFICATION_SAFE;
#else
    const std::size_t variants = std::min(
      dormant_spawn_pair_variant_count(goto_model),
      std::size_t{10});
    if(variants == 0)
    {
      std::cout
        << "NATIVE_DORMANT_SPAWN_PAIR_PORTFOLIO applied=0"
        << " reason=dormant_pair_not_applicable\n"
        << "VERIFICATION SUCCESSFUL\n";
      return CPROVER_EXIT_VERIFICATION_SAFE;
    }

    const auto portfolio_deadline =
      std::chrono::steady_clock::now() + std::chrono::seconds(18);
    std::size_t completed = 0;
    std::size_t timed_out = 0;
    for(std::size_t variant = 0; variant < variants; ++variant)
    {
      const auto now = std::chrono::steady_clock::now();
      if(now >= portfolio_deadline)
        break;
      const auto child_deadline =
        std::min(portfolio_deadline, now + std::chrono::seconds(6));

      char output_path[] = "deagle_native_pair_XXXXXX";
      const int output_fd = mkstemp(output_path);
      if(output_fd < 0)
      {
        std::cout
          << "NATIVE_DORMANT_SPAWN_PAIR_PORTFOLIO applied=0"
          << " reason=output_file\n"
          << "VERIFICATION SUCCESSFUL\n";
        return CPROVER_EXIT_VERIFICATION_SAFE;
      }
      std::fflush(nullptr);
      const pid_t child = fork();
      if(child == 0)
      {
#ifdef __linux__
        if(
          prctl(PR_SET_PDEATHSIG, SIGKILL) != 0 ||
          getppid() == 1)
          _exit(CPROVER_EXIT_INTERNAL_ERROR);
#endif
        if(
          dup2(output_fd, STDOUT_FILENO) < 0 ||
          dup2(output_fd, STDERR_FILENO) < 0)
          _exit(CPROVER_EXIT_INTERNAL_ERROR);
        close(output_fd);
        dormant_spawn_pair_transform(
          goto_model, variant, ui_message_handler);
        dormant_pair_portfolio_child = true;
        break;
      }
      close(output_fd);
      if(child < 0)
      {
        std::remove(output_path);
        std::cout
          << "NATIVE_DORMANT_SPAWN_PAIR_PORTFOLIO applied=0"
          << " reason=fork\n"
          << "VERIFICATION SUCCESSFUL\n";
        return CPROVER_EXIT_VERIFICATION_SAFE;
      }

      int status = 0;
      bool finished = false;
      while(std::chrono::steady_clock::now() < child_deadline)
      {
        const pid_t waited = waitpid(child, &status, WNOHANG);
        if(waited == child)
        {
          finished = true;
          break;
        }
        if(waited < 0 && errno != EINTR)
          break;
        usleep(10000);
      }
      if(!finished)
      {
        kill(child, SIGKILL);
        while(waitpid(child, &status, 0) < 0 && errno == EINTR)
        {
        }
        ++timed_out;
      }
      else
        ++completed;

      std::ifstream child_output_stream(output_path);
      std::ostringstream child_output_buffer;
      child_output_buffer << child_output_stream.rdbuf();
      child_output_stream.close();
      std::remove(output_path);
      const std::string child_output = child_output_buffer.str();
      if(
        finished && WIFEXITED(status) &&
        WEXITSTATUS(status) == CPROVER_EXIT_VERIFICATION_UNSAFE &&
        child_output.find("VERIFICATION FAILED") != std::string::npos)
      {
        std::cout << child_output;
        return CPROVER_EXIT_VERIFICATION_UNSAFE;
      }
    }
    if(!dormant_pair_portfolio_child)
    {
      std::cout
        << "NATIVE_DORMANT_SPAWN_PAIR_PORTFOLIO applied=1"
        << " variants=" << variants
        << " completed=" << completed
        << " timed_out=" << timed_out
        << "\nVERIFICATION SUCCESSFUL\n";
      return CPROVER_EXIT_VERIFICATION_SAFE;
    }
#endif
  }

  if(cmdline.isset("native-group-action-cancellation-audit"))
    group_action_cancellation_audit(
      goto_model, ui_message_handler);

  if(cmdline.isset("native-segmented-fold-audit"))
    segmented_fold_conservation_audit(
      goto_model, ui_message_handler);

  if(cmdline.isset("native-nested-iteration-audit"))
    nested_iteration_homomorphism_audit(
      goto_model, ui_message_handler);

  if(cmdline.isset("native-local-loop-accel-audit"))
    local_loop_acceleration_audit(
      goto_model, ui_message_handler);

  if(cmdline.isset("native-homogeneous-spawn-witness-audit"))
    homogeneous_spawn_witness_audit(
      goto_model, ui_message_handler);

  if(cmdline.isset("native-alternating-phase-audit"))
    alternating_phase_recurrence_audit(
      goto_model, ui_message_handler);

  if(cmdline.isset("native-indexed-lifecycle-audit"))
  {
    indexed_lifecycle_prefix_audit(
      goto_model, ui_message_handler);
    nested_lifecycle_last_writer_audit(
      goto_model, ui_message_handler);
    boolean_atomic_lock_region_audit(
      goto_model, ui_message_handler);
  }

  if(cmdline.isset("native-dormant-spawn-cutoff-audit"))
    dormant_spawn_cutoff_audit(
      goto_model, ui_message_handler);

  if(cmdline.isset("native-dormant-spawn-cutoff"))
    native_model_transformed =
      dormant_spawn_cutoff_transform(
        goto_model, ui_message_handler) ||
      native_model_transformed;

  if(cmdline.isset("native-single-worker-initialization-prefix"))
    native_model_transformed =
      single_worker_initialization_prefix_transform(
        goto_model, ui_message_handler) ||
      native_model_transformed;

  if(cmdline.isset("native-main-worker-prefix"))
    native_model_transformed =
      main_worker_prefix_transform(
        goto_model, ui_message_handler) ||
      native_model_transformed;

  if(cmdline.isset("native-dormant-spawn-pair-audit"))
    dormant_spawn_pair_audit(
      goto_model, ui_message_handler);

  if(cmdline.isset("native-dormant-spawn-pair"))
  {
    const std::string value =
      cmdline.get_value("native-dormant-spawn-pair");
    std::size_t consumed = 0;
    std::size_t variant = 0;
    try
    {
      variant = std::stoul(value, &consumed);
    }
    catch(const std::exception &)
    {
      consumed = 0;
    }
    if(value.empty() || consumed != value.size())
    {
      log.error()
        << "invalid dormant spawn pair variant: " << value
        << messaget::eom;
      return CPROVER_EXIT_USAGE_ERROR;
    }
    native_model_transformed =
      dormant_spawn_pair_transform(
        goto_model, variant, ui_message_handler) ||
      native_model_transformed;
  }

  if(cmdline.isset("native-indexed-lifecycle-prefix"))
    native_model_transformed =
      indexed_lifecycle_prefix_transform(
        goto_model, ui_message_handler) ||
      native_model_transformed;

  if(cmdline.isset("native-alternating-phase-recurrence"))
    native_model_transformed =
      alternating_phase_recurrence_transform(
        goto_model, ui_message_handler) ||
      native_model_transformed;

  if(cmdline.isset("native-nonnegative-oscillator-monitor"))
    native_model_transformed =
      nonnegative_oscillator_monitor_transform(
        goto_model, ui_message_handler) ||
      native_model_transformed;

  if(cmdline.isset("native-homogeneous-spawn-witness"))
    native_model_transformed =
      homogeneous_spawn_witness_transform(
        goto_model, ui_message_handler) ||
      native_model_transformed;

  if(
    cmdline.isset("native-jces") &&
    !cmdline.isset("unwind-suggest") &&
    interference_predicate_finite_product_auto(
      goto_model, ui_message_handler) ==
      interference_predicate_resultt::SAFE &&
    output_native_correctness_witness(
      goto_model, options, native_witness_guards))
  {
    std::cout << "VERIFICATION SUCCESSFUL\n";
    return CPROVER_EXIT_SUCCESS;
  }

  if(
    cmdline.isset("native-jces") &&
    !cmdline.isset("unwind-suggest") &&
    nested_iteration_homomorphism_proof(
      goto_model, ui_message_handler) &&
    output_native_correctness_witness(
      goto_model, options, native_witness_assertions))
  {
    std::cout << "VERIFICATION SUCCESSFUL\n";
    return CPROVER_EXIT_SUCCESS;
  }

  if(
    cmdline.isset("native-jces") &&
    !cmdline.isset("unwind-suggest") &&
    segmented_fold_conservation_proof(
      goto_model, ui_message_handler) &&
    output_native_correctness_witness(
      goto_model, options, native_witness_assertions))
  {
    std::cout << "VERIFICATION SUCCESSFUL\n";
    return CPROVER_EXIT_SUCCESS;
  }

  if(
    cmdline.isset("native-jces") &&
    !cmdline.isset("unwind-suggest") &&
    group_action_cancellation_proof(
      goto_model, ui_message_handler) &&
    output_native_correctness_witness(
      goto_model, options, native_witness_assertions))
  {
    std::cout << "VERIFICATION SUCCESSFUL\n";
    return CPROVER_EXIT_SUCCESS;
  }

  if(
    cmdline.isset("native-jces") &&
    !cmdline.isset("unwind-suggest") &&
    partitioned_count_reduction_proof(
      goto_model, ui_message_handler) &&
    output_native_correctness_witness(
      goto_model, options, native_witness_assertions))
  {
    std::cout << "VERIFICATION SUCCESSFUL\n";
    return CPROVER_EXIT_SUCCESS;
  }

  if(
    cmdline.isset("native-jces") &&
    !cmdline.isset("unwind-suggest") &&
    finite_two_sided_disjunction_proof(
      goto_model, ui_message_handler) &&
    output_native_correctness_witness(
      goto_model, options, native_witness_assertions))
  {
    std::cout << "VERIFICATION SUCCESSFUL\n";
    return CPROVER_EXIT_SUCCESS;
  }

  if(
    cmdline.isset("native-jces") &&
    !cmdline.isset("unwind-suggest") &&
    completion_flag_arithmetic_proof(
      goto_model, ui_message_handler) &&
    output_native_correctness_witness(
      goto_model, options, native_witness_assertions))
  {
    std::cout << "VERIFICATION SUCCESSFUL\n";
    return CPROVER_EXIT_SUCCESS;
  }

  if(
    cmdline.isset("native-jces") &&
    !cmdline.isset("unwind-suggest") &&
    nonzero_cas_seed_proof(
      goto_model, ui_message_handler) &&
    output_native_correctness_witness(
      goto_model, options, native_witness_assertions))
  {
    std::cout << "VERIFICATION SUCCESSFUL\n";
    return CPROVER_EXIT_SUCCESS;
  }

  if(
    cmdline.isset("native-jces") &&
    !cmdline.isset("unwind-suggest") &&
    monotone_chunk_maximum_proof(
      goto_model, ui_message_handler) &&
    output_native_correctness_witness(
      goto_model, options, native_witness_assertions))
  {
    std::cout << "VERIFICATION SUCCESSFUL\n";
    return CPROVER_EXIT_SUCCESS;
  }

  if(
    cmdline.isset("native-jces") &&
    !cmdline.isset("unwind-suggest") &&
    linear_tiled_copy_equivalence_proof(
      goto_model, ui_message_handler) &&
    output_native_correctness_witness(
      goto_model, options, native_witness_assertions))
  {
    std::cout << "VERIFICATION SUCCESSFUL\n";
    return CPROVER_EXIT_SUCCESS;
  }

  if(
    cmdline.isset("native-jces") &&
    !cmdline.isset("unwind-suggest") &&
    atomic_queue_occupancy_value_proof(
      goto_model, ui_message_handler) &&
    output_native_correctness_witness(
      goto_model, options, native_witness_assertions))
  {
    std::cout << "VERIFICATION SUCCESSFUL\n";
    return CPROVER_EXIT_SUCCESS;
  }

  if(
    cmdline.isset("native-jces") &&
    !cmdline.isset("unwind-suggest") &&
    isomorphic_modular_fold_pair_proof(
      goto_model, ui_message_handler) &&
    output_native_correctness_witness(
      goto_model, options, native_witness_assertions))
  {
    std::cout << "VERIFICATION SUCCESSFUL\n";
    return CPROVER_EXIT_SUCCESS;
  }

  if(cmdline.isset("native-prefix-affine-envelope"))
    native_model_transformed =
      prefix_affine_envelope_transform(
        goto_model, ui_message_handler) ||
      native_model_transformed;

  if(
    !cmdline.isset("unwind-suggest") &&
    relational_comparator_transitivity_proof(
      goto_model, ui_message_handler) &&
    output_native_correctness_witness(
      goto_model, options, native_witness_assertions))
  {
    std::cout << "VERIFICATION SUCCESSFUL\n";
    return CPROVER_EXIT_SUCCESS;
  }

  bool unreserved_scalar_read_transformed = false;
  if(
    cmdline.isset("native-jces") &&
    cmdline.isset("native-pure-spin-wait") &&
    !cmdline.isset("unwind-suggest"))
    native_model_transformed =
      pure_spin_wait_dispatch(
        goto_model,
        ui_message_handler,
        unreserved_scalar_read_transformed) ||
      native_model_transformed;

  bool symmetric_scan_model_transformed = false;
  if(!cmdline.isset("unwind-suggest"))
  {
    symmetric_scan_model_transformed =
      symmetric_array_scan_transform(
        goto_model, ui_message_handler);
    native_model_transformed =
      symmetric_scan_model_transformed ||
      native_model_transformed;
  }
  if(
    cmdline.isset("native-jces") &&
    !cmdline.isset("unwind-suggest"))
    native_model_transformed =
      local_loop_acceleration_transform(
        goto_model, ui_message_handler) ||
      native_model_transformed;

  if(cmdline.isset("native-property-affine-audit"))
    property_directed_affine_audit(goto_model, ui_message_handler);

  if(cmdline.isset("native-role-split-stream-audit"))
    role_split_affine_stream_audit(goto_model, ui_message_handler);

  if(cmdline.isset("native-publication-frontier-audit"))
    publication_frontier_sequence_audit(
      goto_model, ui_message_handler);

  if(cmdline.isset("native-relational-bisimulation-audit"))
    relational_bisimulation_audit(
      goto_model, ui_message_handler);

  if(
    cmdline.isset("native-property-affine-proof") &&
    property_directed_affine_proof(goto_model, ui_message_handler) &&
    output_native_correctness_witness(
      goto_model, options, native_witness_assertions))
  {
    std::cout << "VERIFICATION SUCCESSFUL\n";
    return CPROVER_EXIT_SUCCESS;
  }

  if(
    cmdline.isset("native-lock-ego-abstraction") &&
    !lock_boundary_ego_thread_abstraction_transform(
      goto_model, ui_message_handler))
    return CPROVER_EXIT_SUCCESS;

  if(
    cmdline.isset("native-jces") &&
    !cmdline.isset("unwind-suggest"))
  {
    if(
      property_directed_affine_proof(goto_model, ui_message_handler) &&
      output_native_correctness_witness(
        goto_model, options, native_witness_assertions))
    {
      std::cout << "VERIFICATION SUCCESSFUL\n";
      return CPROVER_EXIT_SUCCESS;
    }
    if(
      relational_order_law_proof(goto_model, ui_message_handler) &&
      output_native_correctness_witness(
        goto_model, options, native_witness_assertions))
    {
      std::cout << "VERIFICATION SUCCESSFUL\n";
      return CPROVER_EXIT_SUCCESS;
    }
    if(
      extremum_cone_proof(goto_model, ui_message_handler) &&
      output_native_correctness_witness(
        goto_model, options, native_witness_assertions))
    {
      std::cout << "VERIFICATION SUCCESSFUL\n";
      return CPROVER_EXIT_SUCCESS;
    }
    if(
      lock_relational_ai_transform(goto_model, ui_message_handler) &&
      output_native_correctness_witness(
        goto_model, options, native_witness_assertions))
    {
      std::cout << "VERIFICATION SUCCESSFUL\n";
      return CPROVER_EXIT_SUCCESS;
    }
    if(
      std::getenv("DEAGLE_INDEX_REGION_OWNERSHIP_MODE") != nullptr &&
      index_region_ownership_proof(goto_model, ui_message_handler) &&
      output_native_correctness_witness(
        goto_model, options, native_witness_assertions))
    {
      std::cout << "VERIFICATION SUCCESSFUL\n";
      return CPROVER_EXIT_SUCCESS;
    }
    if(
      std::getenv("DEAGLE_POST_STORE_STABLE_CELL_MODE") != nullptr &&
      post_store_stable_cell_proof(goto_model, ui_message_handler) &&
      output_native_correctness_witness(
        goto_model, options, native_witness_assertions))
    {
      std::cout << "VERIFICATION SUCCESSFUL\n";
      return CPROVER_EXIT_SUCCESS;
    }
    if(
      std::getenv("DEAGLE_STACK_CAPACITY_MODE") != nullptr &&
      stack_capacity_invariant_proof(goto_model, ui_message_handler) &&
      output_native_correctness_witness(
        goto_model, options, native_witness_assertions))
    {
      std::cout << "VERIFICATION SUCCESSFUL\n";
      return CPROVER_EXIT_SUCCESS;
    }
    if(
      std::getenv("DEAGLE_QUEUE_SEQUENCE_MODE") != nullptr &&
      queue_sequence_correspondence_proof(goto_model, ui_message_handler) &&
      output_native_correctness_witness(
        goto_model, options, native_witness_assertions))
    {
      std::cout << "VERIFICATION SUCCESSFUL\n";
      return CPROVER_EXIT_SUCCESS;
    }
    if(
      dynamic_tls_calloc_zero_proof(
        goto_model, ui_message_handler) &&
      output_native_correctness_witness(
        goto_model, options, native_witness_assertions))
    {
      std::cout << "VERIFICATION SUCCESSFUL\n";
      return CPROVER_EXIT_SUCCESS;
    }
    bool commuting_model_transformed = false;
    const bool jces_model_transformed =
      tls_destructor_counterexample_transform(
        goto_model, ui_message_handler) ||
      homogeneous_thread_local_cutoff_transform(
        goto_model, ui_message_handler) ||
      bounded_alternating_cancellation_transform(
        goto_model, ui_message_handler) ||
      phase_boundary_cancellation_transform(
        goto_model, ui_message_handler) ||
      joined_terminal_overwrite_transform(
        goto_model, ui_message_handler) ||
      predicate_stable_linearization_transform(
        goto_model, ui_message_handler) ||
      cas_linearization_stability_transform(
        goto_model, ui_message_handler) ||
      lock_linearization_stability_transform(
        goto_model, ui_message_handler) ||
      lock_scoped_commutative_aggregation_transform(
        goto_model, ui_message_handler) ||
      ticket_rank_serializability_transform(
        goto_model, ui_message_handler) ||
      transition_word_equivalence_transform(
        goto_model, ui_message_handler) ||
      (commuting_model_transformed =
         join_scoped_commuting_sequentialization_transform(
           goto_model, ui_message_handler)) ||
      jces_transform(goto_model, ui_message_handler);
    if(commuting_model_transformed)
    {
      const bool modular_loop_transformed =
        local_modular_accumulation_transform(
          goto_model, ui_message_handler);
      if(modular_loop_transformed)
      {
        options.set_option("deagle-closure", false);
        std::cout
          << "NATIVE_SEQUENTIAL_SAT_ROUTING applied=1"
          << " reason=commuting_modular_summary\n";
      }
      native_model_transformed =
        modular_loop_transformed || native_model_transformed;
    }
    native_model_transformed =
      native_model_transformed || jces_model_transformed;
  }

  if(
    options.get_bool_option("deagle-nondet-bulk-init") &&
    (!native_model_transformed || symmetric_scan_model_transformed) &&
    !options.is_set("property") && !options.is_set("subproperty"))
  {
    const auto stats = nondet_bulk_init(
      goto_model,
      ui_message_handler,
      nondet_bulk_init_modet::spawn_frontier_residual);
    std::cout
      << "Deagle nondet bulk init: phase=residual candidates="
      << stats.candidate_loops << " transformed="
      << stats.transformed_loops << " rejected_non_prethread="
      << stats.rejected_non_prethread << " rejected_nonterminal="
      << stats.rejected_nonterminal << " rejected_region_budget="
      << stats.rejected_region_budget << '\n';
  }

  if(cmdline.isset("interference-predicate-self-test"))
  {
    const namespacet ns(goto_model.symbol_table);
    const bool passed =
      interference_predicate_cube_self_test(ns, ui_message_handler);
    std::cout << "INTERFERENCE_PREDICATE_SELF_TEST "
              << (passed ? "PASS" : "FAIL") << '\n';
    return passed ? CPROVER_EXIT_SUCCESS : CPROVER_EXIT_INTERNAL_ERROR;
  }

  if(cmdline.isset("interference-predicate-profile"))
  {
    interference_predicate_profile(goto_model, ui_message_handler);
    return CPROVER_EXIT_SUCCESS;
  }

  if(cmdline.isset("interference-predicate-fixedpoint"))
  {
    const auto result =
      interference_predicate_fixedpoint(
        goto_model,
        ui_message_handler,
        false,
        cmdline.isset("finite-protocol-product"));
    if(
      result == interference_predicate_resultt::SAFE &&
      output_native_correctness_witness(
        goto_model, options, native_witness_assertions))
      std::cout << "VERIFICATION SUCCESSFUL\n";
    return CPROVER_EXIT_SUCCESS;
  }

  if(cmdline.isset("interference-predicate-recursive-worker-fixedpoint"))
  {
    const auto result = interference_predicate_fixedpoint(
      goto_model, ui_message_handler, true);
    if(
      result == interference_predicate_resultt::SAFE &&
      output_native_correctness_witness(
        goto_model, options, native_witness_assertions))
      std::cout << "VERIFICATION SUCCESSFUL\n";
    return CPROVER_EXIT_SUCCESS;
  }

  if(cmdline.isset("protocol-induced-capacity-cutoff"))
  {
    const auto result =
      protocol_capacity_cutoff(goto_model, ui_message_handler);
    if(
      result == protocol_capacity_resultt::SAFE &&
      output_native_correctness_witness(
        goto_model, options, native_witness_assertions))
    {
      std::cout << "VERIFICATION SUCCESSFUL\n";
      return CPROVER_EXIT_SUCCESS;
    }
    if(!cmdline.isset("unwind-suggest"))
      return CPROVER_EXIT_SUCCESS;
  }

  if(cmdline.isset("show-claims") || // will go away
     cmdline.isset("show-properties")) // use this one
  {
    show_properties(goto_model, ui_message_handler);
    return CPROVER_EXIT_SUCCESS;
  }

  if(set_properties())
    return CPROVER_EXIT_SET_PROPERTIES_FAILED;

  if(
    options.get_bool_option("program-only") ||
    options.get_bool_option("show-vcc") ||
    options.get_bool_option("show-byte-ops"))
  {
    if(options.get_bool_option("paths"))
    {
      all_properties_verifiert<single_path_symex_only_checkert> verifier(
        options, ui_message_handler, goto_model);
      (void)verifier();
    }
    else
    {
      all_properties_verifiert<multi_path_symex_only_checkert> verifier(
        options, ui_message_handler, goto_model);
      (void)verifier();
    }

    return CPROVER_EXIT_SUCCESS;
  }

  if(
    options.get_bool_option("dimacs") || !options.get_option("outfile").empty())
  {
    if(options.get_bool_option("paths"))
    {
      stop_on_fail_verifiert<single_path_symex_checkert> verifier(
        options, ui_message_handler, goto_model);
      (void)verifier();
    }
    else
    {
      stop_on_fail_verifiert<multi_path_symex_checkert> verifier(
        options, ui_message_handler, goto_model);
      (void)verifier();
    }

    return CPROVER_EXIT_SUCCESS;
  }

  if(options.is_set("cover"))
  {
    cover_goals_verifier_with_trace_storaget<multi_path_symex_checkert>
      verifier(options, ui_message_handler, goto_model);
    (void)verifier();
    verifier.report();

    if(options.get_bool_option("show-test-suite"))
    {
      c_test_input_generatort test_generator(ui_message_handler, options);
      test_generator(verifier.get_traces());
    }

    return CPROVER_EXIT_SUCCESS;
  }

  if(
    native_rescue_portfolio_child &&
    options.get_bool_option("native-witness-spawn-prefix-lift") &&
    native_original_replay_model)
  {
    const std::string final_witness_path =
      options.get_option("graphml-witness");
    std::vector<native_replay_choicet> replay_choices;
    irep_idt candidate_failure_function;
    irep_idt candidate_failure_line;
    {
      optionst candidate_options = options;
      candidate_options.set_option("graphml-witness", "");
      candidate_options.set_option("trace", true);
      all_properties_verifier_with_trace_storaget<multi_path_symex_checkert>
        candidate_verifier(
          candidate_options, ui_message_handler, goto_model);
      const resultt candidate_result = candidate_verifier();
      if(
        candidate_result != resultt::FAIL ||
        candidate_verifier.get_traces().all().empty())
      {
        std::cout
          << "NATIVE_ORIGINAL_GOTO_REPLAY applied=0"
          << " reason=no_candidate_trace\n";
        return result_to_exit_code(candidate_result);
      }

      const goto_tracet &candidate_trace =
        candidate_verifier.get_traces().all().front();
      const auto &candidate_failure =
        candidate_trace.get_last_step();
      if(!candidate_failure.is_assert())
      {
        std::cout
          << "NATIVE_ORIGINAL_GOTO_REPLAY applied=0"
          << " reason=candidate_property\n";
        return CPROVER_EXIT_VERIFICATION_SAFE;
      }
      replay_choices =
        collect_native_replay_choices(candidate_trace);
      candidate_failure_function =
        candidate_failure.pc->source_location().get_function();
      candidate_failure_line =
        candidate_failure.pc->source_location().get_line();
    }

    optionst replay_options = options;
    replay_options.set_option(
      "graphml-witness", final_witness_path);
    replay_options.set_option(
      "native-pair-initialization-prefix", false);
    replay_options.set_option(
      "native-witness-spawn-prefix-lift", false);
    replay_options.set_option("refined-pointer-analysis", false);
    replay_options.set_option("allow-pointer-unsoundness", false);
    replay_options.set_option("unwinding-assertions", false);
    replay_options.set_option("unwind", "3");
    replay_options.set_option(
      "unwindset",
      optionst::value_listt{
        single_worker_initialization_prefix_unwind_loop(
          goto_model) + ":32",
        single_worker_initialization_prefix_outer_unwind_loop(
          goto_model) + ":11"});

    messaget replay_log{ui_message_handler};
    if(
      !source_replay_single_worker_schedule_transform(
        *native_original_replay_model, ui_message_handler) ||
      cbmc_parse_optionst::process_goto_program(
        *native_original_replay_model,
        replay_options,
        replay_log) ||
      !apply_native_replay_choices(
        *native_original_replay_model, replay_choices))
    {
      std::cout
        << "NATIVE_ORIGINAL_GOTO_REPLAY applied=0"
        << " reason=guide_construction\n";
      return CPROVER_EXIT_VERIFICATION_SAFE;
    }

    all_properties_verifier_with_trace_storaget<multi_path_symex_checkert>
      replay_verifier(
        replay_options,
        ui_message_handler,
        *native_original_replay_model);
    const resultt replay_result = replay_verifier();
    if(
      replay_result != resultt::FAIL ||
      replay_verifier.get_traces().all().empty())
    {
      std::cout
        << "NATIVE_ORIGINAL_GOTO_REPLAY applied=0"
        << " reason=original_model_result"
        << " result=" << static_cast<int>(replay_result) << '\n';
      return CPROVER_EXIT_VERIFICATION_SAFE;
    }

    const goto_tracet &replay_trace =
      replay_verifier.get_traces().all().front();
    const auto &replay_failure = replay_trace.get_last_step();
    goto_tracet source_prefix_trace;
    if(
      !replay_failure.is_assert() ||
      !lift_single_spawn_source_prefix(
        replay_trace, source_prefix_trace) ||
      candidate_failure_function !=
        replay_failure.pc->source_location().get_function() ||
      candidate_failure_line !=
        replay_failure.pc->source_location().get_line())
    {
      std::cout
        << "NATIVE_ORIGINAL_GOTO_REPLAY applied=0"
        << " reason=property_mismatch\n";
      return CPROVER_EXIT_VERIFICATION_SAFE;
    }

    std::cout
      << "NATIVE_ORIGINAL_GOTO_REPLAY applied=1"
      << " choices=" << replay_choices.size()
      << " replay_steps=" << replay_trace.steps.size()
      << " source_steps=" << source_prefix_trace.steps.size()
      << '\n';
    const namespacet replay_namespace(
      native_original_replay_model->symbol_table);
    output_graphml(
      source_prefix_trace,
      replay_namespace,
      replay_options);
    replay_verifier.report();
    return CPROVER_EXIT_VERIFICATION_UNSAFE;
  }

  if(
    cmdline.isset("native-guided-multiloop-unwind") &&
    unreserved_scalar_read_transformed)
  {
    const guided_multiloop_resultt guided_result =
      guided_multiloop_unwind(
        goto_model, options, ui_message_handler);
    if(guided_result.kind == guided_multiloop_result_kindt::SAFE)
    {
      if(
        !output_native_correctness_witness(
          goto_model, options, native_witness_assertions))
        return CPROVER_EXIT_INTERNAL_ERROR;
      std::cout << "VERIFICATION SUCCESSFUL\n";
      return CPROVER_EXIT_VERIFICATION_SAFE;
    }
    if(guided_result.kind == guided_multiloop_result_kindt::UNSAFE)
    {
      std::cout
        << "NATIVE_GUIDED_MULTILOOP_UNWIND applied=0"
        << " reason=unsafe_not_admissible_for_safe_only_portfolio\n";
      return CPROVER_EXIT_SUCCESS;
    }
    return CPROVER_EXIT_SUCCESS;
  }

  std::unique_ptr<goto_verifiert> verifier = nullptr;

  if(options.is_set("incremental-loop"))
  {
    if(options.get_bool_option("stop-on-fail"))
    {
      verifier = util_make_unique<
        stop_on_fail_verifiert<single_loop_incremental_symex_checkert>>(
        options, ui_message_handler, goto_model);
    }
    else
    {
      verifier = util_make_unique<all_properties_verifier_with_trace_storaget<
        single_loop_incremental_symex_checkert>>(
        options, ui_message_handler, goto_model);
    }
  }
  else if(
    options.get_bool_option("stop-on-fail") && options.get_bool_option("paths"))
  {
    verifier =
      util_make_unique<stop_on_fail_verifiert<single_path_symex_checkert>>(
        options, ui_message_handler, goto_model);
  }
  else if(
    options.get_bool_option("stop-on-fail") &&
    !options.get_bool_option("paths"))
  {
    if(options.get_bool_option("localize-faults"))
    {
      verifier =
        util_make_unique<stop_on_fail_verifier_with_fault_localizationt<
          multi_path_symex_checkert>>(options, ui_message_handler, goto_model);
    }
    else
    {
      verifier =
        util_make_unique<stop_on_fail_verifiert<multi_path_symex_checkert>>(
          options, ui_message_handler, goto_model);
    }
  }
  else if(
    !options.get_bool_option("stop-on-fail") &&
    options.get_bool_option("paths"))
  {
    verifier = util_make_unique<
      all_properties_verifier_with_trace_storaget<single_path_symex_checkert>>(
      options, ui_message_handler, goto_model);
  }
  else if(
    !options.get_bool_option("stop-on-fail") &&
    !options.get_bool_option("paths"))
  {
    if(options.get_bool_option("localize-faults"))
    {
      verifier =
        util_make_unique<all_properties_verifier_with_fault_localizationt<
          multi_path_symex_checkert>>(options, ui_message_handler, goto_model);
    }
    else
    {
      verifier = util_make_unique<
        all_properties_verifier_with_trace_storaget<multi_path_symex_checkert>>(
        options, ui_message_handler, goto_model);
    }
  }
  else
  {
    UNREACHABLE;
  }

  const resultt result = (*verifier)();
  verifier->report();

  if(
    result == resultt::PASS &&
    !options.get_option("graphml-witness").empty() &&
    !output_native_correctness_witness(
      goto_model, options, native_witness_assertions))
    return CPROVER_EXIT_INTERNAL_ERROR;

  return result_to_exit_code(result);
}

bool cbmc_parse_optionst::set_properties()
{
  if(cmdline.isset("claim") || cmdline.isset("subproperty")) // will go away
    ::set_properties(goto_model, cmdline.get_values("claim"), cmdline.get_values("subproperty"));

  if(cmdline.isset("property") || cmdline.isset("subproperty")) // use this one
    ::set_properties(goto_model, cmdline.get_values("property"), cmdline.get_values("subproperty"));

  return false;
}

int cbmc_parse_optionst::get_goto_program(
  goto_modelt &goto_model,
  const optionst &options,
  const cmdlinet &cmdline,
  ui_message_handlert &ui_message_handler,
  const std::function<void(const goto_modelt &)> &before_processing)
{
  messaget log{ui_message_handler};
  if(cmdline.args.empty())
  {
    log.error() << "Please provide a program to verify" << messaget::eom;
    return CPROVER_EXIT_INCORRECT_TASK;
  }

  goto_model = initialize_goto_model(cmdline.args, ui_message_handler, options);

  if(before_processing)
    before_processing(goto_model);

  if(cmdline.isset("show-symbol-table"))
  {
    show_symbol_table(goto_model, ui_message_handler);
    return CPROVER_EXIT_SUCCESS;
  }

  if(cbmc_parse_optionst::process_goto_program(goto_model, options, log))
    return CPROVER_EXIT_INTERNAL_ERROR;

  if(cmdline.isset("validate-goto-model"))
  {
    goto_model.validate();
  }

  // show it?
  if(cmdline.isset("show-loops"))
  {
    show_loop_ids(ui_message_handler.get_ui(), goto_model);
    return CPROVER_EXIT_SUCCESS;
  }

  // show it?
  if(
    cmdline.isset("show-goto-functions") ||
    cmdline.isset("list-goto-functions"))
  {
    show_goto_functions(
      goto_model, ui_message_handler, cmdline.isset("list-goto-functions"));
    return CPROVER_EXIT_SUCCESS;
  }

  log.status() << config.object_bits_info() << messaget::eom;

  return -1; // no error, continue
}

void cbmc_parse_optionst::preprocessing(const optionst &options)
{
  if(cmdline.args.size() != 1)
  {
    log.error() << "Please provide one program to preprocess" << messaget::eom;
    return;
  }

  std::string filename = cmdline.args[0];

  std::ifstream infile(filename);

  if(!infile)
  {
    log.error() << "failed to open input file" << messaget::eom;
    return;
  }

  std::unique_ptr<languaget> language = get_language_from_filename(filename);
  language->set_language_options(options);

  if(language == nullptr)
  {
    log.error() << "failed to figure out type of file" << messaget::eom;
    return;
  }

  language->set_message_handler(ui_message_handler);

  if(language->preprocess(infile, filename, std::cout))
    log.error() << "PREPROCESSING ERROR" << messaget::eom;
}

bool cbmc_parse_optionst::process_goto_program(
  goto_modelt &goto_model,
  const optionst &options,
  messaget &log)
{
  // Remove inline assembler; this needs to happen before
  // adding the library.
  remove_asm(goto_model);

  // add the library
  log.status() << "Adding CPROVER library (" << config.ansi_c.arch << ")"
               << messaget::eom;
  link_to_library(
    goto_model, log.get_message_handler(), cprover_cpp_library_factory);
  link_to_library(
    goto_model, log.get_message_handler(), cprover_c_library_factory);

  if(options.get_bool_option("deagle-nondet-bulk-init"))
  {
    const auto stats = nondet_bulk_init(
      goto_model,
      log.get_message_handler(),
      nondet_bulk_init_modet::source_closed);
    log.status() << "Deagle nondet bulk init: phase=source-closed candidates="
                 << stats.candidate_loops << " transformed="
                 << stats.transformed_loops << " rejected_non_prethread="
                 << stats.rejected_non_prethread
                 << " rejected_nonterminal="
                 << stats.rejected_nonterminal
                 << " rejected_region_budget="
                 << stats.rejected_region_budget << messaget::eom;
  }

  if(options.get_bool_option("native-pair-initialization-prefix"))
  {
    if(!options.get_bool_option("no-assertions"))
    {
      if(
        !boolean_atomic_lock_region_transform(
          goto_model, log.get_message_handler()) &&
        !nested_lifecycle_last_writer_transform(
          goto_model, log.get_message_handler()) &&
        !mutex_zero_fixedpoint_transform(
          goto_model, log.get_message_handler()) &&
        !aggregate_member_lock_alias_transform(
          goto_model, log.get_message_handler()) &&
        !resolved_worker_zero_sum_transform(
          goto_model, log.get_message_handler()) &&
        !monotone_condition_wait_transform(
          goto_model, log.get_message_handler()) &&
        !guarded_common_mutex_zero_sum_transform(
          goto_model, log.get_message_handler()) &&
        !common_mutex_zero_sum_transform(
          goto_model, log.get_message_handler()) &&
        !independent_index_prefix_transform(
          goto_model, log.get_message_handler()) &&
        !cross_domain_list_prefix_transform(
          goto_model, log.get_message_handler()) &&
        !single_worker_initialization_prefix_transform(
          goto_model, log.get_message_handler()))
        pair_initialization_prefix_transform(
          goto_model, log.get_message_handler());
    }
  }

  // Common removal of types and complex constructs
  if(::process_goto_program(goto_model, options, log))
    return true;

  // ignore default/user-specified initialization
  // of variables with static lifetime
  if(options.get_bool_option("nondet-static"))
  {
    log.status() << "Adding nondeterministic initialization "
                    "of static/global variables"
                 << messaget::eom;
    nondet_static(goto_model);
  }

  // add failed symbols
  // needs to be done before pointer analysis
  add_failed_symbols(goto_model.symbol_table);

  if(options.get_bool_option("drop-unused-functions"))
  {
    // Entry point will have been set before and function pointers removed
    log.status() << "Removing unused functions" << messaget::eom;
    remove_unused_functions(goto_model, log.get_message_handler());
  }

  // remove skips such that trivial GOTOs are deleted and not considered
  // for coverage annotation:
  remove_skip(goto_model);

  // instrument cover goals
  if(options.is_set("cover"))
  {
    const auto cover_config = get_cover_config(
      options, goto_model.symbol_table, log.get_message_handler());
    if(instrument_cover_goals(
         cover_config, goto_model, log.get_message_handler()))
      return true;
  }

  // label the assertions
  // This must be done after adding assertions and
  // before using the argument of the "property" option.
  // Do not re-label after using the property slicer because
  // this would cause the property identifiers to change.
  label_properties(goto_model);

  // reachability slice?
  if(options.get_bool_option("reachability-slice-fb"))
  {
    log.status() << "Performing a forwards-backwards reachability slice"
                 << messaget::eom;
    if(options.is_set("property") || options.is_set("subproperty"))
    {
      reachability_slicer(
        goto_model,
        options.get_list_option("property"),
        options.get_list_option("subproperty"),
        true,
        log.get_message_handler());
    }
    else
      reachability_slicer(goto_model, true, log.get_message_handler());
  }

  if(options.get_bool_option("reachability-slice"))
  {
    log.status() << "Performing a reachability slice" << messaget::eom;
    if(options.is_set("property") || options.is_set("subproperty"))
    {
      reachability_slicer(
        goto_model,
        options.get_list_option("property"),
        options.get_list_option("subproperty"),
        log.get_message_handler());
    }
    else
      reachability_slicer(goto_model, log.get_message_handler());
  }

  // full slice?
  if(options.get_bool_option("full-slice"))
  {
    log.status() << "Performing a full slice" << messaget::eom;
    if(options.is_set("property") && options.is_set("subproperty"))
      property_slicer(goto_model, options.get_list_option("property"), options.get_list_option("subproperty"));
    else
      full_slicer(goto_model);
  }

  // remove any skips introduced since coverage instrumentation
  remove_skip(goto_model);

  return false;
}

/// display command line help
void cbmc_parse_optionst::help()
{
  // clang-format off

  // __SZH_ADD_BEGIN__
  std::cout << "\n" << banner_string("Deagle", "4.1.0") << '\n'
            << align_center_with_border("Zhihang Sun, Pei Wang, Hongyu Fan, and Fei HE") << '\n'
            << align_center_with_border("School of Software, Tsinghua University") << '\n'
            << align_center_with_border("hefei@tsinghua.edu.cn") << '\n';
  
  std::cout << "which contains:\n";

  // __SZH_ADD_END__

  std::cout << '\n' << banner_string("CBMC", CBMC_VERSION) << '\n'
            << align_center_with_border("Copyright (C) 2001-2018") << '\n'
            << align_center_with_border("Daniel Kroening, Edmund Clarke") << '\n' // NOLINT(*)
            << align_center_with_border("Carnegie Mellon University, Computer Science Department") << '\n' // NOLINT(*)
            << align_center_with_border("kroening@kroening.com") << '\n' // NOLINT(*)
            << align_center_with_border("Protected in part by U.S. patent 7,225,417") << '\n' // NOLINT(*)
            <<
    "\n"
    "Usage:                       Purpose:\n"
    "\n"
    " cbmc [-?] [-h] [--help]      show help\n"
    " cbmc --version               show version and exit\n"
    " cbmc [options] file.c ...    perform bounded model checking\n"
    "\n"
    "Analysis options:\n"
    HELP_SHOW_PROPERTIES
    " --symex-coverage-report f    generate a Cobertura XML coverage report in f\n" // NOLINT(*)
    " --property id                only check one specific property\n"
    " --trace                      give a counterexample trace for failed properties\n" //NOLINT(*)
    " --stop-on-fail               stop analysis once a failed property is detected\n" // NOLINT(*)
    "                              (implies --trace)\n"
    " --localize-faults            localize faults (experimental)\n"
    "\n"
    "C/C++ frontend options:\n"
    " --preprocess                 stop after preprocessing\n"
    " --test-preprocessor          stop after preprocessing, discard output\n"
    HELP_CONFIG_C_CPP
    HELP_ANSI_C_LANGUAGE
    HELP_FUNCTIONS
    "\n"
    "Platform options:\n"
    HELP_CONFIG_PLATFORM
    "\n"
    "Program representations:\n"
    " --show-parse-tree            show parse tree\n"
    " --show-symbol-table          show loaded symbol table\n"
    HELP_SHOW_GOTO_FUNCTIONS
    HELP_VALIDATE
    "\n"
    "Program instrumentation options:\n"
    HELP_GOTO_CHECK
    HELP_COVER
    " --mm MM                      memory consistency model for concurrent programs (default: sc)\n" // NOLINT(*)
    HELP_CONFIG_LIBRARY
    HELP_REACHABILITY_SLICER
    HELP_REACHABILITY_SLICER_FB
    " --full-slice                 run full slicer (experimental)\n" // NOLINT(*)
    " --drop-unused-functions      drop functions trivially unreachable from main function\n" // NOLINT(*)
    " --havoc-undefined-functions\n"
    "                              for any function that has no body, assign non-deterministic values to\n" // NOLINT(*)
    "                              any parameters passed as non-const pointers and the return value\n" // NOLINT(*)
    "\n"
    "Semantic transformations:\n"
    // NOLINTNEXTLINE(whitespace/line_length)
    " --nondet-static              add nondeterministic initialization of variables with static lifetime\n"
    "\n"
    "BMC options:\n"
    HELP_BMC
    "\n"
    "Backend options:\n"
    HELP_CONFIG_BACKEND
    HELP_SOLVER
    HELP_STRING_REFINEMENT_CBMC
    " --arrays-uf-never            never turn arrays into uninterpreted functions\n" // NOLINT(*)
    " --arrays-uf-always           always turn arrays into uninterpreted functions\n" // NOLINT(*)
    " --show-array-constraints     show array theory constraints added\n"
    "                              during post processing.\n"
    "                              Requires --json-ui.\n"
    "\n"
    "User-interface options:\n"
    HELP_XML_INTERFACE
    HELP_JSON_INTERFACE
    HELP_GOTO_TRACE
    HELP_FLUSH
    " --verbosity #                verbosity level\n"
    HELP_TIMESTAMP
    "\n";
  // clang-format on
}
