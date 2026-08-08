/*******************************************************************\

Module: Bounded Model Checking Utilities

Author: Daniel Kroening, Peter Schrammel

\*******************************************************************/

/// \file
/// Bounded Model Checking Utilities

#include "bmc_util.h"

#include <algorithm>
#include <iostream>
#include <unordered_set>

#include <goto-programs/graphml_witness.h>
#include <goto-programs/json_goto_trace.h>
#include <goto-programs/xml_goto_trace.h>

#include <goto-symex/build_goto_trace.h>
#include <goto-symex/memory_model_pso.h>
#include <goto-symex/memory_model_general.h>
#include <goto-symex/slice.h>
#include <goto-symex/symex_target_equation.h>

#include <linking/static_lifetime_init.h>

#include <solvers/decision_procedure.h>

#include <util/json_stream.h>
#include <util/find_symbols.h>
#include <util/make_unique.h>
#include <util/ui_message.h>

#include <cat/cat_parsing_driver.h>

#include "goto_symex_property_decider.h"
#include "symex_bmc.h"

#include "util/std_code.h"

namespace
{
bool equation_correctness_witness_write_succeeded = false;

void add_expression_symbols(
  const exprt &expression,
  find_symbols_sett &symbols)
{
  if(!expression.is_nil())
    find_symbols(expression, symbols);
}

bool is_standard_synchronization_event(const SSA_stept &step)
{
  const std::string function = id2string(step.source.function_id);
  return function.find("pthread_mutex") != std::string::npos ||
         function.find("pthread_rwlock") != std::string::npos ||
         function.find("pthread_spin") != std::string::npos ||
         function.find("pthread_cond") != std::string::npos ||
         function.find("pthread_barrier") != std::string::npos ||
         function.find("pthread_join") != std::string::npos ||
         function.find("sem_") != std::string::npos;
}

/// Audit a conservative property-rooted event closure without changing the
/// equation. This is intentionally broader than a future slicer: locations
/// are grouped by their L1 object and every write to a relevant object is
/// retained.
void property_event_cone(
  symex_target_equationt &equation,
  bool apply)
{
  using event_ptrt = const SSA_stept *;

  std::vector<event_ptrt> reads;
  std::vector<event_ptrt> writes;
  find_symbols_sett needed_symbols;
  std::unordered_set<irep_idt> relevant_locations;
  std::unordered_set<event_ptrt> retained_events;
  std::unordered_set<unsigned> retained_atomic_sections;
  std::size_t synchronization_seeds = 0;

  for(const auto &step : equation.SSA_steps)
  {
    if(step.is_shared_read())
      reads.push_back(&step);
    else if(step.is_shared_write())
      writes.push_back(&step);

    if(
      (step.is_shared_read() || step.is_shared_write()) &&
      is_standard_synchronization_event(step))
    {
      retained_events.insert(&step);
      relevant_locations.insert(step.ssa_lhs.get_l1_object_identifier());
      needed_symbols.insert(step.ssa_lhs.get_identifier());
      add_expression_symbols(step.guard, needed_symbols);
      if(step.atomic_section_id != 0)
        retained_atomic_sections.insert(step.atomic_section_id);
      ++synchronization_seeds;
    }

    if(step.is_assert() || step.is_assume() || step.is_constraint())
    {
      add_expression_symbols(step.cond_expr, needed_symbols);
      add_expression_symbols(step.guard, needed_symbols);
    }
  }

  std::size_t iterations = 0;
  bool changed = true;
  while(changed)
  {
    changed = false;
    ++iterations;

    for(const auto &step : equation.SSA_steps)
    {
      if(
        (step.is_assignment() || step.is_decl()) &&
        needed_symbols.find(step.ssa_lhs.get_identifier()) !=
          needed_symbols.end())
      {
        const auto old_symbol_count = needed_symbols.size();
        add_expression_symbols(step.ssa_rhs, needed_symbols);
        add_expression_symbols(step.guard, needed_symbols);
        add_expression_symbols(step.cond_expr, needed_symbols);
        changed = changed || needed_symbols.size() != old_symbol_count;
      }
    }

    for(const auto *read : reads)
    {
      if(
        needed_symbols.find(read->ssa_lhs.get_identifier()) ==
          needed_symbols.end() &&
        (read->atomic_section_id == 0 ||
         retained_atomic_sections.find(read->atomic_section_id) ==
           retained_atomic_sections.end()))
        continue;

      if(retained_events.insert(read).second)
        changed = true;
      if(
        relevant_locations.insert(
          read->ssa_lhs.get_l1_object_identifier()).second)
        changed = true;
      if(
        read->atomic_section_id != 0 &&
        retained_atomic_sections.insert(read->atomic_section_id).second)
        changed = true;

      const auto old_symbol_count = needed_symbols.size();
      add_expression_symbols(read->guard, needed_symbols);
      changed = changed || needed_symbols.size() != old_symbol_count;
    }

    for(const auto *write : writes)
    {
      const bool location_is_relevant =
        relevant_locations.find(write->ssa_lhs.get_l1_object_identifier()) !=
        relevant_locations.end();
      const bool atomic_section_is_relevant =
        write->atomic_section_id != 0 &&
        retained_atomic_sections.find(write->atomic_section_id) !=
          retained_atomic_sections.end();
      if(!location_is_relevant && !atomic_section_is_relevant)
        continue;

      if(retained_events.insert(write).second)
        changed = true;
      if(
        write->atomic_section_id != 0 &&
        retained_atomic_sections.insert(write->atomic_section_id).second)
        changed = true;

      const auto old_symbol_count = needed_symbols.size();
      needed_symbols.insert(write->ssa_lhs.get_identifier());
      add_expression_symbols(write->guard, needed_symbols);
      changed = changed || needed_symbols.size() != old_symbol_count;
    }
  }

  const std::size_t total_events = reads.size() + writes.size();
  const std::size_t retained_reads = std::count_if(
    reads.begin(), reads.end(), [&retained_events](const event_ptrt event) {
      return retained_events.find(event) != retained_events.end();
    });
  const std::size_t retained_writes = std::count_if(
    writes.begin(), writes.end(), [&retained_events](const event_ptrt event) {
      return retained_events.find(event) != retained_events.end();
    });

  std::cout << "NATIVE_PROPERTY_EVENT_CONE total=" << total_events
            << " reads=" << reads.size() << " writes=" << writes.size()
            << " retained=" << retained_events.size()
            << " retained_reads=" << retained_reads
            << " retained_writes=" << retained_writes
            << " removable=" << (total_events - retained_events.size())
            << " locations=" << relevant_locations.size()
            << " sync_seeds=" << synchronization_seeds
            << " iterations=" << iterations
            << " applied=" << (apply ? 1 : 0) << '\n';

  if(apply)
  {
    for(auto &step : equation.SSA_steps)
    {
      if(
        (step.is_shared_read() || step.is_shared_write()) &&
        retained_events.find(&step) == retained_events.end())
        step.ignore = true;
    }
  }
}
} // namespace

void message_building_error_trace(messaget &log)
{
  log.status() << "Building error trace" << messaget::eom;
}

void build_error_trace(
  goto_tracet &goto_trace,
  const namespacet &ns,
  const symex_target_equationt &symex_target_equation,
  const decision_proceduret &decision_procedure,
  ui_message_handlert &ui_message_handler)
{
  messaget log(ui_message_handler);
  message_building_error_trace(log);

  build_goto_trace(symex_target_equation, decision_procedure, ns, goto_trace);
}

ssa_step_predicatet
ssa_step_matches_failing_property(const irep_idt &property_id)
{
  return [property_id](
           symex_target_equationt::SSA_stepst::const_iterator step,
           const decision_proceduret &decision_procedure) {
    return step->is_assert() && step->get_property_id() == property_id &&
           decision_procedure.get(step->guard_handle).is_true() &&
           decision_procedure.get(step->cond_handle).is_false();
  };
}

void output_error_trace(
  const goto_tracet &goto_trace,
  const namespacet &ns,
  const trace_optionst &trace_options,
  ui_message_handlert &ui_message_handler)
{
  messaget msg(ui_message_handler);
  switch(ui_message_handler.get_ui())
  {
  case ui_message_handlert::uit::PLAIN:
    msg.result() << "Counterexample:" << messaget::eom;
    show_goto_trace(msg.result(), ns, goto_trace, trace_options);
    msg.result() << messaget::eom;
    break;

  case ui_message_handlert::uit::XML_UI:
  {
    const goto_trace_stept &last_step = goto_trace.get_last_step();
    property_infot info{
      last_step.pc, last_step.comment, property_statust::FAIL};
    xmlt xml_result = xml(last_step.property_id, info);
    convert(ns, goto_trace, xml_result.new_element());
    msg.result() << xml_result;
  }
  break;

  case ui_message_handlert::uit::JSON_UI:
  {
    json_stream_objectt &json_result =
      ui_message_handler.get_json_stream().push_back_stream_object();
    const goto_trace_stept &step = goto_trace.get_last_step();
    json_result["property"] = json_stringt(step.property_id);
    json_result["description"] = json_stringt(step.comment);
    json_result["status"] = json_stringt("failed");
    json_stream_arrayt &json_trace =
      json_result.push_back_stream_array("trace");
    convert<json_stream_arrayt>(ns, goto_trace, json_trace, trace_options);
  }
  break;
  }
}

/// outputs an error witness in graphml format
static bool lift_native_spawn_prefix_witness(
  const goto_tracet &input,
  goto_tracet &output)
{
  const auto reject =
    [](const std::string &reason)
    {
      std::cout
        << "NATIVE_WITNESS_PREFIX_LIFT applied=0 reason="
        << reason << '\n';
      return false;
    };
  const auto is_thread_creation =
    [](const goto_trace_stept &step)
    {
      if(
        step.pc->source_location().get("deagle_trace_provenance") ==
        "original_first_thread_create")
        return true;
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
  auto failed_assertion = input.steps.end();
  bool has_lift_provenance = false;
  std::size_t worker_guard_visits = 0;
  bool selector_value = false;
  for(auto step = input.steps.begin(); step != input.steps.end(); ++step)
  {
    const auto &location = step->pc->source_location();
    if(
      location.get("deagle_trace_lift") ==
      "single_worker_initialization_prefix_v1")
      has_lift_provenance = true;
    const irep_idt provenance =
      location.get("deagle_trace_provenance");
    if(provenance == "restricted_worker_first_iteration")
      ++worker_guard_visits;
    else if(
      provenance == "original_nondet_choice" &&
      step->is_assignment() &&
      step->full_lhs_value.is_one())
      selector_value = true;
    if(step->is_assert() && !step->cond_value)
      failed_assertion = step;
  }
  if(
    !has_lift_provenance ||
    failed_assertion == input.steps.end() ||
    failed_assertion->thread_nr == 0 ||
    worker_guard_visits != 1 ||
    !selector_value)
    return reject(
      "prefix_obligation"
      " marker=" + std::to_string(has_lift_provenance) +
      " failed=" +
      std::to_string(failed_assertion != input.steps.end()) +
      " worker_guards=" + std::to_string(worker_guard_visits) +
      " selector=" + std::to_string(selector_value));

  const unsigned failing_thread = failed_assertion->thread_nr;
  auto first_failing_thread_step = input.steps.end();
  auto spawning_step = input.steps.end();
  std::size_t spawn_guard_visits = 0;
  for(auto step = input.steps.begin(); step != input.steps.end(); ++step)
  {
    if(step->thread_nr == failing_thread)
    {
      first_failing_thread_step = step;
      break;
    }
    if(
      step->thread_nr == 0 &&
      step->pc->source_location().get("deagle_trace_provenance") ==
        "restricted_spawn_first_iteration")
      ++spawn_guard_visits;
    if(step->thread_nr == 0 && is_thread_creation(*step))
      spawning_step = step;
  }
  if(
    first_failing_thread_step == input.steps.end() ||
    spawning_step == input.steps.end() ||
    spawn_guard_visits == 0)
    return reject("missing_create_or_worker");

  for(auto step = input.steps.begin();; ++step)
  {
    output.add_step(*step);
    if(step == spawning_step)
      break;
  }
  for(auto step = first_failing_thread_step;
      step != input.steps.end(); ++step)
  {
    if(step->thread_nr == failing_thread)
      output.add_step(*step);
    if(step == failed_assertion)
      break;
  }

  std::size_t step_number = 0;
  for(auto &step : output.steps)
    step.step_nr = ++step_number;
  const bool lifted =
    !output.steps.empty() &&
    output.steps.back().is_assert() &&
    !output.steps.back().cond_value;
  if(lifted)
    std::cout
      << "NATIVE_WITNESS_PREFIX_LIFT applied=1"
      << " steps=" << output.steps.size() << '\n';
  return lifted ? true : reject("missing_final_property");
}

void output_graphml(
  const goto_tracet &goto_trace,
  const namespacet &ns,
  const optionst &options)
{
  const std::string graphml = options.get_option("graphml-witness");
  if(graphml.empty())
    return;

  // __SZH_ADD_BEGIN__
  // FALSE proof not required in no-data-race
  bool enable_datarace = options.get_bool_option("datarace");
  if(enable_datarace)
    return;
  // __SZH_ADD_END__

  goto_tracet lifted_trace;
  const goto_tracet *witness_trace = &goto_trace;
  if(
    options.get_bool_option("native-witness-spawn-prefix-lift"))
  {
    if(!lift_native_spawn_prefix_witness(
         goto_trace, lifted_trace))
      return;
    witness_trace = &lifted_trace;
  }

  graphml_witnesst graphml_witness(ns);
  graphml_witness(*witness_trace);

  std::string filename = options.get_option("filename");

  if(graphml == "-")
    write_graphml(graphml_witness.graph(), std::cout, filename, options);
  else
  {
    std::ofstream out(graphml);
    write_graphml(graphml_witness.graph(), out, filename, options);
  }
}

/// outputs a proof in graphml format
void output_graphml(
  const symex_target_equationt &symex_target_equation,
  const namespacet &ns,
  const optionst &options)
{
  const std::string graphml = options.get_option("graphml-witness");
  if(graphml.empty())
    return;

  graphml_witnesst graphml_witness(ns);
  graphml_witness(symex_target_equation);

  std::string filename = options.get_option("filename");

  if(graphml == "-")
  {
    const bool write_failed =
      write_graphml(graphml_witness.graph(), std::cout, filename, options);
    std::cout.flush();
    equation_correctness_witness_write_succeeded =
      !write_failed && std::cout.good();
  }
  else
  {
    std::ofstream out(graphml);
    const bool open_succeeded = out.good();
    const bool write_failed =
      open_succeeded
        ? write_graphml(graphml_witness.graph(), out, filename, options)
        : true;
    out.close();
    equation_correctness_witness_write_succeeded =
      open_succeeded && !write_failed && !out.fail();
  }
}

void reset_equation_correctness_witness_status()
{
  equation_correctness_witness_write_succeeded = false;
}

bool equation_correctness_witness_written()
{
  return equation_correctness_witness_write_succeeded;
}

void convert_symex_target_equation(
  symex_target_equationt &equation,
  decision_proceduret &decision_procedure,
  message_handlert &message_handler)
{
  messaget msg(message_handler);
  msg.status() << "converting SSA" << messaget::eom;

  equation.convert(decision_procedure);
}

std::unique_ptr<memory_model_baset>
get_memory_model(const optionst &options, const namespacet &ns)
{
  const std::string mm = options.get_option("mm");

  if(mm.empty() || mm == "sc")
    return util_make_unique<memory_model_sct>(ns);
  else if(mm == "tso")
    return util_make_unique<memory_model_tsot>(ns);
  else if(mm == "pso")
    return util_make_unique<memory_model_psot>(ns);
// __SZH_ADD_BEGIN__
  else // is this a .cat file?
  {
    cat_parsing_drivert cat_parser;
    cat_parser.mm_flag = options.get_bool_option("mm-flag");

    if(cat_parser.parse(mm))
    {
      std::cout << "cat parsing failed: " << mm << "\n";
      std::exit(1);
    }
    cat_parser.get_module().remove_unnecessary();
    cat_parser.get_module().build_propagate_map_all();

    bool strict_guard = options.get_bool_option("mm-strict-guard");
    bool enable_cutting = options.get_bool_option("mm-cutting");

    return util_make_unique<memory_model_generalt>(ns, cat_parser.get_module(), strict_guard, enable_cutting);
  }
// __SZH_ADD_END__
}

void setup_symex(
  symex_bmct &symex,
  const namespacet &ns,
  const optionst &options,
  ui_message_handlert &ui_message_handler)
{
  messaget msg(ui_message_handler);
  const symbolt *init_symbol;
  if(!ns.lookup(INITIALIZE_FUNCTION, init_symbol))
    symex.language_mode = init_symbol->mode;

  msg.status() << "Starting Bounded Model Checking" << messaget::eom;

  symex.last_source_location.make_nil();

  symex.unwindset.parse_unwind(options.get_option("unwind"));
  symex.unwindset.parse_unwindset(
    options.get_list_option("unwindset"), ui_message_handler);
}

void slice(
  symex_bmct &symex,
  symex_target_equationt &symex_target_equation,
  const namespacet &ns,
  const optionst &options,
  ui_message_handlert &ui_message_handler)
{
  messaget msg(ui_message_handler);

  // any properties to check at all?
  if(symex_target_equation.has_threads())
  {
    // we should build a thread-aware SSA slicer
    msg.statistics() << "no slicing due to threads" << messaget::eom;
  }
  else
  {
    if(options.get_bool_option("slice-formula"))
    {
      ::slice(symex_target_equation);
      msg.statistics() << "slicing removed "
                       << symex_target_equation.count_ignored_SSA_steps()
                       << " assignments" << messaget::eom;
    }
    else
    {
      if(options.get_bool_option("simple-slice"))
      {
        simple_slice(symex_target_equation);
        msg.statistics() << "simple slicing removed "
                         << symex_target_equation.count_ignored_SSA_steps()
                         << " assignments" << messaget::eom;
      }
    }
  }
  msg.statistics() << "Generated " << symex.get_total_vccs() << " VCC(s), "
                   << symex.get_remaining_vccs()
                   << " remaining after simplification" << messaget::eom;
}

void update_properties_status_from_symex_target_equation(
  propertiest &properties,
  std::unordered_set<irep_idt> &updated_properties,
  const symex_target_equationt &equation)
{
  for(const auto &step : equation.SSA_steps)
  {
    if(!step.is_assert())
      continue;

    irep_idt property_id = step.get_property_id();
    CHECK_RETURN(!property_id.empty());

    // Don't update status of properties that are constant 'false';
    // we wouldn't have traces for them.
    const auto status = step.cond_expr.is_true() ? property_statust::PASS
                                                 : property_statust::UNKNOWN;
    auto emplace_result = properties.emplace(
      property_id, property_infot{step.source.pc, step.comment, status});

    if(emplace_result.second)
    {
      updated_properties.insert(property_id);
    }
    else
    {
      property_infot &property_info = emplace_result.first->second;
      property_statust old_status = property_info.status;
      property_info.status |= status;

      if(property_info.status != old_status)
        updated_properties.insert(property_id);
    }
  }
}

void update_status_of_not_checked_properties(
  propertiest &properties,
  std::unordered_set<irep_idt> &updated_properties)
{
  for(auto &property_pair : properties)
  {
    if(property_pair.second.status == property_statust::NOT_CHECKED)
    {
      // This could be a NOT_CHECKED, NOT_REACHABLE or PASS,
      // but the equation doesn't give us precise information.
      property_pair.second.status = property_statust::PASS;
      updated_properties.insert(property_pair.first);
    }
  }
}

void update_status_of_unknown_properties(
  propertiest &properties,
  std::unordered_set<irep_idt> &updated_properties)
{
  for(auto &property_pair : properties)
  {
    if(property_pair.second.status == property_statust::UNKNOWN)
    {
      // This could have any status except NOT_CHECKED.
      // We consider them PASS because we do verification modulo bounds.
      property_pair.second.status = property_statust::PASS;
      updated_properties.insert(property_pair.first);
    }
  }
}

void output_coverage_report(
  const std::string &cov_out,
  const abstract_goto_modelt &goto_model,
  const symex_bmct &symex,
  ui_message_handlert &ui_message_handler)
{
  if(
    !cov_out.empty() &&
    symex.output_coverage_report(goto_model.get_goto_functions(), cov_out))
  {
    messaget log(ui_message_handler);
    log.error() << "Failed to write symex coverage report to '" << cov_out
                << "'" << messaget::eom;
  }
}

void postprocess_equation(
  symex_bmct &symex,
  symex_target_equationt &equation,
  const optionst &options,
  const namespacet &ns,
  ui_message_handlert &ui_message_handler)
{
  const auto postprocess_equation_start = std::chrono::steady_clock::now();
  // add a partial ordering, if required

  if(equation.has_threads())
  {
    const std::string memory_model_name = options.get_option("mm");
    const bool supported_memory_model =
      memory_model_name.empty() || memory_model_name == "sc" ||
      memory_model_name == "tso" || memory_model_name == "pso";
    const bool apply_property_event_cone =
      supported_memory_model && !options.get_bool_option("datarace") &&
      !options.get_bool_option("deadlock") &&
      !options.get_bool_option("pointer-check") &&
      !options.get_bool_option("alloc-check") &&
      !options.get_bool_option("memory-leak-check");
    property_event_cone(equation, apply_property_event_cone);

    std::unique_ptr<memory_model_baset> memory_model =
      get_memory_model(options, ns);

    // __SZH_ADD_BEGIN__
    if(options.get_bool_option("deagle-closure"))
    {
      memory_model->use_deagle = true;
      equation.use_deagle_closure = true;
      if(options.get_bool_option("native-indexed-dispatch"))
        equation.use_native_indexed_dispatch = true;
      else if(options.get_bool_option("native-adaptive-indexed-dispatch"))
        equation.use_native_adaptive_indexed_dispatch = true;
    }
    else if(options.get_bool_option("deagle-icd"))
    {
      memory_model->use_deagle = true;
      equation.use_deagle_icd = true;
    }
    else if(options.get_bool_option("deagle-segment"))
    {
      memory_model->use_deagle = true;
      equation.use_deagle_segment = true;
      if(
        options.get_bool_option("native-indexed-dispatch") ||
        options.get_bool_option("native-adaptive-indexed-dispatch"))
        equation.use_native_indexed_dispatch = true;
    }
    if(options.get_bool_option("datarace"))
      memory_model->enable_datarace = true;
    // __SZH_ADD_END__

    // __WP_ADD_BEGIN__
    if(options.get_bool_option("deadlock"))
      memory_model->enable_deadlock = true;
    // __WP_ADD_END__

    (*memory_model)(equation, ui_message_handler);
  }

  messaget log(ui_message_handler);
  log.statistics() << "size of program expression: "
                   << equation.SSA_steps.size() << " steps" << messaget::eom;

  slice(symex, equation, ns, options, ui_message_handler);

  if(options.get_bool_option("validate-ssa-equation"))
  {
    symex.validate(validation_modet::INVARIANT);
  }

  const auto postprocess_equation_stop = std::chrono::steady_clock::now();
  std::chrono::duration<double> postprocess_equation_runtime =
    std::chrono::duration<double>(
      postprocess_equation_stop - postprocess_equation_start);
  log.status() << "Runtime Postprocess Equation: "
               << postprocess_equation_runtime.count() << "s" << messaget::eom;
}

#include <solvers/sat/satcheck_minisat2.h>
#include <solvers/prop/prop_conv_solver.h>

std::chrono::duration<double> prepare_property_decider(
  propertiest &properties,
  symex_target_equationt &equation,
  goto_symex_property_decidert &property_decider,
  ui_message_handlert &ui_message_handler)
{
  auto solver_start = std::chrono::steady_clock::now();

  messaget log(ui_message_handler);
  log.status()
    << "Passing problem to "
    << property_decider.get_decision_procedure().decision_procedure_text()
    << messaget::eom;

  convert_symex_target_equation(
    equation, property_decider.get_decision_procedure(), ui_message_handler);
  property_decider.update_properties_goals_from_symex_target_equation(
    properties);
  property_decider.convert_goals();

  // __SZH_ADD_BEGIN__
  if(equation.use_cat)
  {
    auto& memory_model_solver = *(memory_model_solvert*)(&(property_decider.get_solver()->prop()));
    auto& decision_procedure = *(prop_conv_solvert*)(&(property_decider.get_decision_procedure()));

    std::cout << "Set Deagle memory model solver's graph\n";

    //set graph
    oc_edge_tablet oc_edge_table;
    for(auto& edge: equation.oc_edges)
    {
      literalt expr = decision_procedure.convert(edge.expr);
      Minisat::Lit expr_final = Minisat::mkLit(expr.var_no(), expr.sign());
      oc_edge_table.push_back(std::make_pair(std::make_pair(edge.e1_str, edge.e2_str), std::make_pair(expr_final, edge.kind)));

      //std::cout << edge.e1_str << " " << edge.e2_str << ": " << edge.kind << "\n";
    }

    oc_label_tablet oc_label_table;
    for(auto& label: equation.oc_labels)
    {
      literalt expr = decision_procedure.convert(label.expr);
      Minisat::Lit expr_final = Minisat::mkLit(expr.var_no(), expr.sign());
      oc_label_table.push_back(std::make_pair(label.e_str, std::make_pair(expr_final, label.label)));

      //std::cout << label.e_str << ": " << label.label << "\n";
    }

    memory_model_solver.save_raw_graph(oc_edge_table, oc_label_table, equation.cat);
  }
  else if(equation.use_deagle_closure)
  {
    auto& deagle_closure_solver = *(deagle_closure_solvert*)(&(property_decider.get_solver()->prop()));
    auto& decision_procedure = *(prop_conv_solvert*)(&(property_decider.get_decision_procedure()));

    if(equation.use_native_indexed_dispatch)
      deagle_closure_solver.enable_native_indexed_dispatch();
    else if(equation.use_native_adaptive_indexed_dispatch)
      deagle_closure_solver.enable_native_adaptive_indexed_dispatch();

    std::cout << "Set Deagle closure solver's graph\n";

    //set graph
    oc_edge_tablet oc_edge_table;

    for(auto& edge: equation.oc_edges)
    {
      literalt expr = decision_procedure.convert(edge.expr);
      Minisat::Lit expr_final = Minisat::mkLit(expr.var_no(), expr.sign());
      oc_edge_table.push_back(std::make_pair(std::make_pair(edge.e1_str, edge.e2_str), std::make_pair(expr_final, edge.kind)));

      //std::cout << edge.e1_str << " " << edge.e2_str << ": " << edge.kind << "\n";
    }

    oc_guard_mapt oc_guard_map;
    oc_location_mapt oc_location_map;
    for(auto& e_it: equation.oc_guard_map)
    {
        std::string name = id2string(e_it->ssa_lhs.get_identifier());
        int location = std::atoi(e_it->source.pc->source_location().get_line().c_str());
        literalt guard = decision_procedure.convert(e_it->guard);
        Minisat::Lit guard_final = Minisat::mkLit(guard.var_no(), guard.sign());
        oc_guard_map.insert(std::make_pair(name, guard_final));
        oc_location_map.insert(std::make_pair(name, location));
    }

    deagle_closure_solver.save_raw_graph(oc_edge_table, oc_guard_map, oc_location_map, equation.oc_result_order);
  }
  else if(equation.use_deagle_icd)
  {
    auto& deagle_icd_solver = *(deagle_icd_solvert*)(&(property_decider.get_solver()->prop()));
    auto& decision_procedure = *(prop_conv_solvert*)(&(property_decider.get_decision_procedure()));

    std::cout << "Set Deagle ICD solver's graph\n";

    //set graph
    oc_edge_tablet oc_edge_table;

    for(auto& edge: equation.oc_edges)
    {
      literalt expr = decision_procedure.convert(edge.expr);
      Minisat::Lit expr_final = Minisat::mkLit(expr.var_no(), expr.sign());
      oc_edge_table.push_back(std::make_pair(std::make_pair(edge.e1_str, edge.e2_str), std::make_pair(expr_final, edge.kind)));

      //std::cout << edge.e1_str << " " << edge.e2_str << ": " << edge.kind << "\n";
    }

    deagle_icd_solver.save_raw_graph(oc_edge_table, equation.oc_result_order);
  }
  else if(equation.use_deagle_segment)
  {
    auto& deagle_segment_solver = *(deagle_segment_solvert*)(&(property_decider.get_solver()->prop()));
    auto& decision_procedure = *(prop_conv_solvert*)(&(property_decider.get_decision_procedure()));

    std::cout << "Set Deagle segment solver's graph\n";

    if(equation.use_native_indexed_dispatch)
      deagle_segment_solver.enable_native_indexed_dispatch();

    //set graph
    oc_edge_tablet oc_edge_table;

    for(auto& edge: equation.oc_edges)
    {
      literalt expr = decision_procedure.convert(edge.expr);
      Minisat::Lit expr_final = Minisat::mkLit(expr.var_no(), expr.sign());
      oc_edge_table.push_back(std::make_pair(std::make_pair(edge.e1_str, edge.e2_str), std::make_pair(expr_final, edge.kind)));

      //std::cout << edge.e1_str << " " << edge.e2_str << ": " << edge.kind << "\n";
    }

    oc_guard_mapt oc_guard_map;
    oc_location_mapt oc_location_map;
    for(auto& e_it: equation.oc_guard_map)
    {
        std::string name = id2string(e_it->ssa_lhs.get_identifier());
        int location = std::atoi(e_it->source.pc->source_location().get_line().c_str());
        literalt guard = decision_procedure.convert(e_it->guard);
        Minisat::Lit guard_final = Minisat::mkLit(guard.var_no(), guard.sign());
        oc_guard_map.insert(std::make_pair(name, guard_final));
        oc_location_map.insert(std::make_pair(name, location));
    }

    deagle_segment_solver.save_raw_graph(oc_edge_table, oc_guard_map, oc_location_map, equation.oc_result_order);
  }
  // __SZH_ADD_END__

  auto solver_stop = std::chrono::steady_clock::now();
  return std::chrono::duration<double>(solver_stop - solver_start);
}

void run_property_decider(
  incremental_goto_checkert::resultt &result,
  propertiest &properties,
  goto_symex_property_decidert &property_decider,
  ui_message_handlert &ui_message_handler,
  std::chrono::duration<double> solver_runtime,
  bool set_pass)
{
  auto solver_start = std::chrono::steady_clock::now();

  messaget log(ui_message_handler);
  log.status()
    << "Running "
    << property_decider.get_decision_procedure().decision_procedure_text()
    << messaget::eom;

  property_decider.add_constraint_from_goals(
    [&properties](const irep_idt &property_id) {
      return is_property_to_check(properties.at(property_id).status);
    });

  auto const sat_solver_start = std::chrono::steady_clock::now();

  decision_proceduret::resultt dec_result = property_decider.solve();

  auto const sat_solver_stop = std::chrono::steady_clock::now();
  std::chrono::duration<double> sat_solver_runtime =
    std::chrono::duration<double>(sat_solver_stop - sat_solver_start);
  log.status() << "Runtime Solver: " << sat_solver_runtime.count() << "s"
               << messaget::eom;

  property_decider.update_properties_status_from_goals(
    properties, result.updated_properties, dec_result, set_pass);

  auto solver_stop = std::chrono::steady_clock::now();
  solver_runtime += std::chrono::duration<double>(solver_stop - solver_start);
  log.status() << "Runtime decision procedure: " << solver_runtime.count()
               << "s" << messaget::eom;

  if(dec_result == decision_proceduret::resultt::D_SATISFIABLE)
  {
    result.progress = incremental_goto_checkert::resultt::progresst::FOUND_FAIL;
  }
}
