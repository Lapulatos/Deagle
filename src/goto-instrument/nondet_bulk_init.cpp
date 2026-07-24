/*******************************************************************\

Module: Exact pre-thread nondeterministic bulk initialization

\*******************************************************************/

#include "nondet_bulk_init.h"

#include <analyses/natural_loops.h>

#include <goto-programs/goto_convert_class.h>
#include <goto-programs/remove_skip.h>

#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/message.h>
#include <util/pointer_expr.h>
#include <util/pointer_offset_size.h>
#include <util/std_expr.h>
#include <util/std_types.h>

#include <algorithm>
#include <iterator>
#include <map>
#include <set>
#include <string>
#include <vector>

namespace
{
class havoc_slice_convertt : public goto_convertt
{
public:
  havoc_slice_convertt(
    symbol_table_baset &symbol_table,
    message_handlert &message_handler)
    : goto_convertt(symbol_table, message_handler)
  {
  }

  void lower(
    const symbol_exprt &function,
    const exprt::operandst &arguments,
    goto_programt &dest,
    const irep_idt &mode)
  {
    do_havoc_slice(nil_exprt{}, function, arguments, dest, mode);
  }
};

struct loop_matcht
{
  goto_programt::targett head;
  goto_programt::targett first_body;
  goto_programt::targett backedge;
  exprt index;
  exprt bound;
  exprt pointer;
  typet element_type;
};

bool is_one(const exprt &expr)
{
  if(!expr.is_constant())
    return false;
  const auto value = numeric_cast<mp_integer>(to_constant_expr(expr));
  return value.has_value() && *value == 1;
}

bool same_expr(const exprt &lhs, const exprt &rhs)
{
  return lhs == rhs;
}

bool match_loop(
  goto_programt &body,
  const goto_programt::targett head,
  const natural_loops_mutablet::natural_loopt &loop,
  loop_matcht &match)
{
  if(loop.size() != 7 || !head->is_goto() || head->condition().id() != ID_not)
    return false;

  const exprt &exit_test = to_not_expr(head->condition()).op();
  if(exit_test.id() != ID_lt)
    return false;
  const auto &less = to_binary_relation_expr(exit_test);
  const exprt &index = less.lhs();
  const exprt &bound = less.rhs();
  if(index.id() != ID_symbol)
    return false;

  auto decl = std::next(head);
  auto nondet = std::next(decl);
  auto store = std::next(nondet);
  auto dead = std::next(store);
  auto increment = std::next(dead);
  auto backedge = std::next(increment);
  if(backedge == body.instructions.end())
    return false;

  const std::vector<goto_programt::targett> ordered = {
    head, decl, nondet, store, dead, increment, backedge};
  if(!std::all_of(
       ordered.begin(), ordered.end(),
       [&](const goto_programt::targett target) {
         return std::find(loop.begin(), loop.end(), target) != loop.end();
       }))
    return false;

  if(
    !decl->is_decl() || !nondet->is_assign() || !store->is_assign() ||
    !dead->is_dead() || !increment->is_assign() || !backedge->is_goto() ||
    !backedge->condition().is_true() || backedge->get_target() != head)
    return false;

  const exprt &assigned_rhs = nondet->assign_rhs();
  const exprt &nondet_rhs =
    assigned_rhs.id() == ID_typecast
      ? to_typecast_expr(assigned_rhs).op()
      : assigned_rhs;
  if(
    nondet_rhs.id() != ID_side_effect ||
    to_side_effect_expr(nondet_rhs).get_statement() != ID_nondet)
    return false;
  if(
    assigned_rhs.id() == ID_typecast &&
    assigned_rhs.type() != store->assign_lhs().type())
    return false;
  if(
    nondet->assign_lhs().id() != ID_symbol ||
    !same_expr(store->assign_rhs(), nondet->assign_lhs()) ||
    store->assign_lhs().id() != ID_dereference)
    return false;

  const exprt &pointer = to_dereference_expr(store->assign_lhs()).pointer();
  if(pointer.id() != ID_plus || pointer.operands().size() != 2)
    return false;
  const auto &plus = to_plus_expr(pointer);
  if(!same_expr(plus.op1(), index))
    return false;

  const exprt &increment_rhs = increment->assign_rhs();
  if(
    !same_expr(increment->assign_lhs(), index) ||
    increment_rhs.id() != ID_plus || increment_rhs.operands().size() != 2)
    return false;
  const auto &increment_plus = to_plus_expr(increment_rhs);
  if(!same_expr(increment_plus.op0(), index) || !is_one(increment_plus.op1()))
    return false;

  if(head == body.instructions.begin())
    return false;
  const auto init = std::prev(head);
  if(
    !init->is_assign() || !same_expr(init->assign_lhs(), index) ||
    !init->assign_rhs().is_zero())
    return false;

  const typet &element_type = store->assign_lhs().type();
  if(
    element_type.id() == ID_signedbv || element_type.id() == ID_unsignedbv)
  {
    if(to_bitvector_type(element_type).get_width() % 8 != 0)
      return false;
  }
  else if(element_type.id() != ID_c_bool && element_type.id() != ID_bool)
    return false;

  match = {head, decl, backedge, index, bound, plus.op0(), element_type};
  return true;
}

optionalt<irep_idt> direct_callee(const goto_programt::instructiont &instruction)
{
  if(
    !instruction.is_function_call() ||
    instruction.call_function().id() != ID_symbol)
    return {};
  return to_symbol_expr(instruction.call_function()).get_identifier();
}

bool is_thread_create(const irep_idt &identifier)
{
  const std::string name = id2string(identifier);
  const std::string suffix = "::pthread_create";
  return name == "pthread_create" ||
         name == CPROVER_PREFIX "pthread_create" ||
         (name.size() > suffix.size() &&
          name.compare(name.size() - suffix.size(), suffix.size(), suffix) == 0);
}

std::set<irep_idt> spawn_capable_functions(const goto_modelt &model)
{
  std::map<irep_idt, std::set<irep_idt>> calls;
  std::set<irep_idt> result;
  for(const auto &entry : model.goto_functions.function_map)
  {
    for(const auto &instruction : entry.second.body.instructions)
    {
      if(instruction.is_start_thread())
        result.insert(entry.first);
      const auto callee = direct_callee(instruction);
      if(callee.has_value())
      {
        calls[entry.first].insert(*callee);
        if(is_thread_create(*callee))
          result.insert(entry.first);
      }
    }
  }

  bool changed;
  do
  {
    changed = false;
    for(const auto &entry : calls)
    {
      if(result.find(entry.first) != result.end())
        continue;
      if(std::any_of(
           entry.second.begin(),
           entry.second.end(),
           [&](const irep_idt &callee) {
             return result.find(callee) != result.end();
           }))
      {
        result.insert(entry.first);
        changed = true;
      }
    }
  } while(changed);
  return result;
}

bool called_only_before_threads(
  const goto_modelt &model,
  const irep_idt &candidate,
  const std::set<irep_idt> &spawn_capable)
{
  const auto main_it = model.goto_functions.function_map.find(ID_main);
  if(main_it == model.goto_functions.function_map.end())
    return false;

  bool found = false;
  bool spawned = false;
  for(const auto &entry : model.goto_functions.function_map)
  {
    for(auto instruction = entry.second.body.instructions.begin();
        instruction != entry.second.body.instructions.end();
        ++instruction)
    {
      const auto callee = direct_callee(*instruction);
      if(!callee.has_value() || *callee != candidate)
        continue;
      if(entry.first != ID_main)
        return false;
      found = true;
    }
  }

  const auto &main_body = main_it->second.body;
  std::vector<goto_programt::const_targett> candidate_calls;
  for(auto instruction = main_body.instructions.begin();
      instruction != main_body.instructions.end();
      ++instruction)
  {
    const auto callee = direct_callee(*instruction);
    if(callee.has_value() && *callee == candidate)
    {
      if(spawned)
        return false;
      candidate_calls.push_back(instruction);
    }
    if(
      instruction->is_start_thread() ||
      (callee.has_value() && is_thread_create(*callee)) ||
      (callee.has_value() && spawn_capable.find(*callee) != spawn_capable.end()))
      spawned = true;
  }
  if(!found || candidate_calls.empty())
    return false;

  if(spawned)
  {
    for(auto instruction = main_body.instructions.begin();
        instruction != main_body.instructions.end();
        ++instruction)
    {
      if(!instruction->is_backwards_goto())
        continue;
      for(const auto call : candidate_calls)
      {
        if(
          instruction->location_number > call->location_number &&
          instruction->get_target()->location_number <= call->location_number)
          return false;
      }
    }
  }
  return true;
}
} // namespace

nondet_bulk_init_statst nondet_bulk_init(
  goto_modelt &goto_model,
  message_handlert &message_handler)
{
  nondet_bulk_init_statst stats;
  const namespacet ns(goto_model.symbol_table);
  const auto spawn_capable = spawn_capable_functions(goto_model);
  havoc_slice_convertt converter(goto_model.symbol_table, message_handler);
  symbol_exprt havoc_function(
    CPROVER_PREFIX "havoc_slice", code_typet({}, empty_typet{}));

  std::set<irep_idt> candidate_source_files;
  std::size_t eligible_candidates = 0;
  for(auto &entry : goto_model.goto_functions.function_map)
  {
    auto &function = entry.second;
    natural_loops_mutablet natural_loops(function.body);
    for(const auto &natural_loop : natural_loops.loop_map)
    {
      loop_matcht match;
      if(
        !match_loop(
          function.body, natural_loop.first, natural_loop.second, match))
        continue;
      ++stats.candidate_loops;
      if(!called_only_before_threads(goto_model, entry.first, spawn_capable))
      {
        ++stats.rejected_non_prethread;
        continue;
      }
      const irep_idt file = match.head->source_location().get_file();
      if(file.empty())
      {
        ++stats.rejected_nonterminal;
        continue;
      }
      candidate_source_files.insert(file);
      ++eligible_candidates;
    }
  }

  std::size_t source_loops = 0;
  for(auto &entry : goto_model.goto_functions.function_map)
  {
    natural_loops_mutablet natural_loops(entry.second.body);
    for(const auto &natural_loop : natural_loops.loop_map)
    {
      const irep_idt file =
        natural_loop.first->source_location().get_file();
      if(candidate_source_files.find(file) != candidate_source_files.end())
        ++source_loops;
    }
  }

  if(
    eligible_candidates == 0 ||
    source_loops != eligible_candidates ||
    stats.rejected_non_prethread != 0 ||
    stats.rejected_nonterminal != 0)
  {
    if(source_loops != eligible_candidates)
      stats.rejected_nonterminal += eligible_candidates;
    return stats;
  }

  for(auto &entry : goto_model.goto_functions.function_map)
  {
    auto &function = entry.second;
    natural_loops_mutablet natural_loops(function.body);
    for(const auto &natural_loop : natural_loops.loop_map)
    {
      loop_matcht match;
      if(
        !match_loop(
          function.body, natural_loop.first, natural_loop.second, match))
        continue;

      const auto element_size = size_of_expr(match.element_type, ns);
      if(!element_size.has_value())
        continue;
      const mult_exprt byte_count(
        typecast_exprt::conditional_cast(*element_size, size_type()),
        typecast_exprt::conditional_cast(match.bound, size_type()));
      const exprt pointer = typecast_exprt::conditional_cast(
        match.pointer, pointer_type(empty_typet{}));

      goto_programt replacement;
      converter.lower(
        havoc_function,
        {pointer, byte_count},
        replacement,
        goto_model.symbol_table.lookup_ref(entry.first).mode);
      replacement.add(goto_programt::make_assignment(
        match.index, match.bound, match.head->source_location()));
      function.body.destructive_insert(match.first_body, replacement);

      for(auto instruction = match.first_body;; ++instruction)
      {
        instruction->turn_into_skip();
        if(instruction == match.backedge)
          break;
      }
      remove_skip(function.body);
      ++stats.transformed_loops;
      break;
    }
  }
  goto_model.goto_functions.update();
  return stats;
}
