/*******************************************************************\

Module: Protocol-Induced Capacity Cutoff

\*******************************************************************/

#include "protocol_capacity_analysis.h"

#include <goto-programs/goto_model.h>

#include <util/arith_tools.h>
#include <util/expr_util.h>
#include <util/pointer_expr.h>
#include <util/std_code.h>
#include <util/std_expr.h>
#include <util/symbol.h>

#include <algorithm>
#include <deque>
#include <iostream>
#include <iterator>
#include <map>
#include <set>
#include <sstream>
#include <string>
#include <vector>

namespace
{
const exprt &strip(const exprt &expr)
{
  return skip_typecast(expr);
}

bool symbol_id(const exprt &src, irep_idt &identifier)
{
  const exprt &expr = strip(src);
  if(expr.id() != ID_symbol)
    return false;
  identifier = to_symbol_expr(expr).get_identifier();
  return true;
}

bool direct_call(
  const goto_programt::instructiont &instruction,
  irep_idt &callee)
{
  return instruction.is_function_call() &&
         symbol_id(instruction.call_function(), callee);
}

bool returns_fresh_allocation(
  const goto_modelt &model,
  const irep_idt &callee)
{
  const auto function = model.goto_functions.function_map.find(callee);
  if(function == model.goto_functions.function_map.end())
    return false;

  std::map<irep_idt, bool> allocation_origin;
  std::size_t malloc_calls = 0;
  std::size_t returns = 0;
  bool all_returns_fresh = true;
  for(const auto &instruction : function->second.body.instructions)
  {
    irep_idt called;
    if(direct_call(instruction, called))
    {
      if(called != "malloc" || instruction.call_lhs().is_nil())
        continue;
      irep_idt lhs;
      if(!symbol_id(instruction.call_lhs(), lhs))
        return false;
      ++malloc_calls;
      allocation_origin[lhs] = true;
      continue;
    }
    if(instruction.is_assign())
    {
      irep_idt lhs;
      irep_idt rhs;
      if(symbol_id(instruction.assign_lhs(), lhs))
        allocation_origin[lhs] =
          symbol_id(instruction.assign_rhs(), rhs) &&
          allocation_origin[rhs];
      continue;
    }
    if(instruction.is_set_return_value())
    {
      irep_idt returned;
      ++returns;
      all_returns_fresh =
        all_returns_fresh &&
        symbol_id(instruction.return_value(), returned) &&
        allocation_origin[returned];
    }
  }
  return malloc_calls == 1 && returns == 1 && all_returns_fresh;
}

bool addressed_symbol(const exprt &src, irep_idt &identifier)
{
  const exprt &expr = strip(src);
  return expr.id() == ID_address_of &&
         symbol_id(to_address_of_expr(expr).object(), identifier);
}

bool thread_entry(const exprt &src, irep_idt &identifier)
{
  const exprt &expr = strip(src);
  return expr.id() == ID_address_of &&
         symbol_id(strip(to_address_of_expr(expr).object()), identifier);
}

bool integer_constant(const exprt &src, mp_integer &value)
{
  const exprt &expr = strip(src);
  return expr.id() == ID_constant &&
         !to_integer(to_constant_expr(expr), value);
}

bool unit_increment(
  const goto_programt::instructiont &instruction,
  irep_idt &identifier)
{
  if(!instruction.is_assign() ||
     !symbol_id(instruction.assign_lhs(), identifier))
    return false;
  const exprt &rhs = strip(instruction.assign_rhs());
  if(rhs.id() != ID_plus || rhs.operands().size() != 2)
    return false;
  irep_idt source;
  mp_integer step;
  return symbol_id(rhs.op0(), source) && source == identifier &&
         integer_constant(rhs.op1(), step) && step == 1;
}

struct indexed_accesst
{
  irep_idt base;
  irep_idt index;
};

bool indexed_access(const exprt &src, indexed_accesst &result)
{
  const exprt &expr = strip(src);
  if(expr.id() == ID_index && expr.operands().size() == 2)
    return symbol_id(expr.op0(), result.base) &&
           symbol_id(expr.op1(), result.index);
  if(expr.id() != ID_dereference || expr.operands().size() != 1)
    return false;
  const exprt &pointer = strip(to_dereference_expr(expr).pointer());
  if(pointer.id() != ID_plus || pointer.operands().size() != 2)
    return false;
  if(
    symbol_id(pointer.op0(), result.base) &&
    symbol_id(pointer.op1(), result.index))
    return true;
  return symbol_id(pointer.op1(), result.base) &&
         symbol_id(pointer.op0(), result.index);
}

struct labelled_accesst
{
  indexed_accesst access;
  irep_idt label;
};

void collect_labelled_equalities(
  const exprt &src,
  std::vector<labelled_accesst> &result)
{
  const exprt &expr = strip(src);
  if(expr.id() == ID_equal && expr.operands().size() == 2)
  {
    labelled_accesst candidate;
    if(
      indexed_access(expr.op0(), candidate.access) &&
      symbol_id(expr.op1(), candidate.label))
      result.push_back(candidate);
    else if(
      indexed_access(expr.op1(), candidate.access) &&
      symbol_id(expr.op0(), candidate.label))
      result.push_back(candidate);
  }
  for(const auto &operand : expr.operands())
    collect_labelled_equalities(operand, result);
}

bool exact_labelled_equality(
  const exprt &src,
  const labelled_accesst &expected)
{
  const exprt &expr = strip(src);
  if(expr.id() != ID_equal || expr.operands().size() != 2)
    return false;
  labelled_accesst candidate;
  if(
    indexed_access(expr.op0(), candidate.access) &&
    symbol_id(expr.op1(), candidate.label))
  {
  }
  else if(
    indexed_access(expr.op1(), candidate.access) &&
    symbol_id(expr.op0(), candidate.label))
  {
  }
  else
    return false;
  return candidate.access.base == expected.access.base &&
         candidate.access.index == expected.access.index &&
         candidate.label == expected.label;
}

bool truth_of_symbol(const exprt &src, const irep_idt &identifier)
{
  const exprt &expr = strip(src);
  irep_idt candidate;
  if(symbol_id(expr, candidate))
    return candidate == identifier;
  if(expr.id() != ID_notequal || expr.operands().size() != 2)
    return false;
  mp_integer zero;
  return
    ((symbol_id(expr.op0(), candidate) && candidate == identifier &&
      integer_constant(expr.op1(), zero) && zero == 0) ||
     (symbol_id(expr.op1(), candidate) && candidate == identifier &&
      integer_constant(expr.op0(), zero) && zero == 0));
}

bool valid_safety_update(
  const exprt &src,
  const irep_idt &safety,
  const labelled_accesst &access)
{
  const exprt &expr = strip(src);
  if(exact_labelled_equality(expr, access))
    return true;
  if(expr.id() != ID_and || expr.operands().size() != 2)
    return false;
  return
    (truth_of_symbol(expr.op0(), safety) &&
     exact_labelled_equality(expr.op1(), access)) ||
    (truth_of_symbol(expr.op1(), safety) &&
     exact_labelled_equality(expr.op0(), access));
}

void count_indexed_bases(
  const exprt &src,
  std::map<irep_idt, std::size_t> &counts)
{
  indexed_accesst access;
  if(indexed_access(src, access))
  {
    ++counts[access.base];
    return;
  }
  for(const auto &operand : src.operands())
    count_indexed_bases(operand, counts);
}

bool find_cursor_bounds(
  const exprt &src,
  const irep_idt &cursor,
  bool &nonnegative,
  irep_idt &size)
{
  const exprt &expr = strip(src);
  if(
    (expr.id() == ID_ge || expr.id() == ID_gt) &&
    expr.operands().size() == 2)
  {
    irep_idt candidate;
    mp_integer value;
    if(
      symbol_id(expr.op0(), candidate) && candidate == cursor &&
      integer_constant(expr.op1(), value) && value == 0)
      nonnegative = true;
  }
  if(expr.id() == ID_lt && expr.operands().size() == 2)
  {
    irep_idt candidate;
    irep_idt bound;
    if(
      symbol_id(expr.op0(), candidate) && candidate == cursor &&
      symbol_id(expr.op1(), bound))
      size = bound;
  }
  for(const auto &operand : expr.operands())
    find_cursor_bounds(operand, cursor, nonnegative, size);
  return nonnegative && !size.empty();
}

void find_greater_peer(
  const exprt &src,
  const irep_idt &cursor,
  irep_idt &peer)
{
  const exprt &expr = strip(src);
  if(expr.id() == ID_gt && expr.operands().size() == 2)
  {
    irep_idt left;
    irep_idt right;
    if(
      symbol_id(expr.op0(), left) && symbol_id(expr.op1(), right) &&
      right == cursor)
      peer = left;
  }
  for(const auto &operand : expr.operands())
    find_greater_peer(operand, cursor, peer);
}

void collect_symbols(const exprt &src, std::set<irep_idt> &result)
{
  const exprt &expr = strip(src);
  if(expr.id() == ID_symbol)
    result.insert(to_symbol_expr(expr).get_identifier());
  for(const auto &operand : expr.operands())
    collect_symbols(operand, result);
}

bool contains_negated_symbol(const exprt &src, const irep_idt &identifier)
{
  const exprt &expr = strip(src);
  if(expr.id() == ID_not && expr.operands().size() == 1)
  {
    std::set<irep_idt> symbols;
    collect_symbols(expr.op0(), symbols);
    return symbols.size() == 1 && *symbols.begin() == identifier;
  }
  if(expr.id() == ID_equal && expr.operands().size() == 2)
  {
    irep_idt candidate;
    mp_integer value;
    return (symbol_id(expr.op0(), candidate) &&
            candidate == identifier &&
            integer_constant(expr.op1(), value) && value == 0) ||
           (symbol_id(expr.op1(), candidate) &&
            candidate == identifier &&
            integer_constant(expr.op0(), value) && value == 0);
  }
  return false;
}

enum class action_kindt
{
  SEND,
  RECEIVE
};

struct protocol_actiont
{
  action_kindt kind;
  irep_idt queue;
  irep_idt cursor;
  irep_idt label;
  irep_idt safety;
  irep_idt size;
  irep_idt nonempty_peer;
  irep_idt phase;
  mp_integer next_phase = 0;
  bool has_phase = false;
  unsigned location = 0;
};

struct protocol_workert
{
  irep_idt entry;
  std::vector<protocol_actiont> actions;
  bool may_terminate_each_phase = false;
};

struct atomic_regiont
{
  goto_programt::const_targett begin;
  goto_programt::const_targett end;
};

bool collect_atomic_regions(
  const goto_programt &program,
  std::vector<atomic_regiont> &regions,
  std::string &reason)
{
  bool inside = false;
  goto_programt::const_targett begin;
  for(auto instruction = program.instructions.begin();
      instruction != program.instructions.end(); ++instruction)
  {
    if(instruction->is_atomic_begin())
    {
      if(inside)
      {
        reason = "nested_atomic";
        return false;
      }
      inside = true;
      begin = instruction;
    }
    else if(instruction->is_atomic_end())
    {
      if(!inside)
      {
        reason = "unbalanced_atomic_end";
        return false;
      }
      regions.push_back({begin, instruction});
      inside = false;
    }
  }
  if(inside)
  {
    reason = "unbalanced_atomic_begin";
    return false;
  }
  if(regions.empty())
  {
    reason = "no_atomic_regions";
    return false;
  }
  return true;
}

bool parse_action(
  const atomic_regiont &region,
  protocol_actiont &result,
  std::string &reason)
{
  std::vector<labelled_accesst> assumed_accesses;
  std::vector<labelled_accesst> assigned_accesses;
  std::vector<irep_idt> increments;
  std::vector<std::pair<irep_idt, mp_integer>> constant_assignments;
  std::vector<irep_idt> assigned_access_lhs;
  std::vector<exprt> assumptions;
  exprt safety_rhs;

  for(auto instruction = std::next(region.begin);
      instruction != region.end; ++instruction)
  {
    if(instruction->is_function_call())
    {
      irep_idt callee;
      if(
        !direct_call(*instruction, callee) ||
        callee != "assume_abort_if_not" ||
        instruction->call_arguments().size() != 1)
      {
        reason = "atomic_call";
        return false;
      }
      collect_labelled_equalities(
        instruction->call_arguments()[0], assumed_accesses);
      assumptions.push_back(instruction->call_arguments()[0]);
    }
    else if(instruction->is_assign())
    {
      irep_idt increment;
      if(unit_increment(*instruction, increment))
      {
        increments.push_back(increment);
        continue;
      }

      irep_idt lhs;
      if(!symbol_id(instruction->assign_lhs(), lhs))
      {
        reason = "atomic_assignment_lhs";
        return false;
      }
      std::vector<labelled_accesst> rhs_accesses;
      collect_labelled_equalities(instruction->assign_rhs(), rhs_accesses);
      if(!rhs_accesses.empty())
      {
        assigned_accesses.insert(
          assigned_accesses.end(),
          rhs_accesses.begin(),
          rhs_accesses.end());
        assigned_access_lhs.push_back(lhs);
        safety_rhs = instruction->assign_rhs();
        continue;
      }
      mp_integer value;
      if(integer_constant(instruction->assign_rhs(), value))
      {
        constant_assignments.emplace_back(lhs, value);
        continue;
      }
      reason = "atomic_assignment_rhs";
      return false;
    }
    else if(
      !instruction->is_skip() && !instruction->is_location() &&
      !instruction->is_dead() && !instruction->is_decl())
    {
      reason = "atomic_instruction";
      return false;
    }
  }

  if(increments.size() != 1)
  {
    reason = "cursor_increment_count";
    return false;
  }
  result.cursor = increments.front();
  result.location = region.begin->location_number;

  if(assumed_accesses.size() == 1 && assigned_accesses.empty())
  {
    result.kind = action_kindt::SEND;
    result.queue = assumed_accesses.front().access.base;
    result.label = assumed_accesses.front().label;
    if(assumed_accesses.front().access.index != result.cursor)
    {
      reason = "send_cursor";
      return false;
    }
    bool exact_send = false;
    for(const auto &assumption : assumptions)
      exact_send =
        exact_send || exact_labelled_equality(
                        assumption, assumed_accesses.front());
    if(!exact_send)
    {
      reason = "send_value_condition";
      return false;
    }
  }
  else if(assigned_accesses.size() == 1 && assumed_accesses.empty())
  {
    result.kind = action_kindt::RECEIVE;
    result.queue = assigned_accesses.front().access.base;
    result.label = assigned_accesses.front().label;
    result.safety = assigned_access_lhs.front();
    if(assigned_accesses.front().access.index != result.cursor)
    {
      reason = "receive_cursor";
      return false;
    }
    if(
      !valid_safety_update(
        safety_rhs, result.safety, assigned_accesses.front()))
    {
      reason = "safety_update";
      return false;
    }
  }
  else
  {
    std::ostringstream detail;
    detail << "channel_action_count_assumed_" << assumed_accesses.size()
           << "_assigned_" << assigned_accesses.size()
           << "_increments_" << increments.size();
    reason = detail.str();
    return false;
  }

  bool nonnegative = false;
  for(const auto &assumption : assumptions)
  {
    find_cursor_bounds(
      assumption, result.cursor, nonnegative, result.size);
    if(result.kind == action_kindt::RECEIVE)
      find_greater_peer(
        assumption, result.cursor, result.nonempty_peer);
  }
  if(
    result.kind == action_kindt::RECEIVE &&
    result.size.empty() && !result.nonempty_peer.empty())
  {
    bool ignored_nonnegative = false;
    for(const auto &assumption : assumptions)
      find_cursor_bounds(
        assumption,
        result.nonempty_peer,
        ignored_nonnegative,
        result.size);
  }
  if(!nonnegative || result.size.empty())
  {
    reason = "cursor_bounds";
    return false;
  }
  if(
    result.kind == action_kindt::RECEIVE &&
    result.nonempty_peer.empty())
  {
    reason = "receive_nonempty_guard";
    return false;
  }

  if(constant_assignments.size() > 1)
  {
    reason = "phase_assignment_count";
    return false;
  }
  if(!constant_assignments.empty())
  {
    result.has_phase = true;
    result.phase = constant_assignments.front().first;
    result.next_phase = constant_assignments.front().second;
  }
  return true;
}

bool phase_guard_before(
  const goto_programt &program,
  goto_programt::const_targett begin,
  const irep_idt &phase,
  const mp_integer &expected)
{
  auto current = begin;
  for(std::size_t distance = 0;
      distance < 8 && current != program.instructions.begin(); ++distance)
  {
    --current;
    if(!current->is_goto())
      continue;
    const exprt &condition = strip(current->condition());
    std::deque<const exprt *> pending{&condition};
    while(!pending.empty())
    {
      const exprt &candidate = strip(*pending.front());
      pending.pop_front();
      if(candidate.id() == ID_equal && candidate.operands().size() == 2)
      {
        irep_idt identifier;
        mp_integer value;
        if(
          (symbol_id(candidate.op0(), identifier) &&
           identifier == phase &&
           integer_constant(candidate.op1(), value) && value == expected) ||
          (symbol_id(candidate.op1(), identifier) &&
           identifier == phase &&
           integer_constant(candidate.op0(), value) && value == expected))
          return true;
      }
      for(const auto &operand : candidate.operands())
        pending.push_back(&operand);
    }
  }
  return false;
}

bool parse_worker(
  const irep_idt &entry,
  const goto_programt &program,
  protocol_workert &worker,
  std::string &reason)
{
  worker.entry = entry;
  std::vector<atomic_regiont> regions;
  if(!collect_atomic_regions(program, regions, reason))
    return false;
  for(const auto &region : regions)
  {
    protocol_actiont action;
    if(!parse_action(region, action, reason))
      return false;
    worker.actions.push_back(std::move(action));
  }

  const bool phase_mode = worker.actions.front().has_phase;
  for(const auto &action : worker.actions)
  {
    if(action.has_phase != phase_mode)
    {
      reason = "mixed_phase_encoding";
      return false;
    }
  }
  if(phase_mode)
  {
    const irep_idt phase = worker.actions.front().phase;
    for(std::size_t index = 0; index < worker.actions.size(); ++index)
    {
      const auto &action = worker.actions[index];
      if(action.phase != phase)
      {
        reason = "multiple_phase_variables";
        return false;
      }
      const mp_integer expected = index;
      const mp_integer next = (index + 1) % worker.actions.size();
      if(
        action.next_phase != next ||
        !phase_guard_before(program, regions[index].begin, phase, expected))
      {
        reason = "phase_cycle";
        return false;
      }
    }
    worker.may_terminate_each_phase = true;
  }
  else
  {
    for(auto instruction = regions.front().begin;
        instruction != regions.back().end; ++instruction)
    {
      if(instruction->is_goto())
      {
        reason = "commit_internal_control";
        return false;
      }
    }
    bool enclosing_backedge = false;
    for(auto instruction = std::next(regions.back().end);
        instruction != program.instructions.end(); ++instruction)
    {
      if(
        instruction->is_backwards_goto() &&
        instruction->get_target()->location_number <
          regions.front().begin->location_number)
      {
        enclosing_backedge = true;
        break;
      }
    }
    if(!enclosing_backedge)
    {
      reason = "commit_loop";
      return false;
    }
  }
  return true;
}

std::set<irep_idt> find_thread_entries(const goto_modelt &model)
{
  std::set<irep_idt> entries;
  const auto main = model.goto_functions.function_map.find("main");
  if(main == model.goto_functions.function_map.end())
    return entries;
  for(const auto &instruction : main->second.body.instructions)
  {
    irep_idt callee;
    if(
      !direct_call(instruction, callee) || callee != "pthread_create" ||
      instruction.call_arguments().size() < 3)
      continue;
    irep_idt entry;
    if(thread_entry(instruction.call_arguments()[2], entry))
      entries.insert(entry);
  }
  return entries;
}

struct queuet
{
  irep_idt base;
  irep_idt front;
  irep_idt back;
  irep_idt size;
  std::set<irep_idt> labels;
};

bool source_checks(
  const goto_modelt &model,
  const std::vector<protocol_workert> &workers,
  std::vector<queuet> &queues,
  irep_idt &safety,
  std::string &reason)
{
  std::map<irep_idt, queuet> by_base;
  std::set<irep_idt> labels;
  for(const auto &worker : workers)
  {
    for(const auto &action : worker.actions)
    {
      auto &queue = by_base[action.queue];
      queue.base = action.queue;
      queue.labels.insert(action.label);
      labels.insert(action.label);
      if(!queue.size.empty() && queue.size != action.size)
      {
        reason = "multiple_queue_sizes";
        return false;
      }
      queue.size = action.size;
      if(action.kind == action_kindt::SEND)
      {
        if(!queue.back.empty() && queue.back != action.cursor)
        {
          reason = "multiple_back_cursors";
          return false;
        }
        queue.back = action.cursor;
      }
      else
      {
        if(!queue.front.empty() && queue.front != action.cursor)
        {
          reason = "multiple_front_cursors";
          return false;
        }
        queue.front = action.cursor;
        if(action.nonempty_peer.empty())
        {
          reason = "missing_nonempty_peer";
          return false;
        }
        if(safety.empty())
          safety = action.safety;
        else if(safety != action.safety)
        {
          reason = "multiple_safety_symbols";
          return false;
        }
      }
    }
  }
  if(by_base.empty() || safety.empty())
  {
    reason = "missing_queue_or_safety";
    return false;
  }
  for(const auto &entry : by_base)
  {
    if(
      entry.second.front.empty() || entry.second.back.empty() ||
      entry.second.front == entry.second.back)
    {
      reason = "queue_cursor_pair";
      return false;
    }
    for(const auto &worker : workers)
    {
      for(const auto &action : worker.actions)
      {
        if(
          action.queue == entry.first &&
          action.kind == action_kindt::RECEIVE &&
          action.nonempty_peer != entry.second.back)
        {
          reason = "receive_nonempty_peer";
          return false;
        }
      }
    }
    queues.push_back(entry.second);
  }

  const auto main = model.goto_functions.function_map.find("main");
  if(main == model.goto_functions.function_map.end())
  {
    reason = "missing_main";
    return false;
  }
  bool spawned = false;
  bool safety_true = false;
  bool safety_last_seen = false;
  std::map<irep_idt, irep_idt> last_symbol_assignment;
  std::set<irep_idt> post_spawn_writes;
  std::set<irep_idt> initialized_queue_bases;
  std::map<irep_idt, irep_idt> queue_initializers;
  std::size_t error_calls = 0;
  bool negated_safety_guard = false;
  for(const auto &instruction : main->second.body.instructions)
  {
    irep_idt callee;
    if(direct_call(instruction, callee))
    {
      if(callee == "pthread_create")
        spawned = true;
      else if(
        callee == "assume_abort_if_not" &&
        instruction.call_arguments().size() == 1)
        negated_safety_guard = contains_negated_symbol(
          instruction.call_arguments()[0], safety);
      else if(callee == "reach_error")
      {
        ++error_calls;
        if(!negated_safety_guard)
        {
          reason = "property_guard";
          return false;
        }
      }
      if(
        !spawned && !instruction.call_lhs().is_nil())
      {
        irep_idt lhs;
        if(symbol_id(instruction.call_lhs(), lhs) &&
           by_base.find(lhs) != by_base.end())
        {
          initialized_queue_bases.insert(lhs);
          queue_initializers[lhs] = callee;
        }
      }
      continue;
    }
    if(!instruction.is_assign())
      continue;
    irep_idt lhs;
    if(!symbol_id(instruction.assign_lhs(), lhs))
      continue;
    if(spawned)
      post_spawn_writes.insert(lhs);
    else
    {
      irep_idt rhs;
      if(symbol_id(instruction.assign_rhs(), rhs))
        last_symbol_assignment[lhs] = rhs;
      mp_integer value;
      if(lhs == safety)
      {
        safety_last_seen = true;
        safety_true =
          integer_constant(instruction.assign_rhs(), value) && value != 0;
      }
      std::set<irep_idt> rhs_symbols;
      collect_symbols(instruction.assign_rhs(), rhs_symbols);
      for(const auto &base : by_base)
      {
        if(base.first != lhs && rhs_symbols.count(base.first) != 0)
        {
          reason = "queue_pointer_alias";
          return false;
        }
      }
    }
  }
  if(!safety_last_seen || !safety_true || error_calls != 1)
  {
    reason = !safety_true ? "safety_initialization" : "property_count";
    return false;
  }
  for(const auto &queue : queues)
  {
    const symbolt *front_symbol = model.symbol_table.lookup(queue.front);
    const symbolt *back_symbol = model.symbol_table.lookup(queue.back);
    const symbolt *size_symbol = model.symbol_table.lookup(queue.size);
    const symbolt *base_symbol = model.symbol_table.lookup(queue.base);
    if(
      last_symbol_assignment[queue.back] != queue.front ||
      initialized_queue_bases.count(queue.base) == 0 ||
      !returns_fresh_allocation(
        model, queue_initializers[queue.base]) ||
      post_spawn_writes.count(queue.front) != 0 ||
      post_spawn_writes.count(queue.back) != 0 ||
      post_spawn_writes.count(queue.base) != 0)
    {
      reason = "queue_initialization_or_main_write";
      return false;
    }
    if(
      front_symbol == nullptr || back_symbol == nullptr ||
      size_symbol == nullptr || base_symbol == nullptr ||
      front_symbol->type.id() != ID_signedbv ||
      back_symbol->type != front_symbol->type ||
      size_symbol->type != front_symbol->type ||
      base_symbol->type.id() != ID_pointer)
    {
      reason = "queue_symbol_types";
      return false;
    }
  }
  for(const auto &label : labels)
  {
    if(post_spawn_writes.count(label) != 0)
    {
      reason = "mutable_message_label";
      return false;
    }
  }

  // All writes to the safety fact in workers must be represented receives.
  std::size_t represented_safety_writes = 0;
  std::map<irep_idt, std::size_t> represented_cursor_writes;
  std::map<irep_idt, std::size_t> represented_array_accesses;
  for(const auto &worker : workers)
  {
    for(const auto &action : worker.actions)
    {
      if(action.kind == action_kindt::RECEIVE)
        ++represented_safety_writes;
      ++represented_cursor_writes[action.cursor];
      ++represented_array_accesses[action.queue];
    }
  }
  std::size_t actual_safety_writes = 0;
  std::map<irep_idt, std::size_t> actual_cursor_writes;
  std::map<irep_idt, std::size_t> actual_array_accesses;
  for(const auto &worker : workers)
  {
    const auto function =
      model.goto_functions.function_map.find(worker.entry);
    for(const auto &instruction : function->second.body.instructions)
    {
      if(!instruction.is_assign())
      {
        if(instruction.is_function_call())
        {
          for(const auto &argument : instruction.call_arguments())
            count_indexed_bases(argument, actual_array_accesses);
        }
        else if(instruction.is_goto() || instruction.is_assert() ||
                instruction.is_assume())
          count_indexed_bases(instruction.condition(), actual_array_accesses);
        continue;
      }
      irep_idt lhs;
      if(symbol_id(instruction.assign_lhs(), lhs))
      {
        if(lhs == safety)
          ++actual_safety_writes;
        if(represented_cursor_writes.count(lhs) != 0)
          ++actual_cursor_writes[lhs];
        if(labels.count(lhs) != 0 || by_base.count(lhs) != 0)
        {
          reason = labels.count(lhs) != 0
                     ? "worker_mutable_message_label"
                     : "worker_mutable_queue_base";
          return false;
        }
      }
      indexed_accesst lhs_access;
      if(
        indexed_access(instruction.assign_lhs(), lhs_access) &&
        by_base.count(lhs_access.base) != 0)
      {
        reason = "worker_queue_write";
        return false;
      }
      count_indexed_bases(
        instruction.assign_lhs(), actual_array_accesses);
      count_indexed_bases(
        instruction.assign_rhs(), actual_array_accesses);
    }
  }
  if(actual_safety_writes != represented_safety_writes)
  {
    reason = "unrepresented_safety_write";
    return false;
  }
  if(actual_cursor_writes != represented_cursor_writes)
  {
    reason = "unrepresented_cursor_write";
    return false;
  }
  for(const auto &entry : represented_array_accesses)
  {
    if(actual_array_accesses[entry.first] != entry.second)
    {
      reason = "unrepresented_queue_access";
      return false;
    }
  }
  return true;
}

struct abstract_statet
{
  std::vector<std::size_t> phases;
  std::vector<bool> terminated;
  std::vector<std::deque<irep_idt>> contents;
};

std::string state_key(const abstract_statet &state)
{
  std::ostringstream out;
  for(std::size_t index = 0; index < state.phases.size(); ++index)
    out << state.phases[index] << (state.terminated[index] ? 't' : 'a') << ';';
  out << '|';
  for(const auto &queue : state.contents)
  {
    for(const auto &token : queue)
      out << id2string(token) << ',';
    out << ';';
  }
  return out.str();
}

struct exploration_resultt
{
  bool overflow = false;
  bool mismatch = false;
  std::size_t states = 0;
  std::vector<std::size_t> maxima;
};

exploration_resultt explore(
  const std::vector<protocol_workert> &workers,
  const std::vector<queuet> &queues,
  std::size_t capacity)
{
  exploration_resultt result;
  result.maxima.assign(queues.size(), 0);
  std::map<irep_idt, std::size_t> queue_index;
  for(std::size_t index = 0; index < queues.size(); ++index)
    queue_index[queues[index].base] = index;

  abstract_statet initial;
  initial.phases.assign(workers.size(), 0);
  initial.terminated.assign(workers.size(), false);
  initial.contents.resize(queues.size());
  std::deque<abstract_statet> pending{initial};
  std::set<std::string> seen{state_key(initial)};
  constexpr std::size_t max_states = 200000;

  while(!pending.empty())
  {
    abstract_statet state = std::move(pending.front());
    pending.pop_front();
    ++result.states;
    if(result.states > max_states)
    {
      result.overflow = true;
      return result;
    }
    for(std::size_t worker_index = 0;
        worker_index < workers.size(); ++worker_index)
    {
      if(state.terminated[worker_index])
        continue;
      const auto &worker = workers[worker_index];
      const std::size_t phase = state.phases[worker_index];

      if(worker.may_terminate_each_phase || phase == 0)
      {
        auto successor = state;
        successor.terminated[worker_index] = true;
        const auto key = state_key(successor);
        if(seen.insert(key).second)
          pending.push_back(std::move(successor));
      }

      const auto &action = worker.actions[phase];
      const std::size_t channel = queue_index[action.queue];
      auto successor = state;
      auto &contents = successor.contents[channel];
      if(action.kind == action_kindt::SEND)
      {
        if(contents.size() == capacity)
        {
          result.overflow = true;
          continue;
        }
        contents.push_back(action.label);
      }
      else
      {
        if(contents.empty())
          continue;
        if(contents.front() != action.label)
        {
          result.mismatch = true;
          continue;
        }
        contents.pop_front();
      }
      result.maxima[channel] =
        std::max(result.maxima[channel], contents.size());
      successor.phases[worker_index] =
        (phase + 1) % worker.actions.size();
      const auto key = state_key(successor);
      if(seen.insert(key).second)
        pending.push_back(std::move(successor));
    }
  }
  return result;
}

protocol_capacity_resultt unknown(
  const std::string &reason,
  std::size_t workers = 0,
  std::size_t actions = 0,
  std::size_t queues = 0)
{
  std::cout << "PROTOCOL_CAPACITY_CUTOFF result=UNKNOWN reason=" << reason
            << " workers=" << workers << " actions=" << actions
            << " queues=" << queues << '\n';
  return protocol_capacity_resultt::UNKNOWN;
}
} // namespace

protocol_capacity_resultt protocol_capacity_cutoff(
  const goto_modelt &goto_model,
  message_handlert &)
{
  const auto entries = find_thread_entries(goto_model);
  if(entries.size() < 2)
    return unknown("thread_count", entries.size());

  std::vector<protocol_workert> workers;
  std::size_t action_count = 0;
  for(const auto &entry : entries)
  {
    const auto function = goto_model.goto_functions.function_map.find(entry);
    if(
      function == goto_model.goto_functions.function_map.end() ||
      !function->second.body_available())
      return unknown("missing_worker", workers.size(), action_count);
    protocol_workert worker;
    std::string reason;
    if(!parse_worker(entry, function->second.body, worker, reason))
      return unknown(reason, workers.size(), action_count);
    action_count += worker.actions.size();
    workers.push_back(std::move(worker));
  }

  std::vector<queuet> queues;
  irep_idt safety;
  std::string reason;
  if(!source_checks(goto_model, workers, queues, safety, reason))
    return unknown(reason, workers.size(), action_count, queues.size());

  constexpr std::size_t max_capacity = 8;
  for(std::size_t capacity = 1; capacity <= max_capacity; ++capacity)
  {
    const auto result = explore(workers, queues, capacity);
    if(result.mismatch)
      return unknown(
        "message_mismatch", workers.size(), action_count, queues.size());
    if(result.overflow)
      continue;
    std::cout << "PROTOCOL_CAPACITY_CUTOFF result=SAFE workers="
              << workers.size() << " actions=" << action_count
              << " queues=" << queues.size() << " capacity=" << capacity
              << " states=" << result.states << " maxima=";
    for(std::size_t index = 0; index < result.maxima.size(); ++index)
      std::cout << (index == 0 ? "" : ",") << result.maxima[index];
    std::cout << '\n';
    return protocol_capacity_resultt::SAFE;
  }
  return unknown(
    "capacity_above_limit", workers.size(), action_count, queues.size());
}
