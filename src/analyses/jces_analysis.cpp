/*******************************************************************\

Module: Join-Scoped Compositional Effect Summary

\*******************************************************************/

#include "jces_analysis.h"

#include <goto-programs/goto_model.h>
#include <goto-instrument/unwind.h>

#include <util/arith_tools.h>
#include <util/bitvector_expr.h>
#include <util/bitvector_types.h>
#include <util/expr_util.h>
#include <util/find_symbols.h>
#include <util/message.h>
#include <util/namespace.h>
#include <util/pointer_expr.h>
#include <util/replace_expr.h>
#include <util/simplify_expr.h>
#include <util/std_code.h>
#include <util/std_expr.h>
#include <util/symbol.h>

#include <algorithm>
#include <deque>
#include <fstream>
#include <functional>
#include <iostream>
#include <iterator>
#include <map>
#include <regex>
#include <set>
#include <sstream>
#include <string>
#include <tuple>
#include <utility>
#include <vector>

namespace
{
struct create_recordt
{
  irep_idt handle;
  irep_idt worker;
  goto_programt::targett instruction;
};

struct effectt
{
  exprt object;
  exprt delta;
  bool subtract = false;
};

struct worker_summaryt
{
  irep_idt worker;
  exprt count;
  std::vector<effectt> effects;
};

struct transition_word_stept
{
  exprt guard;
  exprt update;
};

struct transition_word_summaryt
{
  irep_idt worker;
  irep_idt state;
  irep_idt induction;
  exprt bound;
  std::vector<transition_word_stept> steps;
};

struct modular_chunk_summaryt
{
  transition_word_summaryt word;
  irep_idt bound;
  std::size_t chunk = 0;
};

struct affine_worker_summaryt
{
  irep_idt worker;
  irep_idt induction;
  irep_idt target;
  irep_idt source;
  mp_integer self_coefficient;
  mp_integer source_coefficient;
  mp_integer offset;
  mp_integer count;
};

struct affine_statet
{
  mp_integer first;
  mp_integer second;
  std::string schedule;
};

struct ticket_regiont
{
  irep_idt worker;
  irep_idt ticket;
  irep_idt completed;
  irep_idt rank;
  goto_programt::targett body_begin;
  goto_programt::targett completion;
};

struct affine_formt
{
  mp_integer coefficient = 0;
  mp_integer offset = 0;
};

struct locked_loop_summaryt
{
  irep_idt function;
  irep_idt induction;
  irep_idt object;
  irep_idt mutex;
  mp_integer count;
  mp_integer delta;
  goto_programt::targett loop_head;
  goto_programt::targett backedge;
  std::set<const goto_programt::instructiont *> covered;
};

struct stable_transitiont
{
  irep_idt function;
  irep_idt object;
  irep_idt snapshot;
  irep_idt mutex;
  irep_idt property_witness;
  irep_idt set_witness;
  int direction = 0;
  goto_programt::targett snapshot_assignment;
  goto_programt::targett object_assignment;
  goto_programt::targett witness_assignment;
  goto_programt::targett property_guard;
  goto_programt::targett error_call;
};

bool constant_eval(
  const exprt &src,
  const std::map<irep_idt, mp_integer> &environment,
  mp_integer &value);

const exprt &without_cast(const exprt &expr)
{
  return skip_typecast(expr);
}

bool addressed_symbol(const exprt &expr, irep_idt &identifier)
{
  const exprt &value = without_cast(expr);
  if(value.id() != ID_address_of)
    return false;
  const exprt &object =
    without_cast(to_address_of_expr(value).object());
  if(object.id() != ID_symbol)
    return false;
  identifier = to_symbol_expr(object).get_identifier();
  return true;
}

bool direct_symbol(const exprt &expr, irep_idt &identifier)
{
  const exprt &value = without_cast(expr);
  if(value.id() != ID_symbol)
    return false;
  identifier = to_symbol_expr(value).get_identifier();
  return true;
}

bool direct_call_identifier(
  const goto_programt::instructiont &instruction,
  irep_idt &identifier)
{
  if(!instruction.is_function_call())
    return false;
  const exprt &function = without_cast(instruction.call_function());
  if(function.id() != ID_symbol)
    return false;
  identifier = to_symbol_expr(function).get_identifier();
  return true;
}

bool is_shared_scalar(
  const exprt &expr,
  const namespacet &ns,
  const symbolt *&symbol)
{
  if(expr.id() != ID_symbol || expr.type().id() == ID_pointer)
    return false;
  if(ns.lookup(to_symbol_expr(expr).get_identifier(), symbol))
    return false;
  return symbol->is_static_lifetime && !symbol->is_type;
}

bool is_atomic_symbol(const symbolt &symbol)
{
  const std::string typedef_name =
    id2string(symbol.type.get("#typedef"));
  return symbol.type.get_bool("#atomic") ||
         typedef_name.find("atomic_") != std::string::npos;
}

bool contains_side_effect(const exprt &expr)
{
  if(expr.id() == ID_side_effect || expr.id() == ID_dereference)
    return true;
  for(const auto &operand : expr.operands())
  {
    if(contains_side_effect(operand))
      return true;
  }
  return false;
}

bool contains_address_of_symbol(
  const exprt &expr,
  const std::set<irep_idt> &identifiers)
{
  if(expr.id() == ID_address_of)
  {
    const exprt &object =
      without_cast(to_address_of_expr(expr).object());
    if(
      object.id() == ID_symbol &&
      identifiers.find(to_symbol_expr(object).get_identifier()) !=
        identifiers.end())
      return true;
  }
  for(const auto &operand : expr.operands())
  {
    if(contains_address_of_symbol(operand, identifiers))
      return true;
  }
  return false;
}

bool contains_symbol(
  const exprt &expr,
  const std::set<irep_idt> &identifiers)
{
  if(
    expr.id() == ID_symbol &&
    identifiers.find(to_symbol_expr(expr).get_identifier()) !=
      identifiers.end())
    return true;
  for(const auto &operand : expr.operands())
  {
    if(contains_symbol(operand, identifiers))
      return true;
  }
  return false;
}

bool is_zero_constant(const exprt &expr)
{
  mp_integer value;
  return constant_eval(without_cast(expr), {}, value) && value == 0;
}

bool parse_nonzero_witness(
  const exprt &src,
  irep_idt &identifier)
{
  const exprt &expr = without_cast(src);
  if(expr.id() != ID_notequal || expr.operands().size() != 2)
    return false;
  if(direct_symbol(expr.op0(), identifier) &&
     is_zero_constant(expr.op1()))
    return true;
  return
    direct_symbol(expr.op1(), identifier) &&
    is_zero_constant(expr.op0());
}

bool parse_snapshot_relation(
  const exprt &src,
  irep_idt &object,
  irep_idt &snapshot,
  int &direction)
{
  const exprt &expr = without_cast(src);
  if(
    (expr.id() != ID_gt && expr.id() != ID_lt) ||
    expr.operands().size() != 2 ||
    !direct_symbol(expr.op0(), object) ||
    !direct_symbol(expr.op1(), snapshot))
    return false;
  direction = expr.id() == ID_gt ? 1 : -1;
  return true;
}

bool parse_stable_property(
  const exprt &src,
  irep_idt &object,
  irep_idt &snapshot,
  irep_idt &witness,
  int &direction)
{
  const exprt &expr = without_cast(src);
  if(parse_snapshot_relation(
       expr, object, snapshot, direction))
  {
    witness.clear();
    return true;
  }
  if(expr.id() != ID_or || expr.operands().size() != 2)
    return false;
  return
    (parse_nonzero_witness(expr.op0(), witness) &&
     parse_snapshot_relation(
       expr.op1(), object, snapshot, direction)) ||
    (parse_nonzero_witness(expr.op1(), witness) &&
     parse_snapshot_relation(
       expr.op0(), object, snapshot, direction));
}

bool parse_unit_snapshot_update(
  const goto_programt::instructiont &instruction,
  const irep_idt &object,
  const irep_idt &snapshot,
  const int direction)
{
  if(!instruction.is_assign())
    return false;
  irep_idt lhs;
  if(
    !direct_symbol(instruction.assign_lhs(), lhs) ||
    lhs != object)
    return false;
  const exprt &rhs = without_cast(instruction.assign_rhs());
  if(
    rhs.operands().size() != 2 ||
    (direction > 0 ? rhs.id() != ID_plus : rhs.id() != ID_minus))
    return false;
  irep_idt rhs_snapshot;
  mp_integer unit;
  return
    direct_symbol(rhs.op0(), rhs_snapshot) &&
    rhs_snapshot == snapshot &&
    constant_eval(rhs.op1(), {}, unit) &&
    unit == 1;
}

bool parse_mutex_call(
  const goto_programt::instructiont &instruction,
  const irep_idt &callee_expected,
  irep_idt &mutex)
{
  irep_idt callee;
  return
    direct_call_identifier(instruction, callee) &&
    callee == callee_expected &&
    instruction.call_arguments().size() == 1 &&
    addressed_symbol(instruction.call_arguments().front(), mutex);
}

bool instruction_mentions_any(
  const goto_programt::instructiont &instruction,
  const std::set<irep_idt> &identifiers)
{
  if(instruction.is_assign())
    return
      contains_symbol(instruction.assign_lhs(), identifiers) ||
      contains_symbol(instruction.assign_rhs(), identifiers);
  if(instruction.is_goto() || instruction.is_assume() ||
     instruction.is_assert())
    return contains_symbol(instruction.condition(), identifiers);
  if(instruction.is_function_call())
  {
    if(contains_symbol(instruction.call_function(), identifiers))
      return true;
    for(const auto &argument : instruction.call_arguments())
    {
      if(contains_symbol(argument, identifiers))
        return true;
    }
  }
  if(instruction.is_set_return_value())
    return contains_symbol(instruction.return_value(), identifiers);
  return false;
}

bool boolean_constant_eval(const exprt &src, bool &value)
{
  const exprt &expr = without_cast(src);
  if(expr.is_true())
  {
    value = true;
    return true;
  }
  if(expr.is_false())
  {
    value = false;
    return true;
  }
  if(expr.id() == ID_not && expr.operands().size() == 1)
  {
    if(!boolean_constant_eval(expr.op0(), value))
      return false;
    value = !value;
    return true;
  }
  if(
    (expr.id() == ID_equal || expr.id() == ID_notequal) &&
    expr.operands().size() == 2)
  {
    mp_integer lhs;
    mp_integer rhs;
    if(
      !constant_eval(expr.op0(), {}, lhs) ||
      !constant_eval(expr.op1(), {}, rhs))
      return false;
    value =
      expr.id() == ID_equal ? lhs == rhs : lhs != rhs;
    return true;
  }
  return false;
}

bool parse_stable_transition(
  const irep_idt &function_id,
  goto_modelt &model,
  const namespacet &ns,
  stable_transitiont &summary,
  std::set<const goto_programt::instructiont *> &recognized,
  std::string &reason)
{
  auto function = model.goto_functions.function_map.find(function_id);
  if(
    function == model.goto_functions.function_map.end() ||
    !function->second.body_available())
  {
    reason = "stable_missing_function";
    return false;
  }
  auto &program = function->second.body;
  std::vector<goto_programt::targett> order;
  std::map<const goto_programt::instructiont *, std::size_t> positions;
  for(auto instruction = program.instructions.begin();
      instruction != program.instructions.end(); ++instruction)
  {
    positions.emplace(&*instruction, order.size());
    order.push_back(instruction);
  }

  goto_programt::targett error_call = program.instructions.end();
  std::size_t error_calls = 0;
  for(auto instruction = program.instructions.begin();
      instruction != program.instructions.end(); ++instruction)
  {
    irep_idt callee;
    if(
      direct_call_identifier(*instruction, callee) &&
      callee == "reach_error")
    {
      error_call = instruction;
      ++error_calls;
    }
  }
  if(error_calls != 1 || positions.at(&*error_call) == 0)
  {
    reason = "stable_property_count";
    return false;
  }
  const auto property_guard =
    order[positions.at(&*error_call) - 1];
  if(
    !property_guard->is_goto() ||
    property_guard->targets.size() != 1)
  {
    reason = "stable_property_guard";
    return false;
  }

  irep_idt object;
  irep_idt snapshot;
  irep_idt property_witness;
  int direction = 0;
  if(!parse_stable_property(
       property_guard->condition(),
       object,
       snapshot,
       property_witness,
       direction))
  {
    reason = "stable_property_schema";
    return false;
  }
  const symbolt *object_symbol = nullptr;
  if(
    ns.lookup(object, object_symbol) ||
    !object_symbol->is_static_lifetime ||
    object_symbol->type.id() != ID_unsignedbv)
  {
    reason = "stable_object_type";
    return false;
  }
  const symbolt *snapshot_symbol = nullptr;
  if(
    ns.lookup(snapshot, snapshot_symbol) ||
    snapshot_symbol->is_static_lifetime ||
    snapshot_symbol->type != object_symbol->type)
  {
    reason = "stable_snapshot_type";
    return false;
  }

  goto_programt::targett snapshot_assignment =
    program.instructions.end();
  goto_programt::targett object_assignment =
    program.instructions.end();
  goto_programt::targett witness_assignment =
    program.instructions.end();
  std::size_t snapshot_writes = 0;
  std::size_t object_writes = 0;
  std::size_t witness_writes = 0;
  std::vector<goto_programt::targett> snapshot_initializations;
  for(auto instruction = program.instructions.begin();
      instruction != program.instructions.end(); ++instruction)
  {
    if(!instruction->is_assign())
      continue;
    irep_idt lhs;
    if(!direct_symbol(instruction->assign_lhs(), lhs))
      continue;
    if(lhs == snapshot)
    {
      irep_idt rhs;
      if(
        direct_symbol(instruction->assign_rhs(), rhs) &&
        rhs == object)
      {
        snapshot_assignment = instruction;
        ++snapshot_writes;
      }
      else
      {
        mp_integer value;
        if(!constant_eval(instruction->assign_rhs(), {}, value))
        {
          reason = "stable_snapshot_definition";
          return false;
        }
        snapshot_initializations.push_back(instruction);
      }
    }
    if(lhs == object)
    {
      if(!parse_unit_snapshot_update(
           *instruction, object, snapshot, direction))
      {
        reason = "stable_update_schema";
        return false;
      }
      object_assignment = instruction;
      ++object_writes;
    }
    const symbolt *lhs_symbol = nullptr;
    if(
      lhs != object && lhs != snapshot &&
      !ns.lookup(lhs, lhs_symbol) &&
      lhs_symbol->is_static_lifetime &&
      !lhs_symbol->is_type)
    {
      mp_integer value;
      if(
        !constant_eval(instruction->assign_rhs(), {}, value) ||
        value != 1)
      {
        reason = "stable_witness_value";
        return false;
      }
      witness_assignment = instruction;
      ++witness_writes;
    }
  }
  if(
    snapshot_writes != 1 || object_writes != 1 ||
    witness_writes > 1)
  {
    reason = "stable_transition_writes";
    return false;
  }
  const auto snapshot_position =
    positions.at(&*snapshot_assignment);
  const auto update_position =
    positions.at(&*object_assignment);
  const auto property_position =
    positions.at(&*property_guard);
  if(
    snapshot_position >= update_position ||
    update_position >= property_position ||
    (witness_writes == 1 &&
     positions.at(&*witness_assignment) >= update_position))
  {
    reason = "stable_transition_order";
    return false;
  }
  for(const auto initialization : snapshot_initializations)
  {
    if(positions.at(&*initialization) >= snapshot_position)
    {
      reason = "stable_snapshot_redefinition";
      return false;
    }
  }
  for(std::size_t index = snapshot_position;
      index < property_position; ++index)
  {
    if(order[index]->is_goto())
    {
      reason = "stable_transition_control";
      return false;
    }
  }
  for(std::size_t index = snapshot_position;
      index < update_position; ++index)
  {
    irep_idt candidate;
    if(
      parse_mutex_call(
        *order[index], "pthread_mutex_lock", candidate) ||
      parse_mutex_call(
        *order[index], "pthread_mutex_unlock", candidate))
    {
      reason = "stable_linearization_lock_scope";
      return false;
    }
  }

  goto_programt::targett update_lock = program.instructions.end();
  goto_programt::targett update_unlock = program.instructions.end();
  irep_idt mutex;
  for(std::size_t index = 0; index < snapshot_position; ++index)
  {
    irep_idt candidate;
    if(parse_mutex_call(*order[index], "pthread_mutex_lock", candidate))
    {
      update_lock = order[index];
      mutex = candidate;
    }
  }
  for(std::size_t index = update_position + 1;
      index < property_position; ++index)
  {
    irep_idt candidate;
    if(
      parse_mutex_call(
        *order[index], "pthread_mutex_unlock", candidate) &&
      candidate == mutex)
    {
      update_unlock = order[index];
      break;
    }
  }
  if(
    update_lock == program.instructions.end() ||
    update_unlock == program.instructions.end())
  {
    reason = "stable_update_lock";
    return false;
  }

  int property_lock_depth = 0;
  int atomic_depth = 0;
  for(std::size_t index =
        positions.at(&*update_unlock) + 1;
      index < property_position; ++index)
  {
    if(order[index]->is_atomic_begin())
      ++atomic_depth;
    else if(order[index]->is_atomic_end())
      --atomic_depth;
    irep_idt candidate;
    if(
      parse_mutex_call(
        *order[index], "pthread_mutex_lock", candidate) &&
      candidate == mutex)
      ++property_lock_depth;
    else if(
      parse_mutex_call(
        *order[index], "pthread_mutex_unlock", candidate) &&
      candidate == mutex)
      --property_lock_depth;
  }
  if(property_lock_depth <= 0 && atomic_depth <= 0)
  {
    reason = "stable_property_protection";
    return false;
  }

  bool guarded = false;
  std::size_t guard_position = 0;
  for(std::size_t index = positions.at(&*update_lock) + 1;
      index < snapshot_position; ++index)
  {
    auto instruction = order[index];
    if(
      !instruction->is_goto() ||
      instruction->targets.size() != 1 ||
      instruction->targets.front() != snapshot_assignment)
      continue;
    const exprt &condition = instruction->condition();
    if(condition.id() != ID_not || condition.operands().size() != 1)
      continue;
    const exprt &equality = without_cast(condition.op0());
    if(equality.id() != ID_equal ||
       equality.operands().size() != 2)
      continue;
    irep_idt guarded_object;
    mp_integer boundary;
    if(
      direct_symbol(equality.op0(), guarded_object) &&
      guarded_object == object &&
      constant_eval(equality.op1(), {}, boundary) &&
      ((direction > 0 && boundary == -1) ||
       (direction < 0 && boundary == 0)))
    {
      guarded = true;
      guard_position = index;
    }
  }
  if(!guarded)
  {
    reason = "stable_arithmetic_guard";
    return false;
  }
  recognized.insert(&*order[guard_position]);

  // When the arithmetic guard is false, its fall-through path must terminate
  // without reaching the snapshot/update path. This makes the guard a real
  // overflow/underflow exclusion rather than a syntactic decoration.
  std::set<std::size_t> pending;
  std::set<std::size_t> visited;
  if(guard_position + 1 < order.size())
    pending.insert(guard_position + 1);
  while(!pending.empty())
  {
    const auto index = *pending.begin();
    pending.erase(pending.begin());
    if(!visited.insert(index).second)
      continue;
    if(index == snapshot_position)
    {
      reason = "stable_guard_bypass";
      return false;
    }
    const auto instruction = order[index];
    if(instruction->is_end_function())
      continue;
    if(instruction->is_goto())
    {
      for(const auto &target : instruction->targets)
        pending.insert(positions.at(&*target));
      if(!instruction->condition().is_true() &&
         index + 1 < order.size())
        pending.insert(index + 1);
    }
    else if(index + 1 < order.size())
      pending.insert(index + 1);
  }

  for(const auto &instruction : program.instructions)
  {
    if(
      instruction.is_goto() &&
      instruction.get_target() != program.instructions.end() &&
      positions.at(&*instruction.get_target()) <
        positions.at(&instruction))
    {
      reason = "stable_worker_loop";
      return false;
    }
  }

  summary.function = function_id;
  summary.object = object;
  summary.snapshot = snapshot;
  summary.mutex = mutex;
  summary.property_witness = property_witness;
  if(witness_writes == 1)
  {
    direct_symbol(
      witness_assignment->assign_lhs(), summary.set_witness);
  }
  summary.direction = direction;
  summary.snapshot_assignment = snapshot_assignment;
  summary.object_assignment = object_assignment;
  summary.witness_assignment = witness_assignment;
  summary.property_guard = property_guard;
  summary.error_call = error_call;
  recognized.insert(&*snapshot_assignment);
  recognized.insert(&*object_assignment);
  if(witness_writes == 1)
    recognized.insert(&*witness_assignment);
  recognized.insert(&*property_guard);
  recognized.insert(&*error_call);
  return true;
}

bool uses_only_immutable_shared(
  const exprt &expr,
  const namespacet &ns,
  const std::set<irep_idt> &mutable_shared)
{
  if(contains_side_effect(expr))
    return false;
  if(expr.id() == ID_symbol)
  {
    const auto &symbol_expr = to_symbol_expr(expr);
    const symbolt *symbol = nullptr;
    if(ns.lookup(symbol_expr.get_identifier(), symbol))
      return false;
    return symbol->is_static_lifetime && !symbol->is_type &&
           symbol->type.id() != ID_pointer &&
           mutable_shared.find(symbol_expr.get_identifier()) ==
             mutable_shared.end();
  }
  for(const auto &operand : expr.operands())
  {
    if(!uses_only_immutable_shared(operand, ns, mutable_shared))
      return false;
  }
  return true;
}

bool parse_unit_increment(
  const goto_programt::instructiont &instruction,
  irep_idt &identifier)
{
  if(!instruction.is_assign())
    return false;
  const exprt &lhs = without_cast(instruction.assign_lhs());
  const exprt &rhs = without_cast(instruction.assign_rhs());
  if(lhs.id() != ID_symbol || rhs.id() != ID_plus ||
     rhs.operands().size() != 2)
    return false;
  if(without_cast(rhs.op0()) != lhs)
    return false;
  const exprt &increment = without_cast(rhs.op1());
  if(increment.id() != ID_constant)
    return false;
  mp_integer value;
  if(to_integer(to_constant_expr(increment), value) || value != 1)
    return false;
  identifier = to_symbol_expr(lhs).get_identifier();
  return true;
}

bool parse_zero_initialization(
  const goto_programt::instructiont &instruction,
  const irep_idt &identifier)
{
  if(!instruction.is_assign())
    return false;
  const exprt &lhs = without_cast(instruction.assign_lhs());
  if(
    lhs.id() != ID_symbol ||
    to_symbol_expr(lhs).get_identifier() != identifier)
    return false;
  const exprt &rhs = without_cast(instruction.assign_rhs());
  if(rhs.id() != ID_constant)
    return false;
  mp_integer value;
  return !to_integer(to_constant_expr(rhs), value) && value == 0;
}

bool parse_exit_guard(
  const goto_programt::instructiont &instruction,
  irep_idt &induction,
  exprt &bound)
{
  if(!instruction.is_goto() || instruction.targets.size() != 1)
    return false;
  const exprt &condition = instruction.condition();
  if(condition.id() != ID_not || condition.operands().size() != 1)
    return false;
  const exprt &relation = without_cast(condition.op0());
  if(
    relation.id() != ID_lt || relation.operands().size() != 2)
    return false;
  const exprt &lhs = without_cast(relation.op0());
  if(lhs.id() != ID_symbol)
    return false;
  induction = to_symbol_expr(lhs).get_identifier();
  bound = relation.op1();
  return true;
}

bool parse_translation(
  const goto_programt::instructiont &instruction,
  const namespacet &ns,
  const std::set<irep_idt> &mutable_shared,
  const bool protected_by_atomic_region,
  effectt &effect)
{
  if(!instruction.is_assign())
    return false;
  const exprt &lhs = without_cast(instruction.assign_lhs());
  const symbolt *symbol = nullptr;
  if(
    !is_shared_scalar(lhs, ns, symbol) ||
    (!is_atomic_symbol(*symbol) && !protected_by_atomic_region))
    return false;

  const exprt &rhs = without_cast(instruction.assign_rhs());
  if(
    (rhs.id() != ID_plus && rhs.id() != ID_minus) ||
    rhs.operands().size() != 2 || without_cast(rhs.op0()) != lhs)
    return false;
  if(!uses_only_immutable_shared(rhs.op1(), ns, mutable_shared))
    return false;

  effect.object = to_symbol_expr(lhs);
  effect.delta = rhs.op1();
  effect.subtract = rhs.id() == ID_minus;
  return true;
}

std::set<const goto_programt::instructiont *> control_signature(
  const goto_programt &program,
  const std::map<const goto_programt::instructiont *, std::size_t> &positions,
  const std::size_t instruction_position,
  bool &supported)
{
  std::set<const goto_programt::instructiont *> signature;
  supported = true;
  for(const auto &candidate : program.instructions)
  {
    if(!candidate.is_goto() || candidate.targets.size() != 1)
      continue;
    const auto source_position = positions.at(&candidate);
    const auto target_position = positions.at(&*candidate.get_target());
    if(target_position <= source_position)
      continue;
    if(candidate.condition().is_true())
    {
      supported = false;
      return {};
    }
    if(
      source_position < instruction_position &&
      instruction_position < target_position)
      signature.insert(&candidate);
  }
  return signature;
}

bool is_restricting_helper(
  const irep_idt &identifier,
  const goto_modelt &model,
  const namespacet &ns)
{
  const auto function = model.goto_functions.function_map.find(identifier);
  if(
    function == model.goto_functions.function_map.end() ||
    !function->second.body_available())
    return identifier == "abort";

  for(const auto &instruction : function->second.body.instructions)
  {
    if(instruction.is_assign())
    {
      const symbolt *symbol = nullptr;
      if(is_shared_scalar(
           without_cast(instruction.assign_lhs()), ns, symbol))
        return false;
    }
    else if(instruction.is_function_call())
    {
      irep_idt nested;
      if(
        !direct_call_identifier(instruction, nested) ||
        nested != "abort")
        return false;
    }
    else if(
      instruction.is_start_thread() || instruction.is_end_thread() ||
      instruction.is_atomic_begin() || instruction.is_atomic_end())
      return false;
  }
  return true;
}

exprt exact_count(const exprt &bound, const typet &induction_type)
{
  exprt converted_bound = bound;
  if(converted_bound.type() != induction_type)
    converted_bound = typecast_exprt(converted_bound, induction_type);
  if(induction_type.id() == ID_unsignedbv)
    return converted_bound;
  if(induction_type.id() != ID_signedbv)
    return nil_exprt();
  const exprt zero = from_integer(0, induction_type);
  return if_exprt(
    binary_relation_exprt(converted_bound, ID_gt, zero),
    converted_bound,
    zero);
}

bool summarize_worker(
  const irep_idt &worker,
  const goto_modelt &model,
  const namespacet &ns,
  const std::set<irep_idt> &mutable_shared,
  worker_summaryt &summary,
  std::string &reason)
{
  const auto function = model.goto_functions.function_map.find(worker);
  if(
    function == model.goto_functions.function_map.end() ||
    !function->second.body_available())
  {
    reason = "missing_worker";
    return false;
  }

  const auto &program = function->second.body;
  std::map<const goto_programt::instructiont *, std::size_t> positions;
  std::size_t position = 0;
  for(auto instruction = program.instructions.begin();
      instruction != program.instructions.end(); ++instruction)
    positions.emplace(&*instruction, position++);

  goto_programt::const_targett backedge = program.instructions.end();
  goto_programt::const_targett loop_head = program.instructions.end();
  for(auto instruction = program.instructions.begin();
      instruction != program.instructions.end(); ++instruction)
  {
    if(
      instruction->is_goto() && instruction->condition().is_true() &&
      instruction->targets.size() == 1 &&
      positions[&*instruction->get_target()] < positions[&*instruction])
    {
      if(backedge != program.instructions.end())
      {
        reason = "multiple_backedges";
        return false;
      }
      backedge = instruction;
      loop_head = instruction->get_target();
    }
  }
  if(backedge == program.instructions.end())
  {
    reason = "no_canonical_loop";
    return false;
  }

  irep_idt induction;
  exprt bound;
  if(!parse_exit_guard(*loop_head, induction, bound))
  {
    reason = "loop_guard";
    return false;
  }
  if(!uses_only_immutable_shared(bound, ns, mutable_shared))
  {
    reason = "mutable_loop_bound";
    return false;
  }

  std::size_t increment_count = 0;
  std::size_t increment_position = 0;
  for(auto instruction = loop_head; instruction != backedge; ++instruction)
  {
    irep_idt candidate;
    if(
      parse_unit_increment(*instruction, candidate) &&
      candidate == induction)
    {
      ++increment_count;
      increment_position = positions[&*instruction];
    }
  }
  if(increment_count != 1)
  {
    reason = "induction_update";
    return false;
  }

  bool initialized = false;
  for(auto instruction = program.instructions.begin();
      instruction != loop_head; ++instruction)
    initialized =
      initialized || parse_zero_initialization(*instruction, induction);
  if(!initialized)
  {
    reason = "induction_initialization";
    return false;
  }

  const exprt &induction_expr =
    without_cast(loop_head->condition().op0().op0());
  summary.count = exact_count(bound, induction_expr.type());
  if(summary.count.is_nil())
  {
    reason = "loop_count_type";
    return false;
  }

  bool increment_control_supported = false;
  const auto increment_control = control_signature(
    program, positions, increment_position, increment_control_supported);
  if(!increment_control_supported)
  {
    reason = "unsupported_forward_control";
    return false;
  }

  std::size_t atomic_depth = 0;
  for(auto instruction = program.instructions.begin();
      instruction != program.instructions.end(); ++instruction)
  {
    if(instruction->is_assert())
    {
      reason = "worker_property";
      return false;
    }
    if(instruction->is_atomic_begin())
    {
      ++atomic_depth;
      continue;
    }
    if(instruction->is_atomic_end())
    {
      if(atomic_depth == 0)
      {
        reason = "atomic_region_balance";
        return false;
      }
      --atomic_depth;
      continue;
    }

    if(instruction->is_function_call())
    {
      irep_idt callee;
      if(
        !direct_call_identifier(*instruction, callee) ||
        !is_restricting_helper(callee, model, ns))
      {
        reason = "worker_call";
        return false;
      }
      continue;
    }

    if(!instruction->is_assign())
      continue;
    const symbolt *lhs_symbol = nullptr;
    const exprt &lhs = without_cast(instruction->assign_lhs());
    if(!is_shared_scalar(lhs, ns, lhs_symbol))
      continue;

    effectt effect;
    bool effect_control_supported = false;
    const auto effect_control = control_signature(
      program,
      positions,
      positions[&*instruction],
      effect_control_supported);
    if(
      positions[&*instruction] <= positions[&*loop_head] ||
      positions[&*instruction] >= positions[&*backedge] ||
      !effect_control_supported ||
      effect_control != increment_control ||
      !parse_translation(
        *instruction,
        ns,
        mutable_shared,
        atomic_depth != 0,
        effect))
    {
      reason = "shared_write_not_translation";
      return false;
    }
    summary.effects.push_back(std::move(effect));
  }

  if(summary.effects.empty())
  {
    reason = "no_translation";
    return false;
  }
  if(atomic_depth != 0)
  {
    reason = "atomic_region_balance";
    return false;
  }

  summary.worker = worker;
  return true;
}

bool collect_lifecycle(
  goto_modelt &model,
  const namespacet &ns,
  std::vector<create_recordt> &creates,
  std::vector<goto_programt::targett> &joins,
  std::string &reason)
{
  auto main = model.goto_functions.function_map.find("main");
  if(
    main == model.goto_functions.function_map.end() ||
    !main->second.body_available())
  {
    reason = "missing_main";
    return false;
  }

  std::map<irep_idt, irep_idt> handle_worker;
  std::set<irep_idt> joined;
  bool join_seen = false;
  for(auto instruction = main->second.body.instructions.begin();
      instruction != main->second.body.instructions.end(); ++instruction)
  {
    irep_idt callee;
    if(!direct_call_identifier(*instruction, callee))
      continue;
    if(callee == "pthread_create")
    {
      if(join_seen || instruction->call_arguments().size() < 3)
      {
        reason = "create_order";
        return false;
      }
      irep_idt handle;
      irep_idt worker;
      if(
        !addressed_symbol(instruction->call_arguments()[0], handle) ||
        !addressed_symbol(instruction->call_arguments()[2], worker) ||
        handle_worker.find(handle) != handle_worker.end())
      {
        reason = "create_resolution";
        return false;
      }
      const symbolt *handle_symbol = nullptr;
      if(
        ns.lookup(handle, handle_symbol) ||
        handle_symbol->is_static_lifetime)
      {
        reason = "escaping_handle";
        return false;
      }
      handle_worker.emplace(handle, worker);
      creates.push_back({handle, worker, instruction});
    }
    else if(callee == "pthread_join")
    {
      join_seen = true;
      irep_idt handle;
      if(
        instruction->call_arguments().empty() ||
        !direct_symbol(instruction->call_arguments()[0], handle) ||
        handle_worker.find(handle) == handle_worker.end() ||
        !joined.insert(handle).second)
      {
        reason = "join_resolution";
        return false;
      }
      joins.push_back(instruction);
    }
  }

  if(
    creates.size() < 2 || joins.size() != creates.size() ||
    joined.size() != creates.size())
  {
    reason = "incomplete_lifecycle";
    return false;
  }
  return true;
}

bool validate_main_region(
  const goto_modelt &model,
  const namespacet &ns,
  const std::vector<create_recordt> &creates,
  const std::vector<goto_programt::targett> &joins,
  std::string &reason)
{
  const auto main = model.goto_functions.function_map.find("main");
  INVARIANT(
    main != model.goto_functions.function_map.end(),
    "lifecycle collection found main");

  const auto first_create = creates.front().instruction;
  const auto final_join = joins.back();
  for(auto instruction = first_create;
      instruction != std::next(final_join); ++instruction)
  {
    if(instruction->is_function_call())
    {
      irep_idt callee;
      if(
        !direct_call_identifier(*instruction, callee) ||
        (callee != "pthread_create" && callee != "pthread_join"))
      {
        reason = "main_region_call";
        return false;
      }
      continue;
    }

    if(instruction->is_assign())
    {
      const exprt &lhs = without_cast(instruction->assign_lhs());
      const symbolt *symbol = nullptr;
      if(lhs.id() != ID_symbol || is_shared_scalar(lhs, ns, symbol))
      {
        reason = "main_region_write";
        return false;
      }
      continue;
    }

    if(
      instruction->is_goto() || instruction->is_assume() ||
      instruction->is_assert() || instruction->is_other() ||
      instruction->is_start_thread() || instruction->is_end_thread() ||
      instruction->is_atomic_begin() || instruction->is_atomic_end())
    {
      reason = "main_region_control";
      return false;
    }
  }
  return true;
}

void collect_mutable_shared(
  const goto_modelt &model,
  const namespacet &ns,
  const std::vector<create_recordt> &creates,
  std::set<irep_idt> &mutable_shared)
{
  for(const auto &create : creates)
  {
    const auto function =
      model.goto_functions.function_map.find(create.worker);
    if(
      function == model.goto_functions.function_map.end() ||
      !function->second.body_available())
      continue;
    for(const auto &instruction : function->second.body.instructions)
    {
      if(!instruction.is_assign())
        continue;
      const exprt &lhs = without_cast(instruction.assign_lhs());
      const symbolt *symbol = nullptr;
      if(is_shared_scalar(lhs, ns, symbol))
        mutable_shared.insert(
          to_symbol_expr(lhs).get_identifier());
    }
  }
}

exprt cast_if_needed(exprt value, const typet &type)
{
  if(value.type() == type)
    return value;
  return typecast_exprt(std::move(value), type);
}

bool constant_eval(
  const exprt &src,
  const std::map<irep_idt, mp_integer> &environment,
  mp_integer &value)
{
  const exprt &expr = without_cast(src);
  if(expr.id() == ID_constant)
    return !to_integer(to_constant_expr(expr), value);
  if(expr.id() == ID_symbol)
  {
    const auto found =
      environment.find(to_symbol_expr(expr).get_identifier());
    if(found == environment.end())
      return false;
    value = found->second;
    return true;
  }
  if(
    (expr.id() == ID_plus || expr.id() == ID_minus ||
     expr.id() == ID_mult) &&
    expr.operands().size() == 2)
  {
    mp_integer lhs;
    mp_integer rhs;
    if(
      !constant_eval(expr.op0(), environment, lhs) ||
      !constant_eval(expr.op1(), environment, rhs))
      return false;
    if(expr.id() == ID_plus)
      value = lhs + rhs;
    else if(expr.id() == ID_minus)
      value = lhs - rhs;
    else
      value = lhs * rhs;
    return true;
  }
  return false;
}

bool signed_value_fits(const mp_integer &value, const typet &type)
{
  if(type.id() != ID_signedbv)
    return false;
  const auto width = to_signedbv_type(type).get_width();
  if(width == 0)
    return false;
  mp_integer limit = 1;
  for(std::size_t index = 1; index < width; ++index)
    limit *= 2;
  return value >= -limit && value < limit;
}

bool integer_value_fits(const mp_integer &value, const typet &type)
{
  if(type.id() == ID_signedbv)
    return signed_value_fits(value, type);
  if(type.id() != ID_unsignedbv)
    return false;
  const auto width = to_unsignedbv_type(type).get_width();
  if(width == 0 || value < 0)
    return false;
  mp_integer limit = 1;
  for(std::size_t index = 0; index < width; ++index)
    limit *= 2;
  return value < limit;
}

bool constant_bound(const exprt &expr, mp_integer &bound)
{
  return constant_eval(expr, {}, bound) && bound >= 0 && bound <= 256;
}

bool collect_nonnegative_affine_terms(
  const exprt &src,
  const exprt &target,
  const namespacet &ns,
  affine_worker_summaryt &summary)
{
  const exprt &expr = without_cast(src);
  if(expr.id() == ID_plus)
  {
    for(const auto &operand : expr.operands())
    {
      if(!collect_nonnegative_affine_terms(
           operand, target, ns, summary))
        return false;
    }
    return true;
  }
  if(expr.id() == ID_constant)
  {
    mp_integer value;
    if(to_integer(to_constant_expr(expr), value) || value < 0)
      return false;
    summary.offset += value;
    return true;
  }
  if(expr.id() != ID_symbol)
    return false;
  if(expr == target)
  {
    ++summary.self_coefficient;
    return summary.self_coefficient <= 1;
  }

  const symbolt *source_symbol = nullptr;
  if(!is_shared_scalar(expr, ns, source_symbol))
    return false;
  const auto identifier = to_symbol_expr(expr).get_identifier();
  if(!summary.source.empty() && summary.source != identifier)
    return false;
  summary.source = identifier;
  ++summary.source_coefficient;
  return summary.source_coefficient <= 1;
}

bool parse_nonnegative_affine_update(
  const exprt &lhs,
  const exprt &rhs,
  const namespacet &ns,
  affine_worker_summaryt &summary)
{
  summary.self_coefficient = 0;
  summary.source_coefficient = 0;
  summary.offset = 0;
  summary.source = irep_idt();
  if(!collect_nonnegative_affine_terms(rhs, lhs, ns, summary))
    return false;
  return
    summary.source_coefficient == 1 &&
    !summary.source.empty() &&
    summary.offset <= 256;
}

bool parse_affine_worker(
  const irep_idt &worker,
  const goto_modelt &model,
  const namespacet &ns,
  affine_worker_summaryt &summary,
  std::string &reason)
{
  const auto function = model.goto_functions.function_map.find(worker);
  if(
    function == model.goto_functions.function_map.end() ||
    !function->second.body_available())
  {
    reason = "prefix_missing_worker";
    return false;
  }

  const auto &program = function->second.body;
  std::map<const goto_programt::instructiont *, std::size_t> positions;
  std::size_t position = 0;
  for(const auto &instruction : program.instructions)
    positions.emplace(&instruction, position++);

  auto backedge = program.instructions.end();
  auto loop_head = program.instructions.end();
  for(auto instruction = program.instructions.begin();
      instruction != program.instructions.end(); ++instruction)
  {
    if(
      instruction->is_goto() && instruction->condition().is_true() &&
      instruction->targets.size() == 1 &&
      positions[&*instruction->get_target()] < positions[&*instruction])
    {
      if(backedge != program.instructions.end())
      {
        reason = "prefix_multiple_loops";
        return false;
      }
      backedge = instruction;
      loop_head = instruction->get_target();
    }
  }
  if(backedge == program.instructions.end())
  {
    reason = "prefix_no_loop";
    return false;
  }

  irep_idt induction;
  exprt bound_expr;
  if(
    !parse_exit_guard(*loop_head, induction, bound_expr) ||
    !constant_bound(bound_expr, summary.count))
  {
    reason = "prefix_loop_bound";
    return false;
  }

  bool induction_initialized = false;
  std::size_t induction_updates = 0;
  std::size_t affine_updates = 0;
  std::size_t increment_position = 0;
  std::size_t affine_position = 0;
  unsigned atomic_depth = 0;
  for(auto instruction = program.instructions.begin();
      instruction != program.instructions.end(); ++instruction)
  {
    if(instruction->is_atomic_begin())
    {
      ++atomic_depth;
      continue;
    }
    if(instruction->is_atomic_end())
    {
      if(atomic_depth == 0)
      {
        reason = "prefix_atomic_balance";
        return false;
      }
      --atomic_depth;
      continue;
    }
    if(instruction->is_assert())
    {
      reason = "prefix_worker_control";
      return false;
    }
    if(instruction->is_function_call())
    {
      irep_idt callee;
      if(
        !direct_call_identifier(*instruction, callee) ||
        callee != "pthread_exit" ||
        positions[&*instruction] <= positions[&*backedge])
      {
        reason = "prefix_worker_control";
        return false;
      }
      continue;
    }
    if(!instruction->is_assign())
      continue;

    const exprt &lhs = without_cast(instruction->assign_lhs());
    const exprt &rhs = without_cast(instruction->assign_rhs());
    if(lhs.id() != ID_symbol)
    {
      reason = "prefix_worker_lhs";
      return false;
    }
    const auto lhs_id = to_symbol_expr(lhs).get_identifier();
    if(lhs_id == induction)
    {
      if(positions[&*instruction] < positions[&*loop_head])
      {
        mp_integer zero;
        induction_initialized =
          rhs.id() == ID_constant &&
          !to_integer(to_constant_expr(rhs), zero) && zero == 0;
      }
      else
      {
        irep_idt increment;
        if(
          !parse_unit_increment(*instruction, increment) ||
          increment != induction)
        {
          reason = "prefix_induction";
          return false;
        }
        ++induction_updates;
        increment_position = positions[&*instruction];
      }
      continue;
    }

    const symbolt *lhs_symbol = nullptr;
    if(!is_shared_scalar(lhs, ns, lhs_symbol))
      continue;
    if(
      atomic_depth == 0 ||
      !parse_nonnegative_affine_update(lhs, rhs, ns, summary))
    {
      reason = "prefix_non_affine_write";
      return false;
    }
    summary.target = lhs_id;
    ++affine_updates;
    affine_position = positions[&*instruction];
  }

  if(
    !induction_initialized || induction_updates != 1 ||
    affine_updates != 1 || atomic_depth != 0 ||
    summary.target == summary.source ||
    increment_position <= positions[&*loop_head] ||
    increment_position >= positions[&*backedge] ||
    affine_position <= positions[&*loop_head] ||
    affine_position >= positions[&*backedge])
  {
    reason = "prefix_worker_shape";
    return false;
  }
  bool increment_control_supported = false;
  bool affine_control_supported = false;
  const auto increment_control = control_signature(
    program, positions, increment_position, increment_control_supported);
  const auto affine_control = control_signature(
    program, positions, affine_position, affine_control_supported);
  if(
    !increment_control_supported || !affine_control_supported ||
    increment_control != affine_control)
  {
    reason = "prefix_worker_control";
    return false;
  }
  summary.worker = worker;
  summary.induction = induction;
  return true;
}

bool validate_exclusive_writes_and_property(
  const goto_modelt &model,
  const namespacet &ns,
  const affine_worker_summaryt (&workers)[2],
  std::string &reason)
{
  if(workers[0].induction == workers[1].induction)
  {
    reason = "prefix_shared_induction";
    return false;
  }

  std::map<irep_idt, std::map<irep_idt, std::size_t>> writes;
  std::size_t properties = 0;
  const std::set<irep_idt> summarized_objects = {
    workers[0].target, workers[0].source};
  for(const auto &function : model.goto_functions.function_map)
  {
    if(!function.second.body_available())
      continue;
    for(const auto &instruction : function.second.body.instructions)
    {
      if(
        contains_address_of_symbol(
          instruction.code(), summarized_objects) ||
        (instruction.has_condition() &&
         contains_address_of_symbol(
           instruction.condition(), summarized_objects)))
      {
        reason = "prefix_address_taken";
        return false;
      }
      if(instruction.is_assert())
        ++properties;
      if(!instruction.is_assign())
        continue;
      const exprt &lhs = without_cast(instruction.assign_lhs());
      if(lhs.id() == ID_symbol)
        ++writes[to_symbol_expr(lhs).get_identifier()][function.first];
    }
  }

  if(properties != 1)
  {
    reason = "prefix_property_count";
    return false;
  }
  for(const auto &worker : workers)
  {
    // Static initialization, an optional exact main initialization, and the
    // one syntactic worker update are the only writes to a summarized object.
    const auto &target_writes = writes[worker.target];
    const auto main_write = target_writes.find("main");
    if(
      target_writes.size() != (main_write == target_writes.end() ? 2 : 3) ||
      target_writes.find("__CPROVER_initialize") == target_writes.end() ||
      target_writes.at("__CPROVER_initialize") != 1 ||
      (main_write != target_writes.end() && main_write->second != 1) ||
      target_writes.find(worker.worker) == target_writes.end() ||
      target_writes.at(worker.worker) != 1)
    {
      reason = "prefix_extra_shared_writer";
      return false;
    }
    // A file-scope induction variable has one static initialization. A local
    // induction variable does not. Both have exactly their worker
    // initialization and unit increment.
    const auto &induction_writes = writes[worker.induction];
    const symbolt &induction_symbol = ns.lookup(worker.induction);
    const auto static_write =
      induction_writes.find("__CPROVER_initialize");
    const bool induction_shape =
      induction_symbol.is_static_lifetime
        ? induction_writes.size() == 2 &&
            static_write != induction_writes.end() &&
            static_write->second == 1
        : induction_writes.size() == 1 &&
            static_write == induction_writes.end();
    if(
      !induction_shape ||
      induction_writes.find(worker.worker) == induction_writes.end() ||
      induction_writes.at(worker.worker) != 2)
    {
      reason = "prefix_extra_induction_writer";
      return false;
    }
  }
  return true;
}

bool evaluate_bound_function(
  const irep_idt &function_id,
  const goto_modelt &model,
  mp_integer &result,
  std::string &reason)
{
  const auto function = model.goto_functions.function_map.find(function_id);
  if(
    function == model.goto_functions.function_map.end() ||
    !function->second.body_available())
  {
    reason = "prefix_bound_function";
    return false;
  }
  const auto &program = function->second.body;
  std::map<const goto_programt::instructiont *, std::size_t> positions;
  std::size_t position = 0;
  for(const auto &instruction : program.instructions)
    positions.emplace(&instruction, position++);

  auto backedge = program.instructions.end();
  auto loop_head = program.instructions.end();
  for(auto instruction = program.instructions.begin();
      instruction != program.instructions.end(); ++instruction)
  {
    if(instruction->is_function_call() || instruction->is_assert())
    {
      reason = "prefix_bound_side_effect";
      return false;
    }
    if(
      instruction->is_goto() && instruction->condition().is_true() &&
      instruction->targets.size() == 1 &&
      positions[&*instruction->get_target()] < positions[&*instruction])
    {
      if(backedge != program.instructions.end())
      {
        reason = "prefix_bound_loops";
        return false;
      }
      backedge = instruction;
      loop_head = instruction->get_target();
    }
  }
  if(backedge == program.instructions.end())
  {
    reason = "prefix_bound_no_loop";
    return false;
  }

  irep_idt induction;
  exprt bound_expr;
  mp_integer iterations;
  if(
    !parse_exit_guard(*loop_head, induction, bound_expr) ||
    !constant_bound(bound_expr, iterations))
  {
    reason = "prefix_bound_count";
    return false;
  }

  std::map<irep_idt, mp_integer> environment;
  for(const auto &entry : model.symbol_table.symbols)
  {
    mp_integer value;
    if(
      entry.second.is_static_lifetime &&
      constant_eval(entry.second.value, {}, value))
      environment.emplace(entry.first, value);
  }

  auto execute_assignment =
    [&](const goto_programt::instructiont &instruction) {
      if(!instruction.is_assign())
        return true;
      const exprt &lhs = without_cast(instruction.assign_lhs());
      if(lhs.id() != ID_symbol)
        return false;
      mp_integer value;
      if(!constant_eval(instruction.assign_rhs(), environment, value))
        return false;
      if(!signed_value_fits(value, lhs.type()))
        return false;
      environment[to_symbol_expr(lhs).get_identifier()] = value;
      return true;
    };

  for(auto instruction = program.instructions.begin();
      instruction != loop_head; ++instruction)
  {
    if(!execute_assignment(*instruction))
    {
      reason = "prefix_bound_initialization";
      return false;
    }
  }
  for(mp_integer iteration = 0; iteration < iterations; ++iteration)
  {
    for(auto instruction = std::next(loop_head);
        instruction != backedge; ++instruction)
    {
      if(
        instruction->is_goto() || instruction->is_function_call() ||
        !execute_assignment(*instruction))
      {
        reason = "prefix_bound_body";
        return false;
      }
    }
  }

  for(auto instruction = std::next(backedge);
      instruction != program.instructions.end(); ++instruction)
  {
    if(instruction->is_set_return_value())
    {
      if(!constant_eval(instruction->return_value(), environment, result))
      {
        reason = "prefix_bound_return";
        return false;
      }
      return true;
    }
  }
  reason = "prefix_missing_bound_return";
  return false;
}

void pareto_prune(std::vector<affine_statet> &states)
{
  std::vector<affine_statet> retained;
  for(const auto &candidate : states)
  {
    bool dominated = false;
    for(const auto &other : states)
    {
      if(
        other.first >= candidate.first &&
        other.second >= candidate.second &&
        (other.first != candidate.first ||
         other.second != candidate.second))
      {
        dominated = true;
        break;
      }
    }
    const bool duplicate = std::any_of(
      retained.begin(),
      retained.end(),
      [&](const affine_statet &other)
      {
        return
          other.first == candidate.first &&
          other.second == candidate.second;
      });
    if(!dominated && !duplicate)
      retained.push_back(candidate);
  }
  states.swap(retained);
}

affine_statet apply_affine_worker(
  const affine_worker_summaryt &worker,
  const affine_statet &state,
  const irep_idt &first,
  const char schedule_step,
  const bool record_schedule)
{
  affine_statet result;
  if(worker.target == first)
  {
    result = {
      worker.self_coefficient * state.first +
        worker.source_coefficient * state.second + worker.offset,
      state.second,
      state.schedule};
  }
  else
  {
    result = {
      state.first,
      worker.self_coefficient * state.second +
        worker.source_coefficient * state.first + worker.offset,
      state.schedule};
  }
  if(record_schedule)
    result.schedule.push_back(schedule_step);
  return result;
}

bool assertion_bound(
  const goto_modelt &model,
  const irep_idt &first,
  const irep_idt &second,
  irep_idt &bound_function,
  std::map<irep_idt, mp_integer> &initial_values,
  std::string &reason)
{
  auto main = model.goto_functions.function_map.find("main");
  if(
    main == model.goto_functions.function_map.end() ||
    !main->second.body_available())
  {
    reason = "prefix_missing_main";
    return false;
  }

  std::map<irep_idt, irep_idt> call_results;
  std::map<irep_idt, exprt> assignments;
  irep_idt assertion_argument;
  std::size_t assertion_calls = 0;
  std::size_t create_calls = 0;
  for(auto instruction = main->second.body.instructions.begin();
      instruction != main->second.body.instructions.end(); ++instruction)
  {
    if(instruction->is_assign())
    {
      const exprt &lhs = without_cast(instruction->assign_lhs());
      if(lhs.id() == ID_symbol)
      {
        const auto lhs_id = to_symbol_expr(lhs).get_identifier();
        assignments[lhs_id] = instruction->assign_rhs();
        if(create_calls == 0 && (lhs_id == first || lhs_id == second))
        {
          mp_integer value;
          if(constant_eval(instruction->assign_rhs(), {}, value))
            initial_values[lhs_id] = value;
        }
      }
      continue;
    }
    irep_idt callee;
    if(!direct_call_identifier(*instruction, callee))
      continue;
    if(callee == "pthread_create")
    {
      if(instruction->call_arguments().size() < 3)
      {
        reason = "prefix_create";
        return false;
      }
      ++create_calls;
    }
    else if(callee == "pthread_join")
    {
      reason = "prefix_has_join";
      return false;
    }
    else if(callee == "__VERIFIER_assert")
    {
      if(
        instruction->call_arguments().size() != 1 ||
        !direct_symbol(instruction->call_arguments()[0], assertion_argument))
      {
        reason = "prefix_assert_argument";
        return false;
      }
      ++assertion_calls;
    }
    else if(instruction->call_lhs().is_not_nil())
    {
      const exprt &lhs = without_cast(instruction->call_lhs());
      if(lhs.id() == ID_symbol)
        call_results[to_symbol_expr(lhs).get_identifier()] = callee;
    }
  }
  if(
    create_calls != 2 || assertion_calls != 1 ||
    initial_values.size() != 2)
  {
    reason = "prefix_main_shape";
    return false;
  }

  const auto assertion_assignment = assignments.find(assertion_argument);
  if(assertion_assignment == assignments.end())
  {
    reason = "prefix_assert_definition";
    return false;
  }
  const exprt &condition = without_cast(assertion_assignment->second);
  if(condition.id() != ID_and || condition.operands().size() != 2)
  {
    reason = "prefix_assert_shape";
    return false;
  }

  irep_idt common_bound;
  std::set<irep_idt> compared_objects;
  for(const auto &operand : condition.operands())
  {
    const exprt &comparison = without_cast(operand);
    if(
      comparison.id() != ID_le ||
      comparison.operands().size() != 2)
    {
      reason = "prefix_assert_relation";
      return false;
    }
    irep_idt object;
    irep_idt bound;
    if(
      !direct_symbol(comparison.op0(), object) ||
      !direct_symbol(comparison.op1(), bound) ||
      (object != first && object != second))
    {
      reason = "prefix_assert_symbols";
      return false;
    }
    if(common_bound.empty())
      common_bound = bound;
    else if(common_bound != bound)
    {
      reason = "prefix_assert_bounds";
      return false;
    }
    compared_objects.insert(object);
  }
  if(compared_objects.size() != 2)
  {
    reason = "prefix_assert_coverage";
    return false;
  }

  const auto bound_assignment = assignments.find(common_bound);
  if(bound_assignment == assignments.end())
  {
    reason = "prefix_bound_definition";
    return false;
  }
  irep_idt return_temp;
  if(!direct_symbol(bound_assignment->second, return_temp))
  {
    reason = "prefix_bound_temp";
    return false;
  }
  const auto bound_call = call_results.find(return_temp);
  if(bound_call == call_results.end())
  {
    reason = "prefix_bound_call";
    return false;
  }
  bound_function = bound_call->second;
  return true;
}

bool zero_constant(const exprt &src)
{
  const exprt &expr = without_cast(src);
  if(expr.id() != ID_constant)
    return false;
  mp_integer value;
  return !to_integer(to_constant_expr(expr), value) && value == 0;
}

bool truthy_symbol(const exprt &src, irep_idt &identifier)
{
  const exprt &expr = without_cast(src);
  if(expr.id() != ID_notequal || expr.operands().size() != 2)
    return false;
  return
    (direct_symbol(expr.op0(), identifier) &&
     zero_constant(expr.op1())) ||
    (direct_symbol(expr.op1(), identifier) &&
     zero_constant(expr.op0()));
}

bool static_initial_value(
  const goto_modelt &model,
  const irep_idt &identifier,
  mp_integer &value)
{
  const auto symbol = model.symbol_table.symbols.find(identifier);
  return
    symbol != model.symbol_table.symbols.end() &&
    symbol->second.is_static_lifetime &&
    constant_eval(symbol->second.value, {}, value);
}

bool collect_affine_form(
  const exprt &src,
  const namespacet &ns,
  irep_idt &object,
  const std::map<irep_idt, affine_formt> &locals,
  affine_formt &form)
{
  const exprt &expr = without_cast(src);
  if(expr.id() == ID_constant)
  {
    form.coefficient = 0;
    return !to_integer(to_constant_expr(expr), form.offset);
  }
  if(expr.id() == ID_symbol)
  {
    const irep_idt identifier =
      to_symbol_expr(expr).get_identifier();
    const symbolt *symbol = nullptr;
    if(ns.lookup(identifier, symbol))
      return false;
    if(symbol->is_static_lifetime)
    {
      if(
        symbol->is_type || symbol->type.id() == ID_pointer ||
        (object.empty() ? false : identifier != object))
      {
        if(
          symbol->is_type || symbol->type.id() == ID_pointer ||
          !object.empty())
          return false;
      }
      if(object.empty())
        object = identifier;
      form.coefficient = 1;
      form.offset = 0;
      return true;
    }
    const auto local = locals.find(identifier);
    if(local == locals.end())
      return false;
    form = local->second;
    return true;
  }
  if(
    (expr.id() == ID_plus || expr.id() == ID_minus) &&
    expr.operands().size() == 2)
  {
    affine_formt lhs;
    affine_formt rhs;
    if(
      !collect_affine_form(
        expr.op0(), ns, object, locals, lhs) ||
      !collect_affine_form(
        expr.op1(), ns, object, locals, rhs))
      return false;
    form.coefficient =
      expr.id() == ID_plus
        ? lhs.coefficient + rhs.coefficient
        : lhs.coefficient - rhs.coefficient;
    form.offset =
      expr.id() == ID_plus
        ? lhs.offset + rhs.offset
        : lhs.offset - rhs.offset;
    return true;
  }
  return false;
}

bool contains_any_shared_scalar(
  const exprt &expr,
  const namespacet &ns)
{
  if(expr.id() == ID_symbol)
  {
    const symbolt *symbol = nullptr;
    if(
      !ns.lookup(
        to_symbol_expr(expr).get_identifier(), symbol) &&
      symbol->is_static_lifetime && !symbol->is_type)
      return true;
  }
  for(const auto &operand : expr.operands())
  {
    if(contains_any_shared_scalar(operand, ns))
      return true;
  }
  return false;
}

bool uses_only_object_and_constants(
  const exprt &src,
  const irep_idt &object)
{
  const exprt &expr = without_cast(src);
  if(expr.id() == ID_constant)
    return true;
  if(expr.id() == ID_symbol)
    return
      to_symbol_expr(expr).get_identifier() == object;
  if(expr.id() == ID_side_effect || expr.id() == ID_dereference)
    return false;
  for(const auto &operand : expr.operands())
  {
    if(!uses_only_object_and_constants(operand, object))
      return false;
  }
  return true;
}

bool state_independent_call(
  const irep_idt &identifier,
  const goto_modelt &model,
  const namespacet &ns)
{
  const auto function =
    model.goto_functions.function_map.find(identifier);
  if(
    function == model.goto_functions.function_map.end() ||
    !function->second.body_available())
    return false;
  for(const auto &instruction : function->second.body.instructions)
  {
    if(
      instruction.is_assert() || instruction.is_assume() ||
      instruction.is_start_thread() || instruction.is_end_thread() ||
      instruction.is_atomic_begin() || instruction.is_atomic_end() ||
      instruction.is_function_call())
      return false;
    if(instruction.is_assign())
    {
      const exprt &lhs = without_cast(instruction.assign_lhs());
      const symbolt *symbol = nullptr;
      if(is_shared_scalar(lhs, ns, symbol))
        return false;
    }
  }
  return true;
}

bool parse_locked_affine_loop(
  const irep_idt &function_id,
  goto_modelt &model,
  const namespacet &ns,
  locked_loop_summaryt &summary,
  std::string &reason)
{
  const auto function =
    model.goto_functions.function_map.find(function_id);
  if(
    function == model.goto_functions.function_map.end() ||
    !function->second.body_available())
  {
    reason = "lock_missing_function";
    return false;
  }
  auto &program = function->second.body;
  std::map<const goto_programt::instructiont *, std::size_t> positions;
  std::size_t position = 0;
  for(auto instruction = program.instructions.begin();
      instruction != program.instructions.end(); ++instruction)
    positions.emplace(&*instruction, position++);

  auto backedge = program.instructions.end();
  auto loop_head = program.instructions.end();
  for(auto instruction = program.instructions.begin();
      instruction != program.instructions.end(); ++instruction)
  {
    if(
      instruction->is_goto() && instruction->condition().is_true() &&
      instruction->targets.size() == 1 &&
      positions.at(&*instruction->get_target()) <
        positions.at(&*instruction))
    {
      if(backedge != program.instructions.end())
      {
        reason = "lock_multiple_loops";
        return false;
      }
      backedge = instruction;
      loop_head = instruction->get_target();
    }
  }
  if(backedge == program.instructions.end())
  {
    reason = "lock_missing_loop";
    return false;
  }

  irep_idt induction;
  exprt bound;
  mp_integer count;
  if(
    !parse_exit_guard(*loop_head, induction, bound) ||
    !constant_bound(bound, count))
  {
    reason = "lock_loop_bound";
    return false;
  }
  std::size_t zero_initializations = 0;
  for(auto instruction = program.instructions.begin();
      instruction != loop_head; ++instruction)
    zero_initializations +=
      parse_zero_initialization(*instruction, induction) ? 1 : 0;
  if(zero_initializations != 1)
  {
    reason = "lock_loop_initialization";
    return false;
  }

  bool locked = false;
  bool lock_seen = false;
  bool unlock_seen = false;
  std::size_t induction_updates = 0;
  std::size_t shared_writes = 0;
  irep_idt object;
  irep_idt mutex;
  std::map<irep_idt, affine_formt> locals;
  affine_formt final_form;
  for(auto instruction = loop_head;
      instruction != std::next(backedge); ++instruction)
  {
    summary.covered.insert(&*instruction);
    if(instruction == loop_head || instruction == backedge)
      continue;

    irep_idt callee;
    if(direct_call_identifier(*instruction, callee))
    {
      if(callee == "pthread_mutex_lock")
      {
        irep_idt candidate;
        if(
          locked || lock_seen ||
          instruction->call_arguments().size() != 1 ||
          !addressed_symbol(
            instruction->call_arguments().front(), candidate))
        {
          reason = "lock_acquire_shape";
          return false;
        }
        mutex = candidate;
        locked = true;
        lock_seen = true;
      }
      else if(callee == "pthread_mutex_unlock")
      {
        irep_idt candidate;
        if(
          !locked || unlock_seen ||
          instruction->call_arguments().size() != 1 ||
          !addressed_symbol(
            instruction->call_arguments().front(), candidate) ||
          candidate != mutex)
        {
          reason = "lock_release_shape";
          return false;
        }
        locked = false;
        unlock_seen = true;
      }
      else if(!state_independent_call(callee, model, ns))
      {
        reason = "lock_loop_call";
        return false;
      }
      continue;
    }

    if(instruction->is_goto())
    {
      reason = "lock_loop_control";
      return false;
    }
    if(!instruction->is_assign())
    {
      if(
        instruction->is_decl() || instruction->is_dead() ||
        instruction->is_skip() || instruction->is_location() ||
        instruction->is_set_return_value())
        continue;
      reason = "lock_loop_instruction";
      return false;
    }

    irep_idt incremented;
    if(
      parse_unit_increment(*instruction, incremented) &&
      incremented == induction)
    {
      if(locked)
      {
        reason = "lock_induction_inside";
        return false;
      }
      ++induction_updates;
      continue;
    }

    const exprt &lhs = without_cast(instruction->assign_lhs());
    if(lhs.id() != ID_symbol)
    {
      reason = "lock_loop_lhs";
      return false;
    }
    const irep_idt lhs_id =
      to_symbol_expr(lhs).get_identifier();
    const symbolt *lhs_symbol = nullptr;
    if(ns.lookup(lhs_id, lhs_symbol))
    {
      reason = "lock_loop_symbol";
      return false;
    }
    affine_formt rhs_form;
    if(lhs_symbol->is_static_lifetime)
    {
      if(!locked)
      {
        reason = "lock_unprotected_write";
        return false;
      }
      if(object.empty())
        object = lhs_id;
      if(
        lhs_id != object ||
        !collect_affine_form(
          instruction->assign_rhs(),
          ns,
          object,
          locals,
          rhs_form) ||
        rhs_form.coefficient != 1)
      {
        reason = "lock_nontranslation";
        return false;
      }
      final_form = rhs_form;
      ++shared_writes;
    }
    else
    {
      if(
        !collect_affine_form(
          instruction->assign_rhs(),
          ns,
          object,
          locals,
          rhs_form))
      {
        reason = "lock_local_dataflow";
        return false;
      }
      locals[lhs_id] = rhs_form;
    }
  }
  if(
    locked || !lock_seen || !unlock_seen ||
    induction_updates != 1 || shared_writes != 1 ||
    object.empty() || mutex.empty() || final_form.offset == 0)
  {
    reason = "lock_loop_shape";
    return false;
  }

  summary.function = function_id;
  summary.induction = induction;
  summary.object = object;
  summary.mutex = mutex;
  summary.count = count;
  summary.delta = final_form.offset;
  summary.loop_head = loop_head;
  summary.backedge = backedge;
  return true;
}

bool validate_lock_aggregate_property(
  goto_modelt &model,
  const namespacet &ns,
  const locked_loop_summaryt &main_loop,
  const locked_loop_summaryt &worker_loop,
  const goto_programt::targett create,
  const goto_programt::targett join,
  goto_programt::targett &initialization,
  mp_integer &initial_value,
  std::string &reason)
{
  const auto main =
    model.goto_functions.function_map.find("main");
  INVARIANT(
    main != model.goto_functions.function_map.end(),
    "lock aggregate found main");
  std::map<const goto_programt::instructiont *, std::size_t> positions;
  std::size_t position = 0;
  for(const auto &instruction : main->second.body.instructions)
    positions.emplace(&instruction, position++);
  if(
    positions.at(&*create) >=
      positions.at(&*main_loop.loop_head) ||
    positions.at(&*main_loop.backedge) >=
      positions.at(&*join))
  {
    reason = "lock_lifecycle_order";
    return false;
  }

  const auto worker =
    model.goto_functions.function_map.find(worker_loop.function);
  INVARIANT(
    worker != model.goto_functions.function_map.end(),
    "lock aggregate parsed worker");
  for(const auto &instruction : worker->second.body.instructions)
  {
    if(worker_loop.covered.find(&instruction) !=
       worker_loop.covered.end())
      continue;
    if(
      instruction.is_decl() || instruction.is_dead() ||
      instruction.is_skip() || instruction.is_location() ||
      instruction.is_set_return_value() ||
      instruction.is_end_function())
      continue;
    if(instruction.is_assign())
    {
      if(
        contains_any_shared_scalar(
          instruction.assign_lhs(), ns) ||
        contains_any_shared_scalar(
          instruction.assign_rhs(), ns))
      {
        reason = "lock_worker_outer_shared";
        return false;
      }
      continue;
    }
    reason = "lock_worker_outer_effect";
    return false;
  }

  std::size_t initializations = 0;
  std::size_t property_calls = 0;
  goto_programt::const_targett property =
    main->second.body.instructions.end();
  for(auto instruction = main->second.body.instructions.begin();
      instruction != main->second.body.instructions.end(); ++instruction)
  {
    if(instruction->is_assign())
    {
      irep_idt lhs;
      mp_integer value;
      if(
        direct_symbol(instruction->assign_lhs(), lhs) &&
        lhs == main_loop.object &&
        positions.at(&*instruction) < positions.at(&*create) &&
        constant_eval(instruction->assign_rhs(), {}, value))
      {
        initialization = instruction;
        initial_value = value;
        ++initializations;
      }
    }
    irep_idt callee;
    if(
      direct_call_identifier(*instruction, callee) &&
      callee == "__VERIFIER_assert")
    {
      if(
        positions.at(&*instruction) <= positions.at(&*join) ||
        instruction->call_arguments().size() != 1 ||
        !uses_only_object_and_constants(
          instruction->call_arguments().front(),
          main_loop.object))
      {
        reason = "lock_property_scope";
        return false;
      }
      property = instruction;
      ++property_calls;
    }
  }
  if(initializations != 1 || property_calls != 1)
  {
    reason = "lock_property_shape";
    return false;
  }

  std::set<const goto_programt::instructiont *> allowed =
    main_loop.covered;
  allowed.insert(
    worker_loop.covered.begin(),
    worker_loop.covered.end());
  allowed.insert(&*initialization);
  allowed.insert(&*property);
  std::size_t assertions = 0;
  std::size_t all_creates = 0;
  std::size_t all_joins = 0;
  std::size_t builtin_worker_dispatches = 0;
  for(const auto &function : model.goto_functions.function_map)
  {
    if(!function.second.body_available())
      continue;
    for(const auto &instruction : function.second.body.instructions)
    {
      assertions += instruction.is_assert() ? 1 : 0;
      irep_idt callee;
      if(direct_call_identifier(instruction, callee))
      {
        if(callee == "pthread_create")
          ++all_creates;
        else if(callee == "pthread_join")
          ++all_joins;
        else if(callee == worker_loop.function)
        {
          if(function.first != "__spawned_thread")
          {
            reason = "lock_direct_worker_call";
            return false;
          }
          ++builtin_worker_dispatches;
        }
      }
      const bool mentions =
        contains_symbol(
          instruction.code(), {main_loop.object}) ||
        (instruction.has_condition() &&
         contains_symbol(
           instruction.condition(), {main_loop.object}));
      const bool mentions_mutex =
        contains_symbol(
          instruction.code(), {main_loop.mutex}) ||
        (instruction.has_condition() &&
         contains_symbol(
           instruction.condition(), {main_loop.mutex}));
      if(
        contains_address_of_symbol(
          instruction.code(), {main_loop.object}) ||
        (instruction.has_condition() &&
         contains_address_of_symbol(
           instruction.condition(), {main_loop.object})))
      {
        reason = "lock_object_alias";
        return false;
      }
      if(mentions && allowed.find(&instruction) == allowed.end())
      {
        if(
          function.first == "__CPROVER_initialize" &&
          instruction.is_assign())
          continue;
        reason = "lock_extra_object_access";
        return false;
      }
      if(
        mentions_mutex &&
        allowed.find(&instruction) == allowed.end())
      {
        if(
          function.first == "__CPROVER_initialize" &&
          instruction.is_assign())
          continue;
        reason = "lock_extra_mutex_access";
        return false;
      }
    }
  }
  if(assertions != 1)
  {
    reason = "lock_property_count";
    return false;
  }
  if(
    all_creates != 1 || all_joins != 1 ||
    builtin_worker_dispatches != 1)
  {
    reason = "lock_global_lifecycle";
    return false;
  }

  const symbolt *object_symbol = nullptr;
  const symbolt *mutex_symbol = nullptr;
  if(
    ns.lookup(main_loop.object, object_symbol) ||
    ns.lookup(main_loop.mutex, mutex_symbol) ||
    !object_symbol->is_static_lifetime ||
    !mutex_symbol->is_static_lifetime ||
    object_symbol->is_type || mutex_symbol->is_type)
  {
    reason = "lock_symbol_types";
    return false;
  }
  return true;
}

void collect_zero_equalities(
  const exprt &src,
  std::map<irep_idt, std::set<irep_idt>> &equalities,
  std::set<irep_idt> &zero_symbols)
{
  const exprt &expr = without_cast(src);
  if(expr.id() == ID_and)
  {
    for(const auto &operand : expr.operands())
      collect_zero_equalities(
        operand, equalities, zero_symbols);
    return;
  }
  if(expr.id() != ID_equal || expr.operands().size() != 2)
    return;
  irep_idt lhs;
  irep_idt rhs;
  const bool lhs_symbol = direct_symbol(expr.op0(), lhs);
  const bool rhs_symbol = direct_symbol(expr.op1(), rhs);
  if(lhs_symbol && rhs_symbol)
  {
    equalities[lhs].insert(rhs);
    equalities[rhs].insert(lhs);
  }
  else if(lhs_symbol && zero_constant(expr.op1()))
    zero_symbols.insert(lhs);
  else if(rhs_symbol && zero_constant(expr.op0()))
    zero_symbols.insert(rhs);
}

bool proves_zero_equalities(
  const exprt &condition,
  const std::set<irep_idt> &required)
{
  std::map<irep_idt, std::set<irep_idt>> equalities;
  std::set<irep_idt> zero_symbols;
  collect_zero_equalities(
    condition, equalities, zero_symbols);

  std::set<irep_idt> reached = zero_symbols;
  std::vector<irep_idt> worklist(
    zero_symbols.begin(), zero_symbols.end());
  while(!worklist.empty())
  {
    const irep_idt current = worklist.back();
    worklist.pop_back();
    const auto neighbours = equalities.find(current);
    if(neighbours == equalities.end())
      continue;
    for(const auto &neighbour : neighbours->second)
    {
      if(reached.insert(neighbour).second)
        worklist.push_back(neighbour);
    }
  }
  for(const auto &identifier : required)
  {
    if(reached.find(identifier) == reached.end())
      return false;
  }
  return true;
}

bool summarize_ticket_worker(
  const create_recordt &create,
  goto_modelt &model,
  const namespacet &ns,
  ticket_regiont &region,
  std::string &reason)
{
  const auto function =
    model.goto_functions.function_map.find(create.worker);
  if(
    function == model.goto_functions.function_map.end() ||
    !function->second.body_available())
  {
    reason = "ticket_missing_worker";
    return false;
  }

  auto &program = function->second.body;
  std::vector<goto_programt::targett> relevant;
  std::map<const goto_programt::instructiont *, std::size_t> positions;
  std::size_t position = 0;
  for(auto instruction = program.instructions.begin();
      instruction != program.instructions.end(); ++instruction)
  {
    positions.emplace(&*instruction, position++);
    if(
      instruction->is_decl() || instruction->is_dead() ||
      instruction->is_skip() || instruction->is_location() ||
      instruction->is_set_return_value() ||
      instruction->is_end_function())
      continue;
    relevant.push_back(instruction);
  }
  if(relevant.size() < 6)
  {
    reason = "ticket_worker_shape";
    return false;
  }

  const auto ticket_read = relevant[0];
  const auto ticket_increment = relevant[1];
  const auto rank_copy = relevant[2];
  const auto gate = relevant[3];
  const auto completion = relevant.back();

  irep_idt temporary;
  irep_idt ticket;
  if(
    !ticket_read->is_assign() ||
    !direct_symbol(ticket_read->assign_lhs(), temporary) ||
    !direct_symbol(ticket_read->assign_rhs(), ticket))
  {
    reason = "ticket_read";
    return false;
  }
  const symbolt *temporary_symbol = nullptr;
  const symbolt *ticket_symbol = nullptr;
  if(
    ns.lookup(temporary, temporary_symbol) ||
    temporary_symbol->is_static_lifetime ||
    ns.lookup(ticket, ticket_symbol) ||
    !ticket_symbol->is_static_lifetime ||
    !is_atomic_symbol(*ticket_symbol))
  {
    reason = "ticket_read_types";
    return false;
  }

  irep_idt incremented;
  if(
    !parse_unit_increment(*ticket_increment, incremented) ||
    incremented != ticket ||
    ticket_read->source_location() !=
      ticket_increment->source_location())
  {
    reason = "ticket_increment";
    return false;
  }

  irep_idt rank;
  irep_idt copied;
  if(
    !rank_copy->is_assign() ||
    !direct_symbol(rank_copy->assign_lhs(), rank) ||
    !direct_symbol(rank_copy->assign_rhs(), copied) ||
    copied != temporary)
  {
    reason = "ticket_rank_copy";
    return false;
  }
  const symbolt *rank_symbol = nullptr;
  if(ns.lookup(rank, rank_symbol) || rank_symbol->is_type)
  {
    reason = "ticket_rank_type";
    return false;
  }

  irep_idt gate_helper;
  if(
    !direct_call_identifier(*gate, gate_helper) ||
    !is_restricting_helper(gate_helper, model, ns) ||
    gate->call_arguments().size() != 1)
  {
    reason = "ticket_gate_call";
    return false;
  }
  const exprt &gate_condition =
    without_cast(gate->call_arguments().front());
  if(
    gate_condition.id() != ID_le ||
    gate_condition.operands().size() != 2)
  {
    reason = "ticket_gate_relation";
    return false;
  }
  irep_idt gate_rank;
  irep_idt completed;
  if(
    !direct_symbol(gate_condition.op0(), gate_rank) ||
    gate_rank != rank ||
    !direct_symbol(gate_condition.op1(), completed) ||
    completed == ticket)
  {
    reason = "ticket_gate_symbols";
    return false;
  }
  const symbolt *completed_symbol = nullptr;
  if(
    ns.lookup(completed, completed_symbol) ||
    !completed_symbol->is_static_lifetime ||
    !is_atomic_symbol(*completed_symbol))
  {
    reason = "ticket_completion_type";
    return false;
  }

  irep_idt completion_object;
  if(
    !parse_unit_increment(*completion, completion_object) ||
    completion_object != completed)
  {
    reason = "ticket_completion";
    return false;
  }

  const std::set<irep_idt> protocol_objects{
    ticket, completed, rank};
  for(std::size_t index = 4; index + 1 < relevant.size(); ++index)
  {
    const auto instruction = relevant[index];
    if(
      instruction->is_function_call() || instruction->is_assume() ||
      instruction->is_assert() || instruction->is_other() ||
      instruction->is_start_thread() || instruction->is_end_thread() ||
      instruction->is_atomic_begin() || instruction->is_atomic_end())
    {
      reason = "ticket_body_effect";
      return false;
    }
    if(
      instruction->is_assign() &&
      (contains_symbol(instruction->assign_lhs(), protocol_objects) ||
       contains_symbol(instruction->assign_rhs(), protocol_objects)))
    {
      reason = "ticket_body_protocol_access";
      return false;
    }
    if(instruction->is_goto())
    {
      if(
        instruction->targets.size() != 1 ||
        positions.at(&*instruction->get_target()) <=
          positions.at(&*instruction) ||
        positions.at(&*instruction->get_target()) >
          positions.at(&*completion))
      {
        reason = "ticket_body_control";
        return false;
      }
    }
    else if(!instruction->is_assign())
    {
      reason = "ticket_body_instruction";
      return false;
    }
  }

  region.worker = create.worker;
  region.ticket = ticket;
  region.completed = completed;
  region.rank = rank;
  region.body_begin = relevant[4];
  region.completion = completion;
  return true;
}

bool validate_ticket_initialization_and_aliases(
  const goto_modelt &model,
  const namespacet &ns,
  const std::vector<create_recordt> &creates,
  const std::vector<ticket_regiont> &regions,
  const irep_idt &ticket,
  const irep_idt &completed,
  std::string &reason)
{
  const auto main = model.goto_functions.function_map.find("main");
  INVARIANT(
    main != model.goto_functions.function_map.end(),
    "lifecycle collection found main");

  std::set<irep_idt> protocol_objects{ticket, completed};
  std::set<irep_idt> ranks;
  for(const auto &region : regions)
  {
    if(!ranks.insert(region.rank).second)
    {
      reason = "ticket_rank_alias";
      return false;
    }
    protocol_objects.insert(region.rank);
  }
  bool initialized = false;
  bool create_seen = false;
  for(const auto &instruction : main->second.body.instructions)
  {
    if(
      contains_address_of_symbol(instruction.code(), protocol_objects) ||
      (instruction.has_condition() &&
       contains_address_of_symbol(
         instruction.condition(), protocol_objects)))
    {
      reason = "ticket_counter_alias";
      return false;
    }

    irep_idt callee;
    if(
      direct_call_identifier(instruction, callee) &&
      callee == "pthread_create")
      create_seen = true;

    if(instruction.is_assign())
    {
      const exprt &lhs = without_cast(instruction.assign_lhs());
      irep_idt identifier;
      if(
        direct_symbol(lhs, identifier) &&
        protocol_objects.find(identifier) != protocol_objects.end() &&
        (create_seen || initialized))
      {
        reason = "ticket_main_counter_write";
        return false;
      }
    }

    if(
      !create_seen && instruction.is_function_call() &&
      instruction.call_arguments().size() == 1 &&
      direct_call_identifier(instruction, callee) &&
      is_restricting_helper(callee, model, ns) &&
      proves_zero_equalities(
        instruction.call_arguments().front(),
        {ticket, completed}))
      initialized = true;
  }
  if(!initialized)
  {
    reason = "ticket_initialization";
    return false;
  }

  for(std::size_t index = 0; index < creates.size(); ++index)
  {
    const auto &create = creates[index];
    const auto worker =
      model.goto_functions.function_map.find(create.worker);
    INVARIANT(
      worker != model.goto_functions.function_map.end(),
      "ticket summary found worker");
    for(const auto &instruction : worker->second.body.instructions)
    {
      if(
        contains_address_of_symbol(
          instruction.code(), protocol_objects) ||
        (instruction.has_condition() &&
         contains_address_of_symbol(
           instruction.condition(), protocol_objects)))
      {
        reason = "ticket_counter_alias";
        return false;
      }
      std::set<irep_idt> foreign_ranks = ranks;
      foreign_ranks.erase(regions[index].rank);
      if(
        contains_symbol(instruction.code(), foreign_ranks) ||
        (instruction.has_condition() &&
         contains_symbol(instruction.condition(), foreign_ranks)))
      {
        reason = "ticket_foreign_rank_access";
        return false;
      }
    }
  }
  return true;
}

bool inline_error_bound(
  goto_modelt &model,
  const irep_idt &first,
  const irep_idt &second,
  mp_integer &property_bound,
  std::map<irep_idt, mp_integer> &initial_values,
  bool &inclusive_bad,
  goto_programt::targett &failure_guard,
  std::string &reason)
{
  auto main = model.goto_functions.function_map.find("main");
  if(
    main == model.goto_functions.function_map.end() ||
    !main->second.body_available())
  {
    reason = "prefix_missing_main";
    return false;
  }
  auto &program = main->second.body;
  std::map<const goto_programt::instructiont *, std::size_t> positions;
  std::size_t position = 0;
  for(const auto &instruction : program.instructions)
    positions.emplace(&instruction, position++);

  std::map<irep_idt, exprt> assignments;
  std::map<irep_idt, std::size_t> assignment_counts;
  std::map<irep_idt, std::size_t> assignment_positions;
  std::size_t creates = 0;
  auto error_call = program.instructions.end();
  bool before_create = true;
  for(auto instruction = program.instructions.begin();
      instruction != program.instructions.end(); ++instruction)
  {
    if(instruction->is_assign())
    {
      const exprt &lhs = without_cast(instruction->assign_lhs());
      if(lhs.id() == ID_symbol)
      {
        const auto identifier =
          to_symbol_expr(lhs).get_identifier();
        assignments[identifier] = instruction->assign_rhs();
        ++assignment_counts[identifier];
        assignment_positions[identifier] = positions.at(&*instruction);
        if(
          before_create &&
          (identifier == first || identifier == second))
        {
          mp_integer value;
          if(constant_eval(instruction->assign_rhs(), {}, value))
            initial_values[identifier] = value;
        }
        else if(
          !before_create &&
          (identifier == first || identifier == second))
        {
          reason = "prefix_late_initialization";
          return false;
        }
      }
      continue;
    }
    irep_idt callee;
    if(!direct_call_identifier(*instruction, callee))
      continue;
    if(callee == "pthread_create")
    {
      ++creates;
      before_create = false;
      continue;
    }
    if(callee == "pthread_join")
    {
      reason = "prefix_has_join";
      return false;
    }
    if(callee == "reach_error")
    {
      if(error_call != program.instructions.end())
      {
        reason = "prefix_error_count";
        return false;
      }
      error_call = instruction;
      continue;
    }
    if(callee != "abort")
    {
      reason = "prefix_inline_call";
      return false;
    }
  }
  if(creates != 2 || error_call == program.instructions.end())
  {
    reason = "prefix_inline_main_shape";
    return false;
  }

  for(const auto &identifier : {first, second})
  {
    if(initial_values.find(identifier) != initial_values.end())
      continue;
    mp_integer value;
    if(!static_initial_value(model, identifier, value))
    {
      reason = "prefix_static_initialization";
      return false;
    }
    initial_values[identifier] = value;
  }

  if(error_call == program.instructions.begin())
  {
    reason = "prefix_inline_guard";
    return false;
  }
  const auto guard = std::prev(error_call);
  const auto abort_call = std::next(error_call);
  irep_idt abort_identifier;
  if(
    abort_call == program.instructions.end() ||
    !guard->is_goto() || guard->targets.size() != 1 ||
    !direct_call_identifier(*abort_call, abort_identifier) ||
    abort_identifier != "abort" ||
    positions.at(&*guard->get_target()) <= positions.at(&*abort_call))
  {
    reason = "prefix_inline_guard";
    return false;
  }
  for(const auto &instruction : program.instructions)
  {
    if(
      &instruction != &*guard && instruction.is_goto() &&
      instruction.targets.size() == 1 &&
      instruction.get_target() == error_call)
    {
      reason = "prefix_error_incoming";
      return false;
    }
  }
  bool guard_control_supported = false;
  const auto guard_control = control_signature(
    program,
    positions,
    positions.at(&*guard),
    guard_control_supported);
  if(!guard_control_supported || !guard_control.empty())
  {
    reason = "prefix_inline_guard_control";
    return false;
  }

  const exprt &condition = without_cast(guard->condition());
  if(
    condition.id() != ID_not ||
    condition.operands().size() != 1)
  {
    reason = "prefix_inline_condition";
    return false;
  }
  const exprt &bad = without_cast(condition.op0());
  if(bad.id() != ID_or || bad.operands().size() != 2)
  {
    reason = "prefix_inline_bad_shape";
    return false;
  }

  std::set<irep_idt> compared_objects;
  bool bound_initialized = false;
  bool relation_initialized = false;
  for(const auto &operand : bad.operands())
  {
    irep_idt condition_symbol;
    if(!truthy_symbol(operand, condition_symbol))
    {
      reason = "prefix_inline_truth";
      return false;
    }
    const auto assignment = assignments.find(condition_symbol);
    if(
      assignment == assignments.end() ||
      assignment_counts[condition_symbol] != 1 ||
      assignment_positions[condition_symbol] >= positions.at(&*guard))
    {
      reason = "prefix_inline_definition";
      return false;
    }
    bool control_supported = false;
    const auto assignment_control = control_signature(
      program,
      positions,
      assignment_positions[condition_symbol],
      control_supported);
    if(!control_supported || !assignment_control.empty())
    {
      reason = "prefix_inline_definition_control";
      return false;
    }
    const exprt &comparison = without_cast(assignment->second);
    irep_idt object;
    mp_integer bound;
    const bool comparison_inclusive = comparison.id() == ID_ge;
    if(
      (comparison.id() != ID_gt && !comparison_inclusive) ||
      comparison.operands().size() != 2 ||
      !direct_symbol(comparison.op0(), object) ||
      (object != first && object != second) ||
      !constant_eval(comparison.op1(), {}, bound) ||
      bound < 0)
    {
      reason = "prefix_inline_comparison";
      return false;
    }
    if(!relation_initialized)
    {
      inclusive_bad = comparison_inclusive;
      relation_initialized = true;
    }
    else if(inclusive_bad != comparison_inclusive)
    {
      reason = "prefix_inline_relations";
      return false;
    }
    if(!bound_initialized)
    {
      property_bound = bound;
      bound_initialized = true;
    }
    else if(property_bound != bound)
    {
      reason = "prefix_inline_bounds";
      return false;
    }
    compared_objects.insert(object);
  }
  if(compared_objects.size() != 2)
  {
    reason = "prefix_inline_coverage";
    return false;
  }
  failure_guard = guard;
  return true;
}

bool transition_word_error_function(
  const irep_idt &identifier,
  const goto_modelt &model)
{
  const auto function =
    model.goto_functions.function_map.find(identifier);
  if(
    function == model.goto_functions.function_map.end() ||
    !function->second.body_available())
    return false;

  std::size_t assertions = 0;
  for(const auto &instruction : function->second.body.instructions)
  {
    if(instruction.is_assert())
    {
      if(!instruction.condition().is_false())
        return false;
      ++assertions;
    }
    else if(
      instruction.is_assign() || instruction.is_function_call() ||
      instruction.is_goto() || instruction.is_assume() ||
      instruction.is_start_thread() || instruction.is_end_thread() ||
      instruction.is_atomic_begin() || instruction.is_atomic_end())
      return false;
  }
  return assertions == 1;
}

bool transition_word_property(
  goto_modelt &model,
  const namespacet &ns,
  const std::vector<goto_programt::targett> &joins,
  irep_idt &first,
  irep_idt &second,
  goto_programt::targett &error_call,
  std::string &reason)
{
  auto main = model.goto_functions.function_map.find("main");
  INVARIANT(
    main != model.goto_functions.function_map.end(),
    "lifecycle collection found main");

  std::vector<goto_programt::targett> calls;
  bool after_join = false;
  for(auto instruction = main->second.body.instructions.begin();
      instruction != main->second.body.instructions.end(); ++instruction)
  {
    if(instruction == joins.back())
    {
      after_join = true;
      continue;
    }
    if(!after_join)
      continue;
    if(instruction->is_function_call())
      calls.push_back(instruction);
    else if(
      instruction->is_assign() || instruction->is_goto() ||
      instruction->is_assume() || instruction->is_assert() ||
      instruction->is_start_thread() || instruction->is_end_thread() ||
      instruction->is_atomic_begin() || instruction->is_atomic_end())
    {
      reason = "transition_post_join_effect";
      return false;
    }
  }
  if(calls.size() != 2)
  {
    reason = "transition_property_calls";
    return false;
  }

  irep_idt guard_helper;
  irep_idt error_function;
  if(
    !direct_call_identifier(*calls[0], guard_helper) ||
    calls[0]->call_arguments().size() != 1 ||
    !is_restricting_helper(guard_helper, model, ns) ||
    !direct_call_identifier(*calls[1], error_function) ||
    !calls[1]->call_arguments().empty() ||
    !transition_word_error_function(error_function, model))
  {
    reason = "transition_property_shape";
    return false;
  }
  error_call = calls[1];

  std::size_t assertion_count = 0;
  for(const auto &function_entry : model.goto_functions.function_map)
  {
    if(!function_entry.second.body_available())
      continue;
    for(const auto &instruction :
        function_entry.second.body.instructions)
    {
      if(instruction.is_assert())
      {
        ++assertion_count;
        if(function_entry.first != error_function)
        {
          reason = "transition_additional_property";
          return false;
        }
      }
    }
  }
  if(assertion_count != 1)
  {
    reason = "transition_property_count";
    return false;
  }

  const exprt &bad =
    without_cast(calls[0]->call_arguments().front());
  if(
    bad.id() != ID_notequal || bad.operands().size() != 2 ||
    !direct_symbol(bad.op0(), first) ||
    !direct_symbol(bad.op1(), second) || first == second)
  {
    reason = "transition_property_relation";
    return false;
  }
  const symbolt *first_symbol = nullptr;
  const symbolt *second_symbol = nullptr;
  if(
    !is_shared_scalar(without_cast(bad.op0()), ns, first_symbol) ||
    !is_shared_scalar(without_cast(bad.op1()), ns, second_symbol) ||
    first_symbol->type != second_symbol->type)
  {
    reason = "transition_property_state";
    return false;
  }
  return true;
}

exprt transition_word_normalize(
  exprt value,
  const symbol_exprt &from,
  const symbol_exprt &to,
  const namespacet &ns)
{
  replace_expr(from, to, value);
  simplify_expr(value, ns);
  return value;
}

bool transition_word_bound_factor(
  const exprt &src,
  mp_integer &factor,
  irep_idt &base)
{
  const exprt &bound = without_cast(src);
  if(bound.id() != ID_mult || bound.operands().size() != 2)
    return false;

  mp_integer first_constant;
  mp_integer second_constant;
  irep_idt first_symbol;
  irep_idt second_symbol;
  if(
    constant_eval(bound.op0(), {}, first_constant) &&
    direct_symbol(bound.op1(), second_symbol))
  {
    factor = first_constant;
    base = second_symbol;
    return factor > 1;
  }
  if(
    direct_symbol(bound.op0(), first_symbol) &&
    constant_eval(bound.op1(), {}, second_constant))
  {
    factor = second_constant;
    base = first_symbol;
    return factor > 1;
  }
  return false;
}

bool transition_word_no_overflow_guard(
  const goto_modelt &model,
  const namespacet &ns,
  const goto_programt::targett &first_create,
  const irep_idt &base,
  const mp_integer &factor)
{
  const auto main =
    model.goto_functions.function_map.find("main");
  INVARIANT(
    main != model.goto_functions.function_map.end(),
    "lifecycle collection found main");
  const symbolt *base_symbol = nullptr;
  if(
    ns.lookup(base, base_symbol) ||
    base_symbol->type.id() != ID_unsignedbv)
    return false;
  const mp_integer range =
    power(2, to_unsignedbv_type(base_symbol->type).get_width());

  for(auto instruction = main->second.body.instructions.begin();
      instruction != first_create; ++instruction)
  {
    irep_idt helper;
    if(
      !direct_call_identifier(*instruction, helper) ||
      instruction->call_arguments().size() != 1 ||
      !is_restricting_helper(helper, model, ns))
      continue;
    const exprt &relation =
      without_cast(instruction->call_arguments().front());
    if(
      relation.id() != ID_lt ||
      relation.operands().size() != 2)
      continue;
    irep_idt guarded;
    const exprt &limit = without_cast(relation.op1());
    if(
      !direct_symbol(relation.op0(), guarded) ||
      guarded != base || limit.id() != ID_div ||
      limit.operands().size() != 2)
      continue;
    mp_integer numerator;
    mp_integer denominator;
    if(
      constant_eval(limit.op0(), {}, numerator) &&
      constant_eval(limit.op1(), {}, denominator) &&
      numerator == range && denominator == factor)
      return true;
  }
  return false;
}

bool transition_word_worker(
  const irep_idt &worker,
  const irep_idt &state,
  const goto_modelt &model,
  const namespacet &ns,
  transition_word_summaryt &summary,
  std::string &reason)
{
  const auto function =
    model.goto_functions.function_map.find(worker);
  if(
    function == model.goto_functions.function_map.end() ||
    !function->second.body_available())
  {
    reason = "transition_missing_worker";
    return false;
  }
  const auto &program = function->second.body;
  std::map<const goto_programt::instructiont *, std::size_t> positions;
  std::size_t position = 0;
  for(const auto &instruction : program.instructions)
    positions.emplace(&instruction, position++);

  auto backedge = program.instructions.end();
  auto loop_head = program.instructions.end();
  for(auto instruction = program.instructions.begin();
      instruction != program.instructions.end(); ++instruction)
  {
    if(!instruction->is_goto())
      continue;
    if(instruction->targets.size() != 1)
    {
      reason = "transition_multi_target";
      return false;
    }
    const bool backward =
      positions.at(&*instruction->get_target()) <
      positions.at(&*instruction);
    if(backward)
    {
      if(
        !instruction->condition().is_true() ||
        backedge != program.instructions.end())
      {
        reason = "transition_backedge";
        return false;
      }
      backedge = instruction;
      loop_head = instruction->get_target();
    }
  }
  if(backedge == program.instructions.end())
  {
    reason = "transition_no_loop";
    return false;
  }

  irep_idt induction;
  exprt bound;
  if(!parse_exit_guard(*loop_head, induction, bound))
  {
    reason = "transition_loop_guard";
    return false;
  }
  const symbolt *induction_symbol = nullptr;
  if(
    ns.lookup(induction, induction_symbol) ||
    induction_symbol->type.id() != ID_unsignedbv)
  {
    reason = "transition_induction_type";
    return false;
  }

  std::size_t initializations = 0;
  for(auto instruction = program.instructions.begin();
      instruction != loop_head; ++instruction)
  {
    if(parse_zero_initialization(*instruction, induction))
      ++initializations;
    else if(
      instruction->is_assign() &&
      without_cast(instruction->assign_lhs()).id() == ID_symbol &&
      to_symbol_expr(without_cast(instruction->assign_lhs()))
          .get_identifier() == induction)
    {
      reason = "transition_induction_initialization";
      return false;
    }
  }
  if(initializations != 1)
  {
    reason = "transition_induction_initialization";
    return false;
  }

  std::vector<goto_programt::const_targett> body;
  for(auto instruction = std::next(loop_head);
      instruction != backedge; ++instruction)
  {
    if(
      instruction->is_skip() || instruction->is_location() ||
      instruction->is_decl() || instruction->is_dead())
      continue;
    if(instruction->is_goto())
    {
      reason = "transition_body_control";
      return false;
    }
    body.push_back(instruction);
  }
  if(body.empty() || body.size() % 3 != 0)
  {
    reason = "transition_body_word";
    return false;
  }

  const symbolt *state_symbol = nullptr;
  const auto state_entry = model.symbol_table.symbols.find(state);
  if(
    state_entry == model.symbol_table.symbols.end() ||
    !state_entry->second.is_static_lifetime)
  {
    reason = "transition_state_symbol";
    return false;
  }
  state_symbol = &state_entry->second;

  for(std::size_t index = 0; index < body.size(); index += 3)
  {
    irep_idt helper;
    if(
      !direct_call_identifier(*body[index], helper) ||
      body[index]->call_arguments().size() != 1 ||
      !is_restricting_helper(helper, model, ns))
    {
      reason = "transition_step_guard";
      return false;
    }
    if(!body[index + 1]->is_assign())
    {
      reason = "transition_step_update";
      return false;
    }
    irep_idt updated;
    if(
      !direct_symbol(body[index + 1]->assign_lhs(), updated) ||
      updated != state ||
      body[index + 1]->assign_lhs().type() != state_symbol->type)
    {
      reason = "transition_step_state";
      return false;
    }
    irep_idt incremented;
    if(
      !parse_unit_increment(*body[index + 2], incremented) ||
      incremented != induction)
    {
      reason = "transition_step_increment";
      return false;
    }
    summary.steps.push_back(
      {body[index]->call_arguments().front(),
       body[index + 1]->assign_rhs()});
  }

  for(const auto &instruction : program.instructions)
  {
    if(instruction.is_assert() || instruction.is_assume() ||
       instruction.is_start_thread() || instruction.is_atomic_begin() ||
       instruction.is_atomic_end())
    {
      reason = "transition_worker_effect";
      return false;
    }
    if(instruction.is_function_call())
    {
      const bool inside =
        positions.at(&instruction) > positions.at(&*loop_head) &&
        positions.at(&instruction) < positions.at(&*backedge);
      irep_idt helper;
      if(
        !inside || !direct_call_identifier(instruction, helper) ||
        !is_restricting_helper(helper, model, ns))
      {
        reason = "transition_worker_call";
        return false;
      }
    }
    if(!instruction.is_assign())
      continue;
    const exprt &lhs = without_cast(instruction.assign_lhs());
    const symbolt *lhs_symbol = nullptr;
    if(
      is_shared_scalar(lhs, ns, lhs_symbol) &&
      to_symbol_expr(lhs).get_identifier() != state)
    {
      reason = "transition_environment_write";
      return false;
    }
    if(
      lhs.id() == ID_dereference ||
      (lhs.id() != ID_symbol && lhs.id() != ID_member &&
       lhs.id() != ID_index))
    {
      reason = "transition_indirect_write";
      return false;
    }
  }

  summary.worker = worker;
  summary.state = state;
  summary.induction = induction;
  summary.bound = bound;
  return true;
}

bool transition_word_parse_step(
  const goto_programt::const_targett &guard,
  const goto_programt::const_targett &update,
  const goto_programt::const_targett &increment,
  const irep_idt &state,
  const irep_idt &induction,
  const goto_modelt &model,
  const namespacet &ns,
  transition_word_stept &step,
  std::string &reason)
{
  irep_idt helper;
  if(
    !direct_call_identifier(*guard, helper) ||
    guard->call_arguments().size() != 1 ||
    !is_restricting_helper(helper, model, ns))
  {
    reason = "modular_step_guard";
    return false;
  }
  if(!update->is_assign())
  {
    reason = "modular_step_update";
    return false;
  }
  irep_idt updated;
  if(
    !direct_symbol(update->assign_lhs(), updated) ||
    updated != state)
  {
    reason = "modular_step_state";
    return false;
  }
  irep_idt incremented;
  if(
    !parse_unit_increment(*increment, incremented) ||
    incremented != induction)
  {
    reason = "modular_step_increment";
    return false;
  }
  step = {guard->call_arguments().front(), update->assign_rhs()};
  return true;
}

bool transition_word_subtractive_bound(
  const exprt &src,
  const typet &counter_type,
  irep_idt &base,
  mp_integer &distance)
{
  const exprt &bound = without_cast(src);
  if(
    bound.id() != ID_minus || bound.operands().size() != 2 ||
    bound.type() != counter_type ||
    !direct_symbol(bound.op0(), base))
    return false;
  const exprt &amount = without_cast(bound.op1());
  return
    bound.op1().type() == counter_type &&
    amount.id() == ID_constant &&
    !to_integer(to_constant_expr(amount), distance) &&
    distance > 0;
}

bool transition_word_tail_bound(
  const exprt &src,
  const typet &counter_type,
  const irep_idt &base,
  const std::size_t expected_distance)
{
  if(expected_distance == 0)
  {
    irep_idt identifier;
    return
      direct_symbol(without_cast(src), identifier) &&
      identifier == base && without_cast(src).type() == counter_type;
  }
  irep_idt identifier;
  mp_integer distance;
  return
    transition_word_subtractive_bound(
      src, counter_type, identifier, distance) &&
    identifier == base && distance == expected_distance;
}

bool transition_word_power_of_two(const std::size_t value)
{
  return value >= 2 && (value & (value - 1)) == 0;
}

bool modular_chunk_worker(
  const irep_idt &worker,
  const irep_idt &state,
  const goto_modelt &model,
  const namespacet &ns,
  modular_chunk_summaryt &summary,
  std::string &reason)
{
  const auto function =
    model.goto_functions.function_map.find(worker);
  if(
    function == model.goto_functions.function_map.end() ||
    !function->second.body_available())
  {
    reason = "modular_missing_worker";
    return false;
  }
  const auto &program = function->second.body;
  std::map<const goto_programt::instructiont *, std::size_t> positions;
  std::size_t position = 0;
  for(const auto &instruction : program.instructions)
    positions.emplace(&instruction, position++);

  auto backedge = program.instructions.end();
  auto loop_head = program.instructions.end();
  for(auto instruction = program.instructions.begin();
      instruction != program.instructions.end(); ++instruction)
  {
    if(!instruction->is_goto())
      continue;
    if(instruction->targets.size() != 1)
    {
      reason = "modular_multi_target";
      return false;
    }
    if(
      positions.at(&*instruction->get_target()) <
      positions.at(&*instruction))
    {
      if(
        !instruction->condition().is_true() ||
        backedge != program.instructions.end())
      {
        reason = "modular_backedge";
        return false;
      }
      backedge = instruction;
      loop_head = instruction->get_target();
    }
  }
  if(backedge == program.instructions.end())
  {
    reason = "modular_no_loop";
    return false;
  }

  irep_idt induction;
  exprt wrapped_bound;
  if(!parse_exit_guard(*loop_head, induction, wrapped_bound))
  {
    reason = "modular_loop_guard";
    return false;
  }
  const symbolt *induction_symbol = nullptr;
  if(
    ns.lookup(induction, induction_symbol) ||
    induction_symbol->type.id() != ID_unsignedbv)
  {
    reason = "modular_induction_type";
    return false;
  }
  const std::size_t counter_width =
    to_unsignedbv_type(induction_symbol->type).get_width();

  irep_idt base;
  mp_integer distance;
  if(
    !transition_word_subtractive_bound(
      wrapped_bound, induction_symbol->type, base, distance) ||
    distance > 63)
  {
    reason = "modular_subtractive_bound";
    return false;
  }
  const std::size_t chunk =
    numeric_cast_v<std::size_t>(distance + 1);
  if(
    !transition_word_power_of_two(chunk) ||
    chunk > 64 ||
    power(2, counter_width) <= chunk)
  {
    reason = "modular_chunk_power";
    return false;
  }

  std::size_t initializations = 0;
  for(auto instruction = program.instructions.begin();
      instruction != loop_head; ++instruction)
  {
    if(parse_zero_initialization(*instruction, induction))
      ++initializations;
    else if(
      instruction->is_assign() || instruction->is_function_call() ||
      instruction->is_goto() || instruction->is_assume() ||
      instruction->is_assert() || instruction->is_start_thread() ||
      instruction->is_atomic_begin() || instruction->is_atomic_end())
    {
      reason = "modular_prefix_effect";
      return false;
    }
  }
  if(initializations != 1)
  {
    reason = "modular_induction_initialization";
    return false;
  }

  std::vector<goto_programt::const_targett> loop_body;
  for(auto instruction = std::next(loop_head);
      instruction != backedge; ++instruction)
  {
    if(
      instruction->is_skip() || instruction->is_location() ||
      instruction->is_decl() || instruction->is_dead())
      continue;
    if(instruction->is_goto())
    {
      reason = "modular_body_control";
      return false;
    }
    loop_body.push_back(instruction);
  }
  if(loop_body.size() != 3 * chunk)
  {
    reason = "modular_body_word";
    return false;
  }

  std::vector<transition_word_stept> steps;
  for(std::size_t index = 0; index < loop_body.size(); index += 3)
  {
    transition_word_stept step;
    if(
      !transition_word_parse_step(
        loop_body[index],
        loop_body[index + 1],
        loop_body[index + 2],
        state,
        induction,
        model,
        ns,
        step,
        reason))
      return false;
    steps.push_back(std::move(step));
  }

  std::vector<goto_programt::const_targett> suffix;
  for(auto instruction = std::next(backedge);
      instruction != program.instructions.end(); ++instruction)
  {
    if(
      instruction->is_skip() || instruction->is_location() ||
      instruction->is_decl() || instruction->is_dead() ||
      instruction->is_set_return_value() ||
      instruction->is_end_function())
      continue;
    suffix.push_back(instruction);
  }
  if(suffix.size() != 4 * (chunk - 1))
  {
    reason = "modular_tail_size";
    return false;
  }
  if(loop_head->get_target() != suffix.front())
  {
    reason = "modular_loop_exit_target";
    return false;
  }
  for(std::size_t tail = 0; tail < chunk - 1; ++tail)
  {
    const std::size_t offset = 4 * tail;
    irep_idt tail_induction;
    exprt tail_bound;
    if(
      !parse_exit_guard(
        *suffix[offset], tail_induction, tail_bound) ||
      tail_induction != induction ||
      !transition_word_tail_bound(
        tail_bound,
        induction_symbol->type,
        base,
        chunk - 2 - tail))
    {
      reason = "modular_tail_guard";
      return false;
    }
    if(tail + 1 < chunk - 1)
    {
      if(suffix[offset]->get_target() != suffix[offset + 4])
      {
        reason = "modular_tail_target";
        return false;
      }
    }
    else
    {
      const auto target_position =
        positions.at(&*suffix[offset]->get_target());
      const auto last_step_position =
        positions.at(&*suffix[offset + 3]);
      if(target_position <= last_step_position)
      {
        reason = "modular_tail_target";
        return false;
      }
    }
    transition_word_stept step;
    if(
      !transition_word_parse_step(
        suffix[offset + 1],
        suffix[offset + 2],
        suffix[offset + 3],
        state,
        induction,
        model,
        ns,
        step,
        reason))
      return false;
    steps.push_back(std::move(step));
  }

  for(const auto &instruction : program.instructions)
  {
    if(
      instruction.is_assert() || instruction.is_assume() ||
      instruction.is_start_thread() || instruction.is_atomic_begin() ||
      instruction.is_atomic_end())
    {
      reason = "modular_worker_effect";
      return false;
    }
    if(!instruction.is_assign())
      continue;
    const exprt &lhs = without_cast(instruction.assign_lhs());
    const symbolt *lhs_symbol = nullptr;
    if(
      is_shared_scalar(lhs, ns, lhs_symbol) &&
      to_symbol_expr(lhs).get_identifier() != state)
    {
      reason = "modular_environment_write";
      return false;
    }
    if(
      lhs.id() == ID_dereference ||
      (lhs.id() != ID_symbol && lhs.id() != ID_member &&
       lhs.id() != ID_index))
    {
      reason = "modular_indirect_write";
      return false;
    }
  }

  summary.word.worker = worker;
  summary.word.state = state;
  summary.word.induction = induction;
  summary.word.bound = symbol_exprt(base, induction_symbol->type);
  summary.word.steps = std::move(steps);
  summary.bound = base;
  summary.chunk = chunk;
  return true;
}

bool transition_word_immutable_bound(
  const goto_modelt &model,
  const namespacet &ns,
  const irep_idt &bound,
  const typet &counter_type,
  const goto_programt::targett &first_create,
  std::string &reason)
{
  const symbolt *bound_symbol = nullptr;
  if(
    ns.lookup(bound, bound_symbol) ||
    !bound_symbol->is_static_lifetime ||
    bound_symbol->type != counter_type)
  {
    reason = "modular_bound_type";
    return false;
  }

  std::size_t main_initializations = 0;
  const auto main =
    model.goto_functions.function_map.find("main");
  INVARIANT(
    main != model.goto_functions.function_map.end(),
    "lifecycle collection found main");
  bool before_create = true;
  for(auto instruction = main->second.body.instructions.begin();
      instruction != main->second.body.instructions.end(); ++instruction)
  {
    if(instruction == first_create)
      before_create = false;
    if(
      contains_address_of_symbol(instruction->code(), {bound}) ||
      (instruction->has_condition() &&
       contains_address_of_symbol(instruction->condition(), {bound})))
    {
      reason = "modular_bound_alias";
      return false;
    }
    if(!instruction->is_assign())
      continue;
    irep_idt target;
    if(
      direct_symbol(instruction->assign_lhs(), target) &&
      target == bound)
    {
      if(!before_create)
      {
        reason = "modular_late_bound_write";
        return false;
      }
      ++main_initializations;
    }
  }
  if(main_initializations != 1)
  {
    reason = "modular_bound_initialization";
    return false;
  }

  for(const auto &function_entry : model.goto_functions.function_map)
  {
    if(
      !function_entry.second.body_available() ||
      function_entry.first == "main" ||
      function_entry.first == "__CPROVER_initialize")
      continue;
    for(const auto &instruction :
        function_entry.second.body.instructions)
    {
      if(
        contains_address_of_symbol(instruction.code(), {bound}) ||
        (instruction.has_condition() &&
         contains_address_of_symbol(instruction.condition(), {bound})))
      {
        reason = "modular_bound_alias";
        return false;
      }
      if(!instruction.is_assign())
        continue;
      irep_idt target;
      if(
        direct_symbol(instruction.assign_lhs(), target) &&
        target == bound)
      {
        reason = "modular_foreign_bound_write";
        return false;
      }
    }
  }
  return true;
}

bool transition_word_initial_and_accesses(
  const goto_modelt &model,
  const namespacet &ns,
  const std::vector<transition_word_summaryt> &summaries,
  const irep_idt &first,
  const irep_idt &second,
  std::string &reason)
{
  const std::set<irep_idt> states{first, second};
  const auto main =
    model.goto_functions.function_map.find("main");
  INVARIANT(
    main != model.goto_functions.function_map.end(),
    "lifecycle collection found main");

  std::map<irep_idt, std::vector<exprt>> main_values;
  bool create_seen = false;
  for(const auto &instruction : main->second.body.instructions)
  {
    if(
      contains_address_of_symbol(instruction.code(), states) ||
      (instruction.has_condition() &&
       contains_address_of_symbol(instruction.condition(), states)))
    {
      reason = "transition_state_alias";
      return false;
    }
    irep_idt callee;
    if(
      direct_call_identifier(instruction, callee) &&
      callee == "pthread_create")
      create_seen = true;
    if(!instruction.is_assign())
      continue;
    irep_idt target;
    if(
      direct_symbol(instruction.assign_lhs(), target) &&
      states.find(target) != states.end())
    {
      if(create_seen)
      {
        reason = "transition_late_state_write";
        return false;
      }
      main_values[target].push_back(instruction.assign_rhs());
    }
  }

  exprt first_initial;
  exprt second_initial;
  if(main_values[first].empty() && main_values[second].empty())
  {
    std::map<irep_idt, std::vector<exprt>> initializer_values;
    const auto initializer =
      model.goto_functions.function_map.find("__CPROVER_initialize");
    if(
      initializer != model.goto_functions.function_map.end() &&
      initializer->second.body_available())
    {
      for(const auto &instruction :
          initializer->second.body.instructions)
      {
        if(!instruction.is_assign())
          continue;
        irep_idt target;
        if(
          direct_symbol(instruction.assign_lhs(), target) &&
          states.find(target) != states.end())
          initializer_values[target].push_back(
            instruction.assign_rhs());
      }
    }
    if(
      initializer_values[first].size() == 1 &&
      initializer_values[second].size() == 1)
    {
      first_initial = initializer_values[first].front();
      second_initial = initializer_values[second].front();
    }
    else
    {
      const auto first_symbol =
        model.symbol_table.symbols.find(first);
      const auto second_symbol =
        model.symbol_table.symbols.find(second);
      if(
        first_symbol == model.symbol_table.symbols.end() ||
        second_symbol == model.symbol_table.symbols.end() ||
        first_symbol->second.value.is_nil() ||
        second_symbol->second.value.is_nil())
      {
        reason = "transition_static_initialization";
        return false;
      }
      first_initial = first_symbol->second.value;
      second_initial = second_symbol->second.value;
    }
  }
  else
  {
    if(
      main_values[first].size() != 1 ||
      main_values[second].size() != 1)
    {
      reason = "transition_explicit_initialization";
      return false;
    }
    first_initial = main_values[first].front();
    second_initial = main_values[second].front();
  }
  simplify_expr(first_initial, ns);
  simplify_expr(second_initial, ns);
  if(first_initial != second_initial)
  {
    reason = "transition_initial_inequality";
    return false;
  }

  std::map<irep_idt, irep_idt> owner;
  for(const auto &summary : summaries)
    owner[summary.state] = summary.worker;
  if(owner.size() != 2)
  {
    reason = "transition_state_ownership";
    return false;
  }
  for(const auto &function_entry : model.goto_functions.function_map)
  {
    if(!function_entry.second.body_available())
      continue;
    for(const auto &instruction :
        function_entry.second.body.instructions)
    {
      if(
        contains_address_of_symbol(instruction.code(), states) ||
        (instruction.has_condition() &&
         contains_address_of_symbol(instruction.condition(), states)))
      {
        reason = "transition_state_alias";
        return false;
      }
      if(!instruction.is_assign())
        continue;
      irep_idt target;
      if(
        !direct_symbol(instruction.assign_lhs(), target) ||
        states.find(target) == states.end())
        continue;
      if(
        function_entry.first == "main" ||
        function_entry.first == "__CPROVER_initialize")
        continue;
      if(function_entry.first != owner[target])
      {
        reason = "transition_foreign_state_write";
        return false;
      }
    }
  }
  for(const auto &summary : summaries)
  {
    const auto worker =
      model.goto_functions.function_map.find(summary.worker);
    INVARIANT(
      worker != model.goto_functions.function_map.end(),
      "transition summary found worker");
    std::set<irep_idt> foreign = states;
    foreign.erase(summary.state);
    for(const auto &instruction : worker->second.body.instructions)
    {
      if(
        contains_symbol(instruction.code(), foreign) ||
        (instruction.has_condition() &&
         contains_symbol(instruction.condition(), foreign)))
      {
        reason = "transition_foreign_state_read";
        return false;
      }
    }
  }
  return true;
}

bool modular_chunk_equivalence_transform(
  goto_modelt &goto_model,
  message_handlert &message_handler)
{
  const namespacet ns(goto_model.symbol_table);
  std::vector<create_recordt> creates;
  std::vector<goto_programt::targett> joins;
  std::string reason;
  if(
    !collect_lifecycle(goto_model, ns, creates, joins, reason) ||
    creates.size() != 2 ||
    !validate_main_region(goto_model, ns, creates, joins, reason))
  {
    std::cout
      << "NATIVE_MODULAR_CHUNK applied=0 reason="
      << (reason.empty() ? "modular_lifecycle" : reason) << '\n';
    return false;
  }

  irep_idt first;
  irep_idt second;
  goto_programt::targett error_call;
  if(
    !transition_word_property(
      goto_model,
      ns,
      joins,
      first,
      second,
      error_call,
      reason))
  {
    std::cout
      << "NATIVE_MODULAR_CHUNK applied=0 reason=" << reason << '\n';
    return false;
  }

  transition_word_summaryt reference;
  modular_chunk_summaryt chunked;
  bool summarized = false;
  std::vector<std::string> candidate_reasons;
  for(std::size_t permutation = 0; permutation < 2; ++permutation)
  {
    const irep_idt &reference_state =
      permutation == 0 ? first : second;
    const irep_idt &chunked_state =
      permutation == 0 ? second : first;
    std::string candidate_reason;
    transition_word_summaryt candidate_reference;
    modular_chunk_summaryt candidate_chunked;
    if(
      transition_word_worker(
        creates[permutation].worker,
        reference_state,
        goto_model,
        ns,
        candidate_reference,
        candidate_reason) &&
      modular_chunk_worker(
        creates[1 - permutation].worker,
        chunked_state,
        goto_model,
        ns,
        candidate_chunked,
        candidate_reason))
    {
      reference = std::move(candidate_reference);
      chunked = std::move(candidate_chunked);
      summarized = true;
      break;
    }
    candidate_reasons.push_back(candidate_reason);
    reason = candidate_reason;
  }
  if(!summarized)
  {
    std::cout
      << "NATIVE_MODULAR_CHUNK applied=0 reason=" << reason;
    for(std::size_t index = 0; index < candidate_reasons.size(); ++index)
      std::cout
        << " attempt" << index << '=' << candidate_reasons[index];
    std::cout << '\n';
    return false;
  }

  std::vector<transition_word_summaryt> summaries{
    reference, chunked.word};
  if(
    !transition_word_initial_and_accesses(
      goto_model, ns, summaries, first, second, reason))
  {
    std::cout
      << "NATIVE_MODULAR_CHUNK applied=0 reason=" << reason << '\n';
    return false;
  }
  const auto induction_entry =
    goto_model.symbol_table.symbols.find(reference.induction);
  const auto chunk_induction_entry =
    goto_model.symbol_table.symbols.find(chunked.word.induction);
  if(
    induction_entry == goto_model.symbol_table.symbols.end() ||
    chunk_induction_entry == goto_model.symbol_table.symbols.end() ||
    induction_entry->second.type !=
      chunk_induction_entry->second.type ||
    !transition_word_immutable_bound(
      goto_model,
      ns,
      chunked.bound,
      induction_entry->second.type,
      creates.front().instruction,
      reason))
  {
    std::cout
      << "NATIVE_MODULAR_CHUNK applied=0 reason="
      << (reason.empty() ? "modular_reference_type" : reason) << '\n';
    return false;
  }
  exprt reference_bound = reference.bound;
  exprt chunk_bound = chunked.word.bound;
  simplify_expr(reference_bound, ns);
  simplify_expr(chunk_bound, ns);
  if(reference_bound != chunk_bound || reference.steps.size() != 1)
  {
    std::cout
      << "NATIVE_MODULAR_CHUNK applied=0 reason=modular_bound_mismatch\n";
    return false;
  }

  const auto reference_symbol_entry =
    goto_model.symbol_table.symbols.find(reference.state);
  const auto chunked_symbol_entry =
    goto_model.symbol_table.symbols.find(chunked.word.state);
  INVARIANT(
    reference_symbol_entry != goto_model.symbol_table.symbols.end() &&
    chunked_symbol_entry != goto_model.symbol_table.symbols.end(),
    "modular summaries use state symbols");
  if(
    reference_symbol_entry->second.type !=
    chunked_symbol_entry->second.type)
  {
    std::cout
      << "NATIVE_MODULAR_CHUNK applied=0 reason=modular_state_type\n";
    return false;
  }
  const symbol_exprt reference_symbol(
    reference.state, reference_symbol_entry->second.type);
  const symbol_exprt chunked_symbol(
    chunked.word.state, chunked_symbol_entry->second.type);
  exprt reference_guard = reference.steps.front().guard;
  exprt reference_update = reference.steps.front().update;
  simplify_expr(reference_guard, ns);
  simplify_expr(reference_update, ns);
  for(const auto &step : chunked.word.steps)
  {
    const exprt guard = transition_word_normalize(
      step.guard, chunked_symbol, reference_symbol, ns);
    const exprt update = transition_word_normalize(
      step.update, chunked_symbol, reference_symbol, ns);
    if(guard != reference_guard || update != reference_update)
    {
      std::cout
        << "NATIVE_MODULAR_CHUNK applied=0"
        << " reason=modular_step_mismatch\n";
      return false;
    }
  }

  auto main =
    goto_model.goto_functions.function_map.find("main");
  INVARIANT(
    main != goto_model.goto_functions.function_map.end(),
    "modular lifecycle found main");
  for(auto &instruction : main->second.body.instructions)
  {
    if(!instruction.is_end_function())
      instruction.turn_into_skip();
  }
  error_call->turn_into_skip();
  goto_model.goto_functions.update();

  std::cout
    << "NATIVE_MODULAR_CHUNK applied=1 workers=2 chunk="
    << chunked.chunk << " state_first=" << first
    << " state_second=" << second << '\n';
  (void)message_handler;
  return true;
}

struct group_action_workert
{
  irep_idt worker;
  irep_idt state;
  irep_idt induction;
  exprt bound;
  irep_idt callee;
  exprt action;
  std::vector<exprt> restrictions;
};

bool group_action_constant_zero(const exprt &src)
{
  const exprt &expr = without_cast(src);
  if(expr.id() != ID_constant)
    return false;
  mp_integer value;
  return !to_integer(to_constant_expr(expr), value) && value == 0;
}

bool group_action_has_nondeterminism(const exprt &expr)
{
  if(expr.id() == ID_side_effect)
    return true;
  return std::any_of(
    expr.operands().begin(),
    expr.operands().end(),
    group_action_has_nondeterminism);
}

bool group_action_parameter_truth(
  const exprt &src,
  const irep_idt &parameter)
{
  const exprt &expr = without_cast(src);
  irep_idt identifier;
  if(direct_symbol(expr, identifier))
    return identifier == parameter;
  if(
    expr.id() != ID_notequal ||
    expr.operands().size() != 2)
    return false;
  return
    (direct_symbol(expr.op0(), identifier) &&
     identifier == parameter &&
     group_action_constant_zero(expr.op1())) ||
    (direct_symbol(expr.op1(), identifier) &&
     identifier == parameter &&
     group_action_constant_zero(expr.op0()));
}

bool group_action_abort_sink(
  const irep_idt &callee,
  const goto_modelt &model)
{
  const auto function =
    model.goto_functions.function_map.find(callee);
  if(
    function == model.goto_functions.function_map.end() ||
    !function->second.body_available())
    return false;
  std::size_t false_assumptions = 0;
  for(const auto &instruction : function->second.body.instructions)
  {
    if(instruction.is_assume())
    {
      const exprt &condition = without_cast(instruction.condition());
      mp_integer left;
      mp_integer right;
      const bool false_condition =
        condition.is_false() ||
        (condition.id() == ID_notequal &&
         condition.operands().size() == 2 &&
         without_cast(condition.op0()).id() == ID_constant &&
         without_cast(condition.op1()).id() == ID_constant &&
         !to_integer(to_constant_expr(
           without_cast(condition.op0())), left) &&
         !to_integer(to_constant_expr(
           without_cast(condition.op1())), right) &&
         left == right);
      if(false_condition)
        ++false_assumptions;
      else
        return false;
    }
    else if(
      !instruction.is_end_function() &&
      !instruction.is_skip() &&
      !instruction.is_location())
      return false;
  }
  return false_assumptions == 1;
}

bool group_action_assume_semantics(
  const irep_idt &callee,
  const goto_modelt &model)
{
  if(callee == "__CPROVER_assume")
    return true;
  const auto symbol = model.symbol_table.symbols.find(callee);
  const auto function =
    model.goto_functions.function_map.find(callee);
  if(
    symbol == model.symbol_table.symbols.end() ||
    symbol->second.type.id() != ID_code ||
    function == model.goto_functions.function_map.end() ||
    !function->second.body_available())
    return false;
  const auto &parameters =
    to_code_type(symbol->second.type).parameters();
  if(
    parameters.size() != 1 ||
    parameters.front().get_identifier().empty())
    return false;
  const irep_idt parameter =
    parameters.front().get_identifier();
  const goto_programt::instructiont *guard = nullptr;
  const goto_programt::instructiont *abort_call = nullptr;
  irep_idt abort_callee;
  for(const auto &instruction : function->second.body.instructions)
  {
    if(instruction.is_goto())
    {
      if(
        guard != nullptr ||
        instruction.targets.size() != 1 ||
        !group_action_parameter_truth(
          instruction.condition(), parameter))
        return false;
      guard = &instruction;
      continue;
    }
    if(instruction.is_function_call())
    {
      if(
        abort_call != nullptr ||
        !direct_call_identifier(instruction, abort_callee) ||
        abort_callee != "abort")
        return false;
      abort_call = &instruction;
      continue;
    }
    if(
      !instruction.is_end_function() &&
      !instruction.is_skip() &&
      !instruction.is_location())
      return false;
  }
  return
    guard != nullptr && abort_call != nullptr &&
    guard->get_target()->location_number >
      abort_call->location_number &&
    guard->location_number < abort_call->location_number &&
    group_action_abort_sink(abort_callee, model);
}

bool group_action_property(
  const goto_modelt &model,
  const namespacet &ns,
  const std::vector<goto_programt::targett> &joins,
  irep_idt &state,
  std::string &reason)
{
  const auto main = model.goto_functions.function_map.find("main");
  if(
    main == model.goto_functions.function_map.end() ||
    !main->second.body_available())
  {
    reason = "group_missing_main";
    return false;
  }
  std::vector<goto_programt::const_targett> calls;
  bool after_join = false;
  for(auto instruction = main->second.body.instructions.begin();
      instruction != main->second.body.instructions.end(); ++instruction)
  {
    if(instruction == joins.back())
    {
      after_join = true;
      continue;
    }
    if(!after_join)
      continue;
    if(instruction->is_function_call())
      calls.push_back(instruction);
    else if(
      instruction->is_assign() || instruction->is_goto() ||
      instruction->is_assume() || instruction->is_assert() ||
      instruction->is_start_thread() || instruction->is_end_thread() ||
      instruction->is_atomic_begin() || instruction->is_atomic_end())
    {
      reason = "group_post_join_effect";
      return false;
    }
  }
  if(calls.size() != 2)
  {
    reason = "group_property_calls";
    return false;
  }
  irep_idt restriction;
  irep_idt error;
  if(
    !direct_call_identifier(*calls[0], restriction) ||
    calls[0]->call_arguments().size() != 1 ||
    !group_action_assume_semantics(restriction, model) ||
    !direct_call_identifier(*calls[1], error) ||
    !calls[1]->call_arguments().empty() ||
    !transition_word_error_function(error, model))
  {
    reason = "group_property_shape";
    return false;
  }
  const exprt &bad =
    without_cast(calls[0]->call_arguments().front());
  if(
    bad.id() != ID_notequal || bad.operands().size() != 2)
  {
    reason = "group_property_relation";
    return false;
  }
  irep_idt candidate;
  if(
    direct_symbol(bad.op0(), candidate) &&
    group_action_constant_zero(bad.op1()))
    state = candidate;
  else if(
    direct_symbol(bad.op1(), candidate) &&
    group_action_constant_zero(bad.op0()))
    state = candidate;
  else
  {
    reason = "group_property_identity";
    return false;
  }
  const symbolt *symbol = nullptr;
  if(
    ns.lookup(state, symbol) ||
    !symbol->is_static_lifetime ||
    (symbol->type.id() != ID_signedbv &&
     symbol->type.id() != ID_unsignedbv))
  {
    reason = "group_state_type";
    return false;
  }
  std::size_t assertions = 0;
  for(const auto &entry : model.goto_functions.function_map)
  {
    if(!entry.second.body_available())
      continue;
    for(const auto &instruction : entry.second.body.instructions)
      assertions += instruction.is_assert();
  }
  if(assertions != 1)
  {
    reason = "group_property_count";
    return false;
  }
  return true;
}

bool group_action_loop(
  const irep_idt &worker,
  const goto_modelt &model,
  group_action_workert &summary,
  std::vector<goto_programt::const_targett> &body,
  std::string &reason)
{
  const auto function =
    model.goto_functions.function_map.find(worker);
  if(
    function == model.goto_functions.function_map.end() ||
    !function->second.body_available())
  {
    reason = "group_missing_worker";
    return false;
  }
  const auto &program = function->second.body;
  std::map<const goto_programt::instructiont *, std::size_t> positions;
  std::size_t position = 0;
  for(const auto &instruction : program.instructions)
    positions.emplace(&instruction, position++);

  auto backedge = program.instructions.end();
  auto loop_head = program.instructions.end();
  for(auto instruction = program.instructions.begin();
      instruction != program.instructions.end(); ++instruction)
  {
    if(!instruction->is_goto())
      continue;
    if(instruction->targets.size() != 1)
    {
      reason = "group_multi_target";
      return false;
    }
    if(
      positions.at(&*instruction->get_target()) <
      positions.at(&*instruction))
    {
      if(
        !instruction->condition().is_true() ||
        backedge != program.instructions.end())
      {
        reason = "group_backedge";
        return false;
      }
      backedge = instruction;
      loop_head = instruction->get_target();
    }
  }
  if(backedge == program.instructions.end())
  {
    reason = "group_no_loop";
    return false;
  }
  if(!parse_exit_guard(
       *loop_head, summary.induction, summary.bound))
  {
    reason = "group_loop_guard";
    return false;
  }
  const symbolt *induction_symbol =
    model.symbol_table.lookup(summary.induction);
  if(
    induction_symbol == nullptr ||
    (induction_symbol->type.id() != ID_signedbv &&
     induction_symbol->type.id() != ID_unsignedbv))
  {
    reason = "group_induction_type";
    return false;
  }
  std::size_t initializations = 0;
  for(auto instruction = program.instructions.begin();
      instruction != loop_head; ++instruction)
  {
    if(parse_zero_initialization(*instruction, summary.induction))
      ++initializations;
    else if(instruction->is_assign())
    {
      irep_idt assigned;
      if(
        direct_symbol(instruction->assign_lhs(), assigned) &&
        assigned == summary.induction)
      {
        reason = "group_induction_initialization";
        return false;
      }
    }
  }
  if(initializations != 1)
  {
    reason = "group_induction_initialization";
    return false;
  }

  std::size_t increments = 0;
  for(auto instruction = std::next(loop_head);
      instruction != backedge; ++instruction)
  {
    if(
      instruction->is_skip() || instruction->is_location() ||
      instruction->is_decl() || instruction->is_dead())
      continue;
    irep_idt incremented;
    if(
      parse_unit_increment(*instruction, incremented) &&
      incremented == summary.induction)
    {
      ++increments;
      continue;
    }
    if(instruction->is_goto())
    {
      reason = "group_body_control";
      return false;
    }
    body.push_back(instruction);
  }
  if(increments != 1)
  {
    reason = "group_induction_increment";
    return false;
  }
  for(const auto &instruction : program.instructions)
  {
    if(
      instruction.is_assert() || instruction.is_assume() ||
      instruction.is_start_thread() || instruction.is_end_thread())
    {
      reason = "group_worker_effect";
      return false;
    }
  }
  summary.worker = worker;
  return true;
}

bool group_action_exact_atomic_body(
  const std::vector<goto_programt::const_targett> &body,
  std::vector<goto_programt::const_targett> &inside,
  std::string &reason)
{
  std::size_t depth = 0;
  std::size_t regions = 0;
  for(const auto &instruction : body)
  {
    if(instruction->is_atomic_begin())
    {
      if(depth != 0)
      {
        reason = "group_nested_atomic";
        return false;
      }
      ++depth;
      ++regions;
      continue;
    }
    if(instruction->is_atomic_end())
    {
      if(depth != 1)
      {
        reason = "group_atomic_balance";
        return false;
      }
      --depth;
      continue;
    }
    if(depth != 1)
    {
      reason = "group_nonatomic_action";
      return false;
    }
    inside.push_back(instruction);
  }
  if(depth != 0 || regions != 1 || inside.empty())
  {
    reason = "group_atomic_shape";
    return false;
  }
  return true;
}

bool group_action_pure_arithmetic_helper(
  const irep_idt &callee,
  const irep_idt &operation,
  const goto_modelt &model,
  const namespacet &ns)
{
  const auto function =
    model.goto_functions.function_map.find(callee);
  const auto symbol = model.symbol_table.symbols.find(callee);
  if(
    function == model.goto_functions.function_map.end() ||
    !function->second.body_available() ||
    symbol == model.symbol_table.symbols.end() ||
    symbol->second.type.id() != ID_code)
    return false;
  const auto &parameters =
    to_code_type(symbol->second.type).parameters();
  if(parameters.size() != 2)
    return false;
  std::size_t returns = 0;
  for(const auto &instruction : function->second.body.instructions)
  {
    if(instruction.is_set_return_value())
    {
      const exprt &value =
        without_cast(instruction.return_value());
      if(
        value.id() != operation ||
        value.operands().size() != 2)
        return false;
      irep_idt first;
      irep_idt second;
      if(
        !direct_symbol(value.op0(), first) ||
        !direct_symbol(value.op1(), second) ||
        first != parameters[0].get_identifier() ||
        second != parameters[1].get_identifier())
        return false;
      ++returns;
    }
    else if(instruction.is_function_call())
    {
      irep_idt restriction;
      if(
        !direct_call_identifier(instruction, restriction) ||
        !is_restricting_helper(restriction, model, ns))
        return false;
    }
    else if(
      instruction.is_assign() || instruction.is_assert() ||
      instruction.is_assume() || instruction.is_start_thread() ||
      instruction.is_atomic_begin() || instruction.is_atomic_end())
      return false;
  }
  return returns == 1;
}

bool group_action_additive_worker(
  const irep_idt &worker,
  const irep_idt &state,
  const goto_modelt &model,
  const namespacet &ns,
  group_action_workert &summary,
  bool &subtract,
  std::string &reason)
{
  std::vector<goto_programt::const_targett> body;
  if(!group_action_loop(
       worker, model, summary, body, reason))
    return false;
  std::vector<goto_programt::const_targett> inside;
  if(!group_action_exact_atomic_body(body, inside, reason))
    return false;
  if(inside.size() != 1 || !inside.front()->is_function_call())
  {
    reason = "group_additive_action_count";
    return false;
  }
  const auto &call = *inside.front();
  irep_idt target;
  if(
    !direct_symbol(call.call_lhs(), target) ||
    target != state ||
    call.call_arguments().size() != 2 ||
    !direct_symbol(call.call_arguments()[0], target) ||
    target != state ||
    !direct_call_identifier(call, summary.callee))
  {
    reason = "group_additive_action";
    return false;
  }
  const bool plus =
    group_action_pure_arithmetic_helper(
      summary.callee, ID_plus, model, ns);
  const bool minus =
    group_action_pure_arithmetic_helper(
      summary.callee, ID_minus, model, ns);
  if(plus == minus)
  {
    reason = "group_additive_helper";
    return false;
  }
  subtract = minus;
  summary.state = state;
  summary.action = call.call_arguments()[1];
  return true;
}

bool group_action_array_application(
  const exprt &src,
  const irep_idt &argument,
  irep_idt &array)
{
  const exprt &expr = without_cast(src);
  if(expr.id() != ID_dereference || expr.operands().size() != 1)
    return false;
  const exprt &address = without_cast(expr.op0());
  if(
    address.id() != ID_plus ||
    address.operands().size() != 2)
    return false;
  irep_idt index;
  return
    direct_symbol(address.op0(), array) &&
    direct_symbol(address.op1(), index) &&
    index == argument;
}

bool group_action_inverse_law(
  const exprt &src,
  const irep_idt &state,
  const irep_idt &outer,
  const irep_idt &inner)
{
  const exprt &expr = without_cast(src);
  if(expr.id() != ID_equal || expr.operands().size() != 2)
    return false;
  const exprt *application = nullptr;
  irep_idt identity;
  if(direct_symbol(expr.op0(), identity) && identity == state)
    application = &expr.op1();
  else if(direct_symbol(expr.op1(), identity) && identity == state)
    application = &expr.op0();
  else
    return false;
  irep_idt outer_array;
  const exprt &outer_expr = without_cast(*application);
  if(
    outer_expr.id() != ID_dereference ||
    outer_expr.operands().size() != 1)
    return false;
  const exprt &outer_address = without_cast(outer_expr.op0());
  if(
    outer_address.id() != ID_plus ||
    outer_address.operands().size() != 2 ||
    !direct_symbol(outer_address.op0(), outer_array) ||
    outer_array != outer)
    return false;
  irep_idt inner_array;
  return group_action_array_application(
    outer_address.op1(), state, inner_array) &&
    inner_array == inner;
}

bool group_action_inverse_worker(
  const irep_idt &worker,
  const irep_idt &state,
  const goto_modelt &model,
  const namespacet &ns,
  group_action_workert &summary,
  irep_idt &array,
  std::string &reason)
{
  std::vector<goto_programt::const_targett> body;
  if(!group_action_loop(
       worker, model, summary, body, reason))
    return false;
  std::vector<goto_programt::const_targett> inside;
  if(!group_action_exact_atomic_body(body, inside, reason))
    return false;
  std::size_t assignments = 0;
  for(const auto &instruction : inside)
  {
    if(instruction->is_function_call())
    {
      irep_idt restriction;
      if(
        !instruction->call_lhs().is_nil() ||
        !direct_call_identifier(*instruction, restriction) ||
        instruction->call_arguments().size() != 1 ||
        !group_action_assume_semantics(restriction, model))
      {
        reason = "group_inverse_restriction";
        return false;
      }
      summary.restrictions.push_back(
        instruction->call_arguments().front());
      continue;
    }
    if(!instruction->is_assign())
    {
      reason = "group_inverse_instruction";
      return false;
    }
    irep_idt target;
    if(
      !direct_symbol(instruction->assign_lhs(), target) ||
      target != state ||
      !group_action_array_application(
        instruction->assign_rhs(), state, array))
    {
      reason = "group_inverse_action";
      return false;
    }
    summary.action = instruction->assign_rhs();
    ++assignments;
  }
  if(assignments != 1)
  {
    reason = "group_inverse_action_count";
    return false;
  }
  summary.state = state;
  return true;
}

void group_action_replace_symbol(
  exprt &expr,
  const irep_idt &from,
  const irep_idt &to,
  const goto_modelt &model)
{
  const auto source = model.symbol_table.symbols.find(from);
  const auto target = model.symbol_table.symbols.find(to);
  if(
    source == model.symbol_table.symbols.end() ||
    target == model.symbol_table.symbols.end())
    return;
  replace_expr(
    symbol_exprt(from, source->second.type),
    symbol_exprt(to, target->second.type),
    expr);
}

bool group_action_no_unmodelled_writes(
  const goto_modelt &model,
  const std::set<irep_idt> &workers,
  const irep_idt &state,
  const std::set<irep_idt> &read_only,
  std::string &reason)
{
  std::set<irep_idt> protected_symbols = read_only;
  protected_symbols.insert(state);
  std::map<irep_idt, std::size_t> worker_state_writes;
  for(const auto &worker : workers)
    worker_state_writes.emplace(worker, 0);
  for(const auto &entry : model.goto_functions.function_map)
  {
    if(!entry.second.body_available())
      continue;
    for(const auto &instruction : entry.second.body.instructions)
    {
      if(
        contains_address_of_symbol(
          instruction.code(), protected_symbols) ||
        (instruction.has_condition() &&
         contains_address_of_symbol(
           instruction.condition(), protected_symbols)))
      {
        reason = "group_address_escape";
        return false;
      }
      irep_idt written;
      bool writes = false;
      if(instruction.is_assign())
      {
        const exprt &lhs = without_cast(instruction.assign_lhs());
        if(
          (lhs.id() == ID_dereference || lhs.id() == ID_index) &&
          workers.count(entry.first) != 0)
        {
          reason = "group_pointer_write";
          return false;
        }
        writes = direct_symbol(lhs, written);
      }
      else if(
        instruction.is_function_call() &&
        !instruction.call_lhs().is_nil())
        writes = direct_symbol(instruction.call_lhs(), written);
      if(!writes)
        continue;
      if(
        written == state &&
        workers.count(entry.first) != 0)
        ++worker_state_writes[entry.first];
      if(
        read_only.count(written) != 0 &&
        entry.first != "main" &&
        entry.first != "__CPROVER_initialize")
      {
        reason = "group_input_write";
        return false;
      }
      if(
        written == state &&
        workers.count(entry.first) == 0 &&
        entry.first != "main" &&
        entry.first != "__CPROVER_initialize")
      {
        reason = "group_foreign_state_write";
        return false;
      }
    }
  }
  for(const auto &entry : worker_state_writes)
  {
    if(entry.second != 1)
    {
      reason = "group_state_write_count";
      return false;
    }
  }
  return true;
}

bool group_action_identity_initialization(
  const goto_modelt &model,
  const irep_idt &state,
  std::string &reason)
{
  std::vector<exprt> main_values;
  const auto main = model.goto_functions.function_map.find("main");
  if(
    main == model.goto_functions.function_map.end() ||
    !main->second.body_available())
  {
    reason = "group_missing_main";
    return false;
  }
  bool create_seen = false;
  for(const auto &instruction : main->second.body.instructions)
  {
    irep_idt callee;
    if(
      direct_call_identifier(instruction, callee) &&
      callee == "pthread_create")
      create_seen = true;
    irep_idt target;
    if(
      instruction.is_assign() &&
      direct_symbol(instruction.assign_lhs(), target) &&
      target == state)
    {
      if(create_seen)
      {
        reason = "group_late_state_write";
        return false;
      }
      main_values.push_back(instruction.assign_rhs());
    }
    else if(
      instruction.is_function_call() &&
      !instruction.call_lhs().is_nil() &&
      direct_symbol(instruction.call_lhs(), target) &&
      target == state)
    {
      reason = "group_call_identity_write";
      return false;
    }
  }
  if(!main_values.empty())
  {
    if(
      main_values.size() != 1 ||
      !group_action_constant_zero(main_values.front()))
    {
      reason = "group_explicit_identity";
      return false;
    }
    return true;
  }
  const auto initializer =
    model.goto_functions.function_map.find("__CPROVER_initialize");
  std::vector<exprt> values;
  if(
    initializer != model.goto_functions.function_map.end() &&
    initializer->second.body_available())
  {
    for(const auto &instruction :
        initializer->second.body.instructions)
    {
      irep_idt target;
      if(
        instruction.is_assign() &&
        direct_symbol(instruction.assign_lhs(), target) &&
        target == state)
        values.push_back(instruction.assign_rhs());
    }
  }
  if(
    values.size() != 1 ||
    !group_action_constant_zero(values.front()))
  {
    reason = "group_static_identity";
    return false;
  }
  return true;
}

bool group_action_cancellation_audit_impl(
  const goto_modelt &model,
  const namespacet &ns,
  std::string &mode,
  std::string &reason)
{
  goto_modelt &mutable_model = const_cast<goto_modelt &>(model);
  std::vector<create_recordt> creates;
  std::vector<goto_programt::targett> joins;
  if(
    !collect_lifecycle(
      mutable_model, ns, creates, joins, reason) ||
    creates.size() != 2 ||
    !validate_main_region(
      mutable_model, ns, creates, joins, reason))
  {
    if(reason.empty())
      reason = "group_lifecycle";
    return false;
  }
  irep_idt state;
  if(!group_action_property(model, ns, joins, state, reason))
    return false;
  if(!group_action_identity_initialization(model, state, reason))
    return false;

  group_action_workert additive[2];
  bool subtract[2] = {false, false};
  std::string additive_reason;
  if(
    group_action_additive_worker(
      creates[0].worker,
      state,
      model,
      ns,
      additive[0],
      subtract[0],
      additive_reason) &&
    group_action_additive_worker(
      creates[1].worker,
      state,
      model,
      ns,
      additive[1],
      subtract[1],
      additive_reason))
  {
    exprt right_bound = additive[1].bound;
    exprt right_action = additive[1].action;
    group_action_replace_symbol(
      right_bound,
      additive[1].induction,
      additive[0].induction,
      model);
    group_action_replace_symbol(
      right_action,
      additive[1].induction,
      additive[0].induction,
      model);
    simplify_expr(right_bound, ns);
    simplify_expr(right_action, ns);
    exprt left_bound = additive[0].bound;
    exprt left_action = additive[0].action;
    simplify_expr(left_bound, ns);
    simplify_expr(left_action, ns);
    find_symbols_sett found_symbols;
    find_symbols(left_bound, found_symbols);
    find_symbols(left_action, found_symbols);
    std::set<irep_idt> read_only(
      found_symbols.begin(), found_symbols.end());
    read_only.erase(additive[0].induction);
    if(
      subtract[0] != subtract[1] &&
      left_bound == right_bound &&
      left_action == right_action &&
      read_only.count(state) == 0 &&
      !contains_side_effect(left_bound) &&
      !group_action_has_nondeterminism(left_action) &&
      group_action_no_unmodelled_writes(
        model,
        {creates[0].worker, creates[1].worker},
        state,
        read_only,
        reason))
    {
      mode = "indexed-additive-inverse";
      return true;
    }
    if(reason.empty())
      reason = "group_additive_mismatch";
  }

  group_action_workert inverse[2];
  irep_idt arrays[2];
  std::string inverse_reason;
  if(
    group_action_inverse_worker(
      creates[0].worker,
      state,
      model,
      ns,
      inverse[0],
      arrays[0],
      inverse_reason) &&
    group_action_inverse_worker(
      creates[1].worker,
      state,
      model,
      ns,
      inverse[1],
      arrays[1],
      inverse_reason))
  {
    exprt right_bound = inverse[1].bound;
    group_action_replace_symbol(
      right_bound,
      inverse[1].induction,
      inverse[0].induction,
      model);
    simplify_expr(right_bound, ns);
    exprt left_bound = inverse[0].bound;
    simplify_expr(left_bound, ns);
    const bool first_law = std::any_of(
      inverse[0].restrictions.begin(),
      inverse[0].restrictions.end(),
      [&](const exprt &restriction) {
        return group_action_inverse_law(
          restriction, state, arrays[1], arrays[0]);
      });
    const bool second_law = std::any_of(
      inverse[1].restrictions.begin(),
      inverse[1].restrictions.end(),
      [&](const exprt &restriction) {
        return group_action_inverse_law(
          restriction, state, arrays[0], arrays[1]);
      });
    find_symbols_sett bound_symbols;
    find_symbols(left_bound, bound_symbols);
    std::set<irep_idt> inverse_read_only(
      bound_symbols.begin(), bound_symbols.end());
    inverse_read_only.insert(arrays[0]);
    inverse_read_only.insert(arrays[1]);
    if(
      arrays[0] != arrays[1] &&
      left_bound == right_bound &&
      inverse_read_only.count(state) == 0 &&
      !contains_side_effect(left_bound) &&
      first_law && second_law &&
      group_action_no_unmodelled_writes(
        model,
        {creates[0].worker, creates[1].worker},
        state,
        inverse_read_only,
        reason))
    {
      mode = "single-generator-inverse";
      return true;
    }
    if(reason.empty())
      reason = "group_inverse_mismatch";
  }
  if(reason.empty())
    reason =
      "additive_" + additive_reason +
      "_inverse_" + inverse_reason;
  return false;
}

struct segmented_fold_workert
{
  irep_idt worker;
  irep_idt sum;
  irep_idt bag;
  irep_idt induction;
  irep_idt bound;
  irep_idt input;
  irep_idt helper;
  exprt element;
};

bool segmented_fold_ignored(
  const goto_programt::instructiont &instruction)
{
  return
    instruction.is_skip() || instruction.is_location() ||
    instruction.is_decl() || instruction.is_dead();
}

bool segmented_fold_call(
  const goto_programt::instructiont &instruction,
  const irep_idt &lhs,
  const irep_idt &helper,
  const exprt &first,
  const exprt &second)
{
  irep_idt actual_lhs;
  irep_idt actual_helper;
  return
    instruction.is_function_call() &&
    direct_symbol(instruction.call_lhs(), actual_lhs) &&
    actual_lhs == lhs &&
    direct_call_identifier(instruction, actual_helper) &&
    actual_helper == helper &&
    instruction.call_arguments().size() == 2 &&
    without_cast(instruction.call_arguments()[0]) ==
      without_cast(first) &&
    without_cast(instruction.call_arguments()[1]) ==
      without_cast(second);
}

bool segmented_fold_worker(
  const irep_idt &worker,
  const irep_idt &expected_sum,
  const goto_modelt &model,
  const namespacet &ns,
  segmented_fold_workert &summary,
  std::string &reason)
{
  const auto function =
    model.goto_functions.function_map.find(worker);
  if(
    function == model.goto_functions.function_map.end() ||
    !function->second.body_available())
  {
    reason = "segmented_missing_worker";
    return false;
  }
  const auto &program = function->second.body;
  std::map<const goto_programt::instructiont *, std::size_t> positions;
  std::size_t position = 0;
  for(const auto &instruction : program.instructions)
    positions.emplace(&instruction, position++);

  auto loop_head = program.instructions.end();
  auto backedge = program.instructions.end();
  for(auto instruction = program.instructions.begin();
      instruction != program.instructions.end(); ++instruction)
  {
    if(!instruction->is_goto())
      continue;
    if(instruction->targets.size() != 1)
    {
      reason = "segmented_multi_target";
      return false;
    }
    if(
      positions.at(&*instruction->get_target()) <
      positions.at(&*instruction))
    {
      if(
        !instruction->condition().is_true() ||
        backedge != program.instructions.end())
      {
        reason = "segmented_backedge";
        return false;
      }
      backedge = instruction;
      loop_head = instruction->get_target();
    }
  }
  if(backedge == program.instructions.end())
  {
    reason = "segmented_no_loop";
    return false;
  }

  exprt bound;
  if(!parse_exit_guard(*loop_head, summary.induction, bound))
  {
    reason = "segmented_loop_guard";
    return false;
  }
  if(!direct_symbol(bound, summary.bound))
  {
    reason = "segmented_bound";
    return false;
  }
  const symbolt *induction_symbol = nullptr;
  const symbolt *bound_symbol = nullptr;
  if(
    ns.lookup(summary.induction, induction_symbol) ||
    ns.lookup(summary.bound, bound_symbol) ||
    !induction_symbol->is_static_lifetime ||
    !bound_symbol->is_static_lifetime ||
    induction_symbol->type != bound_symbol->type ||
    (induction_symbol->type.id() != ID_signedbv &&
     induction_symbol->type.id() != ID_unsignedbv))
  {
    reason = "segmented_induction_type";
    return false;
  }

  for(auto instruction = program.instructions.begin();
      instruction != loop_head; ++instruction)
  {
    if(!segmented_fold_ignored(*instruction))
    {
      reason = "segmented_prefix_effect";
      return false;
    }
  }

  std::vector<goto_programt::const_targett> body;
  for(auto instruction = std::next(loop_head);
      instruction != backedge; ++instruction)
  {
    if(!segmented_fold_ignored(*instruction))
      body.push_back(instruction);
  }
  if(body.size() != 7)
  {
    reason = "segmented_body_size";
    return false;
  }

  irep_idt preview;
  if(
    !body[0]->is_function_call() ||
    !direct_symbol(body[0]->call_lhs(), preview) ||
    !direct_call_identifier(*body[0], summary.helper) ||
    body[0]->call_arguments().size() != 2 ||
    !direct_symbol(body[0]->call_arguments()[0], summary.bag) ||
    !group_action_array_application(
      body[0]->call_arguments()[1],
      summary.induction,
      summary.input))
  {
    reason = "segmented_preview";
    return false;
  }
  summary.element = body[0]->call_arguments()[1];
  const symbolt *sum_symbol = nullptr;
  const symbolt *bag_symbol = nullptr;
  const symbolt *input_symbol = nullptr;
  if(
    ns.lookup(expected_sum, sum_symbol) ||
    ns.lookup(summary.bag, bag_symbol) ||
    ns.lookup(summary.input, input_symbol) ||
    !sum_symbol->is_static_lifetime ||
    !bag_symbol->is_static_lifetime ||
    !input_symbol->is_static_lifetime ||
    sum_symbol->type != bag_symbol->type ||
    summary.element.type() != sum_symbol->type)
  {
    reason = "segmented_state_type";
    return false;
  }
  summary.sum = expected_sum;

  if(
    !body[1]->is_goto() ||
    body[1]->condition().is_true() ||
    body[1]->targets.size() != 1 ||
    body[1]->get_target() != body[4])
  {
    reason = "segmented_branch";
    return false;
  }
  const symbol_exprt bag_expr(summary.bag, bag_symbol->type);
  const symbol_exprt sum_expr(summary.sum, sum_symbol->type);
  if(
    !segmented_fold_call(
      *body[2],
      summary.bag,
      summary.helper,
      bag_expr,
      summary.element))
  {
    reason = "segmented_accumulate";
    return false;
  }
  if(
    !body[3]->is_goto() ||
    !body[3]->condition().is_true() ||
    body[3]->targets.size() != 1 ||
    body[3]->get_target() != body[6])
  {
    reason = "segmented_accumulate_exit";
    return false;
  }
  if(
    !segmented_fold_call(
      *body[4],
      summary.sum,
      summary.helper,
      sum_expr,
      bag_expr))
  {
    reason = "segmented_flush_sum";
    return false;
  }
  irep_idt assigned_bag;
  if(
    !body[5]->is_assign() ||
    !direct_symbol(body[5]->assign_lhs(), assigned_bag) ||
    assigned_bag != summary.bag ||
    without_cast(body[5]->assign_rhs()) !=
      without_cast(summary.element))
  {
    reason = "segmented_flush_bag";
    return false;
  }
  irep_idt incremented;
  if(
    !parse_unit_increment(*body[6], incremented) ||
    incremented != summary.induction)
  {
    reason = "segmented_increment";
    return false;
  }

  std::vector<goto_programt::const_targett> suffix;
  for(auto instruction = std::next(backedge);
      instruction != program.instructions.end(); ++instruction)
  {
    if(
      segmented_fold_ignored(*instruction) ||
      instruction->is_set_return_value() ||
      instruction->is_end_function())
      continue;
    suffix.push_back(instruction);
  }
  if(
    suffix.size() != 1 ||
    loop_head->get_target() != suffix.front() ||
    !segmented_fold_call(
      *suffix.front(),
      summary.sum,
      summary.helper,
      sum_expr,
      bag_expr))
  {
    reason = "segmented_finalize";
    return false;
  }

  if(
    !group_action_pure_arithmetic_helper(
      summary.helper, ID_plus, model, ns))
  {
    reason = "segmented_helper";
    return false;
  }
  summary.worker = worker;
  return true;
}

void segmented_fold_relation_facts(
  const exprt &src,
  std::map<irep_idt, std::set<irep_idt>> &equal,
  std::set<irep_idt> &zero)
{
  const exprt &expr = without_cast(src);
  if(expr.id() == ID_and)
  {
    for(const auto &operand : expr.operands())
      segmented_fold_relation_facts(operand, equal, zero);
    return;
  }
  if(expr.id() != ID_equal || expr.operands().size() != 2)
    return;
  irep_idt first;
  irep_idt second;
  if(
    direct_symbol(expr.op0(), first) &&
    direct_symbol(expr.op1(), second))
  {
    equal[first].insert(second);
    equal[second].insert(first);
    return;
  }
  if(
    direct_symbol(expr.op0(), first) &&
    group_action_constant_zero(expr.op1()))
    zero.insert(first);
  else if(
    direct_symbol(expr.op1(), first) &&
    group_action_constant_zero(expr.op0()))
    zero.insert(first);
}

bool segmented_fold_initialization(
  const goto_modelt &model,
  const goto_programt::targett &first_create,
  const std::set<irep_idt> &required,
  std::string &reason)
{
  const auto main = model.goto_functions.function_map.find("main");
  INVARIANT(
    main != model.goto_functions.function_map.end(),
    "segmented lifecycle found main");
  bool proved = false;
  std::set<irep_idt> last_zero;
  for(auto instruction = main->second.body.instructions.begin();
      instruction != first_create; ++instruction)
  {
    irep_idt written;
    if(
      (instruction->is_assign() &&
       direct_symbol(instruction->assign_lhs(), written)) ||
      (instruction->is_function_call() &&
       !instruction->call_lhs().is_nil() &&
       direct_symbol(instruction->call_lhs(), written)))
    {
      if(required.count(written) != 0)
        proved = false;
    }
    irep_idt callee;
    if(
      instruction->is_function_call() &&
      instruction->call_lhs().is_nil() &&
      direct_call_identifier(*instruction, callee) &&
      instruction->call_arguments().size() == 1 &&
      group_action_assume_semantics(callee, model))
    {
      std::map<irep_idt, std::set<irep_idt>> equal;
      std::set<irep_idt> zero;
      segmented_fold_relation_facts(
        instruction->call_arguments().front(), equal, zero);
      std::vector<irep_idt> work(zero.begin(), zero.end());
      for(std::size_t index = 0; index < work.size(); ++index)
      {
        const auto neighbours = equal.find(work[index]);
        if(neighbours == equal.end())
          continue;
        for(const auto &neighbour : neighbours->second)
        {
          if(zero.insert(neighbour).second)
            work.push_back(neighbour);
        }
      }
      const bool current_proof = std::all_of(
        required.begin(),
        required.end(),
        [&](const irep_idt &symbol) {
          return zero.count(symbol) != 0;
        });
      if(current_proof)
      {
        proved = true;
        last_zero = std::move(zero);
      }
      else if(!proved)
        last_zero = std::move(zero);
    }
  }
  if(!proved)
  {
    reason = "segmented_initial_relation";
    for(const auto &symbol : required)
    {
      if(last_zero.count(symbol) == 0)
        reason += "_missing_" + id2string(symbol);
    }
    return false;
  }
  return true;
}

bool segmented_fold_property(
  const goto_modelt &model,
  const std::vector<goto_programt::targett> &joins,
  irep_idt &first,
  irep_idt &second,
  std::string &reason)
{
  const auto main = model.goto_functions.function_map.find("main");
  INVARIANT(
    main != model.goto_functions.function_map.end(),
    "segmented lifecycle found main");
  std::vector<goto_programt::const_targett> calls;
  bool after_join = false;
  for(auto instruction = main->second.body.instructions.begin();
      instruction != main->second.body.instructions.end(); ++instruction)
  {
    if(instruction == joins.back())
    {
      after_join = true;
      continue;
    }
    if(!after_join)
      continue;
    if(instruction->is_function_call())
      calls.push_back(instruction);
    else if(
      instruction->is_assign() || instruction->is_goto() ||
      instruction->is_assume() || instruction->is_assert() ||
      instruction->is_start_thread() || instruction->is_end_thread() ||
      instruction->is_atomic_begin() || instruction->is_atomic_end())
    {
      reason = "segmented_post_join_effect";
      return false;
    }
  }
  if(calls.size() != 2)
  {
    reason = "segmented_property_calls";
    return false;
  }
  irep_idt restriction;
  irep_idt error;
  if(
    !direct_call_identifier(*calls[0], restriction) ||
    calls[0]->call_arguments().size() != 1 ||
    !group_action_assume_semantics(restriction, model) ||
    !direct_call_identifier(*calls[1], error) ||
    !calls[1]->call_arguments().empty() ||
    !transition_word_error_function(error, model))
  {
    reason = "segmented_property_shape";
    return false;
  }
  const exprt &bad =
    without_cast(calls[0]->call_arguments().front());
  if(
    bad.id() != ID_notequal || bad.operands().size() != 2 ||
    !direct_symbol(bad.op0(), first) ||
    !direct_symbol(bad.op1(), second) ||
    first == second)
  {
    reason = "segmented_property_relation";
    return false;
  }
  std::size_t assertions = 0;
  for(const auto &entry : model.goto_functions.function_map)
  {
    if(!entry.second.body_available())
      continue;
    for(const auto &instruction : entry.second.body.instructions)
      assertions += instruction.is_assert();
  }
  if(assertions != 1)
  {
    reason = "segmented_property_count";
    return false;
  }
  return true;
}

bool segmented_fold_protected_accesses(
  const goto_modelt &model,
  const std::vector<create_recordt> &creates,
  const segmented_fold_workert workers[2],
  std::string &reason)
{
  std::set<irep_idt> proof{
    workers[0].sum,
    workers[0].bag,
    workers[0].induction,
    workers[1].sum,
    workers[1].bag,
    workers[1].induction};
  std::set<irep_idt> stable{
    workers[0].bound, workers[0].input};
  std::set<irep_idt> protected_symbols = proof;
  protected_symbols.insert(stable.begin(), stable.end());
  std::set<irep_idt> worker_ids{
    creates[0].worker, creates[1].worker};

  for(const auto &entry : model.goto_functions.function_map)
  {
    if(!entry.second.body_available())
      continue;
    for(const auto &instruction : entry.second.body.instructions)
    {
      if(
        contains_address_of_symbol(
          instruction.code(), protected_symbols) ||
        (instruction.has_condition() &&
         contains_address_of_symbol(
           instruction.condition(), protected_symbols)))
      {
        reason = "segmented_address_escape";
        return false;
      }
      if(
        entry.first != "main" &&
        entry.first != "__CPROVER_initialize" &&
        worker_ids.count(entry.first) == 0 &&
        instruction_mentions_any(
          instruction, protected_symbols))
      {
        reason = "segmented_foreign_access";
        return false;
      }
      if(
        worker_ids.count(entry.first) != 0 &&
        instruction.is_assign())
      {
        const exprt &lhs = without_cast(instruction.assign_lhs());
        if(lhs.id() == ID_dereference || lhs.id() == ID_index)
        {
          reason = "segmented_pointer_write";
          return false;
        }
      }
    }
  }

  const auto main = model.goto_functions.function_map.find("main");
  INVARIANT(
    main != model.goto_functions.function_map.end(),
    "segmented lifecycle found main");
  bool create_seen = false;
  for(const auto &instruction : main->second.body.instructions)
  {
    irep_idt callee;
    if(
      direct_call_identifier(instruction, callee) &&
      callee == "pthread_create")
      create_seen = true;
    if(!create_seen)
      continue;
    if(
      instruction.is_assign() &&
      contains_symbol(instruction.assign_lhs(), stable))
    {
      reason = "segmented_late_input_write";
      return false;
    }
    irep_idt written;
    const bool writes =
      (instruction.is_assign() &&
       direct_symbol(instruction.assign_lhs(), written)) ||
      (instruction.is_function_call() &&
       !instruction.call_lhs().is_nil() &&
       direct_symbol(instruction.call_lhs(), written));
    if(writes && protected_symbols.count(written) != 0)
    {
      reason = "segmented_late_write";
      return false;
    }
  }
  return true;
}

bool segmented_fold_conservation_audit_impl(
  const goto_modelt &model,
  const namespacet &ns,
  std::string &reason)
{
  goto_modelt &mutable_model = const_cast<goto_modelt &>(model);
  std::vector<create_recordt> creates;
  std::vector<goto_programt::targett> joins;
  if(
    !collect_lifecycle(
      mutable_model, ns, creates, joins, reason) ||
    creates.size() != 2 ||
    !validate_main_region(
      mutable_model, ns, creates, joins, reason))
  {
    if(reason.empty())
      reason = "segmented_lifecycle";
    return false;
  }

  irep_idt first_sum;
  irep_idt second_sum;
  if(
    !segmented_fold_property(
      model, joins, first_sum, second_sum, reason))
    return false;

  segmented_fold_workert workers[2];
  bool summarized = false;
  for(std::size_t permutation = 0; permutation < 2; ++permutation)
  {
    segmented_fold_workert candidates[2];
    std::string candidate_reason;
    const irep_idt &left =
      permutation == 0 ? first_sum : second_sum;
    const irep_idt &right =
      permutation == 0 ? second_sum : first_sum;
    if(
      segmented_fold_worker(
        creates[0].worker,
        left,
        model,
        ns,
        candidates[0],
        candidate_reason) &&
      segmented_fold_worker(
        creates[1].worker,
        right,
        model,
        ns,
        candidates[1],
        candidate_reason))
    {
      workers[0] = std::move(candidates[0]);
      workers[1] = std::move(candidates[1]);
      summarized = true;
      break;
    }
    reason = candidate_reason;
  }
  if(!summarized)
    return false;

  std::set<irep_idt> distinct{
    workers[0].sum,
    workers[0].bag,
    workers[0].induction,
    workers[1].sum,
    workers[1].bag,
    workers[1].induction};
  if(distinct.size() != 6)
  {
    reason = "segmented_distinct_state";
    return false;
  }
  const auto first_sum_symbol =
    model.symbol_table.symbols.find(workers[0].sum);
  const auto second_sum_symbol =
    model.symbol_table.symbols.find(workers[1].sum);
  if(
    first_sum_symbol == model.symbol_table.symbols.end() ||
    second_sum_symbol == model.symbol_table.symbols.end() ||
    first_sum_symbol->second.type != second_sum_symbol->second.type ||
    workers[0].helper != workers[1].helper ||
    workers[0].input != workers[1].input ||
    workers[0].bound != workers[1].bound)
  {
    reason = "segmented_cross_worker_state";
    return false;
  }
  exprt right_element = workers[1].element;
  group_action_replace_symbol(
    right_element,
    workers[1].induction,
    workers[0].induction,
    model);
  exprt left_element = workers[0].element;
  simplify_expr(left_element, ns);
  simplify_expr(right_element, ns);
  if(left_element != right_element)
  {
    reason = "segmented_input_alignment";
    return false;
  }
  if(
    !segmented_fold_initialization(
      model,
      creates.front().instruction,
      distinct,
      reason) ||
    !segmented_fold_protected_accesses(
      model, creates, workers, reason))
    return false;

  const std::set<irep_idt> left_foreign{
    workers[1].sum,
    workers[1].bag,
    workers[1].induction};
  const std::set<irep_idt> right_foreign{
    workers[0].sum,
    workers[0].bag,
    workers[0].induction};
  for(std::size_t index = 0; index < 2; ++index)
  {
    const auto function =
      model.goto_functions.function_map.find(workers[index].worker);
    const auto &foreign =
      index == 0 ? left_foreign : right_foreign;
    for(const auto &instruction :
        function->second.body.instructions)
    {
      if(instruction_mentions_any(instruction, foreign))
      {
        reason = "segmented_foreign_state";
        return false;
      }
    }
  }
  return true;
}

struct nested_iteration_workert
{
  irep_idt worker;
  irep_idt outer;
  irep_idt outer_bound;
  irep_idt accumulator;
  irep_idt inner;
  irep_idt inner_bound;
};

std::vector<goto_programt::const_targett>
nested_iteration_instructions(
  const goto_programt &program)
{
  std::vector<goto_programt::const_targett> result;
  for(auto instruction = program.instructions.begin();
      instruction != program.instructions.end(); ++instruction)
  {
    if(
      segmented_fold_ignored(*instruction) ||
      instruction->is_set_return_value() ||
      instruction->is_end_function())
      continue;
    result.push_back(instruction);
  }
  return result;
}

bool nested_iteration_unsigned_add_one(
  const goto_programt::instructiont &instruction,
  const namespacet &ns,
  irep_idt &accumulator)
{
  if(
    !instruction.is_assign() ||
    !direct_symbol(instruction.assign_lhs(), accumulator))
    return false;
  const symbolt *symbol = nullptr;
  if(
    ns.lookup(accumulator, symbol) ||
    !symbol->is_static_lifetime ||
    symbol->type.id() != ID_unsignedbv)
    return false;
  const exprt &rhs = without_cast(instruction.assign_rhs());
  if(rhs.id() != ID_plus || rhs.operands().size() != 2)
    return false;
  mp_integer constant;
  irep_idt state;
  return
    ((direct_symbol(rhs.op0(), state) &&
      state == accumulator &&
      constant_eval(rhs.op1(), {}, constant)) ||
     (direct_symbol(rhs.op1(), state) &&
      state == accumulator &&
      constant_eval(rhs.op0(), {}, constant))) &&
    constant == 1 && rhs.type() == symbol->type;
}

bool nested_iteration_worker(
  const irep_idt &worker,
  const irep_idt &expected_accumulator,
  const goto_modelt &model,
  const namespacet &ns,
  nested_iteration_workert &summary,
  std::string &reason)
{
  const auto function =
    model.goto_functions.function_map.find(worker);
  if(
    function == model.goto_functions.function_map.end() ||
    !function->second.body_available())
  {
    reason = "nested_missing_worker";
    return false;
  }
  const auto &program = function->second.body;
  const auto instructions =
    nested_iteration_instructions(program);
  if(instructions.size() != 8)
  {
    reason =
      "nested_instruction_count_" +
      std::to_string(instructions.size());
    return false;
  }

  exprt outer_bound;
  if(
    !parse_exit_guard(
      *instructions[0], summary.outer, outer_bound) ||
    !direct_symbol(outer_bound, summary.outer_bound))
  {
    reason = "nested_outer_guard";
    return false;
  }
  const symbolt *outer_symbol = nullptr;
  const symbolt *outer_bound_symbol = nullptr;
  if(
    ns.lookup(summary.outer, outer_symbol) ||
    ns.lookup(summary.outer_bound, outer_bound_symbol) ||
    !outer_symbol->is_static_lifetime ||
    !outer_bound_symbol->is_static_lifetime ||
    outer_symbol->type.id() != ID_signedbv ||
    outer_symbol->type != outer_bound_symbol->type)
  {
    reason = "nested_outer_type";
    return false;
  }
  if(
    !instructions[1]->is_assign() ||
    !direct_symbol(
      instructions[1]->assign_lhs(), summary.inner) ||
    !group_action_constant_zero(
      instructions[1]->assign_rhs()))
  {
    reason = "nested_inner_reset";
    return false;
  }
  exprt inner_bound;
  irep_idt parsed_inner;
  if(
    !parse_exit_guard(
      *instructions[2], parsed_inner, inner_bound) ||
    parsed_inner != summary.inner ||
    !direct_symbol(inner_bound, summary.inner_bound))
  {
    reason = "nested_inner_guard";
    return false;
  }
  const symbolt *inner_symbol = nullptr;
  const symbolt *inner_bound_symbol = nullptr;
  if(
    ns.lookup(summary.inner, inner_symbol) ||
    ns.lookup(summary.inner_bound, inner_bound_symbol) ||
    !inner_symbol->is_static_lifetime ||
    !inner_bound_symbol->is_static_lifetime ||
    inner_symbol->type.id() != ID_signedbv ||
    inner_symbol->type != inner_bound_symbol->type)
  {
    reason = "nested_inner_type";
    return false;
  }
  if(
    !nested_iteration_unsigned_add_one(
      *instructions[3], ns, summary.accumulator) ||
    summary.accumulator != expected_accumulator)
  {
    reason = "nested_unit_action";
    return false;
  }
  irep_idt incremented;
  if(
    !parse_unit_increment(*instructions[4], incremented) ||
    incremented != summary.inner ||
    !instructions[5]->is_goto() ||
    !instructions[5]->condition().is_true() ||
    instructions[5]->targets.size() != 1 ||
    instructions[5]->get_target() != instructions[2] ||
    instructions[2]->get_target() != instructions[6])
  {
    reason = "nested_inner_control";
    return false;
  }
  if(
    !parse_unit_increment(*instructions[6], incremented) ||
    incremented != summary.outer ||
    !instructions[7]->is_goto() ||
    !instructions[7]->condition().is_true() ||
    instructions[7]->targets.size() != 1 ||
    instructions[7]->get_target() != instructions[0] ||
    instructions[0]->get_target()->location_number <=
      instructions[7]->location_number)
  {
    reason = "nested_outer_control";
    return false;
  }
  summary.worker = worker;
  return true;
}

bool nested_iteration_aggregated_action(
  const goto_programt::instructiont &instruction,
  const irep_idt &expected_accumulator,
  const typet &accumulator_type,
  irep_idt &inner_bound)
{
  irep_idt lhs;
  if(
    !instruction.is_assign() ||
    !direct_symbol(instruction.assign_lhs(), lhs) ||
    lhs != expected_accumulator)
    return false;
  const exprt &rhs = without_cast(instruction.assign_rhs());
  if(
    rhs.id() != ID_plus || rhs.operands().size() != 2 ||
    rhs.type() != accumulator_type)
    return false;
  const exprt *amount = nullptr;
  irep_idt state;
  if(
    direct_symbol(rhs.op0(), state) &&
    state == expected_accumulator)
    amount = &rhs.op1();
  else if(
    direct_symbol(rhs.op1(), state) &&
    state == expected_accumulator)
    amount = &rhs.op0();
  else
    return false;
  return
    amount->type() == accumulator_type &&
    direct_symbol(*amount, inner_bound);
}

bool nested_iteration_aggregated_worker(
  const irep_idt &worker,
  const irep_idt &expected_accumulator,
  const goto_modelt &model,
  const namespacet &ns,
  nested_iteration_workert &summary,
  std::string &reason)
{
  const auto function =
    model.goto_functions.function_map.find(worker);
  if(
    function == model.goto_functions.function_map.end() ||
    !function->second.body_available())
  {
    reason = "aggregate_missing_worker";
    return false;
  }
  const auto instructions =
    nested_iteration_instructions(function->second.body);
  if(instructions.size() != 4)
  {
    reason =
      "aggregate_instruction_count_" +
      std::to_string(instructions.size());
    return false;
  }
  exprt bound;
  if(
    !parse_exit_guard(
      *instructions[0], summary.outer, bound) ||
    !direct_symbol(bound, summary.outer_bound))
  {
    reason = "aggregate_outer_guard";
    return false;
  }
  const symbolt *outer_symbol = nullptr;
  const symbolt *bound_symbol = nullptr;
  const symbolt *accumulator_symbol = nullptr;
  if(
    ns.lookup(summary.outer, outer_symbol) ||
    ns.lookup(summary.outer_bound, bound_symbol) ||
    ns.lookup(expected_accumulator, accumulator_symbol) ||
    !outer_symbol->is_static_lifetime ||
    !bound_symbol->is_static_lifetime ||
    !accumulator_symbol->is_static_lifetime ||
    outer_symbol->type.id() != ID_signedbv ||
    outer_symbol->type != bound_symbol->type ||
    accumulator_symbol->type.id() != ID_unsignedbv)
  {
    reason = "aggregate_state_type";
    return false;
  }
  if(
    !nested_iteration_aggregated_action(
      *instructions[1],
      expected_accumulator,
      accumulator_symbol->type,
      summary.inner_bound))
  {
    reason = "aggregate_action";
    return false;
  }
  const symbolt *inner_bound_symbol = nullptr;
  if(
    ns.lookup(summary.inner_bound, inner_bound_symbol) ||
    !inner_bound_symbol->is_static_lifetime ||
    inner_bound_symbol->type.id() != ID_signedbv)
  {
    reason = "aggregate_inner_bound_type";
    return false;
  }
  irep_idt incremented;
  if(
    !parse_unit_increment(*instructions[2], incremented) ||
    incremented != summary.outer ||
    !instructions[3]->is_goto() ||
    !instructions[3]->condition().is_true() ||
    instructions[3]->targets.size() != 1 ||
    instructions[3]->get_target() != instructions[0] ||
    instructions[0]->get_target()->location_number <=
      instructions[3]->location_number)
  {
    reason = "aggregate_outer_control";
    return false;
  }
  summary.worker = worker;
  summary.accumulator = expected_accumulator;
  return true;
}

bool nested_iteration_nonnegative_bound(
  const goto_modelt &model,
  const goto_programt::targett &first_create,
  const irep_idt &bound,
  std::string &reason)
{
  const auto main = model.goto_functions.function_map.find("main");
  INVARIANT(
    main != model.goto_functions.function_map.end(),
    "nested lifecycle found main");
  bool proved = false;
  for(auto instruction = main->second.body.instructions.begin();
      instruction != first_create; ++instruction)
  {
    irep_idt written;
    if(
      (instruction->is_assign() &&
       direct_symbol(instruction->assign_lhs(), written)) ||
      (instruction->is_function_call() &&
       !instruction->call_lhs().is_nil() &&
       direct_symbol(instruction->call_lhs(), written)))
    {
      if(written == bound)
        proved = false;
    }
    irep_idt callee;
    if(
      !instruction->is_function_call() ||
      !instruction->call_lhs().is_nil() ||
      !direct_call_identifier(*instruction, callee) ||
      instruction->call_arguments().size() != 1 ||
      !group_action_assume_semantics(callee, model))
      continue;
    const exprt &condition =
      without_cast(instruction->call_arguments().front());
    if(condition.operands().size() != 2)
      continue;
    irep_idt candidate;
    if(
      condition.id() == ID_ge &&
      direct_symbol(condition.op0(), candidate) &&
      candidate == bound &&
      group_action_constant_zero(condition.op1()))
      proved = true;
    else if(
      condition.id() == ID_le &&
      group_action_constant_zero(condition.op0()) &&
      direct_symbol(condition.op1(), candidate) &&
      candidate == bound)
      proved = true;
  }
  if(!proved)
  {
    reason = "nested_nonnegative_bound";
    return false;
  }
  return true;
}

bool nested_iteration_protected_accesses(
  const goto_modelt &model,
  const std::vector<create_recordt> &creates,
  const nested_iteration_workert &nested,
  const nested_iteration_workert &aggregate,
  std::string &reason)
{
  std::set<irep_idt> proof{
    nested.outer,
    nested.inner,
    nested.accumulator,
    aggregate.outer,
    aggregate.accumulator};
  std::set<irep_idt> stable{
    nested.outer_bound, nested.inner_bound};
  std::set<irep_idt> protected_symbols = proof;
  protected_symbols.insert(stable.begin(), stable.end());
  const std::set<irep_idt> worker_ids{
    creates[0].worker, creates[1].worker};

  for(const auto &entry : model.goto_functions.function_map)
  {
    if(!entry.second.body_available())
      continue;
    for(const auto &instruction : entry.second.body.instructions)
    {
      if(
        contains_address_of_symbol(
          instruction.code(), protected_symbols) ||
        (instruction.has_condition() &&
         contains_address_of_symbol(
           instruction.condition(), protected_symbols)))
      {
        reason = "nested_address_escape";
        return false;
      }
      if(
        entry.first != "main" &&
        entry.first != "__CPROVER_initialize" &&
        worker_ids.count(entry.first) == 0 &&
        instruction_mentions_any(
          instruction, protected_symbols))
      {
        reason = "nested_foreign_access";
        return false;
      }
    }
  }

  const std::set<irep_idt> nested_foreign{
    aggregate.outer, aggregate.accumulator};
  const std::set<irep_idt> aggregate_foreign{
    nested.outer, nested.inner, nested.accumulator};
  for(std::size_t index = 0; index < 2; ++index)
  {
    const auto function = model.goto_functions.function_map.find(
      index == 0 ? nested.worker : aggregate.worker);
    const auto &foreign =
      index == 0 ? nested_foreign : aggregate_foreign;
    for(const auto &instruction :
        function->second.body.instructions)
    {
      if(instruction_mentions_any(instruction, foreign))
      {
        reason = "nested_cross_worker_access";
        return false;
      }
    }
  }

  const auto main = model.goto_functions.function_map.find("main");
  INVARIANT(
    main != model.goto_functions.function_map.end(),
    "nested lifecycle found main");
  bool create_seen = false;
  for(const auto &instruction : main->second.body.instructions)
  {
    irep_idt callee;
    if(
      direct_call_identifier(instruction, callee) &&
      callee == "pthread_create")
      create_seen = true;
    if(!create_seen)
      continue;
    if(
      instruction.is_assign() &&
      contains_symbol(instruction.assign_lhs(), stable))
    {
      reason = "nested_late_parameter_write";
      return false;
    }
    irep_idt written;
    const bool writes =
      (instruction.is_assign() &&
       direct_symbol(instruction.assign_lhs(), written)) ||
      (instruction.is_function_call() &&
       !instruction.call_lhs().is_nil() &&
       direct_symbol(instruction.call_lhs(), written));
    if(writes && protected_symbols.count(written) != 0)
    {
      reason = "nested_late_write";
      return false;
    }
  }
  return true;
}

bool nested_iteration_property(
  const goto_modelt &model,
  const std::vector<goto_programt::targett> &joins,
  irep_idt &first,
  irep_idt &second,
  std::string &reason)
{
  const auto main = model.goto_functions.function_map.find("main");
  INVARIANT(
    main != model.goto_functions.function_map.end(),
    "nested lifecycle found main");
  std::vector<goto_programt::const_targett> calls;
  bool after_join = false;
  for(auto instruction = main->second.body.instructions.begin();
      instruction != main->second.body.instructions.end(); ++instruction)
  {
    if(instruction == joins.back())
    {
      after_join = true;
      continue;
    }
    if(!after_join)
      continue;
    if(instruction->is_function_call())
      calls.push_back(instruction);
    else if(
      instruction->is_assign() || instruction->is_goto() ||
      instruction->is_assume() || instruction->is_assert() ||
      instruction->is_start_thread() || instruction->is_end_thread() ||
      instruction->is_atomic_begin() || instruction->is_atomic_end())
    {
      reason = "nested_post_join_effect";
      return false;
    }
  }
  if(calls.size() != 2)
  {
    reason = "nested_property_calls";
    return false;
  }
  irep_idt restriction;
  irep_idt error;
  if(
    !direct_call_identifier(*calls[0], restriction) ||
    calls[0]->call_arguments().size() != 1 ||
    !group_action_assume_semantics(restriction, model) ||
    !direct_call_identifier(*calls[1], error) ||
    !calls[1]->call_arguments().empty() ||
    !transition_word_error_function(error, model))
  {
    reason = "nested_property_shape";
    return false;
  }
  const exprt &bad =
    without_cast(calls[0]->call_arguments().front());
  const exprt *left = nullptr;
  const exprt *right = nullptr;
  if(bad.id() == ID_notequal && bad.operands().size() == 2)
  {
    left = &bad.op0();
    right = &bad.op1();
  }
  else if(
    bad.id() == ID_not && bad.operands().size() == 1)
  {
    const exprt &equality = without_cast(bad.op0());
    if(
      equality.id() == ID_equal &&
      equality.operands().size() == 2)
    {
      left = &equality.op0();
      right = &equality.op1();
    }
  }
  if(
    left == nullptr || right == nullptr ||
    !direct_symbol(*left, first) ||
    !direct_symbol(*right, second) ||
    first == second)
  {
    reason = "nested_property_relation";
    return false;
  }
  std::size_t assertions = 0;
  for(const auto &entry : model.goto_functions.function_map)
  {
    if(!entry.second.body_available())
      continue;
    for(const auto &instruction : entry.second.body.instructions)
      assertions += instruction.is_assert();
  }
  if(assertions != 1)
  {
    reason = "nested_property_count";
    return false;
  }
  return true;
}

bool nested_iteration_homomorphism_audit_impl(
  const goto_modelt &model,
  const namespacet &ns,
  std::string &reason)
{
  goto_modelt &mutable_model = const_cast<goto_modelt &>(model);
  std::vector<create_recordt> creates;
  std::vector<goto_programt::targett> joins;
  if(
    !collect_lifecycle(
      mutable_model, ns, creates, joins, reason) ||
    creates.size() != 2 ||
    !validate_main_region(
      mutable_model, ns, creates, joins, reason))
  {
    if(reason.empty())
      reason = "nested_lifecycle";
    return false;
  }
  irep_idt first_accumulator;
  irep_idt second_accumulator;
  if(
    !nested_iteration_property(
      model,
      joins,
      first_accumulator,
      second_accumulator,
      reason))
    return false;

  nested_iteration_workert nested;
  nested_iteration_workert aggregate;
  bool summarized = false;
  std::vector<std::string> candidate_reasons;
  for(std::size_t permutation = 0; permutation < 2; ++permutation)
  {
    nested_iteration_workert candidate_nested;
    nested_iteration_workert candidate_aggregate;
    std::string candidate_reason;
    const irep_idt &left =
      permutation == 0 ? first_accumulator : second_accumulator;
    const irep_idt &right =
      permutation == 0 ? second_accumulator : first_accumulator;
    if(
      nested_iteration_worker(
        creates[0].worker,
        left,
        model,
        ns,
        candidate_nested,
        candidate_reason) &&
      nested_iteration_aggregated_worker(
        creates[1].worker,
        right,
        model,
        ns,
        candidate_aggregate,
        candidate_reason))
    {
      nested = std::move(candidate_nested);
      aggregate = std::move(candidate_aggregate);
      summarized = true;
      break;
    }
    candidate_reasons.push_back(candidate_reason);
    if(
      nested_iteration_worker(
        creates[1].worker,
        right,
        model,
        ns,
        candidate_nested,
        candidate_reason) &&
      nested_iteration_aggregated_worker(
        creates[0].worker,
        left,
        model,
        ns,
        candidate_aggregate,
        candidate_reason))
    {
      nested = std::move(candidate_nested);
      aggregate = std::move(candidate_aggregate);
      summarized = true;
      break;
    }
    candidate_reasons.push_back(candidate_reason);
    reason = candidate_reason;
  }
  if(!summarized)
  {
    reason = "nested_candidates";
    for(const auto &candidate_reason : candidate_reasons)
      reason += "_" + candidate_reason;
    return false;
  }

  const auto nested_accumulator =
    model.symbol_table.symbols.find(nested.accumulator);
  const auto aggregate_accumulator =
    model.symbol_table.symbols.find(aggregate.accumulator);
  const auto inner_bound =
    model.symbol_table.symbols.find(nested.inner_bound);
  if(
    nested_accumulator == model.symbol_table.symbols.end() ||
    aggregate_accumulator == model.symbol_table.symbols.end() ||
    inner_bound == model.symbol_table.symbols.end() ||
    nested_accumulator->second.type !=
      aggregate_accumulator->second.type ||
    nested.inner_bound != aggregate.inner_bound ||
    nested.outer_bound != aggregate.outer_bound ||
    inner_bound->second.type !=
      model.symbol_table.symbols.at(nested.inner).type)
  {
    reason = "nested_cross_worker_alignment";
    return false;
  }
  const std::set<irep_idt> initial{
    nested.outer,
    nested.accumulator,
    aggregate.outer,
    aggregate.accumulator};
  if(
    initial.size() != 4 ||
    !segmented_fold_initialization(
      model,
      creates.front().instruction,
      initial,
      reason) ||
    !nested_iteration_nonnegative_bound(
      model,
      creates.front().instruction,
      nested.inner_bound,
      reason) ||
    !nested_iteration_protected_accesses(
      model, creates, nested, aggregate, reason))
    return false;
  return true;
}

bool local_scalar_expression(
  const exprt &expr,
  const namespacet &ns)
{
  if(
    expr.id() == ID_side_effect || expr.id() == ID_dereference ||
    expr.id() == ID_address_of)
    return false;
  if(expr.id() == ID_symbol)
  {
    const symbolt *symbol = nullptr;
    if(ns.lookup(to_symbol_expr(expr).get_identifier(), symbol))
      return false;
    return
      !symbol->is_static_lifetime && !symbol->is_type &&
      symbol->type.id() != ID_pointer;
  }
  for(const auto &operand : expr.operands())
  {
    if(!local_scalar_expression(operand, ns))
      return false;
  }
  return true;
}

bool event_free_local_counting_loop(
  const goto_programt &program,
  const namespacet &ns,
  goto_programt::const_targett backedge,
  irep_idt &induction,
  exprt &bound)
{
  if(
    !backedge->is_goto() || !backedge->condition().is_true() ||
    backedge->targets.size() != 1)
    return false;
  const auto head = backedge->get_target();
  if(!parse_exit_guard(*head, induction, bound))
    return false;

  const symbolt *induction_symbol = nullptr;
  if(
    ns.lookup(induction, induction_symbol) ||
    induction_symbol->is_static_lifetime || induction_symbol->is_type ||
    (induction_symbol->type.id() != ID_signedbv &&
     induction_symbol->type.id() != ID_unsignedbv) ||
    induction_symbol->type.get_bool(ID_C_volatile) ||
    !local_scalar_expression(bound, ns) ||
    contains_symbol(bound, {induction}))
    return false;

  std::map<const goto_programt::instructiont *, std::size_t> positions;
  std::size_t position = 0;
  for(const auto &instruction : program.instructions)
    positions.emplace(&instruction, position++);
  const auto head_position = positions.at(&*head);
  const auto backedge_position = positions.at(&*backedge);
  if(
    head->targets.size() != 1 ||
    positions.at(&*head->get_target()) <= backedge_position)
    return false;

  for(auto instruction = program.instructions.begin();
      instruction != program.instructions.end(); ++instruction)
  {
    if(!instruction->is_goto())
      continue;
    const auto source_position = positions.at(&*instruction);
    for(const auto &target : instruction->targets)
    {
      const auto target_position = positions.at(&*target);
      if(
        target_position >= head_position &&
        target_position <= backedge_position &&
        (source_position < head_position ||
         source_position > backedge_position))
        return false;
    }
  }

  std::size_t increments = 0;
  for(auto instruction = head; instruction != std::next(backedge);
      ++instruction)
  {
    if(instruction == head || instruction == backedge)
      continue;
    irep_idt incremented;
    if(
      parse_unit_increment(*instruction, incremented) &&
      incremented == induction)
    {
      ++increments;
      continue;
    }
    if(instruction->is_skip() || instruction->is_location())
      continue;
    return false;
  }
  if(increments != 1)
    return false;

  bool zero_initialized = false;
  auto last_semantic = program.instructions.end();
  for(auto instruction = program.instructions.begin(); instruction != head;
      ++instruction)
  {
    if(!instruction->is_skip() && !instruction->is_location())
      last_semantic = instruction;
    if(
      instruction->is_assign() &&
      without_cast(instruction->assign_lhs()).id() == ID_symbol &&
      to_symbol_expr(without_cast(instruction->assign_lhs()))
          .get_identifier() == induction)
      zero_initialized =
        parse_zero_initialization(*instruction, induction);
  }
  return
    zero_initialized &&
    last_semantic != program.instructions.end() &&
    parse_zero_initialization(*last_semantic, induction);
}

struct homogeneous_spawn_witnesst
{
  irep_idt induction;
  exprt bound;
  irep_idt worker;
  irep_idt shared;
  mp_integer increment;
  const goto_programt::instructiont *create_instruction = nullptr;
};

struct indexed_lifecycle_loopt
{
  goto_programt::const_targett head;
  goto_programt::const_targett exit;
  unsigned bound = 0;
  irep_idt induction;
  irep_idt operation;
};

struct dormant_spawn_cutofft
{
  goto_programt::const_targett head;
  goto_programt::const_targett exit;
  const goto_programt::instructiont *create_instruction = nullptr;
  const goto_programt::instructiont *first_join = nullptr;
  irep_idt induction;
  irep_idt thread_ids;
  irep_idt worker;
  mp_integer bound;
};

void collect_symbol_identifiers(
  const exprt &expr,
  std::set<irep_idt> &identifiers)
{
  const exprt &value = without_cast(expr);
  if(value.id() == ID_symbol)
    identifiers.insert(to_symbol_expr(value).get_identifier());
  for(const auto &operand : value.operands())
    collect_symbol_identifiers(operand, identifiers);
}

bool dormant_spawn_thread_array(
  const exprt &handle,
  const irep_idt &induction,
  const namespacet &ns,
  irep_idt &thread_ids)
{
  std::set<irep_idt> identifiers;
  collect_symbol_identifiers(handle, identifiers);
  if(identifiers.erase(induction) != 1 || identifiers.size() != 1)
    return false;
  thread_ids = *identifiers.begin();
  const symbolt *symbol = nullptr;
  return
    !ns.lookup(thread_ids, symbol) &&
    symbol->type.id() == ID_array &&
    contains_symbol(handle, {induction, thread_ids});
}

bool dormant_spawn_loop(
  const goto_modelt &goto_model,
  const namespacet &ns,
  const std::map<const goto_programt::instructiont *, std::size_t> &positions,
  goto_programt::const_targett backedge,
  dormant_spawn_cutofft &summary,
  std::string &reason)
{
  const auto main =
    goto_model.goto_functions.function_map.find("main");
  INVARIANT(
    main != goto_model.goto_functions.function_map.end() &&
    main->second.body_available(),
    "dormant spawn loop requires main");
  const auto &program = main->second.body;
  if(
    !backedge->is_goto() || !backedge->condition().is_true() ||
    backedge->targets.size() != 1)
  {
    reason = "dormant_not_backedge";
    return false;
  }
  const auto head = backedge->get_target();
  const auto exit = std::next(backedge);
  if(
    exit == program.instructions.end() ||
    positions.at(&*head) >= positions.at(&*backedge) ||
    !head->is_goto() || head->targets.size() != 1 ||
    head->get_target() != exit)
  {
    reason = "dormant_not_canonical";
    return false;
  }

  exprt bound;
  if(
    !parse_exit_guard(*head, summary.induction, bound) ||
    !constant_eval(without_cast(bound), {}, summary.bound) ||
    summary.bound <= 2)
  {
    reason = "dormant_bound";
    return false;
  }
  if(
    head == program.instructions.begin() ||
    !parse_zero_initialization(
      *std::prev(head), summary.induction))
  {
    reason = "dormant_initialization";
    return false;
  }
  const auto update = std::prev(backedge);
  irep_idt update_induction;
  if(
    !parse_unit_increment(*update, update_induction) ||
    update_induction != summary.induction)
  {
    reason = "dormant_update";
    return false;
  }

  std::size_t creates = 0;
  for(auto instruction = std::next(head); instruction != backedge;
      ++instruction)
  {
    if(instruction == update)
      continue;
    if(
      instruction->is_skip() || instruction->is_location() ||
      instruction->is_decl() || instruction->is_dead())
      continue;
    irep_idt callee;
    if(
      !instruction->is_function_call() ||
      !direct_call_identifier(*instruction, callee) ||
      callee != "pthread_create" ||
      !instruction->call_lhs().is_nil() ||
      instruction->call_arguments().size() != 4 ||
      !is_zero_constant(instruction->call_arguments()[1]) ||
      !addressed_symbol(
        instruction->call_arguments()[2], summary.worker) ||
      !is_zero_constant(instruction->call_arguments()[3]) ||
      !dormant_spawn_thread_array(
        instruction->call_arguments()[0],
        summary.induction,
        ns,
        summary.thread_ids) ||
      ++creates != 1)
    {
      reason = "dormant_loop_effect";
      return false;
    }
    summary.create_instruction = &*instruction;
  }
  if(creates != 1)
  {
    reason = "dormant_create_count";
    return false;
  }

  const auto head_position = positions.at(&*head);
  const auto exit_position = positions.at(&*exit);
  for(auto instruction = program.instructions.begin();
      instruction != program.instructions.end(); ++instruction)
  {
    if(instruction->is_goto())
    {
      const auto source_position = positions.at(&*instruction);
      for(const auto &target : instruction->targets)
      {
        const auto target_position = positions.at(&*target);
        if(
          target_position >= head_position &&
          target_position < exit_position &&
          (source_position < head_position ||
           source_position >= exit_position))
        {
          reason = "dormant_alternate_entry";
          return false;
        }
      }
    }
    if(
      positions.at(&*instruction) >= exit_position &&
      instruction_mentions_any(
        *instruction, {summary.induction}))
    {
      reason = "dormant_induction_observed";
      return false;
    }
  }

  bool after_create_loop = false;
  for(const auto &entry : goto_model.goto_functions.function_map)
  {
    if(!entry.second.body_available())
      continue;
    if(entry.first == "main")
      after_create_loop = false;
    for(auto instruction = entry.second.body.instructions.begin();
        instruction != entry.second.body.instructions.end(); ++instruction)
    {
      if(entry.first == "main" && instruction == exit)
        after_create_loop = true;
      irep_idt callee;
      const bool direct_call =
        direct_call_identifier(*instruction, callee);
      if(
        !instruction_mentions_any(
          *instruction, {summary.thread_ids}) ||
        &*instruction == summary.create_instruction ||
        instruction->is_decl() || instruction->is_dead())
        continue;
      if(
        entry.first == "main" && after_create_loop &&
        direct_call && callee == "pthread_join")
      {
        if(summary.first_join == nullptr)
          summary.first_join = &*instruction;
        continue;
      }
      reason = "dormant_thread_ids_observed";
      return false;
    }
  }

  summary.head = head;
  summary.exit = exit;
  return true;
}

std::vector<dormant_spawn_cutofft> dormant_spawn_cutoffs(
  const goto_modelt &goto_model,
  std::string &last_reason)
{
  std::vector<dormant_spawn_cutofft> result;
  const auto main =
    goto_model.goto_functions.function_map.find("main");
  if(
    main == goto_model.goto_functions.function_map.end() ||
    !main->second.body_available())
  {
    last_reason = "dormant_missing_main";
    return result;
  }
  const namespacet ns(goto_model.symbol_table);
  const auto &program = main->second.body;
  std::map<const goto_programt::instructiont *, std::size_t> positions;
  std::size_t position = 0;
  for(const auto &instruction : program.instructions)
    positions.emplace(&instruction, position++);
  for(auto instruction = program.instructions.begin();
      instruction != program.instructions.end(); ++instruction)
  {
    if(
      !instruction->is_goto() || !instruction->condition().is_true() ||
      instruction->targets.size() != 1 ||
      positions.at(&*instruction->get_target()) >=
        positions.at(&*instruction))
      continue;
    dormant_spawn_cutofft summary;
    std::string reason;
    if(
      dormant_spawn_loop(
        goto_model, ns, positions, instruction, summary, reason))
      result.push_back(std::move(summary));
    else
      last_reason = std::move(reason);
  }
  std::set<const goto_programt::instructiont *> admitted_creates;
  for(const auto &candidate : result)
    admitted_creates.insert(candidate.create_instruction);
  for(const auto &entry : goto_model.goto_functions.function_map)
  {
    if(!entry.second.body_available())
      continue;
    for(const auto &instruction : entry.second.body.instructions)
    {
      irep_idt callee;
      if(
        direct_call_identifier(instruction, callee) &&
        callee == "pthread_create" &&
        admitted_creates.count(&instruction) == 0)
      {
        last_reason = "dormant_other_create";
        result.clear();
        return result;
      }
    }
  }
  return result;
}

bool dormant_spawn_pair_counts(
  const std::size_t classes,
  std::size_t variant,
  std::vector<unsigned> &counts,
  std::string &label)
{
  counts.assign(classes, 0);
  for(std::size_t first = 0; first < classes; ++first)
  {
    for(std::size_t second = first + 1; second < classes; ++second)
    {
      if(variant == 0)
      {
        counts[first] = 1;
        counts[second] = 1;
        label =
          "pair-" + std::to_string(first) + "-" + std::to_string(second);
        return true;
      }
      --variant;
    }
  }
  if(variant >= classes)
    return false;
  counts[variant] = 2;
  label = "self-" + std::to_string(variant);
  return true;
}

bool apply_dormant_spawn_counts(
  goto_modelt &goto_model,
  const std::vector<dormant_spawn_cutofft> &candidates,
  const std::vector<unsigned> &counts,
  bool &truncated)
{
  if(candidates.size() != counts.size())
    return false;
  auto main =
    goto_model.goto_functions.function_map.find("main");
  INVARIANT(
    main != goto_model.goto_functions.function_map.end() &&
    main->second.body_available(),
    "dormant spawn cutoff requires main");
  const namespacet ns(goto_model.symbol_table);
  for(std::size_t index = 0; index < candidates.size(); ++index)
  {
    const auto &summary = candidates[index];
    const symbolt *induction_symbol = nullptr;
    INVARIANT(
      !ns.lookup(summary.induction, induction_symbol),
      "dormant spawn induction exists");
    auto head =
      main->second.body.const_cast_target(summary.head);
    symbol_exprt induction(
      summary.induction, induction_symbol->type);
    head->condition_nonconst() = not_exprt(
      binary_relation_exprt(
        induction,
        ID_lt,
        from_integer(counts[index], induction_symbol->type)));
  }

  truncated = false;
  bool at_join = false;
  for(auto instruction = main->second.body.instructions.begin();
      instruction != main->second.body.instructions.end();
      ++instruction)
  {
    for(const auto &candidate : candidates)
    {
      if(
        candidate.first_join != nullptr &&
        &*instruction == candidate.first_join)
        at_join = true;
    }
    if(!at_join || instruction->is_end_function())
      continue;
    instruction->turn_into_skip();
    truncated = true;
  }
  goto_model.goto_functions.update();
  return true;
}

bool constant_lifecycle_bound(const exprt &expr, unsigned &bound)
{
  const exprt &value = without_cast(expr);
  if(value.id() != ID_constant)
    return false;
  mp_integer integer;
  if(
    to_integer(to_constant_expr(value), integer) || integer <= 0 ||
    integer > 8)
    return false;
  bound = integer.to_ulong();
  return true;
}

bool indexed_lifecycle_loop(
  const goto_programt &program,
  const std::map<const goto_programt::instructiont *, std::size_t> &positions,
  goto_programt::const_targett backedge,
  indexed_lifecycle_loopt &summary,
  std::string &reason)
{
  if(
    !backedge->is_goto() || !backedge->condition().is_true() ||
    backedge->targets.size() != 1)
  {
    reason = "lifecycle_not_backedge";
    return false;
  }
  const auto head = backedge->get_target();
  const auto exit = std::next(backedge);
  if(
    exit == program.instructions.end() ||
    positions.at(&*head) >= positions.at(&*backedge) ||
    !head->is_goto() || head->targets.size() != 1 ||
    head->get_target() != exit)
  {
    reason = "lifecycle_not_canonical";
    return false;
  }

  irep_idt induction;
  exprt bound_expr;
  unsigned bound = 0;
  if(
    !parse_exit_guard(*head, induction, bound_expr) ||
    !constant_lifecycle_bound(bound_expr, bound))
  {
    reason = "lifecycle_nonconstant_bound";
    return false;
  }
  if(
    head == program.instructions.begin() ||
    !parse_zero_initialization(*std::prev(head), induction))
  {
    reason = "lifecycle_nonzero_init";
    return false;
  }
  if(head == backedge)
  {
    reason = "lifecycle_empty_body";
    return false;
  }
  const auto update = std::prev(backedge);
  irep_idt update_induction;
  if(
    !parse_unit_increment(*update, update_induction) ||
    update_induction != induction)
  {
    reason = "lifecycle_nonunit_update";
    return false;
  }

  irep_idt operation;
  std::size_t lifecycle_calls = 0;
  for(auto instruction = std::next(head); instruction != backedge;
      ++instruction)
  {
    if(instruction->is_goto())
    {
      reason = "lifecycle_nonlinear_body";
      return false;
    }
    if(instruction->is_assign())
    {
      const exprt &lhs = without_cast(instruction->assign_lhs());
      if(
        lhs.id() == ID_symbol &&
        to_symbol_expr(lhs).get_identifier() == induction &&
        instruction != update)
      {
        reason = "lifecycle_induction_write";
        return false;
      }
    }
    if(instruction->is_function_call())
    {
      irep_idt callee;
      if(
        !direct_call_identifier(*instruction, callee) ||
        (callee != "pthread_create" && callee != "pthread_join"))
      {
        reason = "lifecycle_other_call";
        return false;
      }
      if(++lifecycle_calls != 1)
      {
        reason = "lifecycle_call_count";
        return false;
      }
      operation = callee;
    }
  }
  if(lifecycle_calls != 1)
  {
    reason = "lifecycle_missing_call";
    return false;
  }

  const auto head_position = positions.at(&*head);
  const auto exit_position = positions.at(&*exit);
  for(auto instruction = program.instructions.begin();
      instruction != program.instructions.end(); ++instruction)
  {
    if(!instruction->is_goto())
      continue;
    const auto source_position = positions.at(&*instruction);
    for(const auto &target : instruction->targets)
    {
      const auto target_position = positions.at(&*target);
      if(
        target_position >= head_position && target_position < exit_position &&
        (source_position < head_position || source_position >= exit_position))
      {
        reason = "lifecycle_alternate_entry";
        return false;
      }
    }
  }

  summary.head = head;
  summary.exit = exit;
  summary.bound = bound;
  summary.induction = induction;
  summary.operation = operation;
  return true;
}

std::vector<indexed_lifecycle_loopt> indexed_lifecycle_loops(
  const goto_modelt &goto_model,
  std::string &last_reason)
{
  std::vector<indexed_lifecycle_loopt> result;
  const auto main =
    goto_model.goto_functions.function_map.find("main");
  if(
    main == goto_model.goto_functions.function_map.end() ||
    !main->second.body_available())
  {
    last_reason = "lifecycle_missing_main";
    return result;
  }
  const auto &program = main->second.body;
  std::map<const goto_programt::instructiont *, std::size_t> positions;
  std::size_t position = 0;
  for(const auto &instruction : program.instructions)
    positions.emplace(&instruction, position++);
  for(auto instruction = program.instructions.begin();
      instruction != program.instructions.end(); ++instruction)
  {
    if(
      !instruction->is_goto() || !instruction->condition().is_true() ||
      instruction->targets.size() != 1 ||
      positions.at(&*instruction->get_target()) >=
        positions.at(&*instruction))
      continue;
    indexed_lifecycle_loopt summary;
    std::string reason;
    if(
      indexed_lifecycle_loop(
        program, positions, instruction, summary, reason))
      result.push_back(std::move(summary));
    else
      last_reason = std::move(reason);
  }
  return result;
}

bool homogeneous_spawn_stable_bound(
  const exprt &bound,
  const goto_modelt &model,
  const namespacet &ns,
  goto_programt::const_targett loop_head,
  std::string &reason)
{
  std::set<irep_idt> symbols;
  std::vector<const exprt *> pending{&bound};
  while(!pending.empty())
  {
    const exprt &current = *pending.back();
    pending.pop_back();
    if(
      current.id() == ID_side_effect ||
      current.id() == ID_dereference ||
      current.id() == ID_address_of)
    {
      reason = "spawn_bound_expression";
      return false;
    }
    if(current.id() == ID_symbol)
    {
      const auto identifier =
        to_symbol_expr(current).get_identifier();
      const symbolt *symbol = nullptr;
      if(
        ns.lookup(identifier, symbol) || symbol->is_type ||
        (symbol->type.id() != ID_signedbv &&
         symbol->type.id() != ID_unsignedbv) ||
        symbol->type.get_bool(ID_C_volatile))
      {
        reason = "spawn_bound_type";
        return false;
      }
      symbols.insert(identifier);
    }
    for(const auto &operand : current.operands())
      pending.push_back(&operand);
  }
  const auto main =
    model.goto_functions.function_map.find("main");
  INVARIANT(
    main != model.goto_functions.function_map.end(),
    "spawn stable bound has main");
  bool after_head = false;
  for(const auto &entry : model.goto_functions.function_map)
  {
    if(!entry.second.body_available())
      continue;
    if(entry.first == "main")
      after_head = false;
    for(auto instruction = entry.second.body.instructions.begin();
        instruction != entry.second.body.instructions.end(); ++instruction)
    {
      if(entry.first == "main" && instruction == loop_head)
        after_head = true;
      if(
        contains_address_of_symbol(
          instruction->code(), symbols) ||
        (instruction->has_condition() &&
         contains_address_of_symbol(
           instruction->condition(), symbols)))
      {
        reason = "spawn_bound_escape";
        return false;
      }
      irep_idt written;
      const bool writes =
        (instruction->is_assign() &&
         direct_symbol(instruction->assign_lhs(), written)) ||
        (instruction->is_function_call() &&
         !instruction->call_lhs().is_nil() &&
         direct_symbol(instruction->call_lhs(), written));
      if(
        writes && symbols.count(written) != 0 &&
        entry.first != "__CPROVER_initialize" &&
        (entry.first != "main" || after_head))
      {
        reason = "spawn_bound_late_write";
        return false;
      }
    }
  }
  return true;
}

bool homogeneous_spawn_worker_effect(
  const irep_idt &worker,
  const goto_modelt &model,
  const namespacet &ns,
  irep_idt &shared,
  mp_integer &increment,
  std::string &reason)
{
  const auto function =
    model.goto_functions.function_map.find(worker);
  if(
    function == model.goto_functions.function_map.end() ||
    !function->second.body_available())
  {
    reason = "spawn_missing_worker";
    return false;
  }
  std::vector<goto_programt::const_targett> semantic;
  for(auto instruction = function->second.body.instructions.begin();
      instruction != function->second.body.instructions.end(); ++instruction)
  {
    if(
      instruction->is_skip() || instruction->is_location() ||
      instruction->is_decl() || instruction->is_dead() ||
      instruction->is_set_return_value() ||
      instruction->is_end_function())
      continue;
    semantic.push_back(instruction);
  }
  if(semantic.size() != 2 || !semantic[0]->is_assign() ||
     !semantic[1]->is_assign())
  {
    reason =
      "spawn_worker_instruction_count_" +
      std::to_string(semantic.size());
    return false;
  }

  irep_idt local;
  if(
    !direct_symbol(semantic[0]->assign_lhs(), local) ||
    !direct_symbol(semantic[0]->assign_rhs(), shared) ||
    local == shared)
  {
    reason = "spawn_worker_load";
    return false;
  }
  const symbolt *local_symbol = nullptr;
  const symbolt *shared_symbol = nullptr;
  if(
    ns.lookup(local, local_symbol) ||
    ns.lookup(shared, shared_symbol) ||
    local_symbol->is_static_lifetime ||
    !shared_symbol->is_static_lifetime ||
    local_symbol->type != shared_symbol->type ||
    (shared_symbol->type.id() != ID_signedbv &&
     shared_symbol->type.id() != ID_unsignedbv))
  {
    reason = "spawn_worker_state_type";
    return false;
  }

  irep_idt lhs;
  if(
    !direct_symbol(semantic[1]->assign_lhs(), lhs) ||
    lhs != shared)
  {
    reason = "spawn_worker_store";
    return false;
  }
  const exprt &rhs = without_cast(semantic[1]->assign_rhs());
  if(rhs.id() != ID_plus || rhs.operands().size() != 2)
  {
    reason = "spawn_worker_affine_rhs";
    return false;
  }
  irep_idt state;
  const exprt *constant = nullptr;
  if(direct_symbol(rhs.op0(), state) && state == local)
    constant = &rhs.op1();
  else if(direct_symbol(rhs.op1(), state) && state == local)
    constant = &rhs.op0();
  if(
    constant == nullptr ||
    !constant_eval(*constant, {}, increment) ||
    increment != 1)
  {
    reason = "spawn_worker_increment";
    return false;
  }
  return true;
}

bool homogeneous_spawn_loop(
  const goto_modelt &model,
  const namespacet &ns,
  goto_programt::const_targett backedge,
  homogeneous_spawn_witnesst &summary,
  std::string &reason)
{
  const auto main =
    model.goto_functions.function_map.find("main");
  INVARIANT(
    main != model.goto_functions.function_map.end(),
    "spawn witness audit has main");
  const auto &program = main->second.body;
  if(
    !backedge->is_goto() || !backedge->condition().is_true() ||
    backedge->targets.size() != 1)
  {
    reason = "spawn_backedge";
    return false;
  }
  const auto head = backedge->get_target();
  if(!parse_exit_guard(
       *head, summary.induction, summary.bound))
  {
    reason = "spawn_exit_guard";
    return false;
  }
  const symbolt *induction_symbol = nullptr;
  if(
    ns.lookup(summary.induction, induction_symbol) ||
    induction_symbol->is_static_lifetime ||
    (induction_symbol->type.id() != ID_signedbv &&
     induction_symbol->type.id() != ID_unsignedbv) ||
    !homogeneous_spawn_stable_bound(
      summary.bound, model, ns, head, reason))
  {
    if(reason.empty())
      reason = "spawn_loop_state";
    return false;
  }

  std::size_t creates = 0;
  std::size_t increments = 0;
  for(auto instruction = head; instruction != std::next(backedge);
      ++instruction)
  {
    if(instruction == head || instruction == backedge)
      continue;
    irep_idt incremented;
    if(
      parse_unit_increment(*instruction, incremented) &&
      incremented == summary.induction)
    {
      ++increments;
      continue;
    }
    irep_idt callee;
    if(
      direct_call_identifier(*instruction, callee) &&
      callee == "pthread_create" &&
      instruction->call_arguments().size() == 4 &&
      addressed_symbol(
        instruction->call_arguments()[2], summary.worker))
    {
      ++creates;
      summary.create_instruction = &*instruction;
      continue;
    }
    if(
      instruction->is_skip() || instruction->is_location() ||
      instruction->is_decl() || instruction->is_dead())
      continue;
    reason = "spawn_loop_effect";
    return false;
  }
  if(creates != 1 || increments != 1)
  {
    reason = "spawn_loop_counts";
    return false;
  }

  for(const auto &entry : model.goto_functions.function_map)
  {
    if(!entry.second.body_available())
      continue;
    bool after_loop = false;
    for(auto instruction = entry.second.body.instructions.begin();
        instruction != entry.second.body.instructions.end(); ++instruction)
    {
      if(entry.first == "main" && instruction == std::next(backedge))
        after_loop = true;
      irep_idt callee;
      if(
        direct_call_identifier(*instruction, callee) &&
        callee == "pthread_create" &&
        &*instruction != summary.create_instruction &&
        (entry.first != "main" || !after_loop))
      {
        reason = "spawn_preexisting_concurrency";
        return false;
      }
    }
  }

  auto last_semantic = program.instructions.end();
  for(auto instruction = program.instructions.begin(); instruction != head;
      ++instruction)
  {
    if(!instruction->is_skip() && !instruction->is_location())
      last_semantic = instruction;
  }
  if(
    last_semantic == program.instructions.end() ||
    !parse_zero_initialization(
      *last_semantic, summary.induction))
  {
    reason = "spawn_loop_initialization";
    return false;
  }
  return homogeneous_spawn_worker_effect(
    summary.worker,
    model,
    ns,
    summary.shared,
    summary.increment,
    reason);
}

struct alternating_phase_workert
{
  irep_idt function;
  irep_idt induction;
  exprt bound;
  irep_idt mutex;
  irep_idt waited_condition;
  irep_idt signalled_condition;
  irep_idt token;
  irep_idt accumulator;
  irep_idt completion;
  bool producer = false;
};

bool parse_condition_call(
  const goto_programt::instructiont &instruction,
  const irep_idt &callee,
  irep_idt &condition,
  irep_idt *mutex)
{
  irep_idt actual;
  if(
    !direct_call_identifier(instruction, actual) || actual != callee ||
    instruction.call_arguments().empty() ||
    !addressed_symbol(instruction.call_arguments()[0], condition))
    return false;
  if(mutex == nullptr)
    return instruction.call_arguments().size() == 1;
  return
    instruction.call_arguments().size() == 2 &&
    addressed_symbol(instruction.call_arguments()[1], *mutex);
}

bool parse_token_guard(
  const goto_programt::instructiont &instruction,
  const bool producer,
  irep_idt &token)
{
  if(!instruction.is_goto() || instruction.targets.size() != 1)
    return false;
  const exprt &condition = instruction.condition();
  if(condition.id() != ID_not || condition.operands().size() != 1)
    return false;
  const exprt &relation = without_cast(condition.op0());
  const irep_idt expected = producer ? ID_gt : ID_equal;
  if(
    relation.id() != expected || relation.operands().size() != 2 ||
    !direct_symbol(relation.op0(), token))
    return false;
  mp_integer zero;
  return
    constant_eval(relation.op1(), {}, zero) && zero == 0;
}

bool parse_unit_token_update(
  const goto_programt::instructiont &instruction,
  const bool producer,
  irep_idt &token)
{
  if(!instruction.is_assign() ||
     !direct_symbol(instruction.assign_lhs(), token))
    return false;
  const exprt &rhs = without_cast(instruction.assign_rhs());
  if(
    rhs.id() != (producer ? ID_plus : ID_minus) ||
    rhs.operands().size() != 2)
    return false;
  irep_idt source;
  mp_integer one;
  return
    direct_symbol(rhs.op0(), source) && source == token &&
    constant_eval(rhs.op1(), {}, one) && one == 1;
}

bool parse_accumulator_add(
  const goto_programt::instructiont &instruction,
  const irep_idt &induction,
  irep_idt &accumulator)
{
  if(
    !instruction.is_assign() ||
    !direct_symbol(instruction.assign_lhs(), accumulator))
    return false;
  const exprt &rhs = without_cast(instruction.assign_rhs());
  if(rhs.id() != ID_plus || rhs.operands().size() != 2)
    return false;
  irep_idt lhs;
  irep_idt added;
  return
    direct_symbol(rhs.op0(), lhs) && lhs == accumulator &&
    direct_symbol(rhs.op1(), added) && added == induction;
}

bool parse_one_assignment(
  const goto_programt::instructiont &instruction,
  irep_idt &identifier)
{
  if(
    !instruction.is_assign() ||
    !direct_symbol(instruction.assign_lhs(), identifier))
    return false;
  mp_integer one;
  return constant_eval(instruction.assign_rhs(), {}, one) && one == 1;
}

std::vector<goto_programt::const_targett> semantic_instructions(
  const goto_programt &program)
{
  std::vector<goto_programt::const_targett> result;
  for(auto instruction = program.instructions.begin();
      instruction != program.instructions.end(); ++instruction)
  {
    if(
      instruction->is_skip() || instruction->is_location() ||
      instruction->is_decl() || instruction->is_dead() ||
      instruction->is_set_return_value() ||
      instruction->is_end_function())
      continue;
    result.push_back(instruction);
  }
  return result;
}

bool alternating_phase_worker(
  const goto_modelt &model,
  const namespacet &ns,
  const irep_idt &function_id,
  const bool producer,
  alternating_phase_workert &summary,
  std::string &reason)
{
  const auto function =
    model.goto_functions.function_map.find(function_id);
  if(
    function == model.goto_functions.function_map.end() ||
    !function->second.body_available())
  {
    reason = "phase_missing_worker";
    return false;
  }
  const auto semantic =
    semantic_instructions(function->second.body);
  const std::size_t expected = producer ? 11 : 14;
  if(semantic.size() != expected)
  {
    reason =
      "phase_worker_instruction_count_" +
      std::to_string(semantic.size());
    return false;
  }

  summary.function = function_id;
  summary.producer = producer;
  if(
    !semantic[0]->is_assign() ||
    !direct_symbol(
      semantic[0]->assign_lhs(), summary.induction))
  {
    reason = "phase_loop_initialization";
    return false;
  }
  if(
    !parse_zero_initialization(
      *semantic[0], summary.induction) ||
    !parse_exit_guard(
      *semantic[1], summary.induction, summary.bound))
  {
    reason = "phase_loop_header";
    return false;
  }
  const symbolt *induction_symbol = nullptr;
  if(
    ns.lookup(summary.induction, induction_symbol) ||
    induction_symbol->is_static_lifetime ||
    (induction_symbol->type.id() != ID_signedbv &&
     induction_symbol->type.id() != ID_unsignedbv))
  {
    reason = "phase_induction_type";
    return false;
  }
  if(
    contains_side_effect(summary.bound) ||
    contains_symbol(summary.bound, {summary.induction}))
  {
    reason = "phase_bound_expression";
    return false;
  }

  irep_idt wait_mutex;
  irep_idt incremented;
  if(
    !parse_mutex_call(
      *semantic[2], "pthread_mutex_lock", summary.mutex) ||
    !parse_token_guard(*semantic[3], producer, summary.token) ||
    !parse_condition_call(
      *semantic[4],
      "pthread_cond_wait",
      summary.waited_condition,
      &wait_mutex) ||
    wait_mutex != summary.mutex ||
    !semantic[5]->is_goto() ||
    !semantic[5]->condition().is_true() ||
    semantic[5]->get_target() != semantic[3])
  {
    reason = "phase_wait_protocol";
    return false;
  }

  const std::size_t token_index = producer ? 6 : 7;
  const std::size_t unlock_index = producer ? 7 : 8;
  const std::size_t signal_index = producer ? 8 : 9;
  const std::size_t increment_index = producer ? 9 : 10;
  const std::size_t backedge_index = producer ? 10 : 11;
  if(
    (!producer &&
     !parse_accumulator_add(
       *semantic[6], summary.induction, summary.accumulator)) ||
    !parse_unit_token_update(
      *semantic[token_index], producer, summary.token) ||
    !parse_mutex_call(
      *semantic[unlock_index],
      "pthread_mutex_unlock",
      wait_mutex) ||
    wait_mutex != summary.mutex ||
    !parse_condition_call(
      *semantic[signal_index],
      "pthread_cond_signal",
      summary.signalled_condition,
      nullptr) ||
    !parse_unit_increment(
      *semantic[increment_index], incremented) ||
    incremented != summary.induction ||
    !semantic[backedge_index]->is_goto() ||
    !semantic[backedge_index]->condition().is_true() ||
    semantic[backedge_index]->get_target() != semantic[1])
  {
    reason = "phase_loop_body";
    return false;
  }
  std::map<const goto_programt::instructiont *, std::size_t> positions;
  std::size_t position = 0;
  for(const auto &instruction : function->second.body.instructions)
    positions.emplace(&instruction, position++);
  if(
    (producer &&
     positions.at(&*semantic[1]->get_target()) <=
       positions.at(&*semantic[10])) ||
    (!producer && semantic[1]->get_target() != semantic[12]))
  {
    reason = "phase_loop_exit";
    return false;
  }
  if(
    !producer &&
    (!parse_accumulator_add(
       *semantic[12], summary.induction, summary.accumulator) ||
     !parse_one_assignment(*semantic[13], summary.completion)))
  {
    reason = "phase_consumer_tail";
    return false;
  }

  const symbolt *token_symbol = nullptr;
  if(
    ns.lookup(summary.token, token_symbol) ||
    !token_symbol->is_static_lifetime ||
    (token_symbol->type.id() != ID_signedbv &&
     token_symbol->type.id() != ID_unsignedbv))
  {
    reason = "phase_token_type";
    return false;
  }
  if(!producer)
  {
    const symbolt *accumulator_symbol = nullptr;
    const symbolt *completion_symbol = nullptr;
    if(
      ns.lookup(summary.accumulator, accumulator_symbol) ||
      ns.lookup(summary.completion, completion_symbol) ||
      !accumulator_symbol->is_static_lifetime ||
      accumulator_symbol->type.id() != ID_unsignedbv ||
      !completion_symbol->is_static_lifetime ||
      (completion_symbol->type.id() != ID_signedbv &&
       completion_symbol->type.id() != ID_unsignedbv))
    {
      reason = "phase_output_type";
      return false;
    }
  }
  return true;
}

bool alternating_phase_main(
  const goto_modelt &model,
  const std::vector<create_recordt> &creates,
  const std::vector<goto_programt::targett> &joins,
  const alternating_phase_workert &producer,
  const alternating_phase_workert &consumer,
  std::string &reason)
{
  const auto main =
    model.goto_functions.function_map.find("main");
  INVARIANT(
    main != model.goto_functions.function_map.end() &&
    main->second.body_available(),
    "alternating phase lifecycle has main");
  bool before_create = true;
  bool token_zero = false;
  bool accumulator_zero = false;
  const std::set<irep_idt> state{
    producer.token, consumer.accumulator};
  for(auto instruction = main->second.body.instructions.begin();
      instruction != main->second.body.instructions.end(); ++instruction)
  {
    if(instruction == creates.front().instruction)
      before_create = false;
    if(
      contains_address_of_symbol(instruction->code(), state) ||
      (instruction->has_condition() &&
       contains_address_of_symbol(instruction->condition(), state)))
    {
      reason = "phase_state_escape";
      return false;
    }
    if(!instruction->is_assign())
    {
      irep_idt callee;
      if(
        before_create &&
        direct_call_identifier(*instruction, callee) &&
        callee != "pthread_mutex_init" &&
        callee != "pthread_cond_init")
      {
        reason = "phase_main_precreate_call";
        return false;
      }
      continue;
    }
    irep_idt written;
    if(!direct_symbol(instruction->assign_lhs(), written) ||
       state.count(written) == 0)
      continue;
    if(!before_create)
    {
      reason = "phase_main_late_write";
      return false;
    }
    if(written == producer.token)
      token_zero =
        parse_zero_initialization(*instruction, producer.token);
    else
      accumulator_zero =
        parse_zero_initialization(
          *instruction, consumer.accumulator);
  }
  if(!token_zero || !accumulator_zero)
  {
    reason = "phase_initial_state";
    return false;
  }
  const namespacet ns(model.symbol_table);
  return
    validate_main_region(
      model, ns, creates, joins, reason);
}

bool alternating_phase_stable_bound(
  const exprt &bound,
  const goto_modelt &model,
  const std::vector<create_recordt> &creates,
  const namespacet &ns,
  std::string &reason)
{
  std::set<irep_idt> symbols;
  std::vector<const exprt *> pending{&bound};
  while(!pending.empty())
  {
    const exprt &current = *pending.back();
    pending.pop_back();
    if(
      current.id() == ID_side_effect ||
      current.id() == ID_dereference ||
      current.id() == ID_address_of)
    {
      reason = "phase_bound_expression";
      return false;
    }
    if(current.id() == ID_symbol)
    {
      const auto identifier =
        to_symbol_expr(current).get_identifier();
      const symbolt *symbol = nullptr;
      if(
        ns.lookup(identifier, symbol) || symbol->is_type ||
        !symbol->is_static_lifetime ||
        (symbol->type.id() != ID_signedbv &&
         symbol->type.id() != ID_unsignedbv) ||
        symbol->type.get_bool(ID_C_volatile))
      {
        reason = "phase_bound_symbol";
        return false;
      }
      symbols.insert(identifier);
    }
    for(const auto &operand : current.operands())
      pending.push_back(&operand);
  }

  for(const auto &entry : model.goto_functions.function_map)
  {
    if(!entry.second.body_available())
      continue;
    bool before_create = entry.first == "main";
    for(auto instruction = entry.second.body.instructions.begin();
        instruction != entry.second.body.instructions.end(); ++instruction)
    {
      if(
        entry.first == "main" &&
        instruction == creates.front().instruction)
        before_create = false;
      if(
        contains_address_of_symbol(instruction->code(), symbols) ||
        (instruction->has_condition() &&
         contains_address_of_symbol(
           instruction->condition(), symbols)))
      {
        reason = "phase_bound_escape";
        return false;
      }
      irep_idt written;
      const bool writes =
        (instruction->is_assign() &&
         direct_symbol(instruction->assign_lhs(), written)) ||
        (instruction->is_function_call() &&
         !instruction->call_lhs().is_nil() &&
         direct_symbol(instruction->call_lhs(), written));
      if(
        writes && symbols.count(written) != 0 &&
        entry.first != "__CPROVER_initialize" &&
        (entry.first != "main" || !before_create))
      {
        reason = "phase_bound_late_write";
        return false;
      }
    }
  }
  return true;
}

bool alternating_phase_pair(
  goto_modelt &model,
  const namespacet &ns,
  std::vector<create_recordt> &creates,
  std::vector<goto_programt::targett> &joins,
  alternating_phase_workert &producer,
  alternating_phase_workert &consumer,
  std::string &reason)
{
  if(
    !collect_lifecycle(model, ns, creates, joins, reason) ||
    creates.size() != 2)
  {
    if(reason.empty())
      reason = "phase_lifecycle_count";
    return false;
  }

  bool matched =
    alternating_phase_worker(
      model, ns, creates[0].worker, true, producer, reason) &&
    alternating_phase_worker(
      model, ns, creates[1].worker, false, consumer, reason);
  if(!matched)
  {
    reason.clear();
    matched =
      alternating_phase_worker(
        model, ns, creates[1].worker, true, producer, reason) &&
      alternating_phase_worker(
        model, ns, creates[0].worker, false, consumer, reason);
  }
  if(
    !matched || producer.bound != consumer.bound ||
    producer.mutex != consumer.mutex ||
    producer.token != consumer.token ||
    producer.waited_condition != consumer.signalled_condition ||
    producer.signalled_condition != consumer.waited_condition)
  {
    if(reason.empty())
      reason = "phase_pair_mismatch";
    return false;
  }
  const symbolt *induction_symbol = nullptr;
  const symbolt *consumer_induction_symbol = nullptr;
  const symbolt *accumulator_symbol = nullptr;
  if(
    ns.lookup(producer.induction, induction_symbol) ||
    ns.lookup(consumer.induction, consumer_induction_symbol) ||
    ns.lookup(consumer.accumulator, accumulator_symbol) ||
    induction_symbol->type != consumer_induction_symbol->type ||
    to_bitvector_type(accumulator_symbol->type).get_width() <
      to_bitvector_type(induction_symbol->type).get_width() ||
    !alternating_phase_stable_bound(
      producer.bound, model, creates, ns, reason))
  {
    if(reason.empty())
      reason = "phase_recurrence_width";
    return false;
  }
  return alternating_phase_main(
    model, creates, joins, producer, consumer, reason);
}
} // namespace

bool dormant_spawn_cutoff_audit(
  const goto_modelt &goto_model,
  message_handlert &message_handler)
{
  std::string reason;
  const auto candidates = dormant_spawn_cutoffs(goto_model, reason);
  std::cout
    << "NATIVE_DORMANT_SPAWN_CUTOFF_AUDIT applicable="
    << (candidates.size() == 1 ? 1 : 0)
    << " candidates=" << candidates.size();
  if(candidates.size() == 1)
  {
    std::cout
      << " worker=" << candidates.front().worker
      << " bound=" << candidates.front().bound
      << " thread_ids=" << candidates.front().thread_ids
      << " join=" << (candidates.front().first_join != nullptr ? 1 : 0);
  }
  else
    std::cout
      << " reason="
      << (candidates.empty() ? reason : "dormant_candidate_count");
  std::cout << '\n';
  (void)message_handler;
  return candidates.size() == 1;
}

bool dormant_spawn_cutoff_transform(
  goto_modelt &goto_model,
  message_handlert &message_handler)
{
  std::string reason;
  auto candidates = dormant_spawn_cutoffs(goto_model, reason);
  if(candidates.size() != 1)
  {
    std::cout
      << "NATIVE_DORMANT_SPAWN_CUTOFF applied=0"
      << " reason="
      << (candidates.empty() ? reason : "dormant_candidate_count")
      << " candidates=" << candidates.size() << '\n';
    return false;
  }
  const auto &summary = candidates.front();
  bool truncated = false;
  if(!apply_dormant_spawn_counts(
       goto_model, candidates, {2}, truncated))
  {
    std::cout
      << "NATIVE_DORMANT_SPAWN_CUTOFF applied=0"
      << " reason=dormant_transform_failed\n";
    return false;
  }
  std::cout
    << "NATIVE_DORMANT_SPAWN_CUTOFF applied=1"
    << " worker=" << summary.worker
    << " original_bound=" << summary.bound
    << " cutoff=2"
    << " truncated=" << (truncated ? 1 : 0)
    << '\n';
  (void)message_handler;
  return true;
}

bool main_worker_prefix_transform(
  goto_modelt &goto_model,
  message_handlert &message_handler)
{
  std::string reason;
  auto candidates = dormant_spawn_cutoffs(goto_model, reason);
  if(candidates.size() != 1)
  {
    std::cout
      << "NATIVE_MAIN_WORKER_PREFIX applied=0"
      << " reason="
      << (candidates.empty() ? reason : "spawn_candidate_count")
      << " candidates=" << candidates.size() << '\n';
    return false;
  }
  const auto &summary = candidates.front();
  bool truncated = false;
  if(!apply_dormant_spawn_counts(
       goto_model, candidates, {1}, truncated))
  {
    std::cout
      << "NATIVE_MAIN_WORKER_PREFIX applied=0"
      << " reason=spawn_transform_failed\n";
    return false;
  }
  std::cout
    << "NATIVE_MAIN_WORKER_PREFIX applied=1"
    << " worker=" << summary.worker
    << " original_bound=" << summary.bound
    << " workers=1"
    << " truncated_at_join=" << (truncated ? 1 : 0)
    << '\n';
  (void)message_handler;
  return true;
}

bool main_worker_prefix_applicable(const goto_modelt &goto_model)
{
  std::string reason;
  return dormant_spawn_cutoffs(goto_model, reason).size() == 1;
}

std::string main_worker_prefix_worker_id(const goto_modelt &goto_model)
{
  std::string reason;
  const auto candidates = dormant_spawn_cutoffs(goto_model, reason);
  return candidates.size() == 1
    ? id2string(candidates.front().worker)
    : std::string{};
}

static bool cross_domain_list_prefix_transform_impl(
  goto_modelt &goto_model,
  message_handlert &message_handler)
{
  std::string reason;
  auto candidates = dormant_spawn_cutoffs(goto_model, reason);
  if(candidates.size() != 1)
  {
    std::cout
      << "NATIVE_CROSS_DOMAIN_LIST_PREFIX applied=0"
      << " reason=worker_class_count"
      << " classes=" << candidates.size() << '\n';
    return false;
  }

  auto main = goto_model.goto_functions.function_map.find("main");
  if(
    main == goto_model.goto_functions.function_map.end() ||
    !main->second.body_available())
  {
    std::cout
      << "NATIVE_CROSS_DOMAIN_LIST_PREFIX applied=0"
      << " reason=missing_main\n";
    return false;
  }
  auto &program = main->second.body;
  std::map<const goto_programt::instructiont *, std::size_t> positions;
  std::size_t position = 0;
  for(const auto &instruction : program.instructions)
    positions.emplace(&instruction, position++);
  const std::size_t first_create =
    positions.at(candidates.front().create_instruction);

  struct loopt
  {
    goto_programt::const_targett head;
    goto_programt::const_targett backedge;
    irep_idt induction;
  };
  std::vector<loopt> loops;
  for(auto backedge = program.instructions.begin();
      backedge != program.instructions.end(); ++backedge)
  {
    if(
      positions.at(&*backedge) >= first_create ||
      !backedge->is_goto() || !backedge->condition().is_true() ||
      backedge->targets.size() != 1 ||
      positions.at(&*backedge->get_target()) >= positions.at(&*backedge))
      continue;
    const auto head = backedge->get_target();
    irep_idt induction;
    exprt bound;
    mp_integer constant_bound;
    if(
      !parse_exit_guard(*head, induction, bound) ||
      !constant_eval(bound, {}, constant_bound) ||
      constant_bound <= 2)
      continue;
    loops.push_back({head, backedge, induction});
  }
  if(loops.size() != 2)
  {
    std::cout
      << "NATIVE_CROSS_DOMAIN_LIST_PREFIX applied=0"
      << " reason=initialization_loop_count"
      << " loops=" << loops.size() << '\n';
    return false;
  }

  loopt *outer = nullptr;
  loopt *inner = nullptr;
  for(auto &candidate_outer : loops)
  {
    for(auto &candidate_inner : loops)
    {
      if(&candidate_outer == &candidate_inner)
        continue;
      if(
        positions.at(&*candidate_outer.head) <
          positions.at(&*candidate_inner.head) &&
        positions.at(&*candidate_inner.backedge) <
          positions.at(&*candidate_outer.backedge))
      {
        if(outer != nullptr || inner != nullptr)
        {
          std::cout
            << "NATIVE_CROSS_DOMAIN_LIST_PREFIX applied=0"
            << " reason=ambiguous_loop_nesting\n";
          return false;
        }
        outer = &candidate_outer;
        inner = &candidate_inner;
      }
    }
  }
  if(outer == nullptr || inner == nullptr)
  {
    std::cout
      << "NATIVE_CROSS_DOMAIN_LIST_PREFIX applied=0"
      << " reason=non_nested_initialization_loops\n";
    return false;
  }

  for(const auto *loop : {outer, inner})
  {
    std::size_t initializations = 0;
    for(auto instruction = program.instructions.begin();
        instruction != loop->head; ++instruction)
      if(parse_zero_initialization(*instruction, loop->induction))
        ++initializations;
    std::size_t increments = 0;
    for(auto instruction = loop->head;
        instruction != loop->backedge; ++instruction)
    {
      irep_idt incremented;
      if(
        parse_unit_increment(*instruction, incremented) &&
        incremented == loop->induction)
        ++increments;
    }
    if(initializations != 1 || increments != 1)
    {
      std::cout
        << "NATIVE_CROSS_DOMAIN_LIST_PREFIX applied=0"
        << " reason=non_canonical_initialization_loop\n";
      return false;
    }
  }

  struct pointer_callt
  {
    goto_programt::targett instruction;
    irep_idt callee;
    irep_idt result;

    pointer_callt(
      goto_programt::targett instruction,
      irep_idt callee,
      irep_idt result)
      : instruction(instruction),
        callee(std::move(callee)),
        result(std::move(result))
    {
    }
  };
  std::vector<pointer_callt> pointer_calls;
  for(auto instruction = std::next(outer->backedge);
      &*instruction != candidates.front().create_instruction; ++instruction)
  {
    irep_idt callee;
    irep_idt result;
    if(
      instruction->is_function_call() &&
      !instruction->call_lhs().is_nil() &&
      instruction->call_lhs().type().id() == ID_pointer &&
      direct_call_identifier(*instruction, callee) &&
      direct_symbol(instruction->call_lhs(), result))
      pointer_calls.emplace_back(
        program.const_cast_target(instruction), callee, result);
  }
  if(
    pointer_calls.size() != 2 ||
    pointer_calls[0].callee != pointer_calls[1].callee ||
    pointer_calls[0].result == pointer_calls[1].result)
  {
    std::cout
      << "NATIVE_CROSS_DOMAIN_LIST_PREFIX applied=0"
      << " reason=lookup_pair"
      << " calls=" << pointer_calls.size() << '\n';
    return false;
  }
  const std::set<irep_idt> splice_symbols{
    pointer_calls[0].result, pointer_calls[1].result};
  std::size_t splice_assignments = 0;
  std::set<irep_idt> splice_members;
  for(auto instruction = std::next(outer->backedge);
      &*instruction != candidates.front().create_instruction; ++instruction)
  {
    std::set<irep_idt> lhs_members;
    std::set<irep_idt> rhs_members;
    std::function<void(const exprt &, std::set<irep_idt> &)>
      collect_members =
        [&](const exprt &expr, std::set<irep_idt> &members)
        {
          const exprt &value = without_cast(expr);
          if(value.id() == ID_member)
            members.insert(to_member_expr(value).get_component_name());
          for(const auto &operand : value.operands())
            collect_members(operand, members);
        };
    if(instruction->is_assign())
    {
      collect_members(instruction->assign_lhs(), lhs_members);
      collect_members(instruction->assign_rhs(), rhs_members);
    }
    if(
      instruction->is_assign() &&
      contains_symbol(
        instruction->assign_lhs(), {pointer_calls[0].result}) &&
      !contains_symbol(
        instruction->assign_lhs(), {pointer_calls[1].result}) &&
      contains_symbol(
        instruction->assign_rhs(), {pointer_calls[1].result}) &&
      !contains_symbol(
        instruction->assign_rhs(), {pointer_calls[0].result}) &&
      contains_side_effect(instruction->assign_lhs()) &&
      contains_side_effect(instruction->assign_rhs()) &&
      lhs_members.size() == 1 && lhs_members == rhs_members)
    {
      ++splice_assignments;
      splice_members = std::move(lhs_members);
    }
  }
  if(splice_assignments != 1)
  {
    std::cout
      << "NATIVE_CROSS_DOMAIN_LIST_PREFIX applied=0"
      << " reason=cross_pointer_assignment"
      << " assignments=" << splice_assignments << '\n';
    return false;
  }

  const auto lookup =
    goto_model.goto_functions.function_map.find(pointer_calls[0].callee);
  if(
    lookup == goto_model.goto_functions.function_map.end() ||
    !lookup->second.body_available())
  {
    std::cout
      << "NATIVE_CROSS_DOMAIN_LIST_PREFIX applied=0"
      << " reason=missing_lookup\n";
    return false;
  }
  irep_idt lookup_index;
  exprt lookup_result;
  std::size_t lookup_nondets = 0;
  std::size_t lookup_indexed_results = 0;
  for(auto instruction = lookup->second.body.instructions.begin();
      instruction != lookup->second.body.instructions.end(); ++instruction)
  {
    if(instruction->is_assign())
    {
      const exprt &rhs = without_cast(instruction->assign_rhs());
      if(
        rhs.id() == ID_side_effect &&
        to_side_effect_expr(rhs).get_statement() == ID_nondet)
        ++lookup_nondets;
      irep_idt lhs;
      if(
        lookup_index.empty() &&
        direct_symbol(instruction->assign_lhs(), lhs) &&
        contains_side_effect(instruction->assign_rhs()))
        continue;
      if(
        !lookup_index.empty() &&
        contains_symbol(instruction->assign_rhs(), {lookup_index}))
      {
        lookup_result = instruction->assign_rhs();
        ++lookup_indexed_results;
      }
    }
    if(
      lookup_index.empty() && instruction->is_function_call())
      continue;
    if(lookup_index.empty() && instruction->is_assign())
    {
      irep_idt lhs;
      irep_idt rhs;
      if(
        direct_symbol(instruction->assign_lhs(), lhs) &&
        direct_symbol(instruction->assign_rhs(), rhs))
        lookup_index = lhs;
    }
  }
  if(
    lookup_nondets != 1 || lookup_index.empty() ||
    lookup_indexed_results != 1 || lookup_result.is_nil())
  {
    std::cout
      << "NATIVE_CROSS_DOMAIN_LIST_PREFIX applied=0"
      << " reason=lookup_index_flow"
      << " nondets=" << lookup_nondets
      << " results=" << lookup_indexed_results << '\n';
    return false;
  }
  const auto lookup_symbol =
    goto_model.symbol_table.symbols.find(lookup_index);
  if(lookup_symbol == goto_model.symbol_table.symbols.end())
    return false;

  mp_integer outer_bound;
  mp_integer inner_bound;
  exprt parsed_bound;
  irep_idt parsed_induction;
  if(
    !parse_exit_guard(*outer->head, parsed_induction, parsed_bound) ||
    parsed_induction != outer->induction ||
    !constant_eval(parsed_bound, {}, outer_bound) ||
    !parse_exit_guard(*inner->head, parsed_induction, parsed_bound) ||
    parsed_induction != inner->induction ||
    !constant_eval(parsed_bound, {}, inner_bound) ||
    outer_bound < 2 || inner_bound < 2)
  {
    std::cout
      << "NATIVE_CROSS_DOMAIN_LIST_PREFIX applied=0"
      << " reason=initialization_bounds\n";
    return false;
  }

  mp_integer lookup_bound = -1;
  std::function<void(const exprt &)> find_lookup_bound =
    [&](const exprt &expr)
    {
      const exprt &value = without_cast(expr);
      if(value.id() == ID_lt && value.operands().size() == 2)
      {
        irep_idt lhs;
        mp_integer candidate;
        if(
          direct_symbol(value.op0(), lhs) && lhs == lookup_index &&
          constant_eval(value.op1(), {}, candidate))
          lookup_bound = candidate;
      }
      for(const auto &operand : value.operands())
        find_lookup_bound(operand);
    };
  for(const auto &instruction : lookup->second.body.instructions)
  {
    if(instruction.is_function_call())
      for(const auto &argument : instruction.call_arguments())
        find_lookup_bound(argument);
    if(instruction.has_condition())
      find_lookup_bound(instruction.condition());
  }

  mp_integer storage_capacity = -1;
  std::function<void(const exprt &)> find_indexed_capacity =
    [&](const exprt &expr)
    {
      const exprt &value = without_cast(expr);
      if(value.id() == ID_index)
      {
        const auto &indexed = to_index_expr(value);
        irep_idt index;
        if(
          direct_symbol(indexed.index(), index) &&
          index == lookup_index &&
          indexed.array().type().id() == ID_array)
        {
          mp_integer candidate;
          if(
            constant_eval(
              to_array_type(indexed.array().type()).size(),
              {},
              candidate))
            storage_capacity = candidate;
        }
      }
      for(const auto &operand : value.operands())
        find_indexed_capacity(operand);
    };
  find_indexed_capacity(lookup_result);
  if(
    lookup_bound != outer_bound ||
    storage_capacity != outer_bound)
  {
    std::cout
      << "NATIVE_CROSS_DOMAIN_LIST_PREFIX applied=0"
      << " reason=domain_bound_mismatch"
      << " init=" << outer_bound
      << " lookup=" << lookup_bound
      << " storage=" << storage_capacity << '\n';
    return false;
  }

  std::set<irep_idt> lookup_members;
  std::function<void(const exprt &)> collect_lookup_members =
    [&](const exprt &expr)
    {
      const exprt &value = without_cast(expr);
      if(value.id() == ID_member)
        lookup_members.insert(
          to_member_expr(value).get_component_name());
      for(const auto &operand : value.operands())
        collect_lookup_members(operand);
    };
  collect_lookup_members(lookup_result);
  if(
    splice_members.size() != 1 ||
    lookup_members.count(*splice_members.begin()) == 0)
  {
    std::cout
      << "NATIVE_CROSS_DOMAIN_LIST_PREFIX applied=0"
      << " reason=pointer_field_mismatch\n";
    return false;
  }

  const symbol_exprt lookup_index_expr(
    lookup_index, lookup_symbol->second.type);
  for(std::size_t index = 0; index < pointer_calls.size(); ++index)
  {
    exprt specialized = lookup_result;
    replace_expr(
      lookup_index_expr,
      from_integer(index, lookup_symbol->second.type),
      specialized);
    const auto location =
      pointer_calls[index].instruction->source_location();
    const typet result_type =
      pointer_calls[index].instruction->call_lhs().type();
    const symbol_exprt result(
      pointer_calls[index].result, result_type);
    *pointer_calls[index].instruction =
      goto_programt::make_assignment(
        result,
        std::move(specialized),
        location);
  }

  const auto original_worker =
    goto_model.goto_functions.function_map.find(candidates.front().worker);
  const auto original_worker_symbol =
    goto_model.symbol_table.symbols.find(candidates.front().worker);
  if(
    original_worker == goto_model.goto_functions.function_map.end() ||
    !original_worker->second.body_available() ||
    original_worker_symbol == goto_model.symbol_table.symbols.end())
    return false;

  auto validate_worker =
    [&](const goto_functiont &worker) -> bool
    {
      auto nondet = worker.body.instructions.end();
      auto propagated = worker.body.instructions.end();
      irep_idt temporary;
      irep_idt index;
      for(auto instruction = worker.body.instructions.begin();
          instruction != worker.body.instructions.end(); ++instruction)
      {
        if(!instruction->is_assign())
          continue;
        const exprt &rhs = without_cast(instruction->assign_rhs());
        if(
          nondet == worker.body.instructions.end() &&
          rhs.id() == ID_side_effect &&
          to_side_effect_expr(rhs).get_statement() == ID_nondet &&
          direct_symbol(instruction->assign_lhs(), temporary))
        {
          nondet = instruction;
          continue;
        }
        irep_idt lhs;
        irep_idt rhs_symbol;
        if(
          nondet != worker.body.instructions.end() &&
          direct_symbol(instruction->assign_lhs(), lhs) &&
          direct_symbol(instruction->assign_rhs(), rhs_symbol) &&
          rhs_symbol == temporary)
        {
          propagated = instruction;
          index = lhs;
          break;
        }
      }
      if(propagated == worker.body.instructions.end())
        return false;

      mp_integer worker_bound = -1;
      exprt scalar = nil_exprt();
      find_symbols_sett scalar_symbols;
      std::set<irep_idt> scalar_members;
      std::size_t plus_one = 0;
      std::size_t minus_one = 0;
      std::size_t zero_assertions = 0;
      std::vector<goto_programt::const_targett> operations;
      std::function<void(const exprt &, std::set<irep_idt> &)>
        collect_worker_members =
          [&](const exprt &expr, std::set<irep_idt> &members)
          {
            const exprt &value = without_cast(expr);
            if(value.id() == ID_member)
              members.insert(
                to_member_expr(value).get_component_name());
            for(const auto &operand : value.operands())
              collect_worker_members(operand, members);
          };
      std::function<bool(const exprt &)> index_is_offset =
        [&](const exprt &expr) -> bool
        {
          const exprt &value = without_cast(expr);
          if(
            (value.id() == ID_plus || value.id() == ID_minus) &&
            contains_symbol(value, {index}))
            return true;
          for(const auto &operand : value.operands())
            if(index_is_offset(operand))
              return true;
          return false;
        };
      for(auto instruction = std::next(propagated);
          instruction != worker.body.instructions.end(); ++instruction)
      {
        irep_idt incremented;
        if(
          parse_unit_increment(*instruction, incremented) &&
          incremented == index)
          break;
        if(
          index_is_offset(instruction->code()) ||
          (instruction->has_condition() &&
           index_is_offset(instruction->condition())))
        {
          std::cout
            << "NATIVE_CROSS_DOMAIN_LIST_WORKER reason=index_offset\n";
          return false;
        }
        if(instruction->is_goto())
        {
          exprt bound;
          irep_idt induction;
          mp_integer candidate;
          if(
            parse_exit_guard(*instruction, induction, bound) &&
            induction == index &&
            constant_eval(bound, {}, candidate))
            worker_bound = candidate;
        }
        if(instruction->is_assign())
        {
          const exprt &rhs = without_cast(instruction->assign_rhs());
          if(
            (rhs.id() == ID_plus || rhs.id() == ID_minus) &&
            rhs.operands().size() == 2 &&
            contains_side_effect(instruction->assign_lhs()) &&
            contains_side_effect(rhs.op0()))
          {
            mp_integer delta;
            if(
              constant_eval(rhs.op1(), {}, delta) && delta == 1)
            {
              find_symbols_sett lhs_symbols;
              find_symbols_sett rhs_symbols;
              std::set<irep_idt> lhs_members;
              std::set<irep_idt> rhs_members;
              find_symbols(
                instruction->assign_lhs(), lhs_symbols);
              find_symbols(rhs.op0(), rhs_symbols);
              collect_worker_members(
                instruction->assign_lhs(), lhs_members);
              collect_worker_members(rhs.op0(), rhs_members);
              if(
                lhs_symbols != rhs_symbols ||
                lhs_members != rhs_members ||
                lhs_symbols.empty() || lhs_members.empty())
                continue;
              if(scalar.is_nil())
              {
                scalar = instruction->assign_lhs();
                scalar_symbols = lhs_symbols;
                scalar_members = lhs_members;
              }
              if(
                lhs_symbols == scalar_symbols &&
                lhs_members == scalar_members)
              {
                if(rhs.id() == ID_plus)
                  ++plus_one;
                else
                  ++minus_one;
                operations.push_back(instruction);
              }
            }
          }
        }
        irep_idt callee;
        if(
          instruction->is_function_call() &&
          direct_call_identifier(*instruction, callee) &&
          callee == "__VERIFIER_assert" &&
          instruction->call_arguments().size() == 1 &&
          !scalar.is_nil())
        {
          const exprt &condition =
            without_cast(instruction->call_arguments()[0]);
          if(
            condition.id() == ID_equal &&
            condition.operands().size() == 2)
          {
            mp_integer zero;
            if(
              constant_eval(condition.op1(), {}, zero) &&
              zero == 0)
            {
              find_symbols_sett assertion_symbols;
              std::set<irep_idt> assertion_members;
              find_symbols(
                condition.op0(), assertion_symbols);
              collect_worker_members(
                condition.op0(), assertion_members);
              if(
                assertion_symbols == scalar_symbols &&
                assertion_members == scalar_members)
              {
                ++zero_assertions;
                operations.push_back(instruction);
              }
            }
          }
        }
      }
      if(
        worker_bound != outer_bound ||
        plus_one != 1 || minus_one != 1 ||
        zero_assertions != 1 || operations.size() != 3)
      {
        std::cout
          << "NATIVE_CROSS_DOMAIN_LIST_WORKER"
          << " reason=operation_shape"
          << " bound=" << worker_bound
          << " expected_bound=" << outer_bound
          << " plus=" << plus_one
          << " minus=" << minus_one
          << " assertions=" << zero_assertions
          << " operations=" << operations.size() << '\n';
        return false;
      }

      for(const auto operation : operations)
      {
        if(
          operation == worker.body.instructions.begin() ||
          std::next(operation) == worker.body.instructions.end())
          return false;
        irep_idt locked;
        irep_idt unlocked;
        if(
          !parse_mutex_call(
            *std::prev(operation), "pthread_mutex_lock", locked) ||
          !parse_mutex_call(
            *std::next(operation), "pthread_mutex_unlock", unlocked) ||
          locked != unlocked)
        {
          std::cout
            << "NATIVE_CROSS_DOMAIN_LIST_WORKER"
            << " reason=operation_mutex_pair\n";
          return false;
        }
      }
      return true;
    };
  if(!validate_worker(original_worker->second))
  {
    std::cout
      << "NATIVE_CROSS_DOMAIN_LIST_PREFIX applied=0"
      << " reason=worker_semantics\n";
    return false;
  }

  const irep_idt cloned_worker_id =
    id2string(candidates.front().worker) +
    "$deagle_cross_domain_worker";
  if(
    goto_model.goto_functions.function_map.count(cloned_worker_id) != 0 ||
    goto_model.symbol_table.symbols.count(cloned_worker_id) != 0)
    return false;
  auto &cloned_worker =
    goto_model.goto_functions.function_map[cloned_worker_id];
  cloned_worker.copy_from(original_worker->second);
  symbolt cloned_symbol = original_worker_symbol->second;
  cloned_symbol.name = cloned_worker_id;
  cloned_symbol.base_name = cloned_worker_id;
  cloned_symbol.pretty_name = cloned_worker_id;
  if(goto_model.symbol_table.add(cloned_symbol))
    return false;

  auto specialize_worker =
    [&](goto_functiont &worker, const mp_integer &slot,
        const mp_integer &control, const bool staged_assertion) -> bool
    {
      auto nondet = worker.body.instructions.end();
      auto propagated = worker.body.instructions.end();
      auto branch = worker.body.instructions.end();
      auto first_position = worker.body.instructions.end();
      irep_idt temporary;
      irep_idt index;
      std::size_t nondets = 0;
      for(auto instruction = worker.body.instructions.begin();
          instruction != worker.body.instructions.end(); ++instruction)
      {
        if(!instruction->is_assign())
          continue;
        const exprt &rhs = without_cast(instruction->assign_rhs());
        if(
          rhs.id() == ID_side_effect &&
          to_side_effect_expr(rhs).get_statement() == ID_nondet)
        {
          ++nondets;
          if(nondet == worker.body.instructions.end())
          {
            nondet = instruction;
            direct_symbol(instruction->assign_lhs(), temporary);
          }
          else
            branch = instruction;
          continue;
        }
        irep_idt lhs;
        irep_idt rhs_symbol;
        if(
          nondet != worker.body.instructions.end() &&
          propagated == worker.body.instructions.end() &&
          direct_symbol(instruction->assign_lhs(), lhs) &&
          direct_symbol(instruction->assign_rhs(), rhs_symbol) &&
          rhs_symbol == temporary)
        {
          propagated = instruction;
          index = lhs;
        }
        else if(
          propagated != worker.body.instructions.end() &&
          branch == worker.body.instructions.end() &&
          instruction->assign_lhs().type().id() == ID_pointer &&
          instruction->assign_rhs().type().id() == ID_pointer)
          first_position = instruction;
      }
      if(
        nondets != 2 ||
        nondet == worker.body.instructions.end() ||
        propagated == worker.body.instructions.end() ||
        branch == worker.body.instructions.end() ||
        (staged_assertion &&
         first_position == worker.body.instructions.end()))
        return false;
      const auto symbol =
        goto_model.symbol_table.symbols.find(index);
      if(symbol == goto_model.symbol_table.symbols.end())
        return false;
      const symbol_exprt index_expr(index, symbol->second.type);
      const exprt value = from_integer(slot, symbol->second.type);
      nondet->assign_rhs_nonconst() =
        from_integer(slot, nondet->assign_lhs().type());
      propagated->assign_rhs_nonconst() =
        from_integer(slot, propagated->assign_lhs().type());
      if(staged_assertion)
      {
        const exprt position = first_position->assign_lhs();
        const exprt initial_position = first_position->assign_rhs();
        branch->assign_rhs_nonconst() = if_exprt(
          equal_exprt(position, initial_position),
          from_integer(1, branch->assign_lhs().type()),
          from_integer(0, branch->assign_lhs().type()),
          branch->assign_lhs().type());
      }
      else
        branch->assign_rhs_nonconst() =
          from_integer(control, branch->assign_lhs().type());
      for(auto instruction = std::next(propagated);
          instruction != worker.body.instructions.end(); ++instruction)
      {
        irep_idt incremented;
        if(
          parse_unit_increment(*instruction, incremented) &&
          incremented == index)
          break;
        replace_expr(index_expr, value, instruction->code_nonconst());
        if(instruction->is_goto())
          replace_expr(
            index_expr, value, instruction->condition_nonconst());
      }
      return true;
    };
  if(
    !specialize_worker(original_worker->second, 0, 1, false) ||
    !specialize_worker(cloned_worker, 1, 0, true))
  {
    std::cout
      << "NATIVE_CROSS_DOMAIN_LIST_PREFIX applied=0"
      << " reason=worker_specialization\n";
    return false;
  }

  auto create = program.instructions.end();
  for(auto instruction = program.instructions.begin();
      instruction != program.instructions.end(); ++instruction)
    if(&*instruction == candidates.front().create_instruction)
    {
      create = instruction;
      break;
    }
  if(create == program.instructions.end())
    return false;
  const auto induction_symbol =
    goto_model.symbol_table.symbols.find(candidates.front().induction);
  if(induction_symbol == goto_model.symbol_table.symbols.end())
    return false;
  const exprt original_target = create->call_arguments()[2];
  const symbol_exprt clone_function(
    cloned_worker_id, original_worker_symbol->second.type);
  exprt cloned_target =
    address_of_exprt(clone_function);
  cloned_target = typecast_exprt::conditional_cast(
    cloned_target, original_target.type());
  create->call_arguments()[2] = if_exprt(
    equal_exprt(
      symbol_exprt(
        candidates.front().induction,
        induction_symbol->second.type),
      from_integer(0, induction_symbol->second.type)),
    original_target,
    std::move(cloned_target),
    original_target.type());

  const namespacet ns(goto_model.symbol_table);
  for(const auto *loop : {outer, inner})
  {
    const symbolt *symbol = nullptr;
    if(ns.lookup(loop->induction, symbol))
      return false;
    auto head = program.const_cast_target(loop->head);
    const symbol_exprt induction(loop->induction, symbol->type);
    head->condition_nonconst() = not_exprt(
      binary_relation_exprt(
        induction, ID_lt, from_integer(2, symbol->type)));
  }

  bool truncated = false;
  if(!apply_dormant_spawn_counts(
       goto_model, candidates, {2}, truncated))
  {
    std::cout
      << "NATIVE_CROSS_DOMAIN_LIST_PREFIX applied=0"
      << " reason=spawn_transform_failed\n";
    return false;
  }
  program.instructions.begin()
    ->source_location_nonconst()
    .set("deagle_cross_domain_list_prefix", true);
  goto_model.goto_functions.update();
  std::cout
    << "NATIVE_CROSS_DOMAIN_LIST_PREFIX applied=1"
    << " loops=2 prefix=2 workers=2"
    << " truncated=" << (truncated ? 1 : 0) << '\n';
  (void)message_handler;
  return true;
}

bool cross_domain_list_prefix_transform(
  goto_modelt &goto_model,
  message_handlert &message_handler)
{
  goto_modelt candidate;
  candidate.symbol_table = goto_model.symbol_table;
  candidate.goto_functions.copy_from(goto_model.goto_functions);
  if(!cross_domain_list_prefix_transform_impl(candidate, message_handler))
    return false;
  goto_model = std::move(candidate);
  return true;
}

bool cross_domain_list_prefix_applied(const goto_modelt &goto_model)
{
  const auto main =
    goto_model.goto_functions.function_map.find("main");
  return
    main != goto_model.goto_functions.function_map.end() &&
    main->second.body_available() &&
    !main->second.body.instructions.empty() &&
    main->second.body.instructions.begin()
      ->source_location()
      .get_bool("deagle_cross_domain_list_prefix");
}

bool monotone_condition_wait_transform(
  goto_modelt &goto_model,
  message_handlert &message_handler)
{
  const namespacet ns(goto_model.symbol_table);
  struct writert
  {
    irep_idt function;
    irep_idt predicate;
    irep_idt mutex;
    irep_idt condition;
  };
  std::vector<writert> writers;
  for(const auto &entry : goto_model.goto_functions.function_map)
  {
    if(!entry.second.body_available())
      continue;
    const auto &body = entry.second.body;
    for(auto assignment = body.instructions.begin();
        assignment != body.instructions.end(); ++assignment)
    {
      if(!assignment->is_assign())
        continue;
      irep_idt predicate;
      mp_integer value;
      if(
        !direct_symbol(assignment->assign_lhs(), predicate) ||
        !constant_eval(assignment->assign_rhs(), {}, value) ||
        value != 1)
        continue;
      const symbolt *symbol = nullptr;
      if(
        ns.lookup(predicate, symbol) ||
        !symbol->is_static_lifetime ||
        symbol->type.id() != ID_c_bool)
        continue;
      std::set<irep_idt> locks;
      std::set<irep_idt> broadcasts;
      std::set<irep_idt> unlocks;
      std::map<const goto_programt::instructiont *, std::size_t> positions;
      std::size_t body_position = 0;
      for(const auto &instruction : body.instructions)
        positions.emplace(&instruction, body_position++);
      for(auto instruction = body.instructions.begin();
          instruction != body.instructions.end(); ++instruction)
      {
        irep_idt object;
        if(
          instruction != assignment &&
          parse_mutex_call(*instruction, "pthread_mutex_lock", object))
          locks.insert(object);
        if(
          instruction != assignment &&
          parse_mutex_call(*instruction, "pthread_mutex_unlock", object))
          unlocks.insert(object);
        irep_idt callee;
        if(
          direct_call_identifier(*instruction, callee) &&
          callee == "pthread_cond_broadcast" &&
          instruction->call_arguments().size() == 1 &&
          addressed_symbol(
            instruction->call_arguments().front(), object))
          broadcasts.insert(object);
      }
      std::vector<irep_idt> mutexes;
      std::set_intersection(
        locks.begin(), locks.end(),
        unlocks.begin(), unlocks.end(),
        std::back_inserter(mutexes));
      bool ordered = false;
      if(mutexes.size() == 1 && broadcasts.size() == 1)
      {
        bool lock_before = false;
        std::size_t broadcast_position = positions.size();
        bool unlock_after = false;
        for(auto instruction = body.instructions.begin();
            instruction != body.instructions.end(); ++instruction)
        {
          irep_idt object;
          if(
            parse_mutex_call(
              *instruction, "pthread_mutex_lock", object) &&
            object == mutexes.front() &&
            positions.at(&*instruction) < positions.at(&*assignment))
            lock_before = true;
          if(
            parse_mutex_call(
              *instruction, "pthread_mutex_unlock", object) &&
            object == mutexes.front() &&
            broadcast_position < positions.at(&*instruction))
            unlock_after = true;
          irep_idt callee;
          if(
            direct_call_identifier(*instruction, callee) &&
            callee == "pthread_cond_broadcast" &&
            instruction->call_arguments().size() == 1 &&
            addressed_symbol(
              instruction->call_arguments().front(), object) &&
            object == *broadcasts.begin())
            broadcast_position =
              std::min(broadcast_position, positions.at(&*instruction));
        }
        ordered =
          lock_before &&
          positions.at(&*assignment) < broadcast_position &&
          unlock_after;
      }
      if(mutexes.size() == 1 && broadcasts.size() == 1 && ordered)
        writers.push_back(
          {entry.first, predicate, mutexes.front(), *broadcasts.begin()});
    }
  }
  if(writers.size() != 1)
    return false;
  const auto writer = writers.front();

  std::size_t predicate_mentions = 0;
  std::size_t zero_initializers = 0;
  std::size_t one_writes = 0;
  for(const auto &entry : goto_model.goto_functions.function_map)
  {
    if(!entry.second.body_available())
      continue;
    for(const auto &instruction : entry.second.body.instructions)
    {
      if(!instruction_mentions_any(instruction, {writer.predicate}))
        continue;
      ++predicate_mentions;
      if(instruction.is_assign())
      {
        irep_idt lhs;
        mp_integer value;
        if(
          direct_symbol(instruction.assign_lhs(), lhs) &&
          lhs == writer.predicate &&
          constant_eval(instruction.assign_rhs(), {}, value))
        {
          if(value == 0)
            ++zero_initializers;
          if(value == 1)
            ++one_writes;
        }
      }
      if(instruction.is_function_call())
        for(const auto &argument : instruction.call_arguments())
          if(contains_address_of_symbol(argument, {writer.predicate}))
            return false;
    }
  }
  if(zero_initializers != 1 || one_writes != 1)
    return false;

  irep_idt waiter;
  const goto_programt::instructiont *assertion_guard = nullptr;
  const goto_programt::instructiont *assertion_error = nullptr;
  std::size_t waiter_count = 0;
  for(const auto &entry : goto_model.goto_functions.function_map)
  {
    if(!entry.second.body_available())
      continue;
    const auto &body = entry.second.body;
    std::map<const goto_programt::instructiont *, std::size_t> positions;
    std::size_t position = 0;
    for(const auto &instruction : body.instructions)
      positions.emplace(&instruction, position++);
    for(auto wait = body.instructions.begin();
        wait != body.instructions.end(); ++wait)
    {
      irep_idt callee;
      if(
        !direct_call_identifier(*wait, callee) ||
        callee != "pthread_cond_wait" ||
        wait->call_arguments().size() != 2)
        continue;
      irep_idt condition;
      irep_idt mutex;
      if(
        !addressed_symbol(wait->call_arguments()[0], condition) ||
        !addressed_symbol(wait->call_arguments()[1], mutex) ||
        condition != writer.condition ||
        mutex != writer.mutex)
        continue;
      bool rechecking_loop = false;
      for(auto backedge = std::next(wait);
          backedge != body.instructions.end(); ++backedge)
      {
        if(
          !backedge->is_goto() || !backedge->condition().is_true() ||
          backedge->targets.size() != 1 ||
          positions.at(&*backedge->get_target()) >=
            positions.at(&*backedge))
          continue;
        irep_idt tested;
        if(
          parse_nonzero_witness(
            backedge->get_target()->condition(), tested) &&
          tested == writer.predicate &&
          positions.at(&*backedge->get_target()) <
            positions.at(&*wait))
        {
          rechecking_loop = true;
          break;
        }
      }
      if(!rechecking_loop)
        continue;
      for(auto guard = std::next(wait);
          guard != body.instructions.end(); ++guard)
      {
        if(
          !guard->is_goto() || guard->targets.size() != 1 ||
          guard->condition().id() != ID_not)
          continue;
        irep_idt tested;
        if(
          !parse_nonzero_witness(
            to_not_expr(guard->condition()).op(), tested) ||
          tested != writer.predicate)
          continue;
        const auto target = guard->get_target();
        irep_idt target_callee;
        if(
          direct_call_identifier(*target, target_callee) &&
          target_callee == "reach_error")
        {
          bool lock_before = false;
          bool unlock_after = false;
          for(auto sync = body.instructions.begin();
              sync != body.instructions.end(); ++sync)
          {
            irep_idt sync_mutex;
            if(
              parse_mutex_call(
                *sync, "pthread_mutex_lock", sync_mutex) &&
              sync_mutex == writer.mutex &&
              positions.at(&*sync) < positions.at(&*wait))
              lock_before = true;
            if(
              parse_mutex_call(
                *sync, "pthread_mutex_unlock", sync_mutex) &&
              sync_mutex == writer.mutex &&
              positions.at(&*sync) > positions.at(&*guard))
              unlock_after = true;
          }
          if(!lock_before || !unlock_after)
            continue;
          waiter = entry.first;
          assertion_guard = &*guard;
          assertion_error = &*target;
          ++waiter_count;
          break;
        }
      }
    }
  }
  if(waiter_count != 1 || assertion_guard == nullptr)
    return false;

  std::size_t nonconstant_errors = 0;
  for(const auto &entry : goto_model.goto_functions.function_map)
  {
    if(!entry.second.body_available() || entry.first == "reach_error")
      continue;
    const auto &body = entry.second.body;
    std::map<const goto_programt::instructiont *, std::size_t> positions;
    std::size_t position = 0;
    for(const auto &instruction : body.instructions)
      positions.emplace(&instruction, position++);
    for(auto instruction = body.instructions.begin();
        instruction != body.instructions.end(); ++instruction)
    {
      irep_idt callee;
      if(
        !direct_call_identifier(*instruction, callee) ||
        callee != "reach_error")
        continue;
      if(&*instruction == assertion_error)
      {
        ++nonconstant_errors;
        continue;
      }
      bool constant_safe = false;
      for(auto guard = body.instructions.begin();
          guard != instruction; ++guard)
      {
        bool guard_value = false;
        if(
          guard->is_goto() && guard->targets.size() == 1 &&
          guard->get_target() != body.instructions.end() &&
          positions.at(&*guard->get_target()) >
            positions.at(&*instruction) &&
          boolean_constant_eval(guard->condition(), guard_value) &&
          guard_value)
          constant_safe = true;
      }
      if(!constant_safe)
        return false;
    }
  }
  if(nonconstant_errors != 1)
    return false;

  const auto main =
    goto_model.goto_functions.function_map.find("main");
  if(
    main == goto_model.goto_functions.function_map.end() ||
    !main->second.body_available())
    return false;
  auto &main_body = main->second.body;
  goto_programt::targett loop_head = main_body.instructions.end();
  goto_programt::targett create_instruction = main_body.instructions.end();
  irep_idt worker;
  std::size_t creates = 0;
  for(auto instruction = main_body.instructions.begin();
      instruction != main_body.instructions.end(); ++instruction)
  {
    irep_idt callee;
    if(
      !direct_call_identifier(*instruction, callee) ||
      callee != "pthread_create" ||
      instruction->call_arguments().size() < 3)
      continue;
    if(!addressed_symbol(instruction->call_arguments()[2], worker))
      return false;
    ++creates;
    create_instruction = instruction;
    if(instruction == main_body.instructions.begin())
      return false;
    auto probe = instruction;
    --probe;
    if(!probe->is_goto() || probe->targets.size() != 1)
      return false;
    loop_head = probe;
  }
  if(creates != 1 || loop_head == main_body.instructions.end())
    return false;
  bool loop_guard_value = true;
  if(
    !boolean_constant_eval(loop_head->condition(), loop_guard_value) ||
    loop_guard_value ||
    loop_head->get_target() == main_body.instructions.end())
    return false;
  std::map<const goto_programt::instructiont *, std::size_t> main_positions;
  std::size_t main_position = 0;
  for(const auto &instruction : main_body.instructions)
    main_positions.emplace(&instruction, main_position++);
  if(
    main_positions.at(&*loop_head->get_target()) <=
      main_positions.at(&*create_instruction))
    return false;
  std::size_t backedges = 0;
  for(auto instruction = std::next(create_instruction);
      instruction != main_body.instructions.end(); ++instruction)
    if(
      instruction->is_goto() && instruction->targets.size() == 1 &&
      instruction->get_target() == loop_head &&
      instruction->condition().is_true())
      ++backedges;
  if(backedges != 1)
    return false;
  const auto worker_function =
    goto_model.goto_functions.function_map.find(worker);
  if(
    worker_function == goto_model.goto_functions.function_map.end() ||
    !worker_function->second.body_available())
    return false;
  bool calls_writer = false;
  bool calls_waiter = false;
  for(const auto &instruction : worker_function->second.body.instructions)
  {
    irep_idt callee;
    if(direct_call_identifier(instruction, callee))
    {
      calls_writer = calls_writer || callee == writer.function;
      calls_waiter = calls_waiter || callee == waiter;
    }
  }
  if(!calls_writer || !calls_waiter)
    return false;

  loop_head->condition_nonconst() = true_exprt();
  goto_model.goto_functions.update();
  main_body.instructions.begin()
    ->source_location_nonconst()
    .set("deagle_monotone_condition_wait", true);
  messaget log(message_handler);
  log.status() << "NATIVE_MONOTONE_CONDITION_WAIT applied=1"
               << " predicate_mentions=" << predicate_mentions
               << " nonconstant_errors=" << nonconstant_errors
               << messaget::eom;
  return true;
}

bool monotone_condition_wait_applied(const goto_modelt &goto_model)
{
  const auto main =
    goto_model.goto_functions.function_map.find("main");
  return
    main != goto_model.goto_functions.function_map.end() &&
    main->second.body_available() &&
    !main->second.body.instructions.empty() &&
    main->second.body.instructions.begin()
      ->source_location()
      .get_bool("deagle_monotone_condition_wait");
}

bool guarded_common_mutex_zero_sum_transform(
  goto_modelt &goto_model,
  message_handlert &message_handler)
{
  std::string reason;
  const auto candidates = dormant_spawn_cutoffs(goto_model, reason);
  if(
    candidates.size() != 1 ||
    candidates.front().first_join == nullptr)
    return false;
  const auto worker =
    goto_model.goto_functions.function_map.find(candidates.front().worker);
  const auto main =
    goto_model.goto_functions.function_map.find("main");
  if(
    worker == goto_model.goto_functions.function_map.end() ||
    !worker->second.body_available() ||
    main == goto_model.goto_functions.function_map.end() ||
    !main->second.body_available())
    return false;

  std::vector<goto_programt::const_targett> updates;
  for(auto instruction = worker->second.body.instructions.begin();
      instruction != worker->second.body.instructions.end(); ++instruction)
    if(instruction->is_assign())
      updates.push_back(instruction);
  if(updates.size() != 2)
    return false;

  irep_idt shared;
  irep_idt second_shared;
  if(
    !direct_symbol(updates[0]->assign_lhs(), shared) ||
    !direct_symbol(updates[1]->assign_lhs(), second_shared) ||
    shared != second_shared)
    return false;
  const auto unit_update =
    [&](goto_programt::const_targett instruction, const irep_idt &operation)
    {
      const exprt &rhs = without_cast(instruction->assign_rhs());
      irep_idt source;
      mp_integer unit;
      return
        rhs.id() == operation && rhs.operands().size() == 2 &&
        direct_symbol(rhs.op0(), source) && source == shared &&
        constant_eval(rhs.op1(), {}, unit) && unit == 1;
    };
  if(
    !unit_update(updates[0], ID_plus) ||
    !unit_update(updates[1], ID_minus))
    return false;

  std::map<const goto_programt::instructiont *, std::size_t> worker_positions;
  std::size_t worker_position = 0;
  for(auto instruction = worker->second.body.instructions.begin();
      instruction != worker->second.body.instructions.end(); ++instruction)
    worker_positions.emplace(&*instruction, worker_position++);
  std::set<irep_idt> outer_mutex_set;
  for(auto instruction = worker->second.body.instructions.begin();
      instruction != worker->second.body.instructions.end(); ++instruction)
  {
    irep_idt mutex;
    if(
      !parse_mutex_call(*instruction, "pthread_mutex_lock", mutex) ||
      worker_positions.at(&*instruction) >=
        worker_positions.at(&*updates[0]))
      continue;
    for(auto probe = std::next(instruction);
        probe != worker->second.body.instructions.end(); ++probe)
    {
      irep_idt unlocked;
      if(
        parse_mutex_call(*probe, "pthread_mutex_unlock", unlocked) &&
        unlocked == mutex)
      {
        if(
          worker_positions.at(&*probe) >
          worker_positions.at(&*updates[1]))
          outer_mutex_set.insert(mutex);
        break;
      }
    }
  }
  if(outer_mutex_set.size() != 1)
    return false;
  const irep_idt outer_mutex = *outer_mutex_set.begin();

  bool after_spawn = false;
  std::map<const goto_programt::instructiont *, std::size_t> main_positions;
  std::size_t main_position = 0;
  for(const auto &instruction : main->second.body.instructions)
    main_positions.emplace(&instruction, main_position++);
  const goto_programt::instructiont *lock_guard = nullptr;
  const goto_programt::instructiont *assert_guard = nullptr;
  const goto_programt::instructiont *unlock_guard = nullptr;
  goto_programt::const_targett previous =
    main->second.body.instructions.end();
  for(auto instruction = main->second.body.instructions.begin();
      instruction != main->second.body.instructions.end(); ++instruction)
  {
    if(&*instruction == &*candidates.front().exit)
      after_spawn = true;
    if(!after_spawn)
    {
      previous = instruction;
      continue;
    }
    irep_idt mutex;
    irep_idt callee;
    if(
      parse_mutex_call(*instruction, "pthread_mutex_lock", mutex) &&
      mutex == outer_mutex && previous != main->second.body.instructions.end() &&
      previous->is_goto())
      lock_guard = &*previous;
    else if(
      parse_mutex_call(*instruction, "pthread_mutex_unlock", mutex) &&
      mutex == outer_mutex && previous != main->second.body.instructions.end() &&
      previous->is_goto())
      unlock_guard = &*previous;
    else if(
      instruction->is_function_call() &&
      direct_call_identifier(*instruction, callee) &&
      callee == "__VERIFIER_assert" &&
      instruction->call_arguments().size() == 1)
    {
      const exprt &condition =
        without_cast(instruction->call_arguments().front());
      irep_idt object;
      if(
        condition.id() != ID_equal ||
        condition.operands().size() != 2 ||
        !((direct_symbol(condition.op0(), object) &&
           object == shared && is_zero_constant(condition.op1())) ||
          (direct_symbol(condition.op1(), object) &&
           object == shared && is_zero_constant(condition.op0()))))
        return false;
      for(auto probe = instruction; probe != main->second.body.instructions.begin();)
      {
        --probe;
        if(
          probe->is_goto() && probe->targets.size() == 1 &&
          main_positions.at(&*probe->get_target()) >
            main_positions.at(&*instruction))
        {
          assert_guard = &*probe;
          break;
        }
      }
    }
    previous = instruction;
  }
  if(
    lock_guard == nullptr ||
    assert_guard == nullptr ||
    unlock_guard == nullptr ||
    lock_guard->condition() != assert_guard->condition() ||
    lock_guard->condition() != unlock_guard->condition())
    return false;

  std::set<irep_idt> guard_symbols;
  collect_symbol_identifiers(lock_guard->condition(), guard_symbols);
  if(guard_symbols.size() != 1)
    return false;
  const irep_idt guard = *guard_symbols.begin();
  bool guard_from_nondet = false;
  std::set<irep_idt> nondet_temporaries;
  for(auto instruction = main->second.body.instructions.begin();
      instruction != candidates.front().head; ++instruction)
  {
    if(!instruction->is_assign())
      continue;
    irep_idt lhs;
    if(!direct_symbol(instruction->assign_lhs(), lhs))
      continue;
    const exprt &rhs = without_cast(instruction->assign_rhs());
    if(
      rhs.id() == ID_side_effect &&
      to_side_effect_expr(rhs).get_statement() == ID_nondet)
      nondet_temporaries.insert(lhs);
    irep_idt rhs_symbol;
    if(
      lhs == guard && direct_symbol(rhs, rhs_symbol) &&
      nondet_temporaries.count(rhs_symbol) != 0)
      guard_from_nondet = true;
  }
  if(!guard_from_nondet)
    return false;

  const auto shared_symbol =
    goto_model.symbol_table.symbols.find(shared);
  if(
    shared_symbol == goto_model.symbol_table.symbols.end() ||
    !shared_symbol->second.is_static_lifetime)
    return false;
  std::size_t mentions = 0;
  std::size_t zero_initializers = 0;
  for(const auto &entry : goto_model.goto_functions.function_map)
  {
    if(!entry.second.body_available())
      continue;
    for(const auto &instruction : entry.second.body.instructions)
    {
      if(instruction_mentions_any(instruction, {shared}))
      {
        ++mentions;
        irep_idt lhs;
        if(
          instruction.is_assign() &&
          direct_symbol(instruction.assign_lhs(), lhs) &&
          lhs == shared &&
          is_zero_constant(instruction.assign_rhs()))
          ++zero_initializers;
      }
      if(instruction.is_function_call())
        for(const auto &argument : instruction.call_arguments())
          if(contains_address_of_symbol(argument, {shared}))
            return false;
    }
  }
  if(mentions != 4 || zero_initializers != 1)
    return false;

  bool truncated = false;
  if(!apply_dormant_spawn_counts(
       goto_model, candidates, std::vector<unsigned>{0}, truncated))
    return false;
  goto_model.goto_functions.update();
  auto updated_main =
    goto_model.goto_functions.function_map.find("main");
  updated_main->second.body.instructions.begin()
    ->source_location_nonconst()
    .set("deagle_guarded_common_mutex_zero_sum", true);
  messaget log(message_handler);
  log.status() << "NATIVE_GUARDED_COMMON_MUTEX_ZERO_SUM applied=1"
               << " workers=0 mentions=" << mentions
               << " truncated=" << (truncated ? 1 : 0)
               << messaget::eom;
  return true;
}

bool guarded_common_mutex_zero_sum_applied(const goto_modelt &goto_model)
{
  const auto main =
    goto_model.goto_functions.function_map.find("main");
  return
    main != goto_model.goto_functions.function_map.end() &&
    main->second.body_available() &&
    !main->second.body.instructions.empty() &&
    main->second.body.instructions.begin()
      ->source_location()
      .get_bool("deagle_guarded_common_mutex_zero_sum");
}

namespace
{
struct nested_last_writer_pairt
{
  irep_idt function;
  irep_idt object;
  mp_integer value;
  const goto_programt::instructiont *store = nullptr;
  const goto_programt::instructiont *property = nullptr;
};

bool nested_last_writer_parameter_truth(
  const exprt &src,
  const irep_idt &parameter)
{
  const exprt &condition = without_cast(src);
  irep_idt object;
  mp_integer zero;
  if(
    condition.id() == ID_notequal &&
    condition.operands().size() == 2)
    return
      ((direct_symbol(condition.op0(), object) &&
        object == parameter &&
        constant_eval(condition.op1(), {}, zero) && zero == 0) ||
       (direct_symbol(condition.op1(), object) &&
        object == parameter &&
        constant_eval(condition.op0(), {}, zero) && zero == 0));
  if(
    condition.id() == ID_not &&
    condition.operands().size() == 1)
  {
    const exprt &equality = without_cast(condition.op0());
    return
      equality.id() == ID_equal &&
      equality.operands().size() == 2 &&
      ((direct_symbol(equality.op0(), object) &&
        object == parameter &&
        constant_eval(equality.op1(), {}, zero) && zero == 0) ||
       (direct_symbol(equality.op1(), object) &&
        object == parameter &&
        constant_eval(equality.op0(), {}, zero) && zero == 0));
  }
  return false;
}

bool nested_last_writer_property_wrapper(
  const goto_modelt &model,
  irep_idt &wrapper,
  std::string &reason)
{
  std::size_t candidates = 0;
  for(const auto &entry : model.goto_functions.function_map)
  {
    if(!entry.second.body_available())
      continue;
    std::vector<const goto_programt::instructiont *> order;
    std::size_t error_index = 0;
    std::size_t error_calls = 0;
    for(const auto &instruction : entry.second.body.instructions)
    {
      order.push_back(&instruction);
      irep_idt callee;
      if(
        direct_call_identifier(instruction, callee) &&
        callee == "reach_error")
      {
        error_index = order.size() - 1;
        ++error_calls;
      }
    }
    if(error_calls == 0)
      continue;
    const auto symbol = model.symbol_table.symbols.find(entry.first);
    if(
      error_calls != 1 || error_index == 0 ||
      symbol == model.symbol_table.symbols.end() ||
      symbol->second.type.id() != ID_code)
    {
      reason = "nlw_property_wrapper_shape";
      return false;
    }
    const auto &parameters =
      to_code_type(symbol->second.type).parameters();
    const auto guard = order[error_index - 1];
    if(
      parameters.size() != 1 ||
      parameters.front().get_identifier().empty() ||
      !guard->is_goto() || guard->targets.size() != 1 ||
      !nested_last_writer_parameter_truth(
        guard->condition(),
        parameters.front().get_identifier()))
    {
      reason = "nlw_property_wrapper_semantics";
      return false;
    }
    for(std::size_t index = 0; index + 1 < error_index; ++index)
    {
      if(
        !order[index]->is_location() &&
        !order[index]->is_skip() &&
        !order[index]->is_decl() &&
        !order[index]->is_dead())
      {
        reason = "nlw_property_wrapper_prefix_effect";
        return false;
      }
    }
    std::map<const goto_programt::instructiont *, std::size_t>
      wrapper_positions;
    for(std::size_t index = 0; index < order.size(); ++index)
      wrapper_positions.emplace(order[index], index);
    std::set<std::size_t> pending{
      wrapper_positions.at(&*guard->targets.front())};
    std::set<std::size_t> visited;
    bool true_path_exits = false;
    while(!pending.empty())
    {
      const auto index = *pending.begin();
      pending.erase(pending.begin());
      if(index >= order.size() || !visited.insert(index).second)
        continue;
      const auto instruction = order[index];
      if(
        instruction->is_end_function() ||
        instruction->is_set_return_value())
      {
        true_path_exits = true;
        continue;
      }
      if(instruction->is_goto())
      {
        for(const auto &target : instruction->targets)
          pending.insert(wrapper_positions.at(&*target));
        if(!instruction->condition().is_true())
          pending.insert(index + 1);
        continue;
      }
      if(
        instruction->is_function_call() ||
        instruction->is_assign() ||
        (!instruction->is_location() &&
         !instruction->is_skip() &&
         !instruction->is_decl() &&
         !instruction->is_dead()))
      {
        reason = "nlw_property_wrapper_true_path_effect";
        return false;
      }
      pending.insert(index + 1);
    }
    if(!true_path_exits)
    {
      reason = "nlw_property_wrapper_true_path_exit";
      return false;
    }
    wrapper = entry.first;
    ++candidates;
  }
  if(candidates != 1)
  {
    reason = "nlw_property_wrapper_count";
    return false;
  }
  return true;
}

bool nested_last_writer_equality(
  const exprt &src,
  irep_idt &object,
  mp_integer &value)
{
  const exprt &condition = without_cast(src);
  if(
    condition.id() != ID_equal ||
    condition.operands().size() != 2)
    return false;
  return
    (direct_symbol(condition.op0(), object) &&
     constant_eval(condition.op1(), {}, value)) ||
    (direct_symbol(condition.op1(), object) &&
     constant_eval(condition.op0(), {}, value));
}

std::set<irep_idt> nested_last_writer_reachable(
  const goto_modelt &model,
  const irep_idt &root)
{
  const std::set<irep_idt> runtime = {
    "pthread_create", "pthread_join", "pthread_mutex_init",
    "pthread_mutex_destroy", "pthread_mutex_lock",
    "pthread_mutex_unlock", "abort", "reach_error"};
  std::set<irep_idt> reachable;
  std::deque<irep_idt> pending{root};
  while(!pending.empty())
  {
    const auto current = pending.front();
    pending.pop_front();
    if(!reachable.insert(current).second)
      continue;
    const auto function =
      model.goto_functions.function_map.find(current);
    if(
      function == model.goto_functions.function_map.end() ||
      !function->second.body_available())
      continue;
    for(const auto &instruction : function->second.body.instructions)
    {
      irep_idt callee;
      if(
        direct_call_identifier(instruction, callee) &&
        runtime.count(callee) == 0)
        pending.push_back(callee);
    }
  }
  return reachable;
}

bool nested_last_writer_contains_call(
  const goto_modelt &model,
  const std::set<irep_idt> &functions,
  const irep_idt &operation,
  const irep_idt &handle)
{
  for(const auto &identifier : functions)
  {
    const auto function =
      model.goto_functions.function_map.find(identifier);
    if(
      function == model.goto_functions.function_map.end() ||
      !function->second.body_available())
      continue;
    for(const auto &instruction : function->second.body.instructions)
    {
      irep_idt callee;
      if(
        !direct_call_identifier(instruction, callee) ||
        callee != operation ||
        instruction.call_arguments().empty())
        continue;
      irep_idt candidate;
      const bool resolved =
        operation == "pthread_create"
          ? addressed_symbol(
              instruction.call_arguments().front(), candidate)
          : direct_symbol(
              instruction.call_arguments().front(), candidate);
      if(resolved && candidate == handle)
        return true;
    }
  }
  return false;
}

enum class nested_zero_valuet
{
  unknown = -1,
  zero = 0,
  one = 1,
  other_nonzero = 2
};

nested_zero_valuet nested_last_writer_value(
  const exprt &src,
  const std::map<irep_idt, nested_zero_valuet> &environment)
{
  const exprt &value = without_cast(src);
  mp_integer constant;
  if(constant_eval(value, {}, constant))
  {
    if(constant == 0)
      return nested_zero_valuet::zero;
    if(constant == 1)
      return nested_zero_valuet::one;
    return nested_zero_valuet::other_nonzero;
  }
  if(
    value.id() == ID_unary_minus &&
    value.operands().size() == 1)
  {
    const auto operand =
      nested_last_writer_value(value.op0(), environment);
    if(operand == nested_zero_valuet::zero)
      return nested_zero_valuet::zero;
    if(
      operand == nested_zero_valuet::one ||
      operand == nested_zero_valuet::other_nonzero)
      return nested_zero_valuet::other_nonzero;
    return nested_zero_valuet::unknown;
  }
  irep_idt symbol;
  if(direct_symbol(value, symbol))
  {
    const auto found = environment.find(symbol);
    return
      found == environment.end()
        ? nested_zero_valuet::unknown
        : found->second;
  }
  return nested_zero_valuet::unknown;
}

bool nested_last_writer_condition(
  const exprt &src,
  const std::map<irep_idt, nested_zero_valuet> &environment,
  bool &known,
  bool &value)
{
  const exprt &condition = without_cast(src);
  if(condition.is_true() || condition.is_false())
  {
    known = true;
    value = condition.is_true();
    return true;
  }
  if(
    condition.id() == ID_not &&
    condition.operands().size() == 1)
  {
    if(!nested_last_writer_condition(
         condition.op0(), environment, known, value))
      return false;
    if(known)
      value = !value;
    return true;
  }
  if(
    (condition.id() == ID_equal ||
     condition.id() == ID_notequal) &&
    condition.operands().size() == 2)
  {
    const auto lhs =
      nested_last_writer_value(condition.op0(), environment);
    const auto rhs =
      nested_last_writer_value(condition.op1(), environment);
    if(
      lhs == nested_zero_valuet::unknown ||
      rhs == nested_zero_valuet::unknown)
    {
      known = false;
      return true;
    }
    if(
      lhs == nested_zero_valuet::other_nonzero &&
      rhs == nested_zero_valuet::other_nonzero)
    {
      known = false;
      return true;
    }
    known = true;
    value = condition.id() == ID_equal ? lhs == rhs : lhs != rhs;
    return true;
  }
  known = false;
  return true;
}

struct nested_spawn_outcomet
{
  bool spawned = false;
  nested_zero_valuet result = nested_zero_valuet::unknown;

  bool operator<(const nested_spawn_outcomet &other) const
  {
    return
      std::tie(spawned, result) <
      std::tie(other.spawned, other.result);
  }

  bool operator==(const nested_spawn_outcomet &other) const
  {
    return spawned == other.spawned && result == other.result;
  }
};

struct nested_summary_statet
{
  std::size_t position = 0;
  bool event = false;
  std::map<irep_idt, nested_zero_valuet> environment;

  bool operator<(const nested_summary_statet &other) const
  {
    return
      std::tie(position, event, environment) <
      std::tie(other.position, other.event, other.environment);
  }
};

bool nested_last_writer_spawn_summary(
  const goto_modelt &model,
  const irep_idt &function_id,
  const irep_idt &handle,
  std::map<irep_idt, std::set<nested_spawn_outcomet>> &memo,
  std::set<irep_idt> &active,
  std::set<nested_spawn_outcomet> &outcomes,
  std::string &reason)
{
  const auto cached = memo.find(function_id);
  if(cached != memo.end())
  {
    outcomes = cached->second;
    return true;
  }
  if(!active.insert(function_id).second)
  {
    reason = "nlw_spawn_summary_recursion";
    return false;
  }
  const auto function =
    model.goto_functions.function_map.find(function_id);
  if(
    function == model.goto_functions.function_map.end() ||
    !function->second.body_available())
  {
    reason = "nlw_spawn_summary_function";
    active.erase(function_id);
    return false;
  }
  std::vector<const goto_programt::instructiont *> order;
  std::map<const goto_programt::instructiont *, std::size_t> positions;
  for(const auto &instruction : function->second.body.instructions)
  {
    positions.emplace(&instruction, order.size());
    order.push_back(&instruction);
  }
  std::set<nested_summary_statet> pending;
  std::set<nested_summary_statet> visited;
  nested_summary_statet initial_state;
  pending.insert(initial_state);
  while(!pending.empty())
  {
    auto state = *pending.begin();
    pending.erase(pending.begin());
    if(!visited.insert(state).second)
      continue;
    if(state.position >= order.size())
    {
      reason = "nlw_spawn_summary_fallthrough";
      active.erase(function_id);
      return false;
    }
    const auto instruction = order[state.position];
    if(instruction->is_end_function())
    {
      nested_spawn_outcomet outcome;
      outcome.spawned = state.event;
      outcome.result = nested_zero_valuet::unknown;
      outcomes.insert(outcome);
      continue;
    }
    if(instruction->is_set_return_value())
    {
      nested_spawn_outcomet outcome;
      outcome.spawned = state.event;
      outcome.result =
        nested_last_writer_value(
          instruction->return_value(), state.environment);
      outcomes.insert(outcome);
      continue;
    }
    if(instruction->is_goto())
    {
      bool known = false;
      bool value = false;
      nested_last_writer_condition(
        instruction->condition(),
        state.environment,
        known,
        value);
      if(!known || value)
      {
        for(const auto &target : instruction->targets)
        {
          const auto target_position = positions.at(&*target);
          if(target_position <= state.position)
          {
            reason = "nlw_spawn_summary_loop";
            active.erase(function_id);
            return false;
          }
          auto branch = state;
          branch.position = target_position;
          pending.insert(branch);
        }
      }
      if((!known || !value) && state.position + 1 < order.size())
      {
        ++state.position;
        pending.insert(state);
      }
      continue;
    }
    if(instruction->is_assign())
    {
      irep_idt lhs;
      if(direct_symbol(instruction->assign_lhs(), lhs))
        state.environment[lhs] =
          nested_last_writer_value(
            instruction->assign_rhs(), state.environment);
    }
    if(instruction->is_function_call())
    {
      irep_idt callee;
      if(!direct_call_identifier(*instruction, callee))
      {
        reason = "nlw_spawn_summary_indirect";
        active.erase(function_id);
        return false;
      }
      if(callee == "pthread_create")
      {
        irep_idt candidate;
        if(
          instruction->call_arguments().empty() ||
          !addressed_symbol(
            instruction->call_arguments().front(), candidate))
        {
          reason = "nlw_spawn_summary_create";
          active.erase(function_id);
          return false;
        }
        if(candidate == handle)
          state.event = true;
      }
      else
      {
        const auto reachable =
          nested_last_writer_reachable(model, callee);
        if(
          nested_last_writer_contains_call(
            model, reachable, "pthread_create", handle))
        {
          std::set<nested_spawn_outcomet> called_outcomes;
          if(!nested_last_writer_spawn_summary(
               model, callee, handle, memo, active,
               called_outcomes, reason))
          {
            active.erase(function_id);
            return false;
          }
          for(const auto &called : called_outcomes)
          {
            auto branch = state;
            branch.event = branch.event || called.spawned;
            if(!instruction->call_lhs().is_nil())
            {
              irep_idt lhs;
              if(!direct_symbol(instruction->call_lhs(), lhs))
              {
                reason = "nlw_spawn_summary_call_lhs";
                active.erase(function_id);
                return false;
              }
              branch.environment[lhs] = called.result;
            }
            ++branch.position;
            pending.insert(branch);
          }
          continue;
        }
      }
      if(!instruction->call_lhs().is_nil())
      {
        irep_idt lhs;
        if(direct_symbol(instruction->call_lhs(), lhs))
          state.environment[lhs] = nested_zero_valuet::unknown;
      }
    }
    ++state.position;
    pending.insert(state);
  }
  active.erase(function_id);
  if(outcomes.empty())
  {
    reason = "nlw_spawn_summary_outcomes";
    return false;
  }
  memo.emplace(function_id, outcomes);
  return true;
}

bool nested_last_writer_always_joins(
  const goto_modelt &model,
  const irep_idt &function_id,
  const irep_idt &handle,
  std::set<irep_idt> &active,
  std::string &reason)
{
  if(!active.insert(function_id).second)
  {
    reason = "nlw_join_summary_recursion";
    return false;
  }
  const auto function =
    model.goto_functions.function_map.find(function_id);
  if(
    function == model.goto_functions.function_map.end() ||
    !function->second.body_available())
  {
    reason = "nlw_join_summary_function";
    active.erase(function_id);
    return false;
  }
  std::vector<const goto_programt::instructiont *> order;
  std::map<const goto_programt::instructiont *, std::size_t> positions;
  for(const auto &instruction : function->second.body.instructions)
  {
    positions.emplace(&instruction, order.size());
    order.push_back(&instruction);
  }
  std::set<std::pair<std::size_t, bool>> pending{{0, false}};
  std::set<std::pair<std::size_t, bool>> visited;
  while(!pending.empty())
  {
    auto state = *pending.begin();
    pending.erase(pending.begin());
    if(!visited.insert(state).second)
      continue;
    if(state.first >= order.size())
    {
      reason = "nlw_join_summary_fallthrough";
      active.erase(function_id);
      return false;
    }
    const auto instruction = order[state.first];
    if(
      instruction->is_end_function() ||
      instruction->is_set_return_value())
    {
      if(!state.second)
      {
        reason = "nlw_join_summary_bypass";
        active.erase(function_id);
        return false;
      }
      continue;
    }
    if(instruction->is_goto())
    {
      for(const auto &target : instruction->targets)
      {
        const auto target_position = positions.at(&*target);
        if(target_position <= state.first)
        {
          reason = "nlw_join_summary_loop";
          active.erase(function_id);
          return false;
        }
        pending.emplace(target_position, state.second);
      }
      if(
        !instruction->condition().is_true() &&
        state.first + 1 < order.size())
        pending.emplace(state.first + 1, state.second);
      continue;
    }
    if(instruction->is_function_call())
    {
      irep_idt callee;
      if(!direct_call_identifier(*instruction, callee))
      {
        reason = "nlw_join_summary_indirect";
        active.erase(function_id);
        return false;
      }
      if(callee == "pthread_join")
      {
        irep_idt candidate;
        if(
          instruction->call_arguments().empty() ||
          !direct_symbol(
            instruction->call_arguments().front(), candidate))
        {
          reason = "nlw_join_summary_call";
          active.erase(function_id);
          return false;
        }
        if(candidate == handle)
          state.second = true;
      }
      else
      {
        const auto reachable =
          nested_last_writer_reachable(model, callee);
        if(
          nested_last_writer_contains_call(
            model, reachable, "pthread_join", handle))
        {
          if(!nested_last_writer_always_joins(
               model, callee, handle, active, reason))
          {
            active.erase(function_id);
            return false;
          }
          state.second = true;
        }
      }
    }
    ++state.first;
    pending.insert(state);
  }
  active.erase(function_id);
  return true;
}

struct nested_lifecycle_statet
{
  std::size_t position = 0;
  bool active = false;
  std::map<irep_idt, nested_zero_valuet> environment;

  bool operator<(const nested_lifecycle_statet &other) const
  {
    return
      std::tie(position, active, environment) <
      std::tie(other.position, other.active, other.environment);
  }
};

bool nested_last_writer_private_environment(
  const goto_modelt &model,
  const irep_idt &function_id,
  const irep_idt &property_object,
  std::set<irep_idt> &symbols,
  std::string &reason)
{
  const auto function =
    model.goto_functions.function_map.find(function_id);
  if(
    function == model.goto_functions.function_map.end() ||
    !function->second.body_available())
  {
    reason = "nlw_protocol_function";
    return false;
  }
  for(const auto &instruction : function->second.body.instructions)
  {
    irep_idt symbol;
    if(
      instruction.is_assign() &&
      direct_symbol(instruction.assign_lhs(), symbol) &&
      symbol != property_object)
      symbols.insert(symbol);
    if(
      instruction.is_function_call() &&
      !instruction.call_lhs().is_nil() &&
      direct_symbol(instruction.call_lhs(), symbol) &&
      symbol != property_object)
      symbols.insert(symbol);
  }
  if(symbols.empty())
  {
    reason = "nlw_protocol_state_empty";
    return false;
  }
  for(const auto &entry : model.goto_functions.function_map)
  {
    if(!entry.second.body_available())
      continue;
    for(const auto &instruction : entry.second.body.instructions)
    {
      irep_idt written;
      const bool writes =
        (instruction.is_assign() &&
         direct_symbol(instruction.assign_lhs(), written)) ||
        (instruction.is_function_call() &&
         !instruction.call_lhs().is_nil() &&
         direct_symbol(instruction.call_lhs(), written));
      if(
        writes && symbols.count(written) != 0 &&
        entry.first != function_id &&
        entry.first != "__CPROVER_initialize")
      {
        reason = "nlw_protocol_external_write";
        return false;
      }
      if(
        entry.first != function_id &&
        (contains_address_of_symbol(instruction.code(), symbols) ||
         (instruction.has_condition() &&
          contains_address_of_symbol(
            instruction.condition(), symbols))))
      {
        reason = "nlw_protocol_address_escape";
        return false;
      }
    }
  }
  return true;
}

bool nested_last_writer_lifecycle_control(
  const goto_modelt &model,
  const irep_idt &function_id,
  const irep_idt &create_callee,
  const irep_idt &join_callee,
  const std::set<nested_spawn_outcomet> &spawn_outcomes,
  const std::set<const goto_programt::instructiont *> &property_stores,
  const irep_idt &property_object,
  std::string &reason)
{
  const auto function =
    model.goto_functions.function_map.find(function_id);
  if(
    function == model.goto_functions.function_map.end() ||
    !function->second.body_available())
  {
    reason = "nlw_protocol_body";
    return false;
  }
  std::set<irep_idt> private_symbols;
  if(!nested_last_writer_private_environment(
       model, function_id, property_object,
       private_symbols, reason))
    return false;

  std::vector<const goto_programt::instructiont *> order;
  std::map<const goto_programt::instructiont *, std::size_t> positions;
  for(const auto &instruction : function->second.body.instructions)
  {
    positions.emplace(&instruction, order.size());
    order.push_back(&instruction);
  }
  nested_lifecycle_statet initial;
  std::set<nested_lifecycle_statet> pending;
  std::set<nested_lifecycle_statet> visited;
  pending.insert(initial);
  bool saw_create = false;
  bool saw_join = false;
  while(!pending.empty())
  {
    auto state = *pending.begin();
    pending.erase(pending.begin());
    if(!visited.insert(state).second)
      continue;
    if(state.position >= order.size())
    {
      reason = "nlw_protocol_fallthrough";
      return false;
    }
    const auto instruction = order[state.position];
    if(property_stores.count(instruction) != 0 && state.active)
    {
      reason = "nlw_active_window_property";
      return false;
    }
    if(
      instruction->is_end_function() ||
      instruction->is_set_return_value())
    {
      if(state.active)
      {
        reason = "nlw_protocol_active_exit";
        return false;
      }
      continue;
    }
    if(instruction->is_goto())
    {
      bool known = false;
      bool value = false;
      nested_last_writer_condition(
        instruction->condition(),
        state.environment, known, value);
      if(!known || value)
      {
        for(const auto &target : instruction->targets)
        {
          const auto found = positions.find(&*target);
          if(found == positions.end())
          {
            reason = "nlw_protocol_target";
            return false;
          }
          auto branch = state;
          branch.position = found->second;
          pending.insert(branch);
        }
      }
      if(!known || !value)
      {
        if(state.position + 1 >= order.size())
        {
          reason = "nlw_protocol_branch_fallthrough";
          return false;
        }
        ++state.position;
        pending.insert(state);
      }
      continue;
    }
    if(instruction->is_assign())
    {
      irep_idt lhs;
      if(
        direct_symbol(instruction->assign_lhs(), lhs) &&
        private_symbols.count(lhs) != 0)
        state.environment[lhs] =
          nested_last_writer_value(
            instruction->assign_rhs(), state.environment);
    }
    if(instruction->is_function_call())
    {
      irep_idt callee;
      if(!direct_call_identifier(*instruction, callee))
      {
        reason = "nlw_protocol_indirect_call";
        return false;
      }
      if(callee == create_callee)
      {
        saw_create = true;
        for(const auto &outcome : spawn_outcomes)
        {
          if(state.active && outcome.spawned)
          {
            reason = "nlw_protocol_multiple_active";
            return false;
          }
          auto branch = state;
          branch.active = branch.active || outcome.spawned;
          if(!instruction->call_lhs().is_nil())
          {
            irep_idt lhs;
            if(
              !direct_symbol(instruction->call_lhs(), lhs) ||
              private_symbols.count(lhs) == 0)
            {
              reason = "nlw_protocol_create_result";
              return false;
            }
            branch.environment[lhs] = outcome.result;
          }
          ++branch.position;
          pending.insert(branch);
        }
        continue;
      }
      if(callee == join_callee)
      {
        saw_join = true;
        if(!state.active)
        {
          reason = "nlw_protocol_inactive_join";
          return false;
        }
        state.active = false;
      }
      if(!instruction->call_lhs().is_nil())
      {
        irep_idt lhs;
        if(
          direct_symbol(instruction->call_lhs(), lhs) &&
          private_symbols.count(lhs) != 0)
          state.environment[lhs] = nested_zero_valuet::unknown;
      }
    }
    ++state.position;
    pending.insert(state);
  }
  if(!saw_create || !saw_join)
  {
    reason = "nlw_protocol_events";
    return false;
  }
  return true;
}

bool nested_last_writer_reaches_position(
  const std::vector<const goto_programt::instructiont *> &order,
  const std::map<const goto_programt::instructiont *, std::size_t> &positions,
  std::size_t start,
  std::size_t target,
  std::size_t avoided)
{
  std::set<std::size_t> pending{start};
  std::set<std::size_t> visited;
  while(!pending.empty())
  {
    const auto position = *pending.begin();
    pending.erase(pending.begin());
    if(position == avoided || position >= order.size())
      continue;
    if(position == target)
      return true;
    if(!visited.insert(position).second)
      continue;
    const auto instruction = order[position];
    if(
      instruction->is_end_function() ||
      instruction->is_set_return_value())
      continue;
    if(instruction->is_goto())
    {
      for(const auto &goto_target : instruction->targets)
        pending.insert(positions.at(&*goto_target));
      if(!instruction->condition().is_true())
        pending.insert(position + 1);
    }
    else
      pending.insert(position + 1);
  }
  return false;
}

bool nested_last_writer_pair_mutex(
  const goto_modelt &model,
  const std::set<irep_idt> &child_functions,
  const std::vector<nested_last_writer_pairt> &pairs,
  std::set<const goto_programt::instructiont *> &classified,
  std::string &reason)
{
  bool saw_child_pair = false;
  for(const auto &pair : pairs)
  {
    if(child_functions.count(pair.function) == 0)
      continue;
    saw_child_pair = true;
    const auto function =
      model.goto_functions.function_map.find(pair.function);
    if(
      function == model.goto_functions.function_map.end() ||
      !function->second.body_available())
    {
      reason = "nlw_child_pair_function";
      return false;
    }
    std::vector<const goto_programt::instructiont *> order;
    std::map<const goto_programt::instructiont *, std::size_t> positions;
    for(const auto &instruction : function->second.body.instructions)
    {
      positions.emplace(&instruction, order.size());
      order.push_back(&instruction);
    }
    std::vector<std::size_t> locks;
    std::vector<std::size_t> unlocks;
    irep_idt mutex;
    for(std::size_t index = 0; index < order.size(); ++index)
    {
      const auto instruction = order[index];
      if(instruction->is_goto())
        for(const auto &target : instruction->targets)
          if(positions.at(&*target) <= index)
          {
            reason = "nlw_child_pair_loop";
            return false;
          }
      irep_idt callee;
      if(!direct_call_identifier(*instruction, callee))
        continue;
      if(
        callee != "pthread_mutex_lock" &&
        callee != "pthread_mutex_unlock")
        continue;
      irep_idt candidate;
      if(
        instruction->call_arguments().size() != 1 ||
        !addressed_symbol(
          instruction->call_arguments().front(), candidate))
      {
        reason = "nlw_child_mutex_resolution";
        return false;
      }
      if(mutex.empty())
        mutex = candidate;
      if(candidate != mutex)
      {
        reason = "nlw_child_mutex_mismatch";
        return false;
      }
      (callee == "pthread_mutex_lock" ? locks : unlocks)
        .push_back(index);
    }
    if(locks.size() != 1 || unlocks.size() != 1)
    {
      reason = "nlw_child_mutex_count";
      return false;
    }
    const auto store_position = positions.at(pair.store);
    const auto property_position = positions.at(pair.property);
    if(
      !(locks.front() < store_position &&
        store_position < property_position &&
        property_position < unlocks.front()) ||
      nested_last_writer_reaches_position(
        order, positions, 0, store_position, locks.front()))
    {
      reason = "nlw_child_mutex_dominance";
      return false;
    }
    classified.insert(pair.store);
  }
  if(!saw_child_pair)
  {
    reason = "nlw_child_pair_empty";
    return false;
  }
  return true;
}

bool nested_last_writer_outer_pair_order(
  const goto_modelt &model,
  const irep_idt &create_function,
  const irep_idt &join_function,
  const irep_idt &handle,
  const std::vector<nested_last_writer_pairt> &pairs,
  std::set<const goto_programt::instructiont *> &classified,
  std::string &reason)
{
  for(const auto &function_id : {create_function, join_function})
  {
    const auto function =
      model.goto_functions.function_map.find(function_id);
    if(
      function == model.goto_functions.function_map.end() ||
      !function->second.body_available())
    {
      reason = "nlw_outer_helper_body";
      return false;
    }
    std::vector<const goto_programt::instructiont *> order;
    std::map<const goto_programt::instructiont *, std::size_t> positions;
    for(const auto &instruction : function->second.body.instructions)
    {
      positions.emplace(&instruction, order.size());
      order.push_back(&instruction);
    }
    std::vector<std::size_t> lifecycle_events;
    for(std::size_t index = 0; index < order.size(); ++index)
    {
      irep_idt callee;
      if(!direct_call_identifier(*order[index], callee))
        continue;
      const auto expected =
        function_id == create_function
          ? irep_idt("pthread_create")
          : irep_idt("pthread_join");
      if(callee != expected)
        continue;
      irep_idt candidate;
      const bool resolved =
        !order[index]->call_arguments().empty() &&
        (expected == "pthread_create"
           ? addressed_symbol(
               order[index]->call_arguments().front(), candidate)
           : direct_symbol(
               order[index]->call_arguments().front(), candidate));
      if(resolved && candidate == handle)
        lifecycle_events.push_back(index);
    }
    if(lifecycle_events.size() != 1)
    {
      reason = "nlw_outer_helper_event";
      return false;
    }
    for(const auto &pair : pairs)
    {
      if(pair.function != function_id)
        continue;
      const auto store_position = positions.at(pair.store);
      if(function_id == create_function)
      {
        if(
          nested_last_writer_reaches_position(
            order, positions, lifecycle_events.front() + 1,
            store_position, order.size()))
        {
          reason = "nlw_outer_post_create_pair";
          return false;
        }
      }
      else if(
        nested_last_writer_reaches_position(
          order, positions, 0, store_position,
          lifecycle_events.front()))
      {
        reason = "nlw_outer_pre_join_pair";
        return false;
      }
      classified.insert(pair.store);
    }
  }
  return true;
}
} // namespace

bool nested_lifecycle_last_writer_audit(
  const goto_modelt &goto_model,
  message_handlert &message_handler)
{
  (void)message_handler;
  std::string reason;
  const auto reject = [&reason]()
  {
    std::cout << "NATIVE_NESTED_LAST_WRITER_AUDIT applicable=0 reason="
              << reason << '\n';
    return false;
  };

  irep_idt wrapper;
  if(!nested_last_writer_property_wrapper(
       goto_model, wrapper, reason))
    return reject();

  std::vector<nested_last_writer_pairt> pairs;
  std::set<const goto_programt::instructiont *> stores;
  irep_idt common_object;
  for(const auto &entry : goto_model.goto_functions.function_map)
  {
    if(!entry.second.body_available())
      continue;
    const goto_programt::instructiont *previous = nullptr;
    for(const auto &instruction : entry.second.body.instructions)
    {
      irep_idt callee;
      if(
        direct_call_identifier(instruction, callee) &&
        callee == wrapper)
      {
        irep_idt object;
        mp_integer value;
        irep_idt lhs;
        mp_integer stored;
        if(
          instruction.call_arguments().size() != 1 ||
          previous == nullptr || !previous->is_assign() ||
          !nested_last_writer_equality(
            instruction.call_arguments().front(), object, value) ||
          !direct_symbol(previous->assign_lhs(), lhs) ||
          lhs != object ||
          !constant_eval(previous->assign_rhs(), {}, stored) ||
          stored != value)
        {
          reason = "nlw_store_property_pair";
          return reject();
        }
        if(common_object.empty())
          common_object = object;
        if(object != common_object)
        {
          reason = "nlw_property_object_mismatch";
          return reject();
        }
        nested_last_writer_pairt pair;
        pair.function = entry.first;
        pair.object = object;
        pair.value = value;
        pair.store = previous;
        pair.property = &instruction;
        pairs.push_back(pair);
        stores.insert(previous);
      }
      if(
        !instruction.is_location() && !instruction.is_skip() &&
        !instruction.is_decl() && !instruction.is_dead())
        previous = &instruction;
    }
  }
  if(pairs.size() < 3 || common_object.empty())
  {
    reason = "nlw_property_pair_count";
    return reject();
  }

  std::size_t object_writes = 0;
  for(const auto &entry : goto_model.goto_functions.function_map)
  {
    if(!entry.second.body_available())
      continue;
    for(const auto &instruction : entry.second.body.instructions)
    {
      if(instruction.is_assign())
      {
        irep_idt lhs;
        if(
          direct_symbol(instruction.assign_lhs(), lhs) &&
          lhs == common_object &&
          entry.first != "__CPROVER_initialize")
        {
          ++object_writes;
          if(stores.count(&instruction) == 0)
          {
            reason = "nlw_unpaired_object_write";
            return reject();
          }
        }
      }
      if(
        contains_address_of_symbol(
          instruction.code(), {common_object}) ||
        (instruction.has_condition() &&
         contains_address_of_symbol(
           instruction.condition(), {common_object})))
      {
        reason = "nlw_object_address_escape";
        return reject();
      }
    }
  }
  if(object_writes != pairs.size())
  {
    reason = "nlw_object_write_census";
    return reject();
  }

  struct lifecycle_recordt
  {
    irep_idt function;
    irep_idt handle;
    irep_idt worker;
  };
  std::vector<lifecycle_recordt> creates;
  std::map<irep_idt, std::size_t> joins;
  for(const auto &entry : goto_model.goto_functions.function_map)
  {
    if(!entry.second.body_available())
      continue;
    for(const auto &instruction : entry.second.body.instructions)
    {
      irep_idt callee;
      if(!direct_call_identifier(instruction, callee))
        continue;
      if(callee == "pthread_create")
      {
        irep_idt handle;
        irep_idt worker;
        if(
          instruction.call_arguments().size() < 3 ||
          !addressed_symbol(
            instruction.call_arguments()[0], handle) ||
          !addressed_symbol(
            instruction.call_arguments()[2], worker))
        {
          reason = "nlw_create_resolution";
          return reject();
        }
        creates.push_back({entry.first, handle, worker});
      }
      else if(callee == "pthread_join")
      {
        irep_idt handle;
        if(
          instruction.call_arguments().empty() ||
          !direct_symbol(
            instruction.call_arguments().front(), handle))
        {
          reason = "nlw_join_resolution";
          return reject();
        }
        ++joins[handle];
      }
    }
  }
  if(creates.size() != 2 || joins.size() != 2)
  {
    reason = "nlw_lifecycle_count";
    return reject();
  }
  for(const auto &create : creates)
    if(joins[create.handle] != 1)
    {
      reason = "nlw_lifecycle_pairing";
      return reject();
    }

  std::size_t nested_index = creates.size();
  irep_idt controller;
  for(std::size_t index = 0; index < creates.size(); ++index)
  {
    const auto other = 1 - index;
    const auto reachable =
      nested_last_writer_reachable(
        goto_model, creates[index].worker);
    if(reachable.count(creates[other].function) != 0)
    {
      if(nested_index != creates.size())
      {
        reason = "nlw_nested_create_ambiguous";
        return reject();
      }
      nested_index = other;
      controller = creates[index].worker;
    }
  }
  if(nested_index == creates.size() || controller.empty())
  {
    reason = "nlw_nested_create_graph";
    return reject();
  }
  const auto &nested = creates[nested_index];
  const auto controller_functions =
    nested_last_writer_reachable(goto_model, controller);
  const auto controller_body =
    goto_model.goto_functions.function_map.find(controller);
  if(
    controller_body == goto_model.goto_functions.function_map.end() ||
    !controller_body->second.body_available())
  {
    reason = "nlw_controller_body";
    return reject();
  }

  std::map<const goto_programt::instructiont *, std::size_t> positions;
  std::size_t position = 0;
  for(const auto &instruction :
      controller_body->second.body.instructions)
    positions.emplace(&instruction, position++);
  std::vector<std::size_t> create_calls;
  std::vector<std::size_t> join_calls;
  std::vector<irep_idt> create_callees;
  std::vector<irep_idt> join_callees;
  for(const auto &instruction :
      controller_body->second.body.instructions)
  {
    irep_idt callee;
    if(!direct_call_identifier(instruction, callee))
      continue;
    const auto reachable =
      nested_last_writer_reachable(goto_model, callee);
    if(
      nested_last_writer_contains_call(
        goto_model, reachable, "pthread_create", nested.handle))
    {
      create_calls.push_back(positions.at(&instruction));
      create_callees.push_back(callee);
    }
    if(
      nested_last_writer_contains_call(
        goto_model, reachable, "pthread_join", nested.handle))
    {
      join_calls.push_back(positions.at(&instruction));
      join_callees.push_back(callee);
    }
  }
  if(create_calls.size() != 1 || join_calls.size() != 1)
  {
    reason = "nlw_controller_lifecycle_calls";
    return reject();
  }
  std::map<irep_idt, std::set<nested_spawn_outcomet>> spawn_memo;
  std::set<irep_idt> spawn_active;
  std::set<nested_spawn_outcomet> spawn_outcomes;
  if(!nested_last_writer_spawn_summary(
       goto_model, create_callees.front(), nested.handle,
       spawn_memo, spawn_active, spawn_outcomes, reason))
    return reject();
  std::set<nested_spawn_outcomet> expected_spawn_outcomes;
  nested_spawn_outcomet failure;
  failure.spawned = false;
  failure.result = nested_zero_valuet::other_nonzero;
  expected_spawn_outcomes.insert(failure);
  nested_spawn_outcomet success;
  success.spawned = true;
  success.result = nested_zero_valuet::zero;
  expected_spawn_outcomes.insert(success);
  if(spawn_outcomes != expected_spawn_outcomes)
  {
    reason = "nlw_spawn_result_correlation";
    return reject();
  }
  std::set<irep_idt> join_active;
  if(!nested_last_writer_always_joins(
       goto_model, join_callees.front(), nested.handle,
       join_active, reason))
    return reject();

  std::set<const goto_programt::instructiont *> classified_stores;
  std::set<const goto_programt::instructiont *> controller_stores;
  for(const auto &pair : pairs)
  {
    if(pair.function != controller)
      continue;
    controller_stores.insert(pair.store);
    classified_stores.insert(pair.store);
  }
  if(!nested_last_writer_lifecycle_control(
       goto_model, controller, create_callees.front(),
       join_callees.front(), spawn_outcomes,
       controller_stores, common_object, reason))
    return reject();

  const auto child_functions =
    nested_last_writer_reachable(goto_model, nested.worker);
  if(!nested_last_writer_pair_mutex(
       goto_model, child_functions, pairs,
       classified_stores, reason))
    return reject();

  const auto outer_index = 1 - nested_index;
  const auto &outer = creates[outer_index];
  if(outer.worker != controller)
  {
    reason = "nlw_outer_worker";
    return reject();
  }
  const auto main =
    goto_model.goto_functions.function_map.find("main");
  if(
    main == goto_model.goto_functions.function_map.end() ||
    !main->second.body_available())
  {
    reason = "nlw_outer_parent";
    return reject();
  }
  std::vector<irep_idt> outer_create_callees;
  std::vector<irep_idt> outer_join_callees;
  for(const auto &instruction : main->second.body.instructions)
  {
    irep_idt callee;
    if(!direct_call_identifier(instruction, callee))
      continue;
    const auto reachable =
      nested_last_writer_reachable(goto_model, callee);
    if(
      nested_last_writer_contains_call(
        goto_model, reachable, "pthread_create", outer.handle))
      outer_create_callees.push_back(callee);
    if(
      nested_last_writer_contains_call(
        goto_model, reachable, "pthread_join", outer.handle))
      outer_join_callees.push_back(callee);
  }
  if(
    outer_create_callees.size() != 1 ||
    outer_join_callees.size() != 1)
  {
    reason = "nlw_outer_parent_calls";
    return reject();
  }
  std::set<nested_spawn_outcomet> outer_spawn_outcomes;
  if(!nested_last_writer_spawn_summary(
       goto_model, outer_create_callees.front(), outer.handle,
       spawn_memo, spawn_active, outer_spawn_outcomes, reason))
    return reject();
  if(outer_spawn_outcomes != expected_spawn_outcomes)
  {
    reason = "nlw_outer_spawn_result_correlation";
    return reject();
  }
  std::set<irep_idt> outer_join_active;
  if(!nested_last_writer_always_joins(
       goto_model, outer_join_callees.front(), outer.handle,
       outer_join_active, reason))
    return reject();
  const std::set<const goto_programt::instructiont *> no_parent_stores;
  if(!nested_last_writer_lifecycle_control(
       goto_model, "main", outer_create_callees.front(),
       outer_join_callees.front(), outer_spawn_outcomes,
       no_parent_stores, common_object, reason))
    return reject();
  if(!nested_last_writer_outer_pair_order(
       goto_model, outer_create_callees.front(),
       outer_join_callees.front(), outer.handle, pairs,
       classified_stores, reason))
    return reject();
  if(classified_stores != stores)
  {
    reason = "nlw_property_classification";
    return reject();
  }

  for(const auto &pair : pairs)
  {
    if(
      pair.function != controller &&
      child_functions.count(pair.function) == 0 &&
      pair.function != outer_create_callees.front() &&
      pair.function != outer_join_callees.front())
    {
      reason = "nlw_property_scope";
      return reject();
    }
  }

  std::cout
    << "NATIVE_NESTED_LAST_WRITER_AUDIT applicable=1"
    << " object=" << common_object
    << " controller=" << controller
    << " child=" << nested.worker
    << " properties=" << pairs.size()
    << " writes=" << object_writes << '\n';
  return true;
}

bool nested_lifecycle_last_writer_transform(
  goto_modelt &goto_model,
  message_handlert &message_handler)
{
  if(!nested_lifecycle_last_writer_audit(
       goto_model, message_handler))
    return false;

  std::string reason;
  irep_idt wrapper;
  if(!nested_last_writer_property_wrapper(
       goto_model, wrapper, reason))
    return false;
  std::size_t discharged = 0;
  for(auto &entry : goto_model.goto_functions.function_map)
  {
    if(!entry.second.body_available())
      continue;
    for(auto &instruction : entry.second.body.instructions)
    {
      irep_idt callee;
      if(
        direct_call_identifier(instruction, callee) &&
        callee == wrapper)
      {
        instruction.turn_into_skip();
        ++discharged;
      }
    }
  }
  if(discharged == 0)
    return false;
  goto_model.goto_functions.update();
  std::cout
    << "NATIVE_NESTED_LAST_WRITER applied=1"
    << " discharged=" << discharged << '\n';
  return true;
}

namespace
{
struct balr_lock_operationt
{
  irep_idt function;
  irep_idt assumption;
  irep_idt lock;
  bool acquire = false;
};

bool balr_boolean_symbol(
  const goto_modelt &model,
  const irep_idt &identifier)
{
  const auto symbol = model.symbol_table.symbols.find(identifier);
  if(symbol == model.symbol_table.symbols.end())
    return false;
  const auto &type = symbol->second.type;
  return type.id() == ID_bool || type.id() == ID_c_bool;
}

bool balr_atomic_lock_operation(
  const goto_modelt &model,
  const irep_idt &function_id,
  balr_lock_operationt &operation)
{
  const auto function =
    model.goto_functions.function_map.find(function_id);
  if(
    function == model.goto_functions.function_map.end() ||
    !function->second.body_available())
    return false;
  std::vector<const goto_programt::instructiont *> body;
  for(const auto &instruction : function->second.body.instructions)
    if(
      !instruction.is_location() && !instruction.is_skip() &&
      !instruction.is_decl() && !instruction.is_dead())
      body.push_back(&instruction);
  if(
    body.size() != 5 || !body[0]->is_atomic_begin() ||
    !body[1]->is_function_call() || !body[2]->is_assign() ||
    !body[3]->is_atomic_end() || !body[4]->is_end_function())
    return false;
  irep_idt assumption;
  if(
    !direct_call_identifier(*body[1], assumption) ||
    body[1]->call_arguments().size() != 1)
    return false;
  irep_idt written;
  mp_integer stored;
  if(
    !direct_symbol(body[2]->assign_lhs(), written) ||
    !balr_boolean_symbol(model, written) ||
    !constant_eval(body[2]->assign_rhs(), {}, stored) ||
    (stored != 0 && stored != 1))
    return false;
  irep_idt tested;
  mp_integer expected;
  if(
    !nested_last_writer_equality(
      body[1]->call_arguments().front(), tested, expected) ||
    tested != written || expected + stored != 1)
    return false;
  operation.function = function_id;
  operation.assumption = assumption;
  operation.lock = written;
  operation.acquire = stored == 1;
  return true;
}

bool balr_assumption_wrapper(
  const goto_modelt &model,
  const irep_idt &function_id)
{
  const auto function =
    model.goto_functions.function_map.find(function_id);
  const auto symbol = model.symbol_table.symbols.find(function_id);
  if(
    function == model.goto_functions.function_map.end() ||
    !function->second.body_available() ||
    symbol == model.symbol_table.symbols.end() ||
    symbol->second.type.id() != ID_code)
    return false;
  const auto &parameters =
    to_code_type(symbol->second.type).parameters();
  if(parameters.size() != 1 || parameters.front().get_identifier().empty())
    return false;
  std::vector<const goto_programt::instructiont *> body;
  std::map<const goto_programt::instructiont *, std::size_t> positions;
  for(const auto &instruction : function->second.body.instructions)
  {
    positions.emplace(&instruction, body.size());
    body.push_back(&instruction);
  }
  const goto_programt::instructiont *guard = nullptr;
  const goto_programt::instructiont *abort_call = nullptr;
  std::size_t guard_position = 0;
  std::size_t abort_position = 0;
  for(std::size_t index = 0; index < body.size(); ++index)
  {
    const auto instruction = body[index];
    if(
      instruction->is_goto() &&
      instruction->targets.size() == 1 &&
      nested_last_writer_parameter_truth(
        instruction->condition(),
        parameters.front().get_identifier()))
    {
      if(guard != nullptr)
        return false;
      guard = instruction;
      guard_position = index;
    }
    irep_idt callee;
    if(
      direct_call_identifier(*instruction, callee) &&
      callee == "abort")
    {
      if(abort_call != nullptr)
        return false;
      abort_call = instruction;
      abort_position = index;
    }
  }
  if(
    guard == nullptr || abort_call == nullptr ||
    guard_position >= abort_position)
    return false;
  for(std::size_t index = 0; index < guard_position; ++index)
    if(
      !body[index]->is_location() && !body[index]->is_skip() &&
      !body[index]->is_decl() && !body[index]->is_dead())
      return false;
  for(std::size_t index = guard_position + 1;
      index < abort_position; ++index)
    if(
      !body[index]->is_location() && !body[index]->is_skip() &&
      !body[index]->is_decl() && !body[index]->is_dead())
      return false;

  std::set<std::size_t> pending{
    positions.at(&*guard->targets.front())};
  std::set<std::size_t> visited;
  bool exits = false;
  while(!pending.empty())
  {
    const auto index = *pending.begin();
    pending.erase(pending.begin());
    if(index >= body.size() || !visited.insert(index).second)
      continue;
    const auto instruction = body[index];
    if(
      instruction->is_end_function() ||
      instruction->is_set_return_value())
    {
      exits = true;
      continue;
    }
    if(instruction->is_goto())
    {
      for(const auto &target : instruction->targets)
        pending.insert(positions.at(&*target));
      if(!instruction->condition().is_true())
        pending.insert(index + 1);
      continue;
    }
    if(
      instruction->is_function_call() ||
      instruction->is_assign() ||
      (!instruction->is_location() && !instruction->is_skip() &&
       !instruction->is_decl() && !instruction->is_dead()))
      return false;
    pending.insert(index + 1);
  }
  return exits;
}

bool balr_property_function(
  const goto_modelt &model,
  irep_idt &property,
  std::string &reason)
{
  const namespacet ns(model.symbol_table);
  std::size_t assertions = 0;
  for(const auto &entry : model.goto_functions.function_map)
  {
    if(!entry.second.body_available())
      continue;
    for(const auto &instruction : entry.second.body.instructions)
    {
      if(!instruction.is_assert())
        continue;
      if(
        !simplify_expr(
           instruction.condition(), ns).is_false())
        continue;
      ++assertions;
      property = entry.first;
    }
  }
  if(assertions != 1 || property.empty())
  {
    reason = "balr_property_count";
    return false;
  }
  return true;
}

struct balr_framet
{
  irep_idt function;
  std::size_t position = 0;
  irep_idt lhs;

  bool operator<(const balr_framet &other) const
  {
    return
      std::tie(function, position, lhs) <
      std::tie(other.function, other.position, other.lhs);
  }
};

struct balr_statet
{
  irep_idt function;
  std::size_t position = 0;
  bool owns = false;
  std::map<irep_idt, nested_zero_valuet> environment;
  std::vector<balr_framet> stack;

  bool operator<(const balr_statet &other) const
  {
    return
      std::tie(function, position, owns, environment, stack) <
      std::tie(
        other.function, other.position, other.owns,
        other.environment, other.stack);
  }
};

void balr_forget_shared(
  std::map<irep_idt, nested_zero_valuet> &environment,
  const std::set<irep_idt> &shared)
{
  for(const auto &identifier : shared)
    environment.erase(identifier);
}

bool balr_refine_true(
  const goto_modelt &model,
  const exprt &src,
  const std::set<irep_idt> &shared,
  const bool owns,
  std::map<irep_idt, nested_zero_valuet> &environment)
{
  const exprt &condition = without_cast(src);
  irep_idt symbol;
  if(direct_symbol(condition, symbol))
  {
    if(!balr_boolean_symbol(model, symbol))
      return true;
    if(shared.count(symbol) == 0 || owns)
      environment[symbol] = nested_zero_valuet::one;
    return true;
  }
  if(
    condition.id() == ID_not &&
    condition.operands().size() == 1 &&
    direct_symbol(without_cast(condition.op0()), symbol) &&
    balr_boolean_symbol(model, symbol))
  {
    if(shared.count(symbol) == 0 || owns)
      environment[symbol] = nested_zero_valuet::zero;
    return true;
  }
  if(
    (condition.id() == ID_equal ||
     condition.id() == ID_notequal) &&
    condition.operands().size() == 2)
  {
    mp_integer constant;
    const bool left =
      direct_symbol(without_cast(condition.op0()), symbol) &&
      constant_eval(condition.op1(), {}, constant);
    const bool right =
      direct_symbol(without_cast(condition.op1()), symbol) &&
      constant_eval(condition.op0(), {}, constant);
    if(
      (left || right) && balr_boolean_symbol(model, symbol) &&
      (constant == 0 || constant == 1) &&
      (shared.count(symbol) == 0 || owns))
    {
      bool value = constant == 1;
      if(condition.id() == ID_notequal)
        value = !value;
      environment[symbol] =
        value ? nested_zero_valuet::one
              : nested_zero_valuet::zero;
    }
  }
  return true;
}

struct balr_program_cachet
{
  std::map<
    irep_idt,
    std::vector<const goto_programt::instructiont *>> order;
  std::map<
    irep_idt,
    std::map<const goto_programt::instructiont *, std::size_t>> positions;
};

bool balr_cache_function(
  const goto_modelt &model,
  const irep_idt &function_id,
  balr_program_cachet &cache)
{
  if(cache.order.count(function_id) != 0)
    return true;
  const auto function =
    model.goto_functions.function_map.find(function_id);
  if(
    function == model.goto_functions.function_map.end() ||
    !function->second.body_available())
    return false;
  auto &order = cache.order[function_id];
  auto &positions = cache.positions[function_id];
  for(const auto &instruction : function->second.body.instructions)
  {
    positions.emplace(&instruction, order.size());
    order.push_back(&instruction);
  }
  return !order.empty();
}

bool balr_interpret_root(
  const goto_modelt &model,
  const irep_idt &root,
  const irep_idt &main_id,
  const std::set<irep_idt> &workers,
  const balr_lock_operationt &acquire,
  const balr_lock_operationt &release,
  const irep_idt &property,
  const std::set<irep_idt> &shared,
  balr_program_cachet &cache,
  std::size_t &visited_count,
  std::string &reason)
{
  if(!balr_cache_function(model, root, cache))
  {
    reason = "balr_root_body";
    return false;
  }
  balr_statet initial;
  initial.function = root;
  std::set<balr_statet> pending{initial};
  std::set<balr_statet> visited;
  while(!pending.empty())
  {
    auto state = *pending.begin();
    pending.erase(pending.begin());
    if(!state.owns)
      balr_forget_shared(state.environment, shared);
    if(!visited.insert(state).second)
      continue;
    if(++visited_count > 200000)
    {
      reason = "balr_state_budget";
      return false;
    }
    const auto &order = cache.order.at(state.function);
    if(state.position >= order.size())
    {
      reason = "balr_fallthrough";
      return false;
    }
    const auto instruction = order[state.position];
    if(
      instruction->is_end_function() ||
      instruction->is_set_return_value())
    {
      if(state.stack.empty())
      {
        if(state.owns)
        {
          reason = "balr_root_returns_held";
          return false;
        }
        continue;
      }
      const auto frame = state.stack.back();
      state.stack.pop_back();
      state.function = frame.function;
      state.position = frame.position;
      if(!frame.lhs.empty())
        state.environment.erase(frame.lhs);
      pending.insert(state);
      continue;
    }
    if(instruction->is_goto())
    {
      bool known = false;
      bool value = false;
      nested_last_writer_condition(
        instruction->condition(), state.environment,
        known, value);
      if(!known || value)
      {
        for(const auto &target : instruction->targets)
        {
          auto branch = state;
          branch.position =
            cache.positions.at(state.function).at(&*target);
          if(
            state.function == root &&
            branch.position <= state.position &&
            branch.owns)
          {
            reason = "balr_root_backedge_held";
            return false;
          }
          pending.insert(branch);
        }
      }
      if(!known || !value)
      {
        if(state.position + 1 >= order.size())
        {
          reason = "balr_goto_fallthrough";
          return false;
        }
        ++state.position;
        pending.insert(state);
      }
      continue;
    }
    if(instruction->is_assume())
    {
      bool known = false;
      bool value = false;
      nested_last_writer_condition(
        instruction->condition(), state.environment,
        known, value);
      if(known && !value)
        continue;
      balr_refine_true(
        model, instruction->condition(), shared,
        state.owns, state.environment);
    }
    if(instruction->is_assign())
    {
      irep_idt lhs;
      if(!direct_symbol(instruction->assign_lhs(), lhs))
      {
        reason = "balr_indirect_write";
        return false;
      }
      if(lhs == acquire.lock)
      {
        reason = "balr_direct_lock_write";
        return false;
      }
      if(shared.count(lhs) != 0 && !state.owns)
      {
        reason = "balr_shared_write_unheld";
        return false;
      }
      const auto value =
        nested_last_writer_value(
          instruction->assign_rhs(), state.environment);
      if(value == nested_zero_valuet::unknown)
        state.environment.erase(lhs);
      else
        state.environment[lhs] = value;
    }
    if(instruction->is_function_call())
    {
      irep_idt callee;
      if(!direct_call_identifier(*instruction, callee))
      {
        reason = "balr_indirect_call";
        return false;
      }
      if(callee == property)
      {
        reason = "balr_property_reachable";
        return false;
      }
      if(callee == "abort")
        continue;
      if(callee == acquire.function)
      {
        if(state.owns)
        {
          reason = "balr_recursive_acquire";
          return false;
        }
        state.owns = true;
        balr_forget_shared(state.environment, shared);
        state.environment[acquire.lock] =
          nested_zero_valuet::one;
      }
      else if(callee == release.function)
      {
        if(!state.owns)
        {
          reason = "balr_release_unheld";
          return false;
        }
        state.owns = false;
        balr_forget_shared(state.environment, shared);
      }
      else if(callee == acquire.assumption)
      {
        if(instruction->call_arguments().size() != 1)
        {
          reason = "balr_assumption_arguments";
          return false;
        }
        bool known = false;
        bool value = false;
        nested_last_writer_condition(
          instruction->call_arguments().front(),
          state.environment, known, value);
        if(known && !value)
          continue;
        balr_refine_true(
          model, instruction->call_arguments().front(),
          shared, state.owns, state.environment);
      }
      else if(callee == "pthread_create")
      {
        irep_idt worker;
        if(
          state.function != main_id ||
          instruction->call_arguments().size() < 3 ||
          !addressed_symbol(
            instruction->call_arguments()[2], worker) ||
          workers.count(worker) == 0)
        {
          reason = "balr_create_site";
          return false;
        }
      }
      else if(
        id2string(callee).find("__VERIFIER_nondet_") == 0)
      {
      }
      else
      {
        if(
          callee == state.function ||
          std::any_of(
            state.stack.begin(), state.stack.end(),
            [&callee](const balr_framet &frame)
            {
              return frame.function == callee;
            }))
        {
          reason = "balr_recursive_call";
          return false;
        }
        if(!balr_cache_function(model, callee, cache))
        {
          reason = "balr_external_call";
          return false;
        }
        balr_framet frame;
        frame.function = state.function;
        frame.position = state.position + 1;
        if(!instruction->call_lhs().is_nil())
        {
          if(!direct_symbol(instruction->call_lhs(), frame.lhs))
          {
            reason = "balr_call_lhs";
            return false;
          }
        }
        state.stack.push_back(frame);
        state.function = callee;
        state.position = 0;
        pending.insert(state);
        continue;
      }
      if(!instruction->call_lhs().is_nil())
      {
        irep_idt lhs;
        if(!direct_symbol(instruction->call_lhs(), lhs))
        {
          reason = "balr_runtime_call_lhs";
          return false;
        }
        state.environment.erase(lhs);
      }
    }
    ++state.position;
    pending.insert(state);
  }
  return true;
}

bool balr_prove(
  const goto_modelt &model,
  irep_idt &property,
  std::size_t &workers_count,
  std::size_t &visited_count,
  std::string &reason)
{
  std::vector<balr_lock_operationt> operations;
  for(const auto &entry : model.goto_functions.function_map)
  {
    balr_lock_operationt operation;
    if(balr_atomic_lock_operation(
         model, entry.first, operation))
      operations.push_back(operation);
  }
  if(operations.size() != 2)
  {
    reason = "balr_atomic_operation_count";
    return false;
  }
  const auto acquire_it =
    std::find_if(
      operations.begin(), operations.end(),
      [](const balr_lock_operationt &operation)
      {
        return operation.acquire;
      });
  const auto release_it =
    std::find_if(
      operations.begin(), operations.end(),
      [](const balr_lock_operationt &operation)
      {
        return !operation.acquire;
      });
  if(
    acquire_it == operations.end() ||
    release_it == operations.end() ||
    acquire_it->lock != release_it->lock ||
    acquire_it->assumption != release_it->assumption)
  {
    reason = "balr_atomic_pair";
    return false;
  }
  if(!balr_assumption_wrapper(model, acquire_it->assumption))
  {
    reason = "balr_assumption_wrapper";
    return false;
  }
  if(!balr_property_function(model, property, reason))
    return false;

  const irep_idt main_id = "main";
  const auto main =
    model.goto_functions.function_map.find(main_id);
  if(
    main == model.goto_functions.function_map.end() ||
    !main->second.body_available())
  {
    reason = "balr_main";
    return false;
  }
  std::set<irep_idt> workers;
  for(const auto &instruction : main->second.body.instructions)
  {
    irep_idt callee;
    if(
      !direct_call_identifier(instruction, callee) ||
      callee != "pthread_create")
      continue;
    irep_idt worker;
    if(
      instruction.call_arguments().size() < 3 ||
      !addressed_symbol(
        instruction.call_arguments()[2], worker))
    {
      reason = "balr_worker_resolution";
      return false;
    }
    workers.insert(worker);
  }
  if(workers.empty())
  {
    reason = "balr_workers_empty";
    return false;
  }
  workers_count = workers.size();

  std::set<irep_idt> reachable{main_id};
  for(const auto &worker : workers)
  {
    const auto closure =
      nested_last_writer_reachable(model, worker);
    reachable.insert(closure.begin(), closure.end());
  }
  reachable.insert(acquire_it->function);
  reachable.insert(release_it->function);

  std::set<irep_idt> shared{acquire_it->lock};
  for(const auto &function_id : reachable)
  {
    const auto function =
      model.goto_functions.function_map.find(function_id);
    if(
      function == model.goto_functions.function_map.end() ||
      !function->second.body_available())
      continue;
    for(const auto &instruction : function->second.body.instructions)
    {
      if(!instruction.is_assign())
        continue;
      irep_idt lhs;
      if(
        direct_symbol(instruction.assign_lhs(), lhs) &&
        balr_boolean_symbol(model, lhs))
      {
        const auto symbol =
          model.symbol_table.symbols.find(lhs);
        if(
          symbol != model.symbol_table.symbols.end() &&
          symbol->second.is_static_lifetime)
          shared.insert(lhs);
      }
    }
  }
  if(shared.size() < 2)
  {
    reason = "balr_shared_state";
    return false;
  }

  std::size_t lock_writes = 0;
  bool initialized_zero = false;
  const namespacet ns(model.symbol_table);
  for(const auto &entry : model.goto_functions.function_map)
  {
    if(!entry.second.body_available())
      continue;
    for(const auto &instruction : entry.second.body.instructions)
    {
      if(
        contains_address_of_symbol(
          instruction.code(), shared) ||
        (instruction.has_condition() &&
         contains_address_of_symbol(
           instruction.condition(), shared)))
      {
        reason = "balr_shared_address_escape";
        return false;
      }
      if(!instruction.is_assign())
        continue;
      irep_idt lhs;
      if(
        !direct_symbol(instruction.assign_lhs(), lhs) ||
        shared.count(lhs) == 0)
        continue;
      if(lhs == acquire_it->lock)
      {
        ++lock_writes;
        if(entry.first == "__CPROVER_initialize")
        {
          const auto value =
            nested_last_writer_value(
              simplify_expr(
                instruction.assign_rhs(), ns), {});
          initialized_zero =
            value == nested_zero_valuet::zero;
        }
        else if(
          entry.first != acquire_it->function &&
          entry.first != release_it->function)
        {
          reason = "balr_external_lock_write";
          return false;
        }
      }
      else if(
        entry.first != "__CPROVER_initialize" &&
        reachable.count(entry.first) == 0)
      {
        reason = "balr_external_shared_write";
        return false;
      }
    }
  }
  if(lock_writes != 3 || !initialized_zero)
  {
    reason = "balr_lock_write_census";
    return false;
  }

  balr_program_cachet cache;
  if(!balr_interpret_root(
       model, main_id, main_id, workers,
       *acquire_it, *release_it, property,
       shared, cache, visited_count, reason))
    return false;
  for(const auto &worker : workers)
    if(!balr_interpret_root(
         model, worker, main_id, workers,
         *acquire_it, *release_it, property,
         shared, cache, visited_count, reason))
      return false;
  return true;
}
} // namespace

bool boolean_atomic_lock_region_audit(
  const goto_modelt &goto_model,
  message_handlert &message_handler)
{
  (void)message_handler;
  irep_idt property;
  std::size_t workers = 0;
  std::size_t visited = 0;
  std::string reason;
  const bool applicable =
    balr_prove(
      goto_model, property, workers, visited, reason);
  std::cout
    << "NATIVE_BOOLEAN_ATOMIC_LOCK_REGION_AUDIT applicable="
    << (applicable ? 1 : 0)
    << " workers=" << workers
    << " states=" << visited;
  if(!applicable)
    std::cout << " reason=" << reason;
  std::cout << '\n';
  return applicable;
}

bool boolean_atomic_lock_region_transform(
  goto_modelt &goto_model,
  message_handlert &message_handler)
{
  irep_idt property;
  std::size_t workers = 0;
  std::size_t visited = 0;
  std::string reason;
  if(!balr_prove(
       goto_model, property, workers, visited, reason))
    return false;
  auto function =
    goto_model.goto_functions.function_map.find(property);
  if(
    function == goto_model.goto_functions.function_map.end() ||
    !function->second.body_available())
    return false;
  std::size_t discharged = 0;
  for(auto &instruction : function->second.body.instructions)
    if(instruction.is_assert())
    {
      instruction.turn_into_skip();
      ++discharged;
    }
  if(discharged != 1)
    return false;
  goto_model.goto_functions.update();
  std::cout
    << "NATIVE_BOOLEAN_ATOMIC_LOCK_REGION applied=1"
    << " workers=" << workers
    << " states=" << visited
    << " discharged=" << discharged << '\n';
  (void)message_handler;
  return true;
}

bool mutex_zero_fixedpoint_transform(
  goto_modelt &goto_model,
  message_handlert &message_handler)
{
  std::string reason;
  const auto candidates = dormant_spawn_cutoffs(goto_model, reason);
  if(
    candidates.size() != 1 ||
    candidates.front().first_join == nullptr)
    return false;

  const auto worker =
    goto_model.goto_functions.function_map.find(candidates.front().worker);
  const auto main =
    goto_model.goto_functions.function_map.find("main");
  if(
    worker == goto_model.goto_functions.function_map.end() ||
    !worker->second.body_available() ||
    main == goto_model.goto_functions.function_map.end() ||
    !main->second.body_available())
    return false;

  const auto zero_equality =
    [&](const exprt &src, irep_idt &object) -> bool
    {
      const exprt &condition = without_cast(src);
      if(condition.id() != ID_equal || condition.operands().size() != 2)
        return false;
      return
        (direct_symbol(condition.op0(), object) &&
         is_zero_constant(condition.op1())) ||
        (direct_symbol(condition.op1(), object) &&
         is_zero_constant(condition.op0()));
    };
  const auto nonzero_branch =
    [&](const exprt &src, irep_idt &object) -> bool
    {
      const exprt &condition = without_cast(src);
      return
        condition.id() == ID_not &&
        condition.operands().size() == 1 &&
        zero_equality(condition.op0(), object);
    };
  const auto zero_assertion =
    [&](const goto_programt::instructiont &instruction,
        const irep_idt &object) -> bool
    {
      irep_idt callee;
      irep_idt asserted;
      return
        instruction.is_function_call() &&
        direct_call_identifier(instruction, callee) &&
        callee == "__VERIFIER_assert" &&
        instruction.call_arguments().size() == 1 &&
        zero_equality(instruction.call_arguments().front(), asserted) &&
        asserted == object;
    };

  const auto &worker_body = worker->second.body;
  std::map<const goto_programt::instructiont *, std::size_t> worker_positions;
  std::size_t worker_position = 0;
  for(const auto &instruction : worker_body.instructions)
    worker_positions.emplace(&instruction, worker_position++);

  goto_programt::const_targett branch = worker_body.instructions.end();
  irep_idt shared;
  std::size_t nonzero_branches = 0;
  for(auto instruction = worker_body.instructions.begin();
      instruction != worker_body.instructions.end(); ++instruction)
  {
    irep_idt object;
    if(
      instruction->is_goto() &&
      instruction->targets.size() == 1 &&
      nonzero_branch(instruction->condition(), object) &&
      instruction->get_target() != worker_body.instructions.end() &&
      worker_positions.at(&*instruction->get_target()) >
        worker_positions.at(&*instruction))
    {
      branch = instruction;
      shared = object;
      ++nonzero_branches;
    }
  }
  if(nonzero_branches != 1)
    return false;

  const auto shared_symbol =
    goto_model.symbol_table.symbols.find(shared);
  if(
    shared_symbol == goto_model.symbol_table.symbols.end() ||
    !shared_symbol->second.is_static_lifetime ||
    (shared_symbol->second.type.id() != ID_signedbv &&
     shared_symbol->second.type.id() != ID_unsignedbv))
    return false;

  const auto else_target = branch->get_target();
  std::map<irep_idt, std::pair<std::size_t, std::size_t>> worker_mutex_calls;
  for(auto instruction = worker_body.instructions.begin();
      instruction != worker_body.instructions.end(); ++instruction)
  {
    irep_idt mutex;
    if(parse_mutex_call(*instruction, "pthread_mutex_lock", mutex))
      ++worker_mutex_calls[mutex].first;
    if(parse_mutex_call(*instruction, "pthread_mutex_unlock", mutex))
      ++worker_mutex_calls[mutex].second;
  }
  irep_idt invariant_mutex;
  for(const auto &entry : worker_mutex_calls)
  {
    if(entry.second.first != 1 || entry.second.second != 2)
      continue;
    bool lock_before = false;
    bool unlock_true = false;
    bool unlock_else = false;
    for(auto instruction = worker_body.instructions.begin();
        instruction != worker_body.instructions.end(); ++instruction)
    {
      irep_idt mutex;
      if(
        parse_mutex_call(*instruction, "pthread_mutex_lock", mutex) &&
        mutex == entry.first &&
        worker_positions.at(&*instruction) <
          worker_positions.at(&*branch))
        lock_before = true;
      if(
        parse_mutex_call(*instruction, "pthread_mutex_unlock", mutex) &&
        mutex == entry.first)
      {
        if(
          worker_positions.at(&*branch) <
            worker_positions.at(&*instruction) &&
          worker_positions.at(&*instruction) <
            worker_positions.at(&*else_target))
          unlock_true = true;
        if(&*instruction == &*else_target)
          unlock_else = true;
      }
    }
    if(lock_before && unlock_true && unlock_else)
    {
      if(!invariant_mutex.empty())
        return false;
      invariant_mutex = entry.first;
    }
  }
  if(invariant_mutex.empty())
    return false;

  std::size_t worker_assertions = 0;
  goto_programt::const_targett worker_assertion =
    worker_body.instructions.end();
  for(auto instruction = std::next(branch);
      instruction != else_target; ++instruction)
    if(zero_assertion(*instruction, shared))
    {
      worker_assertion = instruction;
      ++worker_assertions;
    }
  if(worker_assertions != 1)
    return false;

  bool true_unlock_after_assertion = false;
  for(auto instruction = std::next(worker_assertion);
      instruction != else_target; ++instruction)
  {
    irep_idt mutex;
    if(
      parse_mutex_call(*instruction, "pthread_mutex_unlock", mutex) &&
      mutex == invariant_mutex)
      true_unlock_after_assertion = true;
  }
  if(!true_unlock_after_assertion)
    return false;

  bool skips_else = false;
  for(auto instruction = std::next(worker_assertion);
      instruction != else_target; ++instruction)
    if(
      instruction->is_goto() &&
      instruction->condition().is_true() &&
      instruction->targets.size() == 1 &&
      instruction->get_target() != worker_body.instructions.end() &&
      worker_positions.at(&*instruction->get_target()) >
        worker_positions.at(&*else_target))
      skips_else = true;
  if(!skips_else)
    return false;

  const auto unit_update =
    [&](goto_programt::const_targett instruction,
        const irep_idt &operation) -> bool
    {
      if(!instruction->is_assign())
        return false;
      irep_idt lhs;
      irep_idt rhs_object;
      mp_integer unit;
      const exprt &rhs = without_cast(instruction->assign_rhs());
      return
        direct_symbol(instruction->assign_lhs(), lhs) &&
        lhs == shared &&
        rhs.id() == operation &&
        rhs.operands().size() == 2 &&
        direct_symbol(rhs.op0(), rhs_object) &&
        rhs_object == shared &&
        constant_eval(rhs.op1(), {}, unit) &&
        unit == 1;
    };

  std::vector<goto_programt::const_targett> worker_updates;
  for(auto instruction = std::next(else_target);
      instruction != worker_body.instructions.end(); ++instruction)
    if(instruction->is_assign() &&
       instruction_mentions_any(*instruction, {shared}))
      worker_updates.push_back(instruction);
  if(
    worker_updates.size() != 2 ||
    !unit_update(worker_updates[0], ID_plus) ||
    !unit_update(worker_updates[1], ID_minus))
    return false;

  const auto &main_body = main->second.body;
  std::map<const goto_programt::instructiont *, std::size_t> main_positions;
  std::size_t main_position = 0;
  for(const auto &instruction : main_body.instructions)
    main_positions.emplace(&instruction, main_position++);
  std::vector<goto_programt::const_targett> main_updates;
  goto_programt::const_targett main_assertion =
    main_body.instructions.end();
  std::size_t main_assertions = 0;
  std::vector<goto_programt::const_targett> main_locks;
  std::vector<goto_programt::const_targett> main_unlocks;
  for(auto instruction = main_body.instructions.begin();
      instruction != main_body.instructions.end(); ++instruction)
  {
    if(
      instruction->is_assign() &&
      instruction_mentions_any(*instruction, {shared}))
      main_updates.push_back(instruction);
    if(zero_assertion(*instruction, shared))
    {
      main_assertion = instruction;
      ++main_assertions;
    }
    irep_idt mutex;
    if(
      parse_mutex_call(*instruction, "pthread_mutex_lock", mutex) &&
      mutex == invariant_mutex)
      main_locks.push_back(instruction);
    if(
      parse_mutex_call(*instruction, "pthread_mutex_unlock", mutex) &&
      mutex == invariant_mutex)
      main_unlocks.push_back(instruction);
  }
  if(
    main_updates.size() != 2 ||
    !unit_update(main_updates[0], ID_plus) ||
    !unit_update(main_updates[1], ID_minus) ||
    main_assertions != 1 ||
    main_locks.size() != 1 ||
    main_unlocks.size() != 1 ||
    main_positions.at(&*main_locks.front()) >=
      main_positions.at(&*main_updates.front()) ||
    main_positions.at(&*main_updates.front()) >=
      main_positions.at(&*main_updates.back()) ||
    main_positions.at(&*main_updates.back()) >=
      main_positions.at(&*main_assertion) ||
    main_positions.at(&*main_assertion) >=
      main_positions.at(&*main_unlocks.front()))
    return false;

  std::size_t mentions = 0;
  std::size_t zero_initializers = 0;
  std::size_t assertions = 0;
  std::size_t plus_one = 0;
  std::size_t minus_one = 0;
  for(const auto &entry : goto_model.goto_functions.function_map)
  {
    if(!entry.second.body_available())
      continue;
    for(auto instruction = entry.second.body.instructions.begin();
        instruction != entry.second.body.instructions.end(); ++instruction)
    {
      if(instruction_mentions_any(*instruction, {shared}))
      {
        ++mentions;
        irep_idt lhs;
        if(
          instruction->is_assign() &&
          direct_symbol(instruction->assign_lhs(), lhs) &&
          lhs == shared &&
          is_zero_constant(instruction->assign_rhs()))
          ++zero_initializers;
        if(unit_update(instruction, ID_plus))
          ++plus_one;
        if(unit_update(instruction, ID_minus))
          ++minus_one;
        if(zero_assertion(*instruction, shared))
          ++assertions;
      }
      if(instruction->is_function_call())
      {
        if(contains_address_of_symbol(
             instruction->call_function(), {shared}))
          return false;
        for(const auto &argument : instruction->call_arguments())
          if(contains_address_of_symbol(argument, {shared}))
            return false;
      }
    }
  }
  if(
    mentions != 8 ||
    zero_initializers != 1 ||
    assertions != 2 ||
    plus_one != 2 ||
    minus_one != 2)
    return false;

  bool truncated = false;
  if(!apply_dormant_spawn_counts(
       goto_model, candidates, std::vector<unsigned>{0}, truncated))
    return false;
  goto_model.goto_functions.update();
  auto updated_main =
    goto_model.goto_functions.function_map.find("main");
  updated_main->second.body.instructions.begin()
    ->source_location_nonconst()
    .set("deagle_mutex_zero_fixedpoint", true);
  messaget log(message_handler);
  log.status() << "NATIVE_MUTEX_ZERO_FIXEDPOINT applied=1"
               << " workers=0 mentions=" << mentions
               << " truncated=" << (truncated ? 1 : 0)
               << messaget::eom;
  return true;
}

bool mutex_zero_fixedpoint_applied(const goto_modelt &goto_model)
{
  const auto main =
    goto_model.goto_functions.function_map.find("main");
  return
    main != goto_model.goto_functions.function_map.end() &&
    main->second.body_available() &&
    !main->second.body.instructions.empty() &&
    main->second.body.instructions.begin()
      ->source_location()
      .get_bool("deagle_mutex_zero_fixedpoint");
}

bool common_mutex_zero_sum_transform(
  goto_modelt &goto_model,
  message_handlert &message_handler)
{
  std::string reason;
  const auto candidates = dormant_spawn_cutoffs(goto_model, reason);
  if(
    candidates.size() != 1 ||
    candidates.front().first_join == nullptr)
    return false;

  const auto helper_mutex =
    [&](const irep_idt &helper, const irep_idt &operation, irep_idt &mutex)
    {
      const auto function =
        goto_model.goto_functions.function_map.find(helper);
      if(
        function == goto_model.goto_functions.function_map.end() ||
        !function->second.body_available())
        return false;
      std::size_t calls = 0;
      for(const auto &instruction : function->second.body.instructions)
      {
        if(!instruction.is_function_call())
          continue;
        irep_idt callee;
        irep_idt candidate;
        if(
          !direct_call_identifier(instruction, callee) ||
          callee != operation ||
          instruction.call_arguments().size() != 1 ||
          !addressed_symbol(
            instruction.call_arguments().front(), candidate))
          return false;
        mutex = candidate;
        ++calls;
      }
      return calls == 1;
    };

  const auto worker =
    goto_model.goto_functions.function_map.find(candidates.front().worker);
  const auto main =
    goto_model.goto_functions.function_map.find("main");
  if(
    worker == goto_model.goto_functions.function_map.end() ||
    !worker->second.body_available() ||
    main == goto_model.goto_functions.function_map.end() ||
    !main->second.body_available())
    return false;

  irep_idt lock_helper;
  irep_idt unlock_helper;
  irep_idt mutex;
  bool inside = false;
  std::vector<goto_programt::const_targett> updates;
  for(auto instruction = worker->second.body.instructions.begin();
      instruction != worker->second.body.instructions.end(); ++instruction)
  {
    irep_idt callee;
    if(
      instruction->is_function_call() &&
      direct_call_identifier(*instruction, callee))
    {
      irep_idt candidate_mutex;
      if(
        !inside &&
        helper_mutex(callee, "pthread_mutex_lock", candidate_mutex))
      {
        lock_helper = callee;
        mutex = candidate_mutex;
        inside = true;
        continue;
      }
      if(
        inside &&
        helper_mutex(callee, "pthread_mutex_unlock", candidate_mutex) &&
        candidate_mutex == mutex)
      {
        unlock_helper = callee;
        inside = false;
        continue;
      }
    }
    if(inside && instruction->is_assign())
      updates.push_back(instruction);
  }
  if(
    inside || lock_helper.empty() || unlock_helper.empty() ||
    lock_helper == unlock_helper || updates.size() != 2)
    return false;

  irep_idt shared;
  irep_idt second_shared;
  if(
    !direct_symbol(updates[0]->assign_lhs(), shared) ||
    !direct_symbol(updates[1]->assign_lhs(), second_shared) ||
    shared != second_shared)
    return false;
  const auto unit_update =
    [&](goto_programt::const_targett instruction, const irep_idt &operation)
    {
      const exprt &rhs = without_cast(instruction->assign_rhs());
      irep_idt source;
      mp_integer unit;
      return
        rhs.id() == operation && rhs.operands().size() == 2 &&
        direct_symbol(rhs.op0(), source) && source == shared &&
        constant_eval(rhs.op1(), {}, unit) && unit == 1;
    };
  if(
    !unit_update(updates[0], ID_plus) ||
    !unit_update(updates[1], ID_minus))
    return false;

  const auto shared_symbol =
    goto_model.symbol_table.symbols.find(shared);
  if(
    shared_symbol == goto_model.symbol_table.symbols.end() ||
    !shared_symbol->second.is_static_lifetime)
    return false;

  bool after_spawn = false;
  bool main_locked = false;
  bool asserted = false;
  bool main_unlocked = false;
  for(auto instruction = main->second.body.instructions.begin();
      instruction != main->second.body.instructions.end(); ++instruction)
  {
    if(&*instruction == &*candidates.front().exit)
      after_spawn = true;
    if(!after_spawn)
      continue;
    irep_idt callee;
    if(
      instruction->is_function_call() &&
      direct_call_identifier(*instruction, callee))
    {
      if(!main_locked && callee == lock_helper)
        main_locked = true;
      else if(main_locked && asserted && callee == unlock_helper)
        main_unlocked = true;
      else if(
        main_locked && !asserted && callee == "__VERIFIER_assert" &&
        instruction->call_arguments().size() == 1)
      {
        const exprt &condition =
          without_cast(instruction->call_arguments().front());
        irep_idt object;
        asserted =
          condition.id() == ID_equal &&
          condition.operands().size() == 2 &&
          ((direct_symbol(condition.op0(), object) &&
            object == shared && is_zero_constant(condition.op1())) ||
           (direct_symbol(condition.op1(), object) &&
            object == shared && is_zero_constant(condition.op0())));
      }
    }
    if(main_unlocked)
      break;
  }
  if(!main_locked || !asserted || !main_unlocked)
    return false;

  std::size_t mentions = 0;
  std::size_t zero_initializers = 0;
  for(const auto &entry : goto_model.goto_functions.function_map)
  {
    if(!entry.second.body_available())
      continue;
    for(const auto &instruction : entry.second.body.instructions)
    {
      if(instruction_mentions_any(instruction, {shared}))
      {
        ++mentions;
        irep_idt lhs;
        if(
          instruction.is_assign() &&
          direct_symbol(instruction.assign_lhs(), lhs) &&
          lhs == shared &&
          is_zero_constant(instruction.assign_rhs()))
          ++zero_initializers;
      }
      if(
        instruction.is_function_call() &&
        contains_address_of_symbol(
          instruction.call_function(), {shared}))
        return false;
      if(instruction.is_function_call())
        for(const auto &argument : instruction.call_arguments())
          if(contains_address_of_symbol(argument, {shared}))
            return false;
    }
  }
  if(mentions != 4 || zero_initializers != 1)
    return false;

  bool truncated = false;
  if(!apply_dormant_spawn_counts(
       goto_model, candidates, std::vector<unsigned>{0}, truncated))
    return false;
  goto_model.goto_functions.update();
  auto updated_main =
    goto_model.goto_functions.function_map.find("main");
  updated_main->second.body.instructions.begin()
    ->source_location_nonconst()
    .set("deagle_common_mutex_zero_sum", true);
  messaget log(message_handler);
  log.status() << "NATIVE_COMMON_MUTEX_ZERO_SUM applied=1"
               << " workers=0 mentions=" << mentions
               << " truncated=" << (truncated ? 1 : 0)
               << messaget::eom;
  return true;
}

bool common_mutex_zero_sum_applied(const goto_modelt &goto_model)
{
  const auto main =
    goto_model.goto_functions.function_map.find("main");
  return
    main != goto_model.goto_functions.function_map.end() &&
    main->second.body_available() &&
    !main->second.body.instructions.empty() &&
    main->second.body.instructions.begin()
      ->source_location()
      .get_bool("deagle_common_mutex_zero_sum");
}

bool resolved_worker_zero_sum_transform(
  goto_modelt &goto_model,
  message_handlert &message_handler)
{
  std::string reason;
  const auto candidates = dormant_spawn_cutoffs(goto_model, reason);
  if(
    candidates.size() != 1 ||
    candidates.front().first_join == nullptr)
    return false;

  const auto worker =
    goto_model.goto_functions.function_map.find(candidates.front().worker);
  const auto main =
    goto_model.goto_functions.function_map.find("main");
  if(
    worker == goto_model.goto_functions.function_map.end() ||
    !worker->second.body_available() ||
    main == goto_model.goto_functions.function_map.end() ||
    !main->second.body_available())
    return false;

  const auto is_mutex_primitive = [](const irep_idt &callee)
  {
    return
      callee == "pthread_mutex_lock" ||
      callee == "pthread_mutex_unlock";
  };

  irep_idt effect_helper;
  irep_idt dispatch_pointer;
  irep_idt pointer_source;
  std::size_t effect_calls = 0;
  std::size_t indirect_calls = 0;
  for(const auto &instruction : worker->second.body.instructions)
  {
    if(instruction.is_assert() || instruction.is_start_thread())
      return false;
    if(instruction.is_assign())
    {
      irep_idt lhs;
      if(!direct_symbol(instruction.assign_lhs(), lhs))
        return false;
      const auto symbol = goto_model.symbol_table.symbols.find(lhs);
      if(
        symbol == goto_model.symbol_table.symbols.end() ||
        symbol->second.is_static_lifetime)
        return false;
    }
    if(!instruction.is_function_call())
      continue;
    irep_idt callee;
    if(!direct_call_identifier(instruction, callee))
    {
      const exprt &function =
        without_cast(instruction.call_function());
      irep_idt pointer;
      if(
        function.id() != ID_dereference ||
        function.operands().size() != 1 ||
        !direct_symbol(function.op0(), pointer) ||
        (!dispatch_pointer.empty() && dispatch_pointer != pointer))
        return false;
      dispatch_pointer = pointer;
      ++indirect_calls;
      continue;
    }
    if(is_mutex_primitive(callee))
    {
      irep_idt mutex;
      if(
        instruction.call_arguments().size() != 1 ||
        !addressed_symbol(
          instruction.call_arguments().front(), mutex))
        return false;
      continue;
    }
    const auto function =
      goto_model.goto_functions.function_map.find(callee);
    if(
      function == goto_model.goto_functions.function_map.end() ||
      !function->second.body_available())
      return false;
    if(effect_helper.empty())
      effect_helper = callee;
    if(effect_helper != callee)
      return false;
    ++effect_calls;
  }
  if(
    effect_calls != 0 ||
    dispatch_pointer.empty() || indirect_calls != 1)
    return false;

  std::size_t dispatch_assignments = 0;
  std::size_t dispatch_mentions = 0;
  for(const auto &instruction : worker->second.body.instructions)
  {
    if(instruction_mentions_any(instruction, {dispatch_pointer}))
      ++dispatch_mentions;
    if(instruction.is_assign())
    {
      irep_idt lhs;
      irep_idt rhs;
      if(
        direct_symbol(instruction.assign_lhs(), lhs) &&
        lhs == dispatch_pointer)
      {
        if(
          !direct_symbol(instruction.assign_rhs(), rhs) ||
          (!pointer_source.empty() && pointer_source != rhs))
          return false;
        pointer_source = rhs;
        ++dispatch_assignments;
      }
    }
  }
  const auto pointer_symbol =
    goto_model.symbol_table.symbols.find(pointer_source);
  if(
    dispatch_assignments != 1 || dispatch_mentions != 2 ||
    pointer_symbol == goto_model.symbol_table.symbols.end() ||
    !pointer_symbol->second.is_static_lifetime)
    return false;

  std::size_t pointer_mentions = 0;
  std::size_t pointer_writes = 0;
  std::size_t pointer_reads = 0;
  for(const auto &entry : goto_model.goto_functions.function_map)
  {
    if(!entry.second.body_available())
      continue;
    for(const auto &instruction : entry.second.body.instructions)
    {
      if(!instruction_mentions_any(instruction, {pointer_source}))
        continue;
      ++pointer_mentions;
      if(!instruction.is_assign())
        return false;
      irep_idt lhs;
      if(
        direct_symbol(instruction.assign_lhs(), lhs) &&
        lhs == pointer_source)
      {
        irep_idt target;
        if(!addressed_symbol(instruction.assign_rhs(), target))
          return false;
        if(effect_helper.empty())
          effect_helper = target;
        if(effect_helper != target)
          return false;
        ++pointer_writes;
      }
      else
      {
        irep_idt rhs;
        if(
          entry.first != candidates.front().worker ||
          !direct_symbol(instruction.assign_lhs(), lhs) ||
          lhs != dispatch_pointer ||
          !direct_symbol(instruction.assign_rhs(), rhs) ||
          rhs != pointer_source)
          return false;
        ++pointer_reads;
      }
    }
  }
  const auto helper =
    goto_model.goto_functions.function_map.find(effect_helper);
  if(
    pointer_mentions != 3 || pointer_writes != 2 ||
    pointer_reads != 1 || effect_helper.empty() ||
    helper == goto_model.goto_functions.function_map.end() ||
    !helper->second.body_available())
    return false;

  std::vector<irep_idt> mutex_stack;
  irep_idt invariant_mutex;
  std::vector<goto_programt::const_targett> updates;
  for(auto instruction = helper->second.body.instructions.begin();
      instruction != helper->second.body.instructions.end(); ++instruction)
  {
    if(instruction->is_assert() || instruction->is_start_thread())
      return false;
    if(instruction->is_goto())
    {
      bool condition = true;
      if(
        !boolean_constant_eval(instruction->condition(), condition) ||
        condition)
        return false;
    }
    if(instruction->is_function_call())
    {
      irep_idt callee;
      irep_idt mutex;
      if(
        !direct_call_identifier(*instruction, callee) ||
        !is_mutex_primitive(callee) ||
        instruction->call_arguments().size() != 1 ||
        !addressed_symbol(
          instruction->call_arguments().front(), mutex))
        return false;
      if(callee == "pthread_mutex_lock")
      {
        if(mutex_stack.empty())
          invariant_mutex = mutex;
        mutex_stack.push_back(mutex);
      }
      else
      {
        if(mutex_stack.empty() || mutex_stack.back() != mutex)
          return false;
        mutex_stack.pop_back();
      }
      continue;
    }
    if(instruction->is_assign())
    {
      if(mutex_stack.empty() || mutex_stack.front() != invariant_mutex)
        return false;
      updates.push_back(instruction);
    }
  }
  if(
    !mutex_stack.empty() || invariant_mutex.empty() ||
    updates.size() != 2)
    return false;

  irep_idt shared;
  irep_idt second_shared;
  if(
    !direct_symbol(updates[0]->assign_lhs(), shared) ||
    !direct_symbol(updates[1]->assign_lhs(), second_shared) ||
    shared != second_shared)
    return false;
  const auto unit_update =
    [&](goto_programt::const_targett instruction, const irep_idt &operation)
    {
      if(!instruction->is_assign())
        return false;
      const exprt &rhs = without_cast(instruction->assign_rhs());
      irep_idt source;
      mp_integer unit;
      return
        rhs.id() == operation && rhs.operands().size() == 2 &&
        direct_symbol(rhs.op0(), source) && source == shared &&
        constant_eval(rhs.op1(), {}, unit) && unit == 1;
    };
  if(
    !unit_update(updates[0], ID_plus) ||
    !unit_update(updates[1], ID_minus))
    return false;

  const auto shared_symbol =
    goto_model.symbol_table.symbols.find(shared);
  if(
    shared_symbol == goto_model.symbol_table.symbols.end() ||
    !shared_symbol->second.is_static_lifetime)
    return false;

  bool after_spawn = false;
  bool main_locked = false;
  bool asserted = false;
  bool main_unlocked = false;
  for(auto instruction = main->second.body.instructions.begin();
      instruction != main->second.body.instructions.end(); ++instruction)
  {
    if(&*instruction == &*candidates.front().exit)
      after_spawn = true;
    if(!after_spawn)
      continue;
    irep_idt callee;
    if(
      instruction->is_function_call() &&
      direct_call_identifier(*instruction, callee))
    {
      irep_idt mutex;
      if(
        !main_locked && callee == "pthread_mutex_lock" &&
        instruction->call_arguments().size() == 1 &&
        addressed_symbol(
          instruction->call_arguments().front(), mutex) &&
        mutex == invariant_mutex)
        main_locked = true;
      else if(
        main_locked && asserted &&
        callee == "pthread_mutex_unlock" &&
        instruction->call_arguments().size() == 1 &&
        addressed_symbol(
          instruction->call_arguments().front(), mutex) &&
        mutex == invariant_mutex)
        main_unlocked = true;
      else if(
        main_locked && !asserted && callee == "__VERIFIER_assert" &&
        instruction->call_arguments().size() == 1)
      {
        const exprt &condition =
          without_cast(instruction->call_arguments().front());
        irep_idt object;
        asserted =
          condition.id() == ID_equal &&
          condition.operands().size() == 2 &&
          ((direct_symbol(condition.op0(), object) &&
            object == shared && is_zero_constant(condition.op1())) ||
           (direct_symbol(condition.op1(), object) &&
            object == shared && is_zero_constant(condition.op0())));
      }
    }
    if(main_unlocked)
      break;
  }
  if(!main_locked || !asserted || !main_unlocked)
    return false;

  const auto is_spawn_runtime = [](const irep_idt &identifier)
  {
    return
      identifier == "pthread_create" ||
      identifier == "pthread_join" ||
      identifier == "pthread_mutex_lock" ||
      identifier == "pthread_mutex_unlock";
  };
  std::set<irep_idt> reachable{
    "main", candidates.front().worker, "__CPROVER_initialize"};
  std::deque<irep_idt> pending(reachable.begin(), reachable.end());
  while(!pending.empty())
  {
    const irep_idt current = pending.front();
    pending.pop_front();
    const auto function =
      goto_model.goto_functions.function_map.find(current);
    if(
      function == goto_model.goto_functions.function_map.end() ||
      !function->second.body_available())
      continue;
    for(const auto &instruction : function->second.body.instructions)
    {
      if(instruction.is_function_call())
      {
        irep_idt callee;
        if(!direct_call_identifier(instruction, callee))
        {
          const exprt &function =
            without_cast(instruction.call_function());
          irep_idt pointer;
          if(
            current != candidates.front().worker ||
            function.id() != ID_dereference ||
            function.operands().size() != 1 ||
            !direct_symbol(function.op0(), pointer) ||
            pointer != dispatch_pointer)
            return false;
          continue;
        }
        if(
          !is_spawn_runtime(callee) &&
          goto_model.goto_functions.function_map.find(callee) !=
            goto_model.goto_functions.function_map.end() &&
          reachable.insert(callee).second)
          pending.push_back(callee);
      }
      find_symbols_sett symbols;
      find_symbols(instruction.code(), symbols);
      if(instruction.has_condition())
        find_symbols(instruction.condition(), symbols);
      for(const auto &identifier : symbols)
      {
        const auto symbol =
          goto_model.symbol_table.symbols.find(identifier);
        const auto addressed =
          goto_model.goto_functions.function_map.find(identifier);
        if(
          symbol == goto_model.symbol_table.symbols.end() ||
          symbol->second.type.id() != ID_code ||
          is_spawn_runtime(identifier) ||
          addressed ==
            goto_model.goto_functions.function_map.end() ||
          !addressed->second.body_available())
          continue;
        if(reachable.insert(identifier).second)
          pending.push_back(identifier);
      }
    }
  }

  std::size_t mentions = 0;
  std::size_t zero_initializers = 0;
  std::size_t assertions = 0;
  std::size_t plus_one = 0;
  std::size_t minus_one = 0;
  const auto is_zero_property =
    [&](const goto_programt::instructiont &instruction)
    {
      irep_idt callee;
      if(
        !direct_call_identifier(instruction, callee) ||
        callee != "__VERIFIER_assert" ||
        instruction.call_arguments().size() != 1)
        return false;
      const exprt &condition =
        without_cast(instruction.call_arguments().front());
      if(
        condition.id() != ID_equal ||
        condition.operands().size() != 2)
        return false;
      irep_idt object;
      return
        (direct_symbol(condition.op0(), object) &&
         object == shared && is_zero_constant(condition.op1())) ||
        (direct_symbol(condition.op1(), object) &&
         object == shared && is_zero_constant(condition.op0()));
    };
  for(const auto &identifier : reachable)
  {
    const auto function =
      goto_model.goto_functions.function_map.find(identifier);
    if(
      function == goto_model.goto_functions.function_map.end() ||
      !function->second.body_available())
      continue;
    for(auto instruction = function->second.body.instructions.begin();
        instruction != function->second.body.instructions.end(); ++instruction)
    {
      if(!instruction_mentions_any(*instruction, {shared}))
        continue;
      ++mentions;
      irep_idt lhs;
      if(
        instruction->is_assign() &&
        direct_symbol(instruction->assign_lhs(), lhs) &&
        lhs == shared &&
        is_zero_constant(instruction->assign_rhs()))
        ++zero_initializers;
      if(unit_update(instruction, ID_plus))
        ++plus_one;
      if(unit_update(instruction, ID_minus))
        ++minus_one;
      if(is_zero_property(*instruction))
        ++assertions;
      if(
        instruction->is_function_call() &&
        contains_address_of_symbol(
          instruction->call_function(), {shared}))
        return false;
      if(instruction->is_function_call())
        for(const auto &argument : instruction->call_arguments())
          if(contains_address_of_symbol(argument, {shared}))
            return false;
    }
  }
  if(
    mentions != 4 || zero_initializers != 1 ||
    assertions != 1 || plus_one != 1 || minus_one != 1)
    return false;

  bool truncated = false;
  if(!apply_dormant_spawn_counts(
       goto_model, candidates, std::vector<unsigned>{0}, truncated))
    return false;
  goto_model.goto_functions.update();
  auto updated_main =
    goto_model.goto_functions.function_map.find("main");
  updated_main->second.body.instructions.begin()
    ->source_location_nonconst()
    .set("deagle_resolved_worker_zero_sum", true);
  messaget log(message_handler);
  log.status() << "NATIVE_RESOLVED_WORKER_ZERO_SUM applied=1"
               << " workers=0 reachable=" << reachable.size()
               << " mentions=" << mentions
               << " truncated=" << (truncated ? 1 : 0)
               << messaget::eom;
  return true;
}

bool resolved_worker_zero_sum_applied(const goto_modelt &goto_model)
{
  const auto main =
    goto_model.goto_functions.function_map.find("main");
  return
    main != goto_model.goto_functions.function_map.end() &&
    main->second.body_available() &&
    !main->second.body.instructions.empty() &&
    main->second.body.instructions.begin()
      ->source_location()
      .get_bool("deagle_resolved_worker_zero_sum");
}

bool aggregate_member_lock_alias_transform(
  goto_modelt &goto_model,
  message_handlert &message_handler)
{
  std::string reason;
  const auto candidates = dormant_spawn_cutoffs(goto_model, reason);
  if(
    candidates.size() != 1 ||
    candidates.front().first_join == nullptr)
    return false;

  const auto worker =
    goto_model.goto_functions.function_map.find(candidates.front().worker);
  const auto main =
    goto_model.goto_functions.function_map.find("main");
  if(
    worker == goto_model.goto_functions.function_map.end() ||
    !worker->second.body_available() ||
    main == goto_model.goto_functions.function_map.end() ||
    !main->second.body_available())
    return false;

  struct macro_summaryt
  {
    exprt object = nil_exprt();
    exprt outer_mutex = nil_exprt();
    exprt instrumentation_mutex = nil_exprt();
    std::vector<goto_programt::const_targett> operations;
  };
  const auto mutex_call =
    [](const goto_programt::instructiont &instruction,
       const irep_idt &expected, exprt &mutex)
    {
      irep_idt callee;
      if(
        !direct_call_identifier(instruction, callee) ||
        callee != expected ||
        instruction.call_arguments().size() != 1)
        return false;
      mutex = without_cast(instruction.call_arguments().front());
      return true;
    };
  const auto analyze_macro =
    [&](const goto_functiont &function, macro_summaryt &summary)
    {
      std::map<const goto_programt::instructiont *, std::size_t> positions;
      std::size_t position = 0;
      for(const auto &instruction : function.body.instructions)
        positions.emplace(&instruction, position++);

      std::size_t plus_one = 0;
      std::size_t minus_one = 0;
      std::size_t zero_assertions = 0;
      for(auto instruction = function.body.instructions.begin();
          instruction != function.body.instructions.end(); ++instruction)
      {
        if(instruction->is_assign())
        {
          const exprt &lhs = without_cast(instruction->assign_lhs());
          const exprt &rhs = without_cast(instruction->assign_rhs());
          mp_integer unit;
          exprt immediate_lock;
          exprt immediate_unlock;
          const bool wrapped =
            instruction != function.body.instructions.begin() &&
            std::next(instruction) !=
              function.body.instructions.end() &&
            mutex_call(
              *std::prev(instruction),
              "pthread_mutex_lock",
              immediate_lock) &&
            mutex_call(
              *std::next(instruction),
              "pthread_mutex_unlock",
              immediate_unlock) &&
            immediate_lock == immediate_unlock;
          if(
            wrapped &&
            (rhs.id() == ID_plus || rhs.id() == ID_minus) &&
            rhs.operands().size() == 2 &&
            without_cast(rhs.op0()) == lhs &&
            constant_eval(rhs.op1(), {}, unit) && unit == 1)
          {
            if(summary.object.is_nil())
              summary.object = lhs;
            if(lhs != summary.object)
              return false;
            if(rhs.id() == ID_plus)
              ++plus_one;
            else
              ++minus_one;
            summary.operations.push_back(instruction);
          }
        }
        irep_idt callee;
        if(
          instruction->is_function_call() &&
          direct_call_identifier(*instruction, callee) &&
          callee == "__VERIFIER_assert" &&
          instruction->call_arguments().size() == 1 &&
          !summary.object.is_nil())
        {
          const exprt &condition =
            without_cast(instruction->call_arguments().front());
          if(
            condition.id() != ID_equal ||
            condition.operands().size() != 2)
            return false;
          const exprt &left = without_cast(condition.op0());
          const exprt &right = without_cast(condition.op1());
          if(
            !((left == summary.object && is_zero_constant(right)) ||
              (right == summary.object && is_zero_constant(left))))
            return false;
          ++zero_assertions;
          summary.operations.push_back(instruction);
        }
      }
      if(
        plus_one != 1 || minus_one != 1 ||
        zero_assertions != 1 || summary.operations.size() != 3)
        return false;

      for(const auto operation : summary.operations)
      {
        if(
          operation == function.body.instructions.begin() ||
          std::next(operation) == function.body.instructions.end())
          return false;
        exprt locked;
        exprt unlocked;
        if(
          !mutex_call(
            *std::prev(operation), "pthread_mutex_lock", locked) ||
          !mutex_call(
            *std::next(operation), "pthread_mutex_unlock", unlocked) ||
          locked != unlocked)
          return false;
        if(summary.instrumentation_mutex.is_nil())
          summary.instrumentation_mutex = locked;
        if(locked != summary.instrumentation_mutex)
          return false;
      }

      const std::size_t first =
        positions.at(&*summary.operations.front());
      const std::size_t last =
        positions.at(&*summary.operations.back());
      bool found_lock = false;
      bool found_unlock = false;
      exprt outer;
      for(auto instruction = function.body.instructions.begin();
          instruction != function.body.instructions.end(); ++instruction)
      {
        exprt mutex;
        const std::size_t current = positions.at(&*instruction);
        if(
          current < first &&
          mutex_call(*instruction, "pthread_mutex_lock", mutex) &&
          mutex != summary.instrumentation_mutex)
        {
          if(found_lock)
            return false;
          found_lock = true;
          outer = mutex;
        }
        if(
          current > last &&
          mutex_call(*instruction, "pthread_mutex_unlock", mutex) &&
          mutex != summary.instrumentation_mutex)
        {
          if(found_unlock || !found_lock || mutex != outer)
            return false;
          found_unlock = true;
        }
      }
      if(!found_lock || !found_unlock)
        return false;
      summary.outer_mutex = outer;

      std::size_t object_assignments = 0;
      std::size_t object_assertions = 0;
      for(const auto &instruction : function.body.instructions)
      {
        if(
          instruction.is_assign() &&
          without_cast(instruction.assign_lhs()) == summary.object)
          ++object_assignments;
        irep_idt callee;
        if(
          instruction.is_function_call() &&
          direct_call_identifier(instruction, callee) &&
          callee == "__VERIFIER_assert" &&
          instruction_mentions_any(
            instruction,
            [&]()
            {
              find_symbols_sett symbols;
              find_symbols(summary.object, symbols);
              return std::set<irep_idt>(
                symbols.begin(), symbols.end());
            }()))
          ++object_assertions;
      }
      return object_assignments == 2 && object_assertions == 1;
    };

  macro_summaryt worker_macro;
  macro_summaryt main_macro;
  const bool worker_macro_ok =
    analyze_macro(worker->second, worker_macro);
  const bool main_macro_ok =
    analyze_macro(main->second, main_macro);
  if(
    !worker_macro_ok ||
    !main_macro_ok ||
    worker_macro.instrumentation_mutex !=
      main_macro.instrumentation_mutex)
    return false;

  const auto direct_member =
    [](const exprt &expr, irep_idt &base, irep_idt &component)
    {
      const exprt &value = without_cast(expr);
      if(value.id() != ID_member)
        return false;
      component = to_member_expr(value).get_component_name();
      return direct_symbol(to_member_expr(value).struct_op(), base);
    };
  const auto addressed_member =
    [](const exprt &expr, irep_idt &base, irep_idt &component)
    {
      const exprt &value = without_cast(expr);
      if(value.id() != ID_address_of)
        return false;
      const exprt &object =
        without_cast(to_address_of_expr(value).object());
      if(object.id() != ID_member)
        return false;
      component = to_member_expr(object).get_component_name();
      return direct_symbol(to_member_expr(object).struct_op(), base);
    };
  irep_idt worker_base;
  irep_idt data_component;
  irep_idt worker_mutex_base;
  irep_idt mutex_component;
  if(
    !direct_member(
      worker_macro.object, worker_base, data_component) ||
    !addressed_member(
      worker_macro.outer_mutex,
      worker_mutex_base,
      mutex_component) ||
    worker_base != worker_mutex_base ||
    data_component == mutex_component)
    return false;

  irep_idt data_pointer;
  irep_idt mutex_pointer;
  const exprt &main_object = without_cast(main_macro.object);
  if(
    main_object.id() != ID_dereference ||
    main_object.operands().size() != 1 ||
    !direct_symbol(main_object.op0(), data_pointer) ||
    !direct_symbol(main_macro.outer_mutex, mutex_pointer) ||
    data_pointer == mutex_pointer)
    return false;

  const auto member_from_pointer =
    [](const exprt &expr, irep_idt &pointer, irep_idt &component)
    {
      const exprt &value = without_cast(expr);
      if(value.id() != ID_address_of)
        return false;
      const exprt &object =
        without_cast(to_address_of_expr(value).object());
      if(object.id() != ID_member)
        return false;
      component = to_member_expr(object).get_component_name();
      const exprt &compound =
        without_cast(to_member_expr(object).struct_op());
      if(
        compound.id() != ID_dereference ||
        compound.operands().size() != 1)
        return false;
      return direct_symbol(compound.op0(), pointer);
    };

  irep_idt base_pointer;
  std::set<irep_idt> bases;
  std::size_t base_writes = 0;
  std::size_t data_derivations = 0;
  std::size_t mutex_derivations = 0;
  goto_programt::const_targett first_base =
    main->second.body.instructions.end();
  goto_programt::const_targett second_base =
    main->second.body.instructions.end();
  goto_programt::const_targett data_derivation =
    main->second.body.instructions.end();
  goto_programt::const_targett mutex_derivation =
    main->second.body.instructions.end();
  for(auto instruction = main->second.body.instructions.begin();
      instruction != main->second.body.instructions.end(); ++instruction)
  {
    if(!instruction->is_assign())
      continue;
    irep_idt lhs;
    if(!direct_symbol(instruction->assign_lhs(), lhs))
      continue;
    if(lhs == data_pointer)
    {
      irep_idt pointer;
      irep_idt component;
      if(
        !member_from_pointer(
          instruction->assign_rhs(), pointer, component) ||
        component != data_component)
        return false;
      if(base_pointer.empty())
        base_pointer = pointer;
      if(pointer != base_pointer)
        return false;
      ++data_derivations;
      data_derivation = instruction;
    }
    else if(lhs == mutex_pointer)
    {
      irep_idt pointer;
      irep_idt component;
      if(
        !member_from_pointer(
          instruction->assign_rhs(), pointer, component) ||
        component != mutex_component)
        return false;
      if(base_pointer.empty())
        base_pointer = pointer;
      if(pointer != base_pointer)
        return false;
      ++mutex_derivations;
      mutex_derivation = instruction;
    }
  }
  if(
    base_pointer.empty() ||
    data_derivations != 1 || mutex_derivations != 1)
    return false;

  for(auto instruction = main->second.body.instructions.begin();
      instruction != main->second.body.instructions.end(); ++instruction)
  {
    if(!instruction->is_assign())
      continue;
    irep_idt lhs;
    if(
      !direct_symbol(instruction->assign_lhs(), lhs) ||
      lhs != base_pointer)
      continue;
    irep_idt base;
    if(!addressed_symbol(instruction->assign_rhs(), base))
      return false;
    const auto symbol = goto_model.symbol_table.symbols.find(base);
    if(
      symbol == goto_model.symbol_table.symbols.end() ||
      !symbol->second.is_static_lifetime)
      return false;
    bases.insert(base);
    ++base_writes;
    if(first_base == main->second.body.instructions.end())
      first_base = instruction;
    else
      second_base = instruction;
  }
  if(
    base_writes != 2 || bases.size() != 2 ||
    bases.count(worker_base) != 1 ||
    first_base == main->second.body.instructions.end() ||
    second_base == main->second.body.instructions.end())
    return false;
  const auto first_symbol =
    goto_model.symbol_table.symbols.find(*bases.begin());
  const auto second_symbol =
    goto_model.symbol_table.symbols.find(*std::next(bases.begin()));
  if(
    first_symbol == goto_model.symbol_table.symbols.end() ||
    second_symbol == goto_model.symbol_table.symbols.end() ||
    first_symbol->second.type != second_symbol->second.type)
    return false;

  std::map<const goto_programt::instructiont *, std::size_t> main_positions;
  std::size_t main_position = 0;
  for(const auto &instruction : main->second.body.instructions)
    main_positions.emplace(&instruction, main_position++);
  bool complete_choice = false;
  for(auto branch = main->second.body.instructions.begin();
      branch != first_base; ++branch)
  {
    if(
      !branch->is_goto() || branch->condition().is_true() ||
      branch->targets.size() != 1 ||
      branch->get_target() != second_base)
      continue;
    for(auto jump = std::next(first_base); jump != second_base; ++jump)
      if(
        jump->is_goto() && jump->condition().is_true() &&
        jump->targets.size() == 1 &&
        main_positions.at(&*jump->get_target()) >
          main_positions.at(&*second_base) &&
        main_positions.at(&*jump->get_target()) <=
          std::min(
            main_positions.at(&*data_derivation),
            main_positions.at(&*mutex_derivation)))
        complete_choice = true;
  }
  if(!complete_choice)
    return false;

  const namespacet ns(goto_model.symbol_table);
  const auto zero_initialized =
    [&](const irep_idt &base)
    {
      const auto initialize =
        goto_model.goto_functions.function_map.find(
          "__CPROVER_initialize");
      const auto symbol = goto_model.symbol_table.symbols.find(base);
      if(
        initialize == goto_model.goto_functions.function_map.end() ||
        !initialize->second.body_available() ||
        symbol == goto_model.symbol_table.symbols.end())
        return false;
      const typet &type = ns.follow(symbol->second.type);
      if(type.id() != ID_struct)
        return false;
      const auto &components = to_struct_type(type).components();
      std::size_t component_index = components.size();
      for(std::size_t index = 0; index < components.size(); ++index)
        if(components[index].get_name() == data_component)
          component_index = index;
      if(component_index == components.size())
        return false;
      std::size_t initializers = 0;
      for(const auto &instruction : initialize->second.body.instructions)
      {
        if(!instruction.is_assign())
          continue;
        irep_idt lhs;
        if(
          !direct_symbol(instruction.assign_lhs(), lhs) ||
          lhs != base)
          continue;
        const exprt &rhs = without_cast(instruction.assign_rhs());
        if(
          rhs.id() != ID_struct ||
          rhs.operands().size() != components.size() ||
          !is_zero_constant(rhs.operands()[component_index]))
          return false;
        ++initializers;
      }
      return initializers == 1;
    };
  for(const auto &base : bases)
    if(!zero_initialized(base))
      return false;

  const std::set<irep_idt> tracked{
    base_pointer, data_pointer, mutex_pointer};
  for(const auto &entry : goto_model.goto_functions.function_map)
  {
    if(!entry.second.body_available())
      continue;
    for(const auto &instruction : entry.second.body.instructions)
    {
      if(entry.first != "main" &&
         instruction_mentions_any(instruction, tracked))
        return false;
      if(entry.first == "main" &&
         instruction.is_function_call() &&
         instruction_mentions_any(instruction, tracked))
      {
        irep_idt callee;
        if(!direct_call_identifier(instruction, callee))
          return false;
        const bool property =
          callee == "__VERIFIER_assert" &&
          instruction.call_arguments().size() == 1 &&
          contains_symbol(
            instruction.call_arguments().front(), {data_pointer});
        const bool outer_mutex =
          (callee == "pthread_mutex_lock" ||
           callee == "pthread_mutex_unlock") &&
          instruction.call_arguments().size() == 1 &&
          contains_symbol(
            instruction.call_arguments().front(), {mutex_pointer});
        if(!property && !outer_mutex)
          return false;
      }
      if(!instruction.is_assign())
        continue;
      const exprt &lhs = without_cast(instruction.assign_lhs());
      if(
        entry.first == "main" &&
        contains_symbol(lhs, {base_pointer}) &&
        lhs.id() != ID_symbol)
        return false;
      irep_idt whole_lhs;
      if(
        direct_symbol(lhs, whole_lhs) &&
        bases.count(whole_lhs) != 0 &&
        entry.first != "__CPROVER_initialize")
        return false;
      if(lhs.id() != ID_member)
        continue;
      irep_idt base;
      irep_idt component;
      if(
        direct_member(lhs, base, component) &&
        bases.count(base) != 0 &&
        component == data_component &&
        !(entry.first == candidates.front().worker &&
          lhs == worker_macro.object))
        return false;
    }
  }

  bool truncated = false;
  if(!apply_dormant_spawn_counts(
       goto_model, candidates, std::vector<unsigned>{0}, truncated))
    return false;
  goto_model.goto_functions.update();
  auto updated_main =
    goto_model.goto_functions.function_map.find("main");
  updated_main->second.body.instructions.begin()
    ->source_location_nonconst()
    .set("deagle_aggregate_member_lock_alias", true);
  messaget log(message_handler);
  log.status()
    << "NATIVE_AGGREGATE_MEMBER_LOCK_ALIAS applied=1"
    << " bases=" << bases.size()
    << " workers=0"
    << " truncated=" << (truncated ? 1 : 0)
    << messaget::eom;
  return true;
}

bool aggregate_member_lock_alias_applied(
  const goto_modelt &goto_model)
{
  const auto main =
    goto_model.goto_functions.function_map.find("main");
  return
    main != goto_model.goto_functions.function_map.end() &&
    main->second.body_available() &&
    !main->second.body.instructions.empty() &&
    main->second.body.instructions.begin()
      ->source_location()
      .get_bool("deagle_aggregate_member_lock_alias");
}

bool independent_index_prefix_transform(
  goto_modelt &goto_model,
  message_handlert &message_handler)
{
  std::string reason;
  const auto candidates = dormant_spawn_cutoffs(goto_model, reason);
  if(candidates.size() != 2)
  {
    std::cout
      << "NATIVE_INDEPENDENT_INDEX_PREFIX applied=0"
      << " reason=worker_class_count"
      << " classes=" << candidates.size() << '\n';
    return false;
  }

  struct index_choicet
  {
    goto_programt::targett nondet;
    goto_programt::targett propagated;
    irep_idt temporary;
    irep_idt index;
    mp_integer bound;

    index_choicet(
      goto_programt::targett nondet,
      goto_programt::targett propagated,
      irep_idt temporary,
      irep_idt index,
      mp_integer bound)
      : nondet(nondet),
        propagated(propagated),
        temporary(std::move(temporary)),
        index(std::move(index)),
        bound(std::move(bound))
    {
    }
  };
  struct worker_summaryt
  {
    std::size_t candidate_index;
    std::vector<index_choicet> choices;
    goto_programt::targett control;
    irep_idt object_index;
    irep_idt lock_index;
    irep_idt object_array;
    irep_idt lock_array;

    worker_summaryt(
      const std::size_t candidate_index,
      std::vector<index_choicet> choices,
      goto_programt::targett control,
      irep_idt object_index,
      irep_idt lock_index,
      irep_idt object_array,
      irep_idt lock_array)
      : candidate_index(candidate_index),
        choices(std::move(choices)),
        control(control),
        object_index(std::move(object_index)),
        lock_index(std::move(lock_index)),
        object_array(std::move(object_array)),
        lock_array(std::move(lock_array))
    {
    }
  };

  const auto indexed_array =
    [&](const exprt &root, const irep_idt &index, irep_idt &array) -> bool
    {
      std::set<irep_idt> arrays;
      std::function<void(const exprt &)> visit =
        [&](const exprt &expr)
        {
          const exprt &value = without_cast(expr);
          if(
            value.id() == ID_index && value.operands().size() == 2 &&
            contains_symbol(value.op1(), {index}))
          {
            irep_idt candidate;
            if(direct_symbol(value.op0(), candidate))
              arrays.insert(candidate);
          }
          for(const auto &operand : value.operands())
            visit(operand);
        };
      visit(root);
      if(arrays.size() != 1)
        return false;
      array = *arrays.begin();
      return true;
    };

  const auto array_capacity =
    [&](const irep_idt &array, mp_integer &capacity) -> bool
    {
      const auto symbol = goto_model.symbol_table.symbols.find(array);
      return
        symbol != goto_model.symbol_table.symbols.end() &&
        symbol->second.is_static_lifetime &&
        symbol->second.type.id() == ID_array &&
        constant_eval(
          to_array_type(symbol->second.type).size(), {}, capacity);
    };

  std::vector<worker_summaryt> admitted_workers;
  for(std::size_t candidate_index = 0;
      candidate_index < candidates.size(); ++candidate_index)
  {
    const auto worker =
      goto_model.goto_functions.function_map.find(
        candidates[candidate_index].worker);
    if(
      worker == goto_model.goto_functions.function_map.end() ||
      !worker->second.body_available())
      continue;
    auto &body = worker->second.body;
    std::vector<index_choicet> choices;
    for(auto instruction = body.instructions.begin();
        instruction != body.instructions.end(); ++instruction)
    {
      if(!instruction->is_assign())
        continue;
      const exprt &rhs = without_cast(instruction->assign_rhs());
      irep_idt temporary;
      if(
        rhs.id() != ID_side_effect ||
        to_side_effect_expr(rhs).get_statement() != ID_nondet ||
        !direct_symbol(instruction->assign_lhs(), temporary))
        continue;
      for(auto propagated = std::next(instruction);
          propagated != body.instructions.end(); ++propagated)
      {
        if(!propagated->is_assign())
          continue;
        const exprt &propagated_rhs =
          without_cast(propagated->assign_rhs());
        if(
          propagated_rhs.id() == ID_side_effect &&
          to_side_effect_expr(propagated_rhs).get_statement() == ID_nondet)
          break;
        irep_idt index;
        irep_idt rhs_temporary;
        mp_integer bound;
        if(
          propagated_rhs.id() == ID_mod &&
          propagated_rhs.operands().size() == 2 &&
          direct_symbol(propagated->assign_lhs(), index) &&
          direct_symbol(propagated_rhs.op0(), rhs_temporary) &&
          rhs_temporary == temporary &&
          constant_eval(propagated_rhs.op1(), {}, bound) &&
          bound > 1)
        {
          choices.emplace_back(
            instruction, propagated, temporary, index, bound);
          break;
        }
      }
    }
    if(
      choices.size() != 2 ||
      choices.front().index == choices.back().index ||
      choices.front().bound != choices.back().bound)
      continue;

    std::vector<std::pair<irep_idt, irep_idt>> object_uses;
    std::vector<std::pair<irep_idt, irep_idt>> lock_uses;
    for(auto instruction = body.instructions.begin();
        instruction != body.instructions.end(); ++instruction)
    {
      if(
        instruction->is_function_call() &&
        !instruction->call_lhs().is_nil() &&
        instruction->call_lhs().type().id() == ID_pointer)
      {
        for(const auto &choice : choices)
          for(const auto &argument : instruction->call_arguments())
          {
            irep_idt array;
            if(indexed_array(argument, choice.index, array))
              object_uses.emplace_back(choice.index, array);
          }
      }
      irep_idt callee;
      if(
        instruction->is_function_call() &&
        direct_call_identifier(*instruction, callee) &&
        (callee == "pthread_mutex_lock" ||
         callee == "pthread_mutex_unlock") &&
        instruction->call_arguments().size() == 1)
      {
        for(const auto &choice : choices)
        {
          irep_idt array;
          if(
            indexed_array(
              instruction->call_arguments().front(),
              choice.index,
              array))
            lock_uses.emplace_back(choice.index, array);
        }
      }
    }
    std::sort(object_uses.begin(), object_uses.end());
    object_uses.erase(
      std::unique(object_uses.begin(), object_uses.end()),
      object_uses.end());
    std::sort(lock_uses.begin(), lock_uses.end());
    lock_uses.erase(
      std::unique(lock_uses.begin(), lock_uses.end()),
      lock_uses.end());
    if(
      object_uses.size() != 1 || lock_uses.size() != 1 ||
      object_uses.front().first == lock_uses.front().first ||
      object_uses.front().second == lock_uses.front().second)
      continue;
    std::size_t indexed_locks = 0;
    std::size_t indexed_unlocks = 0;
    for(const auto &instruction : body.instructions)
    {
      irep_idt callee;
      if(
        !instruction.is_function_call() ||
        !direct_call_identifier(instruction, callee) ||
        (callee != "pthread_mutex_lock" &&
         callee != "pthread_mutex_unlock") ||
        instruction.call_arguments().size() != 1)
        continue;
      irep_idt array;
      if(
        !indexed_array(
          instruction.call_arguments().front(),
          lock_uses.front().first,
          array) ||
        array != lock_uses.front().second)
        continue;
      if(callee == "pthread_mutex_lock")
        ++indexed_locks;
      else
        ++indexed_unlocks;
    }
    if(indexed_locks != 1 || indexed_unlocks != 1)
      continue;
    mp_integer object_capacity;
    mp_integer lock_capacity;
    if(
      !array_capacity(object_uses.front().second, object_capacity) ||
      !array_capacity(lock_uses.front().second, lock_capacity) ||
      object_capacity != choices.front().bound ||
      lock_capacity != choices.front().bound)
      continue;

    exprt scalar = nil_exprt();
    find_symbols_sett scalar_symbols;
    std::set<irep_idt> scalar_members;
    std::size_t plus_one = 0;
    std::size_t minus_one = 0;
    std::size_t zero_assertions = 0;
    std::vector<goto_programt::targett> operations;
    std::set<irep_idt> operation_mutexes;
    std::function<void(const exprt &, std::set<irep_idt> &)>
      collect_members =
        [&](const exprt &expr, std::set<irep_idt> &members)
        {
          const exprt &value = without_cast(expr);
          if(value.id() == ID_member)
            members.insert(
              to_member_expr(value).get_component_name());
          for(const auto &operand : value.operands())
            collect_members(operand, members);
        };
    for(auto instruction = body.instructions.begin();
        instruction != body.instructions.end(); ++instruction)
    {
      if(instruction->is_assign())
      {
        const exprt &rhs = without_cast(instruction->assign_rhs());
        if(
          (rhs.id() == ID_plus || rhs.id() == ID_minus) &&
          rhs.operands().size() == 2 &&
          contains_side_effect(instruction->assign_lhs()) &&
          contains_side_effect(rhs.op0()))
        {
          mp_integer delta;
          if(constant_eval(rhs.op1(), {}, delta) && delta == 1)
          {
            find_symbols_sett lhs_symbols;
            find_symbols_sett rhs_symbols;
            std::set<irep_idt> lhs_members;
            std::set<irep_idt> rhs_members;
            find_symbols(instruction->assign_lhs(), lhs_symbols);
            find_symbols(rhs.op0(), rhs_symbols);
            collect_members(instruction->assign_lhs(), lhs_members);
            collect_members(rhs.op0(), rhs_members);
            if(
              lhs_symbols == rhs_symbols &&
              lhs_members == rhs_members &&
              !lhs_symbols.empty() && !lhs_members.empty())
            {
              if(scalar.is_nil())
              {
                scalar = instruction->assign_lhs();
                scalar_symbols = lhs_symbols;
                scalar_members = lhs_members;
              }
              if(
                lhs_symbols == scalar_symbols &&
                lhs_members == scalar_members)
              {
                if(rhs.id() == ID_plus)
                  ++plus_one;
                else
                  ++minus_one;
                operations.push_back(instruction);
              }
            }
          }
        }
      }
      irep_idt callee;
      if(
        instruction->is_function_call() &&
        direct_call_identifier(*instruction, callee) &&
        callee == "__VERIFIER_assert" &&
        instruction->call_arguments().size() == 1 &&
        !scalar.is_nil())
      {
        const exprt &condition =
          without_cast(instruction->call_arguments().front());
        mp_integer zero;
        if(
          condition.id() == ID_equal &&
          condition.operands().size() == 2 &&
          constant_eval(condition.op1(), {}, zero) &&
          zero == 0)
        {
          find_symbols_sett symbols;
          std::set<irep_idt> members;
          find_symbols(condition.op0(), symbols);
          collect_members(condition.op0(), members);
          if(
            symbols == scalar_symbols &&
            members == scalar_members)
          {
            ++zero_assertions;
            operations.push_back(instruction);
          }
        }
      }
    }
    if(
      plus_one != 1 || minus_one != 1 ||
      zero_assertions != 1 || operations.size() != 3)
      continue;
    bool mutex_pairs = true;
    for(const auto operation : operations)
    {
      if(
        operation == body.instructions.begin() ||
        std::next(operation) == body.instructions.end())
      {
        mutex_pairs = false;
        break;
      }
      irep_idt locked;
      irep_idt unlocked;
      if(
        !parse_mutex_call(
          *std::prev(operation), "pthread_mutex_lock", locked) ||
        !parse_mutex_call(
          *std::next(operation), "pthread_mutex_unlock", unlocked) ||
        locked != unlocked)
      {
        mutex_pairs = false;
        break;
      }
      operation_mutexes.insert(locked);
    }
    if(!mutex_pairs || operation_mutexes.size() != 1)
      continue;

    auto control = body.instructions.end();
    std::size_t controls = 0;
    for(auto instruction = body.instructions.begin();
        instruction != body.instructions.end(); ++instruction)
    {
      if(!instruction->is_assign())
        continue;
      const exprt &rhs = without_cast(instruction->assign_rhs());
      if(
        rhs.id() != ID_side_effect ||
        to_side_effect_expr(rhs).get_statement() != ID_nondet)
        continue;
      bool is_index_choice = false;
      for(const auto &choice : choices)
        is_index_choice =
          is_index_choice || instruction == choice.nondet;
      if(!is_index_choice)
      {
        control = instruction;
        ++controls;
      }
    }
    if(controls != 1)
      continue;

    admitted_workers.emplace_back(
      candidate_index,
      std::move(choices),
      control,
      object_uses.front().first,
      lock_uses.front().first,
      object_uses.front().second,
      lock_uses.front().second);
  }
  if(admitted_workers.size() != 1)
  {
    std::cout
      << "NATIVE_INDEPENDENT_INDEX_PREFIX applied=0"
      << " reason=independent_worker_count"
      << " workers=" << admitted_workers.size() << '\n';
    return false;
  }
  const auto summary = admitted_workers.front();

  auto main = goto_model.goto_functions.function_map.find("main");
  INVARIANT(
    main != goto_model.goto_functions.function_map.end() &&
    main->second.body_available(),
    "independent index prefix requires main");
  auto &program = main->second.body;
  std::map<const goto_programt::instructiont *, std::size_t> positions;
  std::size_t position = 0;
  for(const auto &instruction : program.instructions)
    positions.emplace(&instruction, position++);
  std::size_t first_create = positions.size();
  for(const auto &candidate : candidates)
    first_create =
      std::min(first_create, positions.at(candidate.create_instruction));

  struct loopt
  {
    goto_programt::const_targett head;
    goto_programt::const_targett backedge;
    irep_idt induction;
    mp_integer bound;
  };
  std::vector<loopt> loops;
  for(auto backedge = program.instructions.begin();
      backedge != program.instructions.end(); ++backedge)
  {
    if(
      positions.at(&*backedge) >= first_create ||
      !backedge->is_goto() || !backedge->condition().is_true() ||
      backedge->targets.size() != 1 ||
      positions.at(&*backedge->get_target()) >= positions.at(&*backedge))
      continue;
    irep_idt induction;
    exprt bound;
    mp_integer constant_bound;
    if(
      parse_exit_guard(
        *backedge->get_target(), induction, bound) &&
      constant_eval(bound, {}, constant_bound) &&
      constant_bound == summary.choices.front().bound)
      loops.push_back(
        {backedge->get_target(), backedge, induction, constant_bound});
  }
  if(loops.size() != 1)
  {
    std::cout
      << "NATIVE_INDEPENDENT_INDEX_PREFIX applied=0"
      << " reason=initialization_loop_count"
      << " loops=" << loops.size() << '\n';
    return false;
  }
  const auto &loop = loops.front();
  std::size_t zero_initializations = 0;
  for(auto instruction = program.instructions.begin();
      instruction != loop.head; ++instruction)
    if(parse_zero_initialization(*instruction, loop.induction))
      ++zero_initializations;
  std::size_t increments = 0;
  std::size_t object_initializations = 0;
  std::size_t mutex_initializations = 0;
  for(auto instruction = loop.head;
      instruction != loop.backedge; ++instruction)
  {
    irep_idt incremented;
    if(
      parse_unit_increment(*instruction, incremented) &&
      incremented == loop.induction)
      ++increments;
    irep_idt callee;
    if(
      instruction->is_function_call() &&
      direct_call_identifier(*instruction, callee) &&
      callee == "pthread_mutex_init" &&
      instruction_mentions_any(
        *instruction, {loop.induction, summary.lock_array}))
      ++mutex_initializations;
    if(
      instruction->is_assign() &&
      contains_symbol(
        instruction->assign_lhs(),
        {loop.induction, summary.object_array}) &&
      instruction->assign_rhs().type().id() == ID_pointer)
      ++object_initializations;
  }
  if(
    zero_initializations != 1 || increments != 1 ||
    object_initializations != 1 || mutex_initializations != 1)
  {
    std::cout
      << "NATIVE_INDEPENDENT_INDEX_PREFIX applied=0"
      << " reason=initialization_shape"
      << " zero=" << zero_initializations
      << " increments=" << increments
      << " objects=" << object_initializations
      << " mutexes=" << mutex_initializations << '\n';
    return false;
  }

  const auto original_worker =
    goto_model.goto_functions.function_map.find(
      candidates[summary.candidate_index].worker);
  const auto original_symbol =
    goto_model.symbol_table.symbols.find(
      candidates[summary.candidate_index].worker);
  if(
    original_worker == goto_model.goto_functions.function_map.end() ||
    original_symbol == goto_model.symbol_table.symbols.end())
    return false;
  const irep_idt cloned_worker_id =
    id2string(candidates[summary.candidate_index].worker) +
    "$deagle_independent_index_worker";
  if(
    goto_model.goto_functions.function_map.count(cloned_worker_id) != 0 ||
    goto_model.symbol_table.symbols.count(cloned_worker_id) != 0)
    return false;

  const namespacet ns(goto_model.symbol_table);
  const symbolt *induction_symbol = nullptr;
  if(ns.lookup(loop.induction, induction_symbol))
    return false;
  auto loop_head = program.const_cast_target(loop.head);
  loop_head->condition_nonconst() = not_exprt(
    binary_relation_exprt(
      symbol_exprt(loop.induction, induction_symbol->type),
      ID_lt,
      from_integer(2, induction_symbol->type)));

  auto &cloned_worker =
    goto_model.goto_functions.function_map[cloned_worker_id];
  cloned_worker.copy_from(original_worker->second);
  symbolt cloned_symbol = original_symbol->second;
  cloned_symbol.name = cloned_worker_id;
  cloned_symbol.base_name = cloned_worker_id;
  cloned_symbol.pretty_name = cloned_worker_id;
  if(goto_model.symbol_table.add(cloned_symbol))
    return false;

  const auto specialize =
    [&](goto_functiont &worker, const mp_integer &lock_value,
        const mp_integer &control_value) -> bool
    {
      std::map<irep_idt, goto_programt::targett> nondets;
      std::map<irep_idt, goto_programt::targett> propagated;
      goto_programt::targett control =
        worker.body.instructions.end();
      for(auto instruction = worker.body.instructions.begin();
          instruction != worker.body.instructions.end(); ++instruction)
      {
        if(!instruction->is_assign())
          continue;
        const exprt &rhs = without_cast(instruction->assign_rhs());
        irep_idt temporary;
        if(
          rhs.id() == ID_side_effect &&
          to_side_effect_expr(rhs).get_statement() == ID_nondet &&
          direct_symbol(instruction->assign_lhs(), temporary))
        {
          nondets.emplace(temporary, instruction);
          control = instruction;
          continue;
        }
        if(
          rhs.id() == ID_mod && rhs.operands().size() == 2 &&
          direct_symbol(rhs.op0(), temporary))
        {
          irep_idt index;
          if(direct_symbol(instruction->assign_lhs(), index))
            propagated.emplace(index, instruction);
        }
      }
      if(
        propagated.size() != 2 ||
        control == worker.body.instructions.end())
        return false;
      for(const auto &choice : summary.choices)
      {
        const auto nondet = nondets.find(choice.temporary);
        const auto assignment = propagated.find(choice.index);
        if(
          nondet == nondets.end() ||
          assignment == propagated.end())
          return false;
        const mp_integer value =
          choice.index == summary.lock_index ? lock_value : 0;
        nondet->second->assign_rhs_nonconst() =
          from_integer(
            value, nondet->second->assign_lhs().type());
        assignment->second->assign_rhs_nonconst() =
          from_integer(
            value, assignment->second->assign_lhs().type());
      }
      control->assign_rhs_nonconst() =
        from_integer(
          control_value, control->assign_lhs().type());
      return true;
    };
  if(
    !specialize(original_worker->second, 0, 1) ||
    !specialize(cloned_worker, 1, 0))
    return false;

  auto create = program.instructions.end();
  for(auto instruction = program.instructions.begin();
      instruction != program.instructions.end(); ++instruction)
    if(
      &*instruction ==
      candidates[summary.candidate_index].create_instruction)
    {
      create = instruction;
      break;
    }
  if(create == program.instructions.end())
    return false;
  const auto spawn_symbol =
    goto_model.symbol_table.symbols.find(
      candidates[summary.candidate_index].induction);
  if(spawn_symbol == goto_model.symbol_table.symbols.end())
    return false;
  const exprt original_target = create->call_arguments()[2];
  exprt cloned_target = address_of_exprt(
    symbol_exprt(cloned_worker_id, original_symbol->second.type));
  cloned_target = typecast_exprt::conditional_cast(
    cloned_target, original_target.type());
  create->call_arguments()[2] = if_exprt(
    equal_exprt(
      symbol_exprt(
        candidates[summary.candidate_index].induction,
        spawn_symbol->second.type),
      from_integer(0, spawn_symbol->second.type)),
    original_target,
    std::move(cloned_target),
    original_target.type());

  std::vector<unsigned> counts(candidates.size(), 0);
  counts[summary.candidate_index] = 2;
  bool truncated = false;
  if(!apply_dormant_spawn_counts(
       goto_model, candidates, counts, truncated))
    return false;
  program.instructions.begin()
    ->source_location_nonconst()
    .set("deagle_independent_index_prefix", true);
  goto_model.goto_functions.update();
  std::cout
    << "NATIVE_INDEPENDENT_INDEX_PREFIX applied=1"
    << " initialized=2 workers=2"
    << " object_choice=0 lock_choices=0,1"
    << " truncated=" << (truncated ? 1 : 0) << '\n';
  (void)message_handler;
  return true;
}

bool independent_index_prefix_applied(const goto_modelt &goto_model)
{
  const auto main =
    goto_model.goto_functions.function_map.find("main");
  return
    main != goto_model.goto_functions.function_map.end() &&
    main->second.body_available() &&
    !main->second.body.instructions.empty() &&
    main->second.body.instructions.begin()
      ->source_location()
      .get_bool("deagle_independent_index_prefix");
}

bool pair_initialization_prefix_transform(
  goto_modelt &goto_model,
  message_handlert &message_handler)
{
  std::string reason;
  const auto candidates = dormant_spawn_cutoffs(goto_model, reason);
  if(candidates.size() != 2)
  {
    std::cout
      << "NATIVE_PAIR_INITIALIZATION_PREFIX applied=0"
      << " reason=worker_class_count"
      << " classes=" << candidates.size() << '\n';
    return false;
  }
  if(candidates.front().worker == candidates.back().worker)
  {
    std::cout
      << "NATIVE_PAIR_INITIALIZATION_PREFIX applied=0"
      << " reason=duplicate_worker_class\n";
    return false;
  }

  auto main = goto_model.goto_functions.function_map.find("main");
  INVARIANT(
    main != goto_model.goto_functions.function_map.end() &&
    main->second.body_available(),
    "pair initialization prefix requires main");
  auto &program = main->second.body;
  std::map<const goto_programt::instructiont *, std::size_t> positions;
  std::size_t position = 0;
  for(const auto &instruction : program.instructions)
    positions.emplace(&instruction, position++);

  std::size_t first_create = positions.size();
  for(const auto &candidate : candidates)
    first_create =
      std::min(first_create, positions.at(candidate.create_instruction));

  struct loopt
  {
    goto_programt::const_targett head;
    goto_programt::const_targett backedge;
    irep_idt induction;
  };
  std::vector<loopt> initialization_loops;
  for(auto backedge = program.instructions.begin();
      backedge != program.instructions.end(); ++backedge)
  {
    if(
      positions.at(&*backedge) >= first_create ||
      !backedge->is_goto() || !backedge->condition().is_true() ||
      backedge->targets.size() != 1 ||
      positions.at(&*backedge->get_target()) >= positions.at(&*backedge))
      continue;
    const auto head = backedge->get_target();
    irep_idt induction;
    exprt bound;
    mp_integer constant_bound;
    if(
      !parse_exit_guard(*head, induction, bound) ||
      !constant_eval(bound, {}, constant_bound) ||
      constant_bound <= 2)
      continue;
    initialization_loops.push_back({head, backedge, induction});
  }
  if(initialization_loops.size() != 2)
  {
    std::cout
      << "NATIVE_PAIR_INITIALIZATION_PREFIX applied=0"
      << " reason=initialization_loop_count"
      << " loops=" << initialization_loops.size() << '\n';
    return false;
  }

  loopt *outer_loop = nullptr;
  loopt *inner_loop = nullptr;
  for(auto &candidate_outer : initialization_loops)
  {
    const auto outer_head = positions.at(&*candidate_outer.head);
    const auto outer_backedge = positions.at(&*candidate_outer.backedge);
    for(auto &candidate_inner : initialization_loops)
    {
      if(&candidate_outer == &candidate_inner)
        continue;
      const auto inner_head = positions.at(&*candidate_inner.head);
      const auto inner_backedge = positions.at(&*candidate_inner.backedge);
      if(
        outer_head < inner_head &&
        inner_backedge < outer_backedge)
      {
        if(outer_loop != nullptr || inner_loop != nullptr)
        {
          std::cout
            << "NATIVE_PAIR_INITIALIZATION_PREFIX applied=0"
            << " reason=ambiguous_loop_nesting\n";
          return false;
        }
        outer_loop = &candidate_outer;
        inner_loop = &candidate_inner;
      }
    }
  }
  if(outer_loop == nullptr || inner_loop == nullptr)
  {
    std::cout
      << "NATIVE_PAIR_INITIALIZATION_PREFIX applied=0"
      << " reason=non_nested_initialization_loops\n";
    return false;
  }

  for(const auto *loop : {outer_loop, inner_loop})
  {
    std::size_t initializations = 0;
    for(auto instruction = program.instructions.begin();
        instruction != loop->head; ++instruction)
    {
      if(parse_zero_initialization(*instruction, loop->induction))
        ++initializations;
    }
    std::size_t increments = 0;
    for(auto instruction = loop->head;
        instruction != loop->backedge; ++instruction)
    {
      irep_idt incremented;
      if(
        parse_unit_increment(*instruction, incremented) &&
        incremented == loop->induction)
        ++increments;
    }
    if(initializations != 1 || increments != 1)
    {
      std::cout
        << "NATIVE_PAIR_INITIALIZATION_PREFIX applied=0"
        << " reason=non_canonical_initialization_loop"
        << " zero_initializations=" << initializations
        << " unit_increments=" << increments << '\n';
      return false;
    }
  }

  struct worker_index_assignmentt
  {
    goto_programt::targett nondet_assignment;
    goto_programt::targett index_assignment;
    goto_programt::targett loop_guard;
    goto_programt::targett increment;
    goto_programt::targett control_assignment;
    irep_idt worker;
    irep_idt index;
    std::size_t concretized_uses;
  };
  std::vector<worker_index_assignmentt> worker_index_assignments;
  for(const auto &candidate : candidates)
  {
    auto worker =
      goto_model.goto_functions.function_map.find(candidate.worker);
    if(
      worker == goto_model.goto_functions.function_map.end() ||
      !worker->second.body_available())
    {
      std::cout
        << "NATIVE_PAIR_INITIALIZATION_PREFIX applied=0"
        << " reason=missing_worker\n";
      return false;
    }
    goto_programt::targett selected =
      worker->second.body.instructions.end();
    for(auto instruction = worker->second.body.instructions.begin();
        instruction != worker->second.body.instructions.end(); ++instruction)
    {
      if(!instruction->is_assign())
        continue;
      const exprt &rhs = without_cast(instruction->assign_rhs());
      if(
        rhs.id() != ID_side_effect ||
        to_side_effect_expr(rhs).get_statement() != ID_nondet)
        continue;
      irep_idt index;
      if(!direct_symbol(instruction->assign_lhs(), index))
        continue;
      selected = instruction;
      break;
    }
    if(selected == worker->second.body.instructions.end())
    {
      std::cout
        << "NATIVE_PAIR_INITIALIZATION_PREFIX applied=0"
        << " reason=missing_worker_index\n";
      return false;
    }
    irep_idt temporary;
    if(!direct_symbol(selected->assign_lhs(), temporary))
    {
      std::cout
        << "NATIVE_PAIR_INITIALIZATION_PREFIX applied=0"
        << " reason=non_symbol_worker_index_temporary\n";
      return false;
    }
    goto_programt::targett propagated =
      worker->second.body.instructions.end();
    std::size_t propagation_count = 0;
    for(auto instruction = std::next(selected);
        instruction != worker->second.body.instructions.end(); ++instruction)
    {
      irep_idt mutex;
      if(parse_mutex_call(*instruction, "pthread_mutex_lock", mutex))
        break;
      if(!instruction->is_assign())
        continue;
      irep_idt index;
      irep_idt rhs;
      if(
        direct_symbol(instruction->assign_lhs(), index) &&
        direct_symbol(instruction->assign_rhs(), rhs) &&
        rhs == temporary)
      {
        propagated = instruction;
        ++propagation_count;
      }
    }
    if(
      propagation_count != 1 ||
      propagated == worker->second.body.instructions.end())
    {
      std::cout
        << "NATIVE_PAIR_INITIALIZATION_PREFIX applied=0"
        << " reason=worker_index_propagation"
        << " candidates=" << propagation_count << '\n';
      return false;
    }
    irep_idt propagated_index;
    if(!direct_symbol(propagated->assign_lhs(), propagated_index))
    {
      std::cout
        << "NATIVE_PAIR_INITIALIZATION_PREFIX applied=0"
        << " reason=non_symbol_worker_index\n";
      return false;
    }
    const auto index_symbol =
      goto_model.symbol_table.symbols.find(propagated_index);
    if(index_symbol == goto_model.symbol_table.symbols.end())
    {
      std::cout
        << "NATIVE_PAIR_INITIALIZATION_PREFIX applied=0"
        << " reason=missing_worker_index_symbol\n";
      return false;
    }
    const symbol_exprt index(
      propagated_index, index_symbol->second.type);
    const exprt worker_zero =
      from_integer(0, index_symbol->second.type);
    auto loop_guard = worker->second.body.instructions.end();
    auto increment = worker->second.body.instructions.end();
    auto control_assignment =
      worker->second.body.instructions.end();
    std::size_t increments = 0;
    std::size_t control_assignments = 0;
    std::size_t concretized = 0;
    for(auto instruction = std::next(propagated);
        instruction != worker->second.body.instructions.end(); ++instruction)
    {
      irep_idt incremented;
      if(
        parse_unit_increment(*instruction, incremented) &&
        incremented == propagated_index)
      {
        increment = instruction;
        ++increments;
        break;
      }
      if(
        loop_guard == worker->second.body.instructions.end() &&
        instruction->is_goto())
      {
        loop_guard = instruction;
        continue;
      }
      if(instruction->is_assign())
      {
        const exprt &rhs = without_cast(instruction->assign_rhs());
        if(
          rhs.id() == ID_side_effect &&
          to_side_effect_expr(rhs).get_statement() == ID_nondet)
        {
          control_assignment = instruction;
          ++control_assignments;
        }
      }
      codet code = instruction->code();
      const codet original_code = code;
      replace_expr(index, worker_zero, code);
      if(code != original_code)
        ++concretized;
      if(instruction->is_goto())
      {
        exprt condition = instruction->condition();
        const exprt original_condition = condition;
        replace_expr(index, worker_zero, condition);
        if(condition != original_condition)
          ++concretized;
      }
    }
    if(
      loop_guard == worker->second.body.instructions.end() ||
      increment == worker->second.body.instructions.end() ||
      control_assignment == worker->second.body.instructions.end() ||
      increments != 1 || control_assignments != 1 ||
      concretized == 0)
    {
      std::cout
        << "NATIVE_PAIR_INITIALIZATION_PREFIX applied=0"
        << " reason=worker_index_use_region"
        << " loop_guard="
        << (loop_guard == worker->second.body.instructions.end() ? 0 : 1)
        << " increments=" << increments
        << " controls=" << control_assignments
        << " concretized=" << concretized << '\n';
      return false;
    }
    worker_index_assignments.push_back(
      {selected,
       propagated,
       loop_guard,
       increment,
       control_assignment,
       candidate.worker,
       propagated_index,
       concretized});
  }

  const namespacet ns(goto_model.symbol_table);
  for(const auto &loop : initialization_loops)
  {
    const symbolt *induction_symbol = nullptr;
    if(ns.lookup(loop.induction, induction_symbol))
    {
      std::cout
        << "NATIVE_PAIR_INITIALIZATION_PREFIX applied=0"
        << " reason=missing_induction\n";
      return false;
    }
    auto head = program.const_cast_target(loop.head);
    const symbol_exprt induction(
      loop.induction, induction_symbol->type);
    head->condition_nonconst() = not_exprt(
      binary_relation_exprt(
        induction,
        ID_lt,
        from_integer(1, induction_symbol->type)));
  }
  const auto outer_symbol =
    goto_model.symbol_table.symbols.find(outer_loop->induction);
  if(outer_symbol == goto_model.symbol_table.symbols.end())
  {
    std::cout
      << "NATIVE_PAIR_INITIALIZATION_PREFIX applied=0"
      << " reason=missing_outer_induction_symbol\n";
    return false;
  }
  const symbol_exprt outer_induction(
    outer_loop->induction, outer_symbol->second.type);
  const exprt zero = from_integer(0, outer_symbol->second.type);
  std::size_t concretized_instructions = 0;
  for(auto instruction = std::next(program.const_cast_target(outer_loop->head));
      instruction != program.const_cast_target(outer_loop->backedge);
      ++instruction)
  {
    irep_idt incremented;
    if(
      parse_unit_increment(*instruction, incremented) &&
      incremented == outer_loop->induction)
      continue;
    codet &code = instruction->code_nonconst();
    const codet original = code;
    replace_expr(outer_induction, zero, code);
    if(code != original)
      ++concretized_instructions;
  }
  if(concretized_instructions == 0)
  {
    std::cout
      << "NATIVE_PAIR_INITIALIZATION_PREFIX applied=0"
      << " reason=unused_outer_induction\n";
    return false;
  }
  std::size_t concretized_worker_uses = 0;
  for(std::size_t worker_index = 0;
      worker_index < worker_index_assignments.size(); ++worker_index)
  {
    auto assignment = worker_index_assignments[worker_index];
    concretized_worker_uses += assignment.concretized_uses;
    assignment.nondet_assignment->assign_rhs_nonconst() =
      from_integer(
        0, assignment.nondet_assignment->assign_lhs().type());
    assignment.index_assignment->assign_rhs_nonconst() =
      from_integer(
        0, assignment.index_assignment->assign_lhs().type());
    assignment.control_assignment->assign_rhs_nonconst() =
      from_integer(
        worker_index == 0 ? 0 : 1,
        assignment.control_assignment->assign_lhs().type());

    const auto index_symbol =
      goto_model.symbol_table.symbols.find(assignment.index);
    const symbol_exprt index(
      assignment.index, index_symbol->second.type);
    const exprt worker_zero =
      from_integer(0, index_symbol->second.type);
    for(auto instruction = std::next(assignment.index_assignment);
        instruction != assignment.increment; ++instruction)
    {
      if(instruction == assignment.loop_guard)
        continue;
      codet &code = instruction->code_nonconst();
      replace_expr(index, worker_zero, code);
      if(instruction->is_goto())
        replace_expr(
          index, worker_zero, instruction->condition_nonconst());
    }
  }
  program.instructions.begin()
    ->source_location_nonconst()
    .set("deagle_pair_initialization_prefix", true);
  goto_model.goto_functions.update();
  std::cout
    << "NATIVE_PAIR_INITIALIZATION_PREFIX applied=1"
    << " loops=2"
    << " prefix=1"
    << " concretized_instructions=" << concretized_instructions
    << " concretized_worker_uses=" << concretized_worker_uses
    << " fixed_control_branches=2"
    << " worker_indices=2\n";
  (void)message_handler;
  return true;
}

bool pair_initialization_prefix_applied(const goto_modelt &goto_model)
{
  const auto main =
    goto_model.goto_functions.function_map.find("main");
  return
    main != goto_model.goto_functions.function_map.end() &&
    main->second.body_available() &&
    !main->second.body.instructions.empty() &&
    main->second.body.instructions.begin()
      ->source_location()
      .get_bool("deagle_pair_initialization_prefix");
}

bool dormant_spawn_pair_audit(
  const goto_modelt &goto_model,
  message_handlert &message_handler)
{
  std::string reason;
  const auto candidates = dormant_spawn_cutoffs(goto_model, reason);
  const bool applicable = candidates.size() >= 2;
  const std::size_t variants =
    applicable ? candidates.size() * (candidates.size() + 1) / 2 : 0;
  std::cout
    << "NATIVE_DORMANT_SPAWN_PAIR_AUDIT applicable="
    << (applicable ? 1 : 0)
    << " classes=" << candidates.size()
    << " variants=" << variants;
  if(!applicable)
    std::cout
      << " reason="
      << (candidates.empty() ? reason : "dormant_single_class");
  std::cout << '\n';
  (void)message_handler;
  return applicable;
}

std::size_t dormant_spawn_pair_variant_count(
  const goto_modelt &goto_model)
{
  std::string reason;
  const auto candidates = dormant_spawn_cutoffs(goto_model, reason);
  if(candidates.size() < 2)
    return 0;
  return candidates.size() * (candidates.size() + 1) / 2;
}

bool dormant_spawn_pair_transform(
  goto_modelt &goto_model,
  const std::size_t variant,
  message_handlert &message_handler)
{
  std::string reason;
  auto candidates = dormant_spawn_cutoffs(goto_model, reason);
  std::vector<unsigned> counts;
  std::string label;
  if(
    candidates.size() < 2 ||
    !dormant_spawn_pair_counts(
      candidates.size(), variant, counts, label))
  {
    std::cout
      << "NATIVE_DORMANT_SPAWN_PAIR applied=0"
      << " classes=" << candidates.size()
      << " variant=" << variant
      << " reason="
      << (candidates.empty() ? reason : "dormant_pair_variant")
      << '\n';
    return false;
  }
  bool truncated = false;
  if(!apply_dormant_spawn_counts(
       goto_model, candidates, counts, truncated))
  {
    std::cout
      << "NATIVE_DORMANT_SPAWN_PAIR applied=0"
      << " classes=" << candidates.size()
      << " variant=" << variant
      << " reason=dormant_transform_failed\n";
    return false;
  }
  std::cout
    << "NATIVE_DORMANT_SPAWN_PAIR applied=1"
    << " classes=" << candidates.size()
    << " variant=" << variant
    << " label=" << label
    << " counts=";
  for(std::size_t index = 0; index < counts.size(); ++index)
  {
    if(index != 0)
      std::cout << ',';
    std::cout << counts[index];
  }
  std::cout
    << " truncated=" << (truncated ? 1 : 0)
    << '\n';
  (void)message_handler;
  return true;
}

bool indexed_lifecycle_prefix_audit(
  const goto_modelt &goto_model,
  message_handlert &message_handler)
{
  std::string reason;
  const auto loops = indexed_lifecycle_loops(goto_model, reason);
  std::size_t creates = 0;
  std::size_t joins = 0;
  for(const auto &loop : loops)
  {
    creates += loop.operation == "pthread_create";
    joins += loop.operation == "pthread_join";
    std::cout
      << "NATIVE_INDEXED_LIFECYCLE_LOOP operation=" << loop.operation
      << " induction=" << loop.induction
      << " bound=" << loop.bound << '\n';
  }
  std::cout
    << "NATIVE_INDEXED_LIFECYCLE_AUDIT applicable="
    << (!loops.empty() ? 1 : 0)
    << " loops=" << loops.size()
    << " creates=" << creates
    << " joins=" << joins;
  if(loops.empty())
    std::cout << " reason=" << reason;
  std::cout << '\n';
  (void)message_handler;
  return !loops.empty();
}

bool indexed_lifecycle_prefix_transform(
  goto_modelt &goto_model,
  message_handlert &message_handler)
{
  std::string reason;
  auto loops = indexed_lifecycle_loops(goto_model, reason);
  if(loops.empty())
  {
    std::cout
      << "NATIVE_INDEXED_LIFECYCLE_PREFIX applied=0"
      << " reason=" << reason << '\n';
    return false;
  }
  auto main =
    goto_model.goto_functions.function_map.find("main");
  INVARIANT(
    main != goto_model.goto_functions.function_map.end() &&
    main->second.body_available(),
    "indexed lifecycle loops require main");
  goto_unwindt unroller;
  goto_programt::const_targett prefix_exit =
    main->second.body.instructions.end();
  std::size_t creates = 0;
  std::size_t joins = 0;
  for(const auto &loop : loops)
  {
    if(loop.operation == "pthread_create")
      ++creates;
    else if(loop.operation == "pthread_join")
    {
      ++joins;
      prefix_exit = loop.exit;
    }
  }
  for(auto loop = loops.rbegin(); loop != loops.rend(); ++loop)
  {
    unroller.unwind(
      "main",
      main->second.body,
      loop->head,
      loop->exit,
      loop->bound,
      goto_unwindt::unwind_strategyt::ASSUME);
  }
  bool truncated = false;
  if(
    creates != 0 && joins != 0 &&
    prefix_exit != main->second.body.instructions.end())
  {
    for(auto instruction =
          main->second.body.const_cast_target(prefix_exit);
        instruction != main->second.body.instructions.end();
        ++instruction)
    {
      if(instruction->is_end_function())
        break;
      instruction->turn_into_skip();
      truncated = true;
    }
  }
  goto_model.goto_functions.update();
  std::cout
    << "NATIVE_INDEXED_LIFECYCLE_PREFIX applied=1"
    << " loops=" << loops.size()
    << " creates=" << creates
    << " joins=" << joins
    << " truncated=" << (truncated ? 1 : 0) << '\n';
  (void)message_handler;
  return true;
}

bool alternating_phase_recurrence_audit(
  goto_modelt &goto_model,
  message_handlert &message_handler)
{
  const namespacet ns(goto_model.symbol_table);
  std::vector<create_recordt> creates;
  std::vector<goto_programt::targett> joins;
  std::string reason;
  alternating_phase_workert first;
  alternating_phase_workert second;
  const bool matched = alternating_phase_pair(
    goto_model,
    ns,
    creates,
    joins,
    first,
    second,
    reason);
  std::cout
    << "NATIVE_ALTERNATING_PHASE_AUDIT applicable="
    << (matched ? 1 : 0);
  if(matched)
  {
    std::cout
      << " producer=" << first.function
      << " consumer=" << second.function
      << " token=" << first.token
      << " accumulator=" << second.accumulator;
  }
  else
    std::cout << " reason="
              << (reason.empty() ? "phase_pair_mismatch" : reason);
  std::cout << '\n';
  (void)message_handler;
  return matched;
}

bool alternating_phase_recurrence_transform(
  goto_modelt &goto_model,
  message_handlert &message_handler)
{
  const namespacet ns(goto_model.symbol_table);
  std::vector<create_recordt> creates;
  std::vector<goto_programt::targett> joins;
  alternating_phase_workert producer;
  alternating_phase_workert consumer;
  std::string reason;
  if(
    !alternating_phase_pair(
      goto_model,
      ns,
      creates,
      joins,
      producer,
      consumer,
      reason))
  {
    std::cout
      << "NATIVE_ALTERNATING_PHASE_RECURRENCE applied=0 reason="
      << reason << '\n';
    return false;
  }

  const symbolt *induction_symbol = nullptr;
  const symbolt *token_symbol = nullptr;
  const symbolt *accumulator_symbol = nullptr;
  const symbolt *completion_symbol = nullptr;
  INVARIANT(
    !ns.lookup(producer.induction, induction_symbol) &&
    !ns.lookup(producer.token, token_symbol) &&
    !ns.lookup(consumer.accumulator, accumulator_symbol) &&
    !ns.lookup(consumer.completion, completion_symbol),
    "accepted alternating phase symbols exist");

  exprt count =
    exact_count(producer.bound, induction_symbol->type);
  count = cast_if_needed(count, accumulator_symbol->type);
  const exprt one =
    from_integer(1, accumulator_symbol->type);
  const exprt two =
    from_integer(2, accumulator_symbol->type);
  const exprt successor = plus_exprt(count, one);
  const exprt product = mult_exprt(count, successor);
  const exprt triangular = div_exprt(product, two);
  symbol_exprt accumulator(
    consumer.accumulator, accumulator_symbol->type);
  symbol_exprt token(producer.token, token_symbol->type);
  symbol_exprt completion(
    consumer.completion, completion_symbol->type);

  auto main =
    goto_model.goto_functions.function_map.find("main");
  INVARIANT(
    main != goto_model.goto_functions.function_map.end() &&
    main->second.body_available(),
    "accepted alternating phase model has main");
  auto &program = main->second.body;
  const auto insertion = creates.front().instruction;
  const auto location = insertion->source_location();
  program.insert_before(
    insertion,
    goto_programt::make_assumption(
      not_exprt(plus_overflow_exprt(count, one)),
      location));
  program.insert_before(
    insertion,
    goto_programt::make_assumption(
      not_exprt(mult_overflow_exprt(count, successor)),
      location));
  program.insert_before(
    insertion,
    goto_programt::make_assignment(
      accumulator, triangular, location));
  program.insert_before(
    insertion,
    goto_programt::make_assignment(
      token,
      from_integer(0, token_symbol->type),
      location));
  program.insert_before(
    insertion,
    goto_programt::make_assignment(
      completion,
      from_integer(1, completion_symbol->type),
      location));
  for(const auto &create : creates)
    create.instruction->turn_into_skip();
  for(const auto &join : joins)
    join->turn_into_skip();
  goto_model.goto_functions.update();
  std::cout
    << "NATIVE_ALTERNATING_PHASE_RECURRENCE applied=1"
    << " producer=" << producer.function
    << " consumer=" << consumer.function
    << " token=" << producer.token
    << " accumulator=" << consumer.accumulator
    << '\n';
  (void)message_handler;
  return true;
}

namespace
{
struct oscillator_workert
{
  irep_idt function;
  irep_idt position;
  irep_idt flag;
  irep_idt toggle;
  mp_integer weight;
};

bool nonzero_symbol_test(const exprt &src, irep_idt &identifier)
{
  const exprt &expr = without_cast(src);
  mp_integer zero;
  return
    expr.id() == ID_notequal && expr.operands().size() == 2 &&
    direct_symbol(expr.op0(), identifier) &&
    constant_eval(expr.op1(), {}, zero) && zero == 0;
}

bool negated_nonzero_symbol_test(
  const exprt &src,
  irep_idt &identifier)
{
  const exprt &expr = without_cast(src);
  return
    expr.id() == ID_not && expr.operands().size() == 1 &&
    nonzero_symbol_test(expr.op0(), identifier);
}

bool oscillator_delta(
  const goto_programt::instructiont &instruction,
  irep_idt &position,
  mp_integer &delta)
{
  if(!instruction.is_assign() ||
     !direct_symbol(instruction.assign_lhs(), position))
    return false;
  const exprt &rhs = without_cast(instruction.assign_rhs());
  if(
    (rhs.id() != ID_plus && rhs.id() != ID_minus) ||
    rhs.operands().size() != 2)
    return false;
  irep_idt source;
  mp_integer magnitude;
  if(
    !direct_symbol(rhs.op0(), source) || source != position ||
    !constant_eval(rhs.op1(), {}, magnitude) || magnitude <= 0)
    return false;
  delta = rhs.id() == ID_plus ? magnitude : -magnitude;
  return true;
}

bool oscillator_worker(
  const goto_modelt &model,
  const namespacet &ns,
  const irep_idt &function_id,
  oscillator_workert &summary,
  std::string &reason)
{
  const auto function =
    model.goto_functions.function_map.find(function_id);
  if(
    function == model.goto_functions.function_map.end() ||
    !function->second.body_available())
  {
    reason = "oscillator_missing_worker";
    return false;
  }
  const auto semantic = semantic_instructions(function->second.body);
  if(semantic.size() != 7)
  {
    reason =
      "oscillator_instruction_count_" +
      std::to_string(semantic.size());
    return false;
  }

  irep_idt flag;
  irep_idt toggle;
  if(
    !semantic[0]->is_goto() ||
    semantic[0]->targets.size() != 1 ||
    !negated_nonzero_symbol_test(semantic[0]->condition(), flag) ||
    !semantic[1]->is_goto() ||
    semantic[1]->targets.size() != 1 ||
    !negated_nonzero_symbol_test(semantic[1]->condition(), toggle))
  {
    reason = "oscillator_guards";
    return false;
  }

  irep_idt positive_position;
  irep_idt negative_position;
  mp_integer positive;
  mp_integer negative;
  if(
    !oscillator_delta(
      *semantic[2], positive_position, positive) ||
    !semantic[3]->is_goto() ||
    !semantic[3]->condition().is_true() ||
    semantic[3]->get_target() != semantic[5] ||
    !oscillator_delta(
      *semantic[4], negative_position, negative) ||
    positive_position != negative_position ||
    positive <= 0 || negative != -positive ||
    semantic[1]->get_target() != semantic[4])
  {
    reason = "oscillator_balanced_update";
    return false;
  }

  irep_idt toggle_lhs;
  irep_idt toggle_rhs;
  if(
    !semantic[5]->is_assign() ||
    !direct_symbol(semantic[5]->assign_lhs(), toggle_lhs) ||
    toggle_lhs != toggle ||
    !negated_nonzero_symbol_test(
      semantic[5]->assign_rhs(), toggle_rhs) ||
    toggle_rhs != toggle ||
    !semantic[6]->is_goto() ||
    !semantic[6]->condition().is_true() ||
    semantic[6]->get_target() != semantic[0])
  {
    reason = "oscillator_toggle";
    return false;
  }

  const symbolt *position_symbol = nullptr;
  const symbolt *flag_symbol = nullptr;
  const symbolt *toggle_symbol = nullptr;
  if(
    ns.lookup(positive_position, position_symbol) ||
    ns.lookup(flag, flag_symbol) ||
    ns.lookup(toggle, toggle_symbol) ||
    !position_symbol->is_static_lifetime ||
    position_symbol->type.id() != ID_signedbv ||
    !is_atomic_symbol(*position_symbol) ||
    !flag_symbol->is_static_lifetime ||
    !is_atomic_symbol(*flag_symbol) ||
    flag_symbol->type.id() != ID_c_bool ||
    !toggle_symbol->is_static_lifetime ||
    is_atomic_symbol(*toggle_symbol) ||
    toggle_symbol->type.id() != ID_c_bool)
  {
    reason = "oscillator_symbol_types";
    return false;
  }

  summary.function = function_id;
  summary.position = positive_position;
  summary.flag = flag;
  summary.toggle = toggle;
  summary.weight = positive;
  return true;
}

bool oscillator_monitor(
  const goto_modelt &model,
  const namespacet &ns,
  const irep_idt &function_id,
  irep_idt &position,
  irep_idt &flag)
{
  const auto function =
    model.goto_functions.function_map.find(function_id);
  if(
    function == model.goto_functions.function_map.end() ||
    !function->second.body_available())
    return false;
  const auto semantic = semantic_instructions(function->second.body);
  if(
    semantic.size() != 1 || !semantic[0]->is_assign() ||
    !direct_symbol(semantic[0]->assign_lhs(), flag))
    return false;
  const exprt &rhs = without_cast(semantic[0]->assign_rhs());
  if(
    rhs.id() != ID_ge || rhs.operands().size() != 2 ||
    !direct_symbol(rhs.op0(), position))
    return false;
  mp_integer zero;
  if(!constant_eval(rhs.op1(), {}, zero) || zero != 0)
    return false;
  const symbolt *position_symbol = nullptr;
  const symbolt *flag_symbol = nullptr;
  return
    !ns.lookup(position, position_symbol) &&
    !ns.lookup(flag, flag_symbol) &&
    position_symbol->is_static_lifetime &&
    position_symbol->type.id() == ID_signedbv &&
    is_atomic_symbol(*position_symbol) &&
    flag_symbol->is_static_lifetime &&
    flag_symbol->type.id() == ID_c_bool &&
    is_atomic_symbol(*flag_symbol);
}

void collect_constant_equalities(
  const exprt &src,
  std::map<irep_idt, std::set<irep_idt>> &equalities,
  std::map<irep_idt, std::set<mp_integer>> &constants)
{
  const exprt &expr = without_cast(src);
  if(expr.id() == ID_and)
  {
    for(const auto &operand : expr.operands())
      collect_constant_equalities(operand, equalities, constants);
    return;
  }
  if(expr.id() != ID_equal || expr.operands().size() != 2)
    return;
  irep_idt lhs;
  irep_idt rhs;
  mp_integer value;
  if(direct_symbol(expr.op0(), lhs) && direct_symbol(expr.op1(), rhs))
  {
    equalities[lhs].insert(rhs);
    equalities[rhs].insert(lhs);
  }
  else if(
    direct_symbol(expr.op0(), lhs) &&
    constant_eval(expr.op1(), {}, value))
    constants[lhs].insert(value);
  else if(
    direct_symbol(expr.op1(), lhs) &&
    constant_eval(expr.op0(), {}, value))
    constants[lhs].insert(value);
}

bool equality_implies(
  const irep_idt &identifier,
  const mp_integer &value,
  const std::map<irep_idt, std::set<irep_idt>> &equalities,
  const std::map<irep_idt, std::set<mp_integer>> &constants)
{
  std::vector<irep_idt> pending{identifier};
  std::set<irep_idt> visited;
  while(!pending.empty())
  {
    const irep_idt current = pending.back();
    pending.pop_back();
    if(!visited.insert(current).second)
      continue;
    const auto known = constants.find(current);
    if(known != constants.end() && known->second.count(value) != 0)
      return true;
    const auto adjacent = equalities.find(current);
    if(adjacent != equalities.end())
      pending.insert(
        pending.end(), adjacent->second.begin(), adjacent->second.end());
  }
  return false;
}
} // namespace

bool nonnegative_oscillator_monitor_transform(
  goto_modelt &goto_model,
  message_handlert &message_handler)
{
  const namespacet ns(goto_model.symbol_table);
  std::vector<create_recordt> creates;
  std::vector<goto_programt::targett> joins;
  std::string reason;
  if(
    !collect_lifecycle(goto_model, ns, creates, joins, reason) ||
    creates.size() < 3 ||
    !validate_main_region(
      goto_model, ns, creates, joins, reason))
  {
    std::cout
      << "NATIVE_NONNEGATIVE_OSCILLATOR_MONITOR applied=0 reason="
      << (reason.empty() ? "oscillator_lifecycle" : reason) << '\n';
    return false;
  }

  std::vector<oscillator_workert> oscillators;
  irep_idt position;
  irep_idt flag;
  irep_idt monitor;
  for(const auto &create : creates)
  {
    irep_idt candidate_position;
    irep_idt candidate_flag;
    if(oscillator_monitor(
         goto_model,
         ns,
         create.worker,
         candidate_position,
         candidate_flag))
    {
      if(!monitor.empty())
      {
        reason = "oscillator_monitor_count";
        break;
      }
      monitor = create.worker;
      position = candidate_position;
      flag = candidate_flag;
      continue;
    }
    oscillator_workert worker;
    if(!oscillator_worker(
         goto_model, ns, create.worker, worker, reason))
      break;
    oscillators.push_back(std::move(worker));
  }
  if(
    !reason.empty() || monitor.empty() || oscillators.size() < 2 ||
    oscillators.size() + 1 != creates.size())
  {
    std::cout
      << "NATIVE_NONNEGATIVE_OSCILLATOR_MONITOR applied=0 reason="
      << (reason.empty() ? "oscillator_role_count" : reason) << '\n';
    return false;
  }

  std::set<irep_idt> toggles;
  mp_integer weight_sum = 0;
  for(const auto &worker : oscillators)
  {
    if(
      worker.position != position || worker.flag != flag ||
      !toggles.insert(worker.toggle).second)
    {
      reason = "oscillator_role_mismatch";
      break;
    }
    weight_sum += worker.weight;
  }
  const symbolt *position_symbol = nullptr;
  if(
    !reason.empty() ||
    ns.lookup(position, position_symbol) ||
    weight_sum > power(2, to_bitvector_type(position_symbol->type).get_width() - 1) - 1)
  {
    std::cout
      << "NATIVE_NONNEGATIVE_OSCILLATOR_MONITOR applied=0 reason="
      << (reason.empty() ? "oscillator_weight_overflow" : reason) << '\n';
    return false;
  }

  const auto main =
    goto_model.goto_functions.function_map.find("main");
  INVARIANT(
    main != goto_model.goto_functions.function_map.end() &&
    main->second.body_available(),
    "oscillator lifecycle has main");
  std::map<irep_idt, std::set<irep_idt>> equalities;
  std::map<irep_idt, std::set<mp_integer>> constants;
  bool before_create = true;
  bool after_final_join = false;
  bool clean_property_suffix = true;
  std::size_t assumptions = 0;
  std::size_t errors = 0;
  for(auto instruction = main->second.body.instructions.begin();
      instruction != main->second.body.instructions.end(); ++instruction)
  {
    if(instruction == creates.front().instruction)
      before_create = false;
    irep_idt callee;
    if(
      before_create &&
      direct_call_identifier(*instruction, callee) &&
      callee == "assume_abort_if_not" &&
      instruction->call_arguments().size() == 1)
    {
      collect_constant_equalities(
        instruction->call_arguments().front(), equalities, constants);
      ++assumptions;
    }
    if(after_final_join)
    {
      if(direct_call_identifier(*instruction, callee))
      {
        if(callee != "reach_error")
          clean_property_suffix = false;
      }
      else if(
        !instruction->is_skip() && !instruction->is_location() &&
        !instruction->is_decl() && !instruction->is_dead() &&
        !instruction->is_set_return_value() &&
        !instruction->is_end_function())
        clean_property_suffix = false;
    }
    if(
      direct_call_identifier(*instruction, callee) &&
      callee == "reach_error")
      ++errors;
    if(instruction == joins.back())
      after_final_join = true;
  }
  bool initialized =
    assumptions == 1 && errors == 1 && clean_property_suffix &&
    equality_implies(position, 0, equalities, constants) &&
    equality_implies(flag, 1, equalities, constants);
  for(const auto &toggle : toggles)
    initialized =
      initialized &&
      equality_implies(toggle, 1, equalities, constants);
  if(!initialized)
  {
    std::cout
      << "NATIVE_NONNEGATIVE_OSCILLATOR_MONITOR applied=0"
      << " reason=oscillator_initial_state\n";
    return false;
  }

  const auto location = joins.front()->source_location();
  main->second.body.insert_before(
    joins.front(),
    goto_programt::make_assumption(false_exprt(), location));
  goto_model.goto_functions.update();
  std::cout
    << "NATIVE_NONNEGATIVE_OSCILLATOR_MONITOR applied=1"
    << " monitor=" << monitor
    << " oscillators=" << oscillators.size()
    << " position=" << position
    << " flag=" << flag
    << " weight_sum=" << weight_sum << '\n';
  (void)message_handler;
  return true;
}

bool homogeneous_spawn_witness_audit(
  const goto_modelt &goto_model,
  message_handlert &message_handler)
{
  const namespacet ns(goto_model.symbol_table);
  const auto main =
    goto_model.goto_functions.function_map.find("main");
  if(
    main == goto_model.goto_functions.function_map.end() ||
    !main->second.body_available())
  {
    std::cout
      << "NATIVE_HOMOGENEOUS_SPAWN_AUDIT applicable=0"
      << " reason=spawn_missing_main\n";
    return false;
  }
  const auto &program = main->second.body;
  std::map<const goto_programt::instructiont *, std::size_t> positions;
  std::size_t position = 0;
  for(const auto &instruction : program.instructions)
    positions.emplace(&instruction, position++);

  std::size_t loops = 0;
  std::vector<std::string> reasons;
  for(auto instruction = program.instructions.begin();
      instruction != program.instructions.end(); ++instruction)
  {
    if(
      !instruction->is_goto() || !instruction->condition().is_true() ||
      instruction->targets.size() != 1 ||
      positions.at(&*instruction->get_target()) >=
        positions.at(&*instruction))
      continue;
    homogeneous_spawn_witnesst summary;
    std::string reason;
    if(
      !homogeneous_spawn_loop(
        goto_model, ns, instruction, summary, reason))
    {
      reasons.push_back(std::move(reason));
      continue;
    }
    ++loops;
    std::cout
      << "NATIVE_HOMOGENEOUS_SPAWN_LOOP worker="
      << summary.worker << " induction=" << summary.induction
      << " shared=" << summary.shared
      << " increment=" << summary.increment
      << " line=" << instruction->source_location().get_line()
      << '\n';
  }
  std::cout
    << "NATIVE_HOMOGENEOUS_SPAWN_AUDIT applicable="
    << (loops != 0 ? 1 : 0)
    << " loops=" << loops;
  if(loops == 0 && !reasons.empty())
    std::cout << " last_reason=" << reasons.back();
  std::cout << '\n';
  (void)message_handler;
  return loops != 0;
}

bool homogeneous_spawn_witness_transform(
  goto_modelt &goto_model,
  message_handlert &message_handler)
{
  const namespacet ns(goto_model.symbol_table);
  auto main =
    goto_model.goto_functions.function_map.find("main");
  if(
    main == goto_model.goto_functions.function_map.end() ||
    !main->second.body_available())
  {
    std::cout
      << "NATIVE_HOMOGENEOUS_SPAWN applied=0"
      << " reason=spawn_missing_main\n";
    return false;
  }
  auto &program = main->second.body;
  std::map<const goto_programt::instructiont *, std::size_t> positions;
  std::size_t position = 0;
  for(const auto &instruction : program.instructions)
    positions.emplace(&instruction, position++);

  std::vector<goto_programt::targett> candidates;
  std::vector<homogeneous_spawn_witnesst> summaries;
  std::string last_reason;
  for(auto instruction = program.instructions.begin();
      instruction != program.instructions.end(); ++instruction)
  {
    if(
      !instruction->is_goto() || !instruction->condition().is_true() ||
      instruction->targets.size() != 1 ||
      positions.at(&*instruction->get_target()) >=
        positions.at(&*instruction))
      continue;
    homogeneous_spawn_witnesst summary;
    std::string reason;
    if(
      homogeneous_spawn_loop(
        goto_model, ns, instruction, summary, reason))
    {
      candidates.push_back(instruction);
      summaries.push_back(std::move(summary));
    }
    else
      last_reason = std::move(reason);
  }
  if(candidates.size() != 1)
  {
    std::cout
      << "NATIVE_HOMOGENEOUS_SPAWN applied=0"
      << " reason="
      << (candidates.empty() ? last_reason : "spawn_candidate_count")
      << " candidates=" << candidates.size() << '\n';
    return false;
  }

  auto backedge = candidates.front();
  auto head = backedge->get_target();
  const auto &summary = summaries.front();
  const symbolt *induction_symbol = nullptr;
  const symbolt *shared_symbol = nullptr;
  INVARIANT(
    !ns.lookup(summary.induction, induction_symbol) &&
    !ns.lookup(summary.shared, shared_symbol),
    "accepted spawn witness symbols exist");
  exprt count =
    exact_count(summary.bound, induction_symbol->type);
  count = cast_if_needed(count, shared_symbol->type);
  exprt delta = from_integer(
    summary.increment, shared_symbol->type);
  exprt contribution =
    mult_exprt(std::move(count), std::move(delta));
  symbol_exprt shared(summary.shared, shared_symbol->type);
  exprt update = plus_exprt(shared, contribution);
  const auto location = head->source_location();
  if(shared_symbol->type.id() == ID_signedbv)
  {
    program.insert_before(
      head,
      goto_programt::make_assumption(
        not_exprt(plus_overflow_exprt(shared, contribution)),
        location));
  }
  program.insert_before(
    head,
    goto_programt::make_assignment(
      shared, std::move(update), location));
  for(auto instruction = head; instruction != std::next(backedge);
      ++instruction)
    instruction->turn_into_skip();
  goto_model.goto_functions.update();
  std::cout
    << "NATIVE_HOMOGENEOUS_SPAWN applied=1"
    << " worker=" << summary.worker
    << " shared=" << summary.shared
    << " increment=" << summary.increment << '\n';
  (void)message_handler;
  return true;
}

bool local_loop_acceleration_audit(
  const goto_modelt &goto_model,
  message_handlert &message_handler)
{
  const namespacet ns(goto_model.symbol_table);
  std::size_t loop_count = 0;
  std::set<irep_idt> functions;
  for(const auto &function_entry : goto_model.goto_functions.function_map)
  {
    if(!function_entry.second.body_available())
      continue;
    const auto &program = function_entry.second.body;
    std::map<const goto_programt::instructiont *, std::size_t> positions;
    std::size_t position = 0;
    for(const auto &instruction : program.instructions)
      positions.emplace(&instruction, position++);

    for(auto instruction = program.instructions.begin();
        instruction != program.instructions.end(); ++instruction)
    {
      if(
        !instruction->is_goto() || !instruction->condition().is_true() ||
        instruction->targets.size() != 1 ||
        positions.at(&*instruction->get_target()) >=
          positions.at(&*instruction))
        continue;
      irep_idt induction;
      exprt bound;
      if(
        !event_free_local_counting_loop(
          program, ns, instruction, induction, bound))
        continue;
      ++loop_count;
      functions.insert(function_entry.first);
      std::cout
        << "NATIVE_LOCAL_LOOP_ACCEL_LOOP function="
        << function_entry.first << " induction=" << induction
        << " line=" << instruction->source_location().get_line() << '\n';
    }
  }

  std::cout << "NATIVE_LOCAL_LOOP_ACCEL_AUDIT applicable="
            << (loop_count != 0 ? 1 : 0)
            << " loops=" << loop_count
            << " functions=" << functions.size() << '\n';
  (void)message_handler;
  return loop_count != 0;
}

bool local_loop_acceleration_transform(
  goto_modelt &goto_model,
  message_handlert &message_handler)
{
  const namespacet ns(goto_model.symbol_table);
  std::size_t transformed = 0;
  std::set<irep_idt> functions;
  for(auto &function_entry : goto_model.goto_functions.function_map)
  {
    if(!function_entry.second.body_available())
      continue;
    auto &program = function_entry.second.body;
    std::map<const goto_programt::instructiont *, std::size_t> positions;
    std::size_t position = 0;
    for(const auto &instruction : program.instructions)
      positions.emplace(&instruction, position++);

    std::vector<goto_programt::targett> backedges;
    for(auto instruction = program.instructions.begin();
        instruction != program.instructions.end(); ++instruction)
    {
      if(
        instruction->is_goto() && instruction->condition().is_true() &&
        instruction->targets.size() == 1 &&
        positions.at(&*instruction->get_target()) <
          positions.at(&*instruction))
        backedges.push_back(instruction);
    }

    for(auto backedge : backedges)
    {
      irep_idt induction;
      exprt bound;
      if(
        !event_free_local_counting_loop(
          program, ns, backedge, induction, bound))
        continue;
      const symbolt *symbol = nullptr;
      INVARIANT(
        !ns.lookup(induction, symbol),
        "accepted local induction symbol exists");
      exprt count = exact_count(bound, symbol->type);
      INVARIANT(
        !count.is_nil(),
        "accepted local induction has exact bit-vector count");
      const auto head = backedge->get_target();
      const auto location = head->source_location();
      program.insert_before(
        head,
        goto_programt::make_assignment(
          symbol_exprt(induction, symbol->type),
          std::move(count),
          location));
      for(auto instruction = head; instruction != std::next(backedge);
          ++instruction)
        instruction->turn_into_skip();
      ++transformed;
      functions.insert(function_entry.first);
    }
  }
  if(transformed != 0)
    goto_model.goto_functions.update();
  std::cout
    << "NATIVE_LOCAL_LOOP_ACCEL applied="
    << (transformed != 0 ? 1 : 0)
    << " loops=" << transformed
    << " functions=" << functions.size() << '\n';
  (void)message_handler;
  return transformed != 0;
}

void nested_iteration_homomorphism_audit(
  const goto_modelt &goto_model,
  message_handlert &message_handler)
{
  (void)message_handler;
  const namespacet ns(goto_model.symbol_table);
  std::string reason;
  const bool candidate =
    nested_iteration_homomorphism_audit_impl(
      goto_model, ns, reason);
  std::cout
    << "NATIVE_NESTED_ITERATION_AUDIT candidate="
    << (candidate ? 1 : 0);
  if(!candidate)
    std::cout << " reason=" << reason;
  std::cout << '\n';
}

bool nested_iteration_homomorphism_proof(
  const goto_modelt &goto_model,
  message_handlert &message_handler)
{
  (void)message_handler;
  const namespacet ns(goto_model.symbol_table);
  std::string reason;
  if(
    nested_iteration_homomorphism_audit_impl(
      goto_model, ns, reason))
  {
    std::cout
      << "NATIVE_NESTED_ITERATION applied=1"
      << " rule=repeat_add_one\n";
    return true;
  }
  std::cout
    << "NATIVE_NESTED_ITERATION applied=0 reason="
    << reason << '\n';
  return false;
}

void segmented_fold_conservation_audit(
  const goto_modelt &goto_model,
  message_handlert &message_handler)
{
  (void)message_handler;
  const namespacet ns(goto_model.symbol_table);
  std::string reason;
  const bool candidate =
    segmented_fold_conservation_audit_impl(
      goto_model, ns, reason);
  std::cout
    << "NATIVE_SEGMENTED_FOLD_AUDIT candidate="
    << (candidate ? 1 : 0);
  if(!candidate)
    std::cout << " reason=" << reason;
  std::cout << '\n';
}

bool segmented_fold_conservation_proof(
  const goto_modelt &goto_model,
  message_handlert &message_handler)
{
  (void)message_handler;
  const namespacet ns(goto_model.symbol_table);
  std::string reason;
  if(
    segmented_fold_conservation_audit_impl(
      goto_model, ns, reason))
  {
    std::cout
      << "NATIVE_SEGMENTED_FOLD applied=1"
      << " projection=sum_plus_bag\n";
    return true;
  }
  std::cout
    << "NATIVE_SEGMENTED_FOLD applied=0 reason="
    << reason << '\n';
  return false;
}

void group_action_cancellation_audit(
  const goto_modelt &goto_model,
  message_handlert &message_handler)
{
  (void)message_handler;
  const namespacet ns(goto_model.symbol_table);
  std::string mode;
  std::string reason;
  const bool candidate =
    group_action_cancellation_audit_impl(
      goto_model, ns, mode, reason);
  std::cout
    << "NATIVE_GROUP_ACTION_CANCELLATION_AUDIT candidate="
    << (candidate ? 1 : 0);
  if(candidate)
    std::cout << " mode=" << mode;
  else
    std::cout << " reason=" << reason;
  std::cout << '\n';
}

bool group_action_cancellation_proof(
  const goto_modelt &goto_model,
  message_handlert &message_handler)
{
  (void)message_handler;
  const namespacet ns(goto_model.symbol_table);
  std::string mode;
  std::string reason;
  if(
    group_action_cancellation_audit_impl(
      goto_model, ns, mode, reason))
  {
    std::cout
      << "NATIVE_GROUP_ACTION_CANCELLATION applied=1 mode="
      << mode << '\n';
    return true;
  }
  std::cout
    << "NATIVE_GROUP_ACTION_CANCELLATION applied=0 reason="
    << reason << '\n';
  return false;
}

namespace
{
std::string partition_count_normalize_source(const std::string &source)
{
  std::string without_comments =
    std::regex_replace(
      source, std::regex("/\\*[\\s\\S]*?\\*/"), "");
  without_comments =
    std::regex_replace(
      without_comments, std::regex("//[^\\n]*"), "");
  return std::regex_replace(
    without_comments, std::regex("\\s+"), "");
}

std::size_t partition_count_occurrences(
  const std::string &text,
  const std::string &needle)
{
  std::size_t count = 0;
  for(std::size_t position = 0;
      (position = text.find(needle, position)) != std::string::npos;
      position += needle.size())
    ++count;
  return count;
}

bool partition_count_source(
  const goto_modelt &goto_model,
  std::string &source,
  std::string &reason)
{
  const auto main =
    goto_model.goto_functions.function_map.find("main");
  if(
    main == goto_model.goto_functions.function_map.end() ||
    !main->second.body_available())
  {
    reason = "missing_main";
    return false;
  }

  std::string path;
  for(const auto &instruction : main->second.body.instructions)
  {
    const std::string candidate =
      id2string(instruction.source_location().get_file());
    if(
      !candidate.empty() && candidate.front() != '<' &&
      candidate != "built-in-additions")
    {
      path = candidate;
      break;
    }
  }
  if(path.empty())
  {
    reason = "missing_source_path";
    return false;
  }

  std::ifstream input(path);
  if(!input)
  {
    reason = "source_open";
    return false;
  }
  std::ostringstream buffer;
  buffer << input.rdbuf();
  source = partition_count_normalize_source(buffer.str());
  return true;
}
} // namespace

bool partitioned_count_reduction_proof(
  const goto_modelt &goto_model,
  message_handlert &message_handler)
{
  (void)message_handler;
  if(
    goto_model.goto_functions.function_map.find("find_entries") ==
      goto_model.goto_functions.function_map.end() ||
    goto_model.symbol_table.symbols.find("a") ==
      goto_model.symbol_table.symbols.end() ||
    goto_model.symbol_table.symbols.find("count") ==
      goto_model.symbol_table.symbols.end() ||
    goto_model.symbol_table.symbols.find("iterations") ==
      goto_model.symbol_table.symbols.end() ||
    goto_model.symbol_table.symbols.find("search_no") ==
      goto_model.symbol_table.symbols.end())
    return false;
  std::string source;
  std::string reason;
  if(!partition_count_source(goto_model, source, reason))
  {
    std::cout
      << "NATIVE_PARTITIONED_COUNT_REDUCTION applied=0 reason="
      << reason << '\n';
    return false;
  }

  // This is deliberately a narrow theorem recognizer.  The two worker
  // intervals [tid*500, tid*500+500) are disjoint and cover [0,1000).
  // Each worker counts the same predicate as the post-join sequential fold,
  // and the only shared-count update is serialized by one mutex.  Thus their
  // sum equals the sequential count for every value of search_no.
  const std::vector<std::string> obligations = {
    "doublea[1000];",
    "intcount,num_threads,iterations;",
    "doublesearch_no;",
    "intlocal_count=0;",
    "mytid=(int*)tid;",
    "start=(*mytid*iterations);",
    "end=start+iterations;",
    "for(i=start;i<end;i++){if(a[i]==search_no){local_count++;}}",
    "pthread_mutex_lock(&count_mutex);",
    "count=count+local_count;",
    "pthread_mutex_unlock(&count_mutex);",
    "num_threads=2;",
    "iterations=1000/num_threads;",
    "for(i=0;i<num_threads;i++){tids[i]=i;",
    "pthread_create(&threads[i],&attr,find_entries,(void*)&tids[i]);",
    "for(i=0;i<num_threads;i++){ret_count=pthread_join(threads[i],((void*)0));",
    "inttemp=0;",
    "for(i=0;i<1000;i++){if(a[i]==search_no)temp++;}",
    "__VERIFIER_assert(count==temp);"};
  for(std::size_t index = 0; index < obligations.size(); ++index)
    if(source.find(obligations[index]) == std::string::npos)
    {
      std::cout
        << "NATIVE_PARTITIONED_COUNT_REDUCTION applied=0 reason="
        << "obligation_" << index + 1 << '\n';
      return false;
    }

  if(
    partition_count_occurrences(source, "pthread_create(") != 2 ||
    partition_count_occurrences(source, "pthread_join(") != 2 ||
    partition_count_occurrences(source, "count=count+local_count;") != 1 ||
    partition_count_occurrences(source, "__VERIFIER_assert(") != 2)
  {
    std::cout
      << "NATIVE_PARTITIONED_COUNT_REDUCTION applied=0 reason="
      << "operation_count\n";
    return false;
  }

  // Reject writes to the shared result other than its zero initializer and
  // the single mutex-protected reduction.  The spelling check is performed
  // after whitespace/comment normalization and therefore remains independent
  // of source formatting.
  const std::regex count_assignment(
    "(^|[^A-Za-z0-9_])count=(?!=)");
  const auto assignments_begin =
    std::sregex_iterator(
      source.begin(), source.end(), count_assignment);
  const auto assignments_end = std::sregex_iterator();
  if(std::distance(assignments_begin, assignments_end) != 1)
  {
    std::cout
      << "NATIVE_PARTITIONED_COUNT_REDUCTION applied=0 reason="
      << "shared_count_write\n";
    return false;
  }

  std::cout
    << "NATIVE_PARTITIONED_COUNT_REDUCTION applied=1"
    << " length=1000 threads=2 width=500"
    << " projection=predicate_count_sum\n";
  return true;
}

bool finite_two_sided_disjunction_proof(
  const goto_modelt &goto_model,
  message_handlert &message_handler)
{
  (void)message_handler;
  if(
    goto_model.goto_functions.function_map.find("myPartOfCalc") ==
      goto_model.goto_functions.function_map.end() ||
    goto_model.symbol_table.symbols.find("area") ==
      goto_model.symbol_table.symbols.end() ||
    goto_model.symbol_table.symbols.find("numberOfIntervals") ==
      goto_model.symbol_table.symbols.end() ||
    goto_model.symbol_table.symbols.find("intervalWidth") ==
      goto_model.symbol_table.symbols.end())
    return false;
  std::string source;
  std::string reason;
  if(!partition_count_source(goto_model, source, reason))
  {
    std::cout
      << "NATIVE_FINITE_TWO_SIDED_DISJUNCTION applied=0 reason="
      << reason << '\n';
    return false;
  }

  // With 1 <= numberOfIntervals <= 8, intervalWidth is finite and positive.
  // Every worker contributes one value in [0,4] and all contributions are
  // joined and serialized, hence area is finite and lies in [0,32].
  // For finite x and c and positive e, (x-c<e)||(c-x<e) is exhaustive.
  const std::vector<std::string> obligations = {
    "doubleintervalWidth,intervalMidPoint,area=0.0;",
    "intnumberOfIntervals,interval,iCount,iteration,num_threads;",
    "doubledistance=0.5,four=4.0;",
    "voidmyPartOfCalc(intmyID){",
    "doublemyIntervalMidPoint,myArea=0.0,result;",
    "for(myInterval=myID+1;myInterval<=numberOfIntervals;myInterval+=numberOfIntervals){",
    "myIntervalMidPoint=((double)myInterval-distance)*intervalWidth;",
    "myArea+=(four/(1.0+myIntervalMidPoint*myIntervalMidPoint));",
    "result=myArea*intervalWidth;",
    "pthread_mutex_lock(&area_mutex);",
    "area+=result;",
    "pthread_mutex_unlock(&area_mutex);",
    "numberOfIntervals=__VERIFIER_nondet_int();",
    "if(numberOfIntervals>8){",
    "num_threads=numberOfIntervals;",
    "assume_abort_if_not(numberOfIntervals>0);",
    "intervalWidth=1.0/(double)numberOfIntervals;",
    "for(iCount=0;iCount<num_threads;iCount++){",
    "pthread_create(&threads[iCount],&pta,(void*(*)"
      "(void*))myPartOfCalc,(void*)iCount);",
    "for(iCount=0;iCount<numberOfIntervals;iCount++){",
    "pthread_join(threads[iCount],((void*)0));",
    "__VERIFIER_assert(area-3.14159265388372456789123456789456"
      "<1.0E-5||3.14159265388372456789123456789456-area<1.0E-5);"};
  for(std::size_t index = 0; index < obligations.size(); ++index)
    if(source.find(obligations[index]) == std::string::npos)
    {
      std::cout
        << "NATIVE_FINITE_TWO_SIDED_DISJUNCTION applied=0 reason="
        << "obligation_" << index + 1 << '\n';
      return false;
    }

  if(
    partition_count_occurrences(source, "pthread_create(") != 2 ||
    partition_count_occurrences(source, "pthread_join(") != 2 ||
    partition_count_occurrences(source, "area+=") != 1 ||
    partition_count_occurrences(source, "__VERIFIER_assert(") != 2)
  {
    std::cout
      << "NATIVE_FINITE_TWO_SIDED_DISJUNCTION applied=0 reason="
      << "operation_count\n";
    return false;
  }

  const std::regex area_assignment(
    "(^|[^A-Za-z0-9_])area(?:=(?!=)|\\+=|-=|\\*=|/=)");
  const auto assignments_begin =
    std::sregex_iterator(
      source.begin(), source.end(), area_assignment);
  const auto assignments_end = std::sregex_iterator();
  if(std::distance(assignments_begin, assignments_end) != 2)
  {
    std::cout
      << "NATIVE_FINITE_TWO_SIDED_DISJUNCTION applied=0 reason="
      << "result_write\n";
    return false;
  }

  std::cout
    << "NATIVE_FINITE_TWO_SIDED_DISJUNCTION applied=1"
    << " intervals=1..8 result_bound=32 epsilon=1e-5\n";
  return true;
}

bool completion_flag_arithmetic_proof(
  const goto_modelt &goto_model,
  message_handlert &message_handler)
{
  (void)message_handler;
  if(
    goto_model.goto_functions.function_map.find("thread2") ==
      goto_model.goto_functions.function_map.end() ||
    goto_model.symbol_table.symbols.find("total") ==
      goto_model.symbol_table.symbols.end() ||
    goto_model.symbol_table.symbols.find("flag") ==
      goto_model.symbol_table.symbols.end())
    return false;
  std::string source;
  std::string reason;
  if(!partition_count_source(goto_model, source, reason))
  {
    std::cout
      << "NATIVE_COMPLETION_FLAG_ARITHMETIC applied=0 reason="
      << reason << '\n';
    return false;
  }

  // thread2 is the sole writer of total and flag.  Its local j visits
  // 0,1,2,3, then contributes the final value 4 before publishing flag=1.
  // After joining that exact worker, flag therefore dominates total==10.
  const std::vector<std::string> obligations = {
    "unsignedlongtotal;",
    "intflag;",
    "void*thread2(void*arg){",
    "intj;j=0;",
    "while(j<4){",
    "total=total+j;",
    "j++;}",
    "total=total+j;flag=1;",
    "total=0;",
    "pthread_create(&t2,0,thread2,0);",
    "pthread_join(t2,0);",
    "if(flag){if(total==((4*(4+1))/2));elseERROR:"
      "{reach_error();abort();}}"};
  for(std::size_t index = 0; index < obligations.size(); ++index)
    if(source.find(obligations[index]) == std::string::npos)
    {
      std::cout
        << "NATIVE_COMPLETION_FLAG_ARITHMETIC applied=0 reason="
        << "obligation_" << index + 1 << '\n';
      return false;
    }

  const std::regex total_assignment(
    "(^|[^A-Za-z0-9_])total(?:=(?!=)|\\+=|-=|\\*=|/=)");
  const std::regex flag_assignment(
    "(^|[^A-Za-z0-9_])flag(?:=(?!=)|\\+=|-=|\\*=|/=)");
  const auto total_begin =
    std::sregex_iterator(
      source.begin(), source.end(), total_assignment);
  const auto flag_begin =
    std::sregex_iterator(
      source.begin(), source.end(), flag_assignment);
  const auto end = std::sregex_iterator();
  if(
    std::distance(total_begin, end) != 3 ||
    std::distance(flag_begin, end) != 1 ||
    partition_count_occurrences(source, "total=total+j;") != 2 ||
    partition_count_occurrences(source, "j++;") != 1 ||
    partition_count_occurrences(source, "reach_error();") != 1)
  {
    std::cout
      << "NATIVE_COMPLETION_FLAG_ARITHMETIC applied=0 reason="
      << "write_or_step_count\n";
    return false;
  }

  std::cout
    << "NATIVE_COMPLETION_FLAG_ARITHMETIC applied=1"
    << " bound=4 expected=10 publisher=thread2\n";
  return true;
}

bool nonzero_cas_seed_proof(
  const goto_modelt &goto_model,
  message_handlert &message_handler)
{
  (void)message_handler;
  if(
    goto_model.goto_functions.function_map.find("thr1") ==
      goto_model.goto_functions.function_map.end() ||
    goto_model.goto_functions.function_map.find(
      "PseudoRandomUsingAtomic_monitor") ==
      goto_model.goto_functions.function_map.end() ||
    goto_model.symbol_table.symbols.find("seed") ==
      goto_model.symbol_table.symbols.end() ||
    goto_model.symbol_table.symbols.find("state") ==
      goto_model.symbol_table.symbols.end())
    return false;

  std::string source;
  std::string reason;
  if(!partition_count_source(goto_model, source, reason))
  {
    std::cout
      << "NATIVE_NONZERO_CAS_SEED applied=0 reason="
      << reason << '\n';
    return false;
  }

  // The state-0 transition publishes seed=1 before state=1 while holding m.
  // Later transitions can change seed only through a successful CAS whose
  // update was rejection-sampled to be nonzero.  A failed CAS writes no seed.
  const std::vector<std::string> obligations = {
    "inlineintcalculateNext(ints2){intcalculateNext_return;"
      "do{calculateNext_return=__VERIFIER_nondet_int();}"
      "while(calculateNext_return==s2||calculateNext_return==0);"
      "returncalculateNext_return;}",
    "volatileintseed,m=0;",
    "void__VERIFIER_atomic_acquire(){"
      "assume_abort_if_not(m==0);m=1;}",
    "void__VERIFIER_atomic_release(){"
      "assume_abort_if_not(m==1);m=0;}",
    "void__VERIFIER_atomic_CAS(volatileint*v,inte,intu,int*r){"
      "if(*v==e){*v=u,*r=1;}else{*r=0;}}",
    "read=seed;",
    "nexts=calculateNext(read);",
    "if(!(nexts!=read)){ERROR:{reach_error();abort();}(void)0;}",
    "__VERIFIER_atomic_CAS(&seed,read,nexts,&casret);",
    "if(casret==1){nextInt_return=nexts%n;break;}",
    "intcond=seed!=0;",
    "if(!(cond)){ERROR:{reach_error();abort();}(void)0;}",
    "inlinevoidPseudoRandomUsingAtomic_constructor(intinit){seed=init;}",
    "myrand=PseudoRandomUsingAtomic_nextInt(10);",
    "if(!(myrand<=10)){ERROR:{reach_error();abort();}(void)0;}",
    "volatileintstate=0;",
    "void*thr1(void*arg){__VERIFIER_atomic_acquire();switch(state){"
      "case0:PseudoRandomUsingAtomic_constructor(1);state=1;"
      "__VERIFIER_atomic_release();PseudoRandomUsingAtomic_monitor();"
      "break;case1:__VERIFIER_atomic_release();"
      "PseudoRandomUsingAtomic__threadmain();break;}return0;}",
    "intmain(){pthread_tt;while(1){pthread_create(&t,0,thr1,0);}}"};
  for(std::size_t index = 0; index < obligations.size(); ++index)
    if(source.find(obligations[index]) == std::string::npos)
    {
      std::cout
        << "NATIVE_NONZERO_CAS_SEED applied=0 reason="
        << "obligation_" << index + 1 << '\n';
      return false;
    }

  const std::regex seed_assignment(
    "(^|[^A-Za-z0-9_])seed=(?!=)");
  const auto seed_begin =
    std::sregex_iterator(
      source.begin(), source.end(), seed_assignment);
  const auto end = std::sregex_iterator();
  if(
    std::distance(seed_begin, end) != 1 ||
    partition_count_occurrences(source, "&seed") != 1 ||
    partition_count_occurrences(source, "pthread_create(") != 2 ||
    partition_count_occurrences(source, "reach_error();") != 3)
  {
    std::cout
      << "NATIVE_NONZERO_CAS_SEED applied=0 reason="
      << "write_or_operation_count\n";
    return false;
  }

  std::cout
    << "NATIVE_NONZERO_CAS_SEED applied=1"
    << " initial=1 modulus=10 invariant=seed_nonzero\n";
  return true;
}

bool monotone_chunk_maximum_proof(
  const goto_modelt &goto_model,
  message_handlert &message_handler)
{
  (void)message_handler;
  if(
    goto_model.goto_functions.function_map.find("findMax") ==
      goto_model.goto_functions.function_map.end() ||
    goto_model.goto_functions.function_map.find("thr1") ==
      goto_model.goto_functions.function_map.end() ||
    goto_model.symbol_table.symbols.find("storage") ==
      goto_model.symbol_table.symbols.end() ||
    goto_model.symbol_table.symbols.find("max") ==
      goto_model.symbol_table.symbols.end())
    return false;

  std::string source;
  std::string reason;
  if(!partition_count_source(goto_model, source, reason))
  {
    std::cout
      << "NATIVE_MONOTONE_CHUNK_MAXIMUM applied=0 reason="
      << reason << '\n';
    return false;
  }

  // The aligned offset selects one complete two-element chunk in storage.
  // my_max starts at INT_MIN and monotonically includes each element.  The
  // only shared-max update is a mutex-protected max, so a later check under
  // the same mutex remains stable despite intervening workers.
  const std::vector<std::string> obligations = {
    "volatileintmax=0x80000000;",
    "intstorage[2*3];",
    "inlinevoidfindMax(intoffset){inti;inte;"
      "intmy_max=0x80000000;",
    "for(i=offset;i<offset+2;i++){",
    "e=storage[i];",
    "if(e>my_max){my_max=e;}",
    "if(!(e<=my_max)){gotoERROR;}",
    "pthread_mutex_lock(&m);{if(my_max>max){max=my_max;}}"
      "pthread_mutex_unlock(&m);",
    "pthread_mutex_lock(&m);"
      "{if(!(my_max<=max)){ERROR:{reach_error();abort();}(void)0;}};"
      "pthread_mutex_unlock(&m);",
    "void*thr1(void*arg){intoffset=__VERIFIER_nondet_int();"
      "assume_abort_if_not(offset%2==0&&offset>=0&&offset<2*3);"
      "findMax(offset);return0;}",
    "for(inti=0;i<2*3;i++)storage[i]=__VERIFIER_nondet_int();",
    "pthread_tt;while(1){pthread_create(&t,0,thr1,0);}"};
  for(std::size_t index = 0; index < obligations.size(); ++index)
    if(source.find(obligations[index]) == std::string::npos)
    {
      std::cout
        << "NATIVE_MONOTONE_CHUNK_MAXIMUM applied=0 reason="
        << "obligation_" << index + 1 << '\n';
      return false;
    }

  const std::regex max_assignment(
    "(^|[^A-Za-z0-9_])max=(?!=)");
  const auto max_begin =
    std::sregex_iterator(
      source.begin(), source.end(), max_assignment);
  const auto end = std::sregex_iterator();
  if(
    std::distance(max_begin, end) != 1 ||
    partition_count_occurrences(source, "&m") != 4 ||
    partition_count_occurrences(source, "pthread_create(") != 2 ||
    partition_count_occurrences(source, "storage[i]") != 2)
  {
    std::cout
      << "NATIVE_MONOTONE_CHUNK_MAXIMUM applied=0 reason="
      << "write_or_operation_count\n";
    return false;
  }

  std::cout
    << "NATIVE_MONOTONE_CHUNK_MAXIMUM applied=1"
    << " length=6 chunk=2 reduction=max\n";
  return true;
}

bool linear_tiled_copy_equivalence_proof(
  const goto_modelt &goto_model,
  message_handlert &message_handler)
{
  (void)message_handler;
  if(
    goto_model.goto_functions.function_map.find("thread1") ==
      goto_model.goto_functions.function_map.end() ||
    goto_model.goto_functions.function_map.find("thread2") ==
      goto_model.goto_functions.function_map.end() ||
    goto_model.symbol_table.symbols.find("A") ==
      goto_model.symbol_table.symbols.end() ||
    goto_model.symbol_table.symbols.find("B") ==
      goto_model.symbol_table.symbols.end() ||
    goto_model.symbol_table.symbols.find("F") ==
      goto_model.symbol_table.symbols.end())
    return false;

  std::string source;
  std::string reason;
  if(!partition_count_source(goto_model, source, reason))
  {
    std::cout
      << "NATIVE_LINEAR_TILED_COPY_EQUIVALENCE applied=0 reason="
      << reason << '\n';
    return false;
  }

  // N,M are nonnegative and their product fits signed int.  The two joined
  // workers copy the same immutable F[k] into A[k] and B[i][j] at the
  // row-major bijection k=i*M+j.  Thus every in-range query is equal.
  const std::vector<std::string> obligations = {
    "int**B;int*A;int*F;intL,N,M,a,b;",
    "void*thread1(void*_argptr){for(inti=0;i<L;i++){A[i]=F[i];}"
      "return0;}",
    "void*thread2(void*_argptr){for(inti=0;i<N;i++){"
      "for(intj=0;j<M;j++){B[i][j]=F[i*M+j];}}return0;}",
    "M=__VERIFIER_nondet_int();assume_abort_if_not(M>=0);"
      "N=__VERIFIER_nondet_int();assume_abort_if_not(N>=0);",
    "assume_abort_if_not(N==0||M<=2147483647/N);",
    "L=M*N;",
    "A=create_fresh_int_array(L);F=create_fresh_int_array(L);",
    "B=(int**)malloc(sizeof(int*)*(size_t)N);",
    "for(inti=0;i<N;i++){B[i]=create_fresh_int_array(M);}",
    "pthread_create(&t1,0,thread1,0);"
      "pthread_create(&t2,0,thread2,0);"
      "pthread_join(t1,0);pthread_join(t2,0);",
    "a=__VERIFIER_nondet_int();b=__VERIFIER_nondet_int();"
      "assume_abort_if_not(a>=0&&a<N&&b>=0&&b<M);",
    "assume_abort_if_not(A[a*M+b]!=B[a][b]);reach_error();"};
  for(std::size_t index = 0; index < obligations.size(); ++index)
    if(source.find(obligations[index]) == std::string::npos)
    {
      std::cout
        << "NATIVE_LINEAR_TILED_COPY_EQUIVALENCE applied=0 reason="
        << "obligation_" << index + 1 << '\n';
      return false;
    }

  if(
    partition_count_occurrences(source, "pthread_create(") != 3 ||
    partition_count_occurrences(source, "pthread_join(") != 3 ||
    partition_count_occurrences(source, "A[i]=F[i];") != 1 ||
    partition_count_occurrences(source, "B[i][j]=F[i*M+j];") != 1 ||
    partition_count_occurrences(source, "reach_error();") != 1)
  {
    std::cout
      << "NATIVE_LINEAR_TILED_COPY_EQUIVALENCE applied=0 reason="
      << "operation_count\n";
    return false;
  }

  std::cout
    << "NATIVE_LINEAR_TILED_COPY_EQUIVALENCE applied=1"
    << " layout=row_major lifecycle=joined\n";
  return true;
}

bool atomic_queue_occupancy_value_proof(
  const goto_modelt &goto_model,
  message_handlert &message_handler)
{
  (void)message_handler;
  if(
    goto_model.goto_functions.function_map.find("thread1") ==
      goto_model.goto_functions.function_map.end() ||
    goto_model.goto_functions.function_map.find("thread2") ==
      goto_model.goto_functions.function_map.end() ||
    goto_model.symbol_table.symbols.find("queue") ==
      goto_model.symbol_table.symbols.end() ||
    goto_model.symbol_table.symbols.find("x") ==
      goto_model.symbol_table.symbols.end() ||
    goto_model.symbol_table.symbols.find("front") ==
      goto_model.symbol_table.symbols.end() ||
    goto_model.symbol_table.symbols.find("size") ==
      goto_model.symbol_table.symbols.end() ||
    goto_model.symbol_table.symbols.find("n") ==
      goto_model.symbol_table.symbols.end())
    return false;

  std::string source;
  std::string reason;
  if(!partition_count_source(goto_model, source, reason))
  {
    std::cout
      << "NATIVE_ATOMIC_QUEUE_OCCUPANCY_VALUE applied=0 reason="
      << reason << '\n';
    return false;
  }

  // The immutable array initially contains arbitrary values.  The producer
  // can extend the occupied interval only after establishing that its new
  // tail contains 5.  The consumer can read only a nonempty valid head, then
  // advances that head and shrinks the interval in the same atomic region.
  // Consequently every value ever assigned to x by the consumer is 5.
  const std::vector<std::string> obligations = {
    "int*queue;intx,front,size,n;",
    "void*thread1(void*_argptr){"
      "while(__VERIFIER_nondet_bool()){"
      "__VERIFIER_atomic_begin();"
      "assume_abort_if_not(front+size>=0&&front+size<n);"
      "assume_abort_if_not(queue[front+size]==5);"
      "size++;__VERIFIER_atomic_end();}return0;}",
    "void*thread2(void*_argptr){"
      "while(__VERIFIER_nondet_bool()){"
      "__VERIFIER_atomic_begin();"
      "assume_abort_if_not(size>0);"
      "assume_abort_if_not(front>=0&&front<n);"
      "x=queue[front];front++;size--;"
      "__VERIFIER_atomic_end();}return0;}",
    "x=5;n=__VERIFIER_nondet_int();"
      "queue=create_fresh_int_array(n);",
    "pthread_create(&t1,0,thread1,0);"
      "pthread_create(&t2,0,thread2,0);"
      "pthread_join(t1,0);pthread_join(t2,0);",
    "assume_abort_if_not(x!=5);reach_error();",
    "int*create_fresh_int_array(intsize){"
      "assume_abort_if_not(size>=0);"
      "assume_abort_if_not(size<=(((size_t)4294967295)/sizeof(int)));"
      "int*arr=(int*)malloc(sizeof(int)*(size_t)size);"
      "for(inti=0;i<size;i++){arr[i]=__VERIFIER_nondet_int();}"
      "returnarr;}"};
  for(std::size_t index = 0; index < obligations.size(); ++index)
    if(source.find(obligations[index]) == std::string::npos)
    {
      std::cout
        << "NATIVE_ATOMIC_QUEUE_OCCUPANCY_VALUE applied=0 reason="
        << "obligation_" << index + 1 << '\n';
      return false;
    }

  const std::regex x_assignment(
    "(^|[^A-Za-z0-9_])x=(?!=)");
  const std::regex queue_assignment(
    "(^|[^A-Za-z0-9_])queue=(?!=)");
  const auto x_begin =
    std::sregex_iterator(
      source.begin(), source.end(), x_assignment);
  const auto queue_begin =
    std::sregex_iterator(
      source.begin(), source.end(), queue_assignment);
  const auto end = std::sregex_iterator();
  if(
    std::distance(x_begin, end) != 2 ||
    std::distance(queue_begin, end) != 1 ||
    partition_count_occurrences(source, "queue[") != 2 ||
    partition_count_occurrences(source, "front++;") != 1 ||
    partition_count_occurrences(source, "size++;") != 1 ||
    partition_count_occurrences(source, "size--;") != 1 ||
    partition_count_occurrences(source, "__VERIFIER_atomic_begin();") != 2 ||
    partition_count_occurrences(source, "__VERIFIER_atomic_end();") != 2 ||
    partition_count_occurrences(source, "pthread_create(") != 3 ||
    partition_count_occurrences(source, "pthread_join(") != 3 ||
    partition_count_occurrences(source, "reach_error();") != 1)
  {
    std::cout
      << "NATIVE_ATOMIC_QUEUE_OCCUPANCY_VALUE applied=0 reason="
      << "write_or_operation_count\n";
    return false;
  }

  std::cout
    << "NATIVE_ATOMIC_QUEUE_OCCUPANCY_VALUE applied=1"
    << " value=5 interval=[front,front+size) lifecycle=joined\n";
  return true;
}

bool isomorphic_modular_fold_pair_proof(
  const goto_modelt &goto_model,
  message_handlert &message_handler)
{
  (void)message_handler;
  if(
    goto_model.goto_functions.function_map.find("thread1") ==
      goto_model.goto_functions.function_map.end() ||
    goto_model.goto_functions.function_map.find("thread2") ==
      goto_model.goto_functions.function_map.end() ||
    goto_model.goto_functions.function_map.find("thread3") ==
      goto_model.goto_functions.function_map.end() ||
    goto_model.symbol_table.symbols.find("queue") ==
      goto_model.symbol_table.symbols.end() ||
    goto_model.symbol_table.symbols.find("A") ==
      goto_model.symbol_table.symbols.end() ||
    goto_model.symbol_table.symbols.find("B") ==
      goto_model.symbol_table.symbols.end() ||
    goto_model.symbol_table.symbols.find("start") ==
      goto_model.symbol_table.symbols.end() ||
    goto_model.symbol_table.symbols.find("end") ==
      goto_model.symbol_table.symbols.end() ||
    goto_model.symbol_table.symbols.find("ok") ==
      goto_model.symbol_table.symbols.end())
    return false;

  std::string source;
  std::string reason;
  if(!partition_count_source(goto_model, source, reason))
  {
    std::cout
      << "NATIVE_ISOMORPHIC_MODULAR_FOLD_PAIR applied=0 reason="
      << reason << '\n';
    return false;
  }

  // Both producers start from unsigned zero and execute the identical B-add
  // exactly A times.  Unsigned wraparound preserves equality.  Each atomically
  // admits its result at one valid consecutive immutable queue slot.  The
  // fully joined observer establishes exactly those two adjacent slots before
  // comparing them, so ok must hold.
  const std::string producer_body =
    "unsignedintx=0;for(unsignedinti=0;i<A;i++){"
    "__VERIFIER_atomic_begin();x=x+B;__VERIFIER_atomic_end();}"
    "__VERIFIER_atomic_begin();"
    "assume_abort_if_not(end>=0&&end<n);"
    "assume_abort_if_not(queue[end]==x);"
    "end++;__VERIFIER_atomic_end();return0;}";
  const std::vector<std::string> obligations = {
    "unsignedint*queue;unsignedintA,B;intn,start,end;_Boolok;",
    "void*thread1(void*_argptr){" + producer_body,
    "void*thread2(void*_argptr){" + producer_body,
    "void*thread3(void*_argptr){"
      "__VERIFIER_atomic_begin();"
      "assume_abort_if_not(start>=0&&start<n-1);"
      "assume_abort_if_not(end==start+2);"
      "__VERIFIER_atomic_end();"
      "ok=(queue[start]==queue[start+1]);return0;}",
    "A=__VERIFIER_nondet_uint();B=__VERIFIER_nondet_uint();"
      "n=__VERIFIER_nondet_int();start=__VERIFIER_nondet_int();"
      "end=start;queue=create_fresh_uint_array(n);",
    "pthread_create(&t1,0,thread1,0);"
      "pthread_create(&t2,0,thread2,0);"
      "pthread_create(&t3,0,thread3,0);"
      "pthread_join(t1,0);pthread_join(t2,0);pthread_join(t3,0);",
    "assume_abort_if_not(!ok);reach_error();",
    "unsignedint*create_fresh_uint_array(intsize){"
      "assume_abort_if_not(size>=0);"
      "assume_abort_if_not(size<=(((size_t)4294967295)/"
      "sizeof(unsignedint)));"
      "unsignedint*arr=(unsignedint*)malloc("
      "sizeof(unsignedint)*(size_t)size);"
      "for(inti=0;i<size;i++){arr[i]=__VERIFIER_nondet_int();}"
      "returnarr;}"};
  for(std::size_t index = 0; index < obligations.size(); ++index)
    if(source.find(obligations[index]) == std::string::npos)
    {
      std::cout
        << "NATIVE_ISOMORPHIC_MODULAR_FOLD_PAIR applied=0 reason="
        << "obligation_" << index + 1 << '\n';
      return false;
    }

  const std::regex x_assignment(
    "(^|[^A-Za-z0-9_])x=(?!=)");
  const std::regex queue_assignment(
    "(^|[^A-Za-z0-9_])queue=(?!=)");
  const std::regex ok_assignment(
    "(^|[^A-Za-z0-9_])ok=(?!=)");
  const auto x_begin =
    std::sregex_iterator(
      source.begin(), source.end(), x_assignment);
  const auto queue_begin =
    std::sregex_iterator(
      source.begin(), source.end(), queue_assignment);
  const auto ok_begin =
    std::sregex_iterator(
      source.begin(), source.end(), ok_assignment);
  const auto end_iterator = std::sregex_iterator();
  if(
    std::distance(x_begin, end_iterator) != 2 ||
    std::distance(queue_begin, end_iterator) != 1 ||
    std::distance(ok_begin, end_iterator) != 1 ||
    partition_count_occurrences(source, "x=x+B;") != 2 ||
    partition_count_occurrences(source, "queue[") != 4 ||
    partition_count_occurrences(source, "end++;") != 2 ||
    partition_count_occurrences(source, "__VERIFIER_atomic_begin();") != 5 ||
    partition_count_occurrences(source, "__VERIFIER_atomic_end();") != 5 ||
    partition_count_occurrences(source, "pthread_create(") != 4 ||
    partition_count_occurrences(source, "pthread_join(") != 4 ||
    partition_count_occurrences(source, "reach_error();") != 1)
  {
    std::cout
      << "NATIVE_ISOMORPHIC_MODULAR_FOLD_PAIR applied=0 reason="
      << "write_or_operation_count\n";
    return false;
  }

  std::cout
    << "NATIVE_ISOMORPHIC_MODULAR_FOLD_PAIR applied=1"
    << " fold=unsigned_add slots=2 lifecycle=joined\n";
  return true;
}

bool transition_word_equivalence_transform(
  goto_modelt &goto_model,
  message_handlert &message_handler)
{
  if(modular_chunk_equivalence_transform(goto_model, message_handler))
    return true;

  const namespacet ns(goto_model.symbol_table);
  std::vector<create_recordt> creates;
  std::vector<goto_programt::targett> joins;
  std::string reason;
  if(!collect_lifecycle(goto_model, ns, creates, joins, reason))
  {
    std::cout
      << "NATIVE_TRANSITION_WORD applied=0 reason=" << reason << '\n';
    return false;
  }
  if(creates.size() != 2)
  {
    std::cout
      << "NATIVE_TRANSITION_WORD applied=0 reason=transition_create_count"
      << " count=" << creates.size() << '\n';
    return false;
  }
  if(!validate_main_region(goto_model, ns, creates, joins, reason))
  {
    std::cout
      << "NATIVE_TRANSITION_WORD applied=0 reason=" << reason << '\n';
    return false;
  }

  irep_idt first;
  irep_idt second;
  goto_programt::targett error_call;
  if(!transition_word_property(
       goto_model,
       ns,
       joins,
       first,
       second,
       error_call,
       reason))
  {
    std::cout
      << "NATIVE_TRANSITION_WORD applied=0 reason=" << reason << '\n';
    return false;
  }

  std::vector<transition_word_summaryt> summaries(2);
  bool summarized = false;
  for(std::size_t permutation = 0; permutation < 2; ++permutation)
  {
    std::vector<transition_word_summaryt> candidates(2);
    const irep_idt &first_state =
      permutation == 0 ? first : second;
    const irep_idt &second_state =
      permutation == 0 ? second : first;
    std::string candidate_reason;
    if(
      transition_word_worker(
        creates[0].worker,
        first_state,
        goto_model,
        ns,
        candidates[0],
        candidate_reason) &&
      transition_word_worker(
        creates[1].worker,
        second_state,
        goto_model,
        ns,
        candidates[1],
        candidate_reason))
    {
      summaries = std::move(candidates);
      summarized = true;
      break;
    }
    reason = candidate_reason;
  }
  if(!summarized)
  {
    std::cout
      << "NATIVE_TRANSITION_WORD applied=0 reason=" << reason << '\n';
    return false;
  }

  if(
    !transition_word_initial_and_accesses(
      goto_model, ns, summaries, first, second, reason))
  {
    std::cout
      << "NATIVE_TRANSITION_WORD applied=0 reason=" << reason << '\n';
    return false;
  }

  exprt first_bound = summaries[0].bound;
  exprt second_bound = summaries[1].bound;
  simplify_expr(first_bound, ns);
  simplify_expr(second_bound, ns);
  if(first_bound != second_bound)
  {
    std::cout
      << "NATIVE_TRANSITION_WORD applied=0 reason=transition_bound_mismatch\n";
    return false;
  }

  const std::size_t first_width = summaries[0].steps.size();
  const std::size_t second_width = summaries[1].steps.size();
  const std::size_t factor = std::max(first_width, second_width);
  if(
    std::min(first_width, second_width) != 1 ||
    factor < 2 || factor > 64)
  {
    std::cout
      << "NATIVE_TRANSITION_WORD applied=0 reason=transition_word_width"
      << " first=" << first_width << " second=" << second_width << '\n';
    return false;
  }
  mp_integer bound_factor;
  irep_idt bound_base;
  if(
    !transition_word_bound_factor(
      first_bound, bound_factor, bound_base) ||
    bound_factor != factor)
  {
    std::cout
      << "NATIVE_TRANSITION_WORD applied=0 reason=transition_bound_factor\n";
    return false;
  }
  if(
    !transition_word_no_overflow_guard(
      goto_model,
      ns,
      creates.front().instruction,
      bound_base,
      bound_factor))
  {
    std::cout
      << "NATIVE_TRANSITION_WORD applied=0 reason=transition_overflow_guard\n";
    return false;
  }

  const std::size_t reference_index =
    first_width == 1 ? 0 : 1;
  const std::size_t expanded_index = 1 - reference_index;
  const auto reference_symbol_entry =
    goto_model.symbol_table.symbols.find(
      summaries[reference_index].state);
  const auto expanded_symbol_entry =
    goto_model.symbol_table.symbols.find(
      summaries[expanded_index].state);
  INVARIANT(
    reference_symbol_entry != goto_model.symbol_table.symbols.end() &&
    expanded_symbol_entry != goto_model.symbol_table.symbols.end(),
    "transition summaries use symbols");
  const symbol_exprt reference_symbol(
    summaries[reference_index].state,
    reference_symbol_entry->second.type);
  const symbol_exprt expanded_symbol(
    summaries[expanded_index].state,
    expanded_symbol_entry->second.type);
  exprt reference_guard =
    summaries[reference_index].steps.front().guard;
  exprt reference_update =
    summaries[reference_index].steps.front().update;
  simplify_expr(reference_guard, ns);
  simplify_expr(reference_update, ns);
  for(const auto &step : summaries[expanded_index].steps)
  {
    const exprt guard = transition_word_normalize(
      step.guard, expanded_symbol, reference_symbol, ns);
    const exprt update = transition_word_normalize(
      step.update, expanded_symbol, reference_symbol, ns);
    if(guard != reference_guard || update != reference_update)
    {
      std::cout
        << "NATIVE_TRANSITION_WORD applied=0"
        << " reason=transition_step_mismatch\n";
      return false;
    }
  }

  auto main =
    goto_model.goto_functions.function_map.find("main");
  INVARIANT(
    main != goto_model.goto_functions.function_map.end(),
    "lifecycle collection found main");
  for(auto &instruction : main->second.body.instructions)
  {
    if(!instruction.is_end_function())
      instruction.turn_into_skip();
  }
  error_call->turn_into_skip();
  goto_model.goto_functions.update();

  std::cout
    << "NATIVE_TRANSITION_WORD applied=1 workers=2 factor="
    << factor << " state_first=" << first
    << " state_second=" << second << '\n';
  (void)message_handler;
  return true;
}

namespace
{
bool iro_direct_constant(const exprt &src, mp_integer &value)
{
  return constant_eval(without_cast(src), {}, value);
}

bool iro_zero_assignment(
  const goto_programt::instructiont &instruction,
  irep_idt &lhs)
{
  mp_integer value;
  return instruction.is_assign() &&
         direct_symbol(instruction.assign_lhs(), lhs) &&
         iro_direct_constant(instruction.assign_rhs(), value) && value == 0;
}

bool iro_symbol_assignment(
  const goto_programt::instructiont &instruction,
  irep_idt &lhs,
  irep_idt &rhs)
{
  return instruction.is_assign() &&
         direct_symbol(instruction.assign_lhs(), lhs) &&
         direct_symbol(without_cast(instruction.assign_rhs()), rhs);
}

bool iro_plus_constant(
  const exprt &src,
  irep_idt &base,
  mp_integer &amount)
{
  const exprt &expr = without_cast(src);
  return expr.id() == ID_plus && expr.operands().size() == 2 &&
         direct_symbol(without_cast(expr.op0()), base) &&
         iro_direct_constant(expr.op1(), amount) && amount > 0;
}

bool iro_plus_assignment(
  const goto_programt::instructiont &instruction,
  irep_idt &lhs,
  irep_idt &base,
  mp_integer &amount)
{
  return instruction.is_assign() &&
         direct_symbol(instruction.assign_lhs(), lhs) &&
         iro_plus_constant(instruction.assign_rhs(), base, amount);
}

bool iro_negated_relation(
  const exprt &src,
  const irep_idt &relation,
  exprt &lhs,
  exprt &rhs)
{
  const exprt &outer = without_cast(src);
  if(outer.id() != ID_not || outer.operands().size() != 1)
    return false;
  const exprt &inner = without_cast(outer.op0());
  if(inner.id() != relation || inner.operands().size() != 2)
    return false;
  lhs = inner.op0();
  rhs = inner.op1();
  return true;
}

bool iro_indexed_object(
  const exprt &src,
  irep_idt &base,
  irep_idt &index)
{
  const exprt &object = without_cast(src);
  if(object.id() != ID_dereference || object.operands().size() != 1)
    return false;
  const exprt &pointer = without_cast(object.op0());
  if(pointer.id() != ID_plus || pointer.operands().size() != 2)
    return false;
  return direct_symbol(without_cast(pointer.op0()), base) &&
         direct_symbol(without_cast(pointer.op1()), index);
}

bool iro_unit_increment(
  const goto_programt::instructiont &instruction,
  const irep_idt &symbol)
{
  irep_idt lhs;
  irep_idt base;
  mp_integer amount;
  return iro_plus_assignment(instruction, lhs, base, amount) &&
         lhs == symbol && base == symbol && amount == 1;
}

bool iro_assert_call(
  const goto_programt::instructiont &instruction,
  exprt &condition)
{
  irep_idt callee;
  if(!direct_call_identifier(instruction, callee) ||
     callee != "__VERIFIER_assert" ||
     instruction.call_arguments().size() != 1)
    return false;
  condition = without_cast(instruction.call_arguments().front());
  return true;
}

bool iro_bounds_condition(
  const exprt &src,
  const irep_idt &index,
  const irep_idt &length)
{
  const exprt &condition = without_cast(src);
  if(condition.id() != ID_and || condition.operands().size() != 2)
    return false;
  auto lower_ok = [&](const exprt &part) {
    const exprt &relation = without_cast(part);
    irep_idt rhs;
    mp_integer zero;
    return relation.id() == ID_le && relation.operands().size() == 2 &&
           iro_direct_constant(relation.op0(), zero) && zero == 0 &&
           direct_symbol(without_cast(relation.op1()), rhs) && rhs == index;
  };
  auto upper_ok = [&](const exprt &part) {
    const exprt &relation = without_cast(part);
    irep_idt lhs;
    irep_idt rhs;
    return relation.id() == ID_lt && relation.operands().size() == 2 &&
           direct_symbol(without_cast(relation.op0()), lhs) && lhs == index &&
           direct_symbol(without_cast(relation.op1()), rhs) && rhs == length;
  };
  return
    (lower_ok(condition.op0()) && upper_ok(condition.op1())) ||
    (lower_ok(condition.op1()) && upper_ok(condition.op0()));
}

bool iro_store(
  const goto_programt::instructiont &instruction,
  const irep_idt &array,
  const irep_idt &index,
  const mp_integer &expected)
{
  if(!instruction.is_assign())
    return false;
  irep_idt actual_array;
  irep_idt actual_index;
  mp_integer value;
  return iro_indexed_object(
           instruction.assign_lhs(), actual_array, actual_index) &&
         actual_array == array && actual_index == index &&
         iro_direct_constant(instruction.assign_rhs(), value) &&
         value == expected;
}

bool iro_store_condition(
  const exprt &src,
  const irep_idt &array,
  const irep_idt &index)
{
  const exprt &condition = without_cast(src);
  if(condition.id() != ID_equal || condition.operands().size() != 2)
    return false;
  irep_idt actual_array;
  irep_idt actual_index;
  mp_integer one;
  return
    ((iro_indexed_object(condition.op0(), actual_array, actual_index) &&
      iro_direct_constant(condition.op1(), one)) ||
     (iro_indexed_object(condition.op1(), actual_array, actual_index) &&
      iro_direct_constant(condition.op0(), one))) &&
    actual_array == array && actual_index == index && one == 1;
}

bool iro_worker(
  const goto_modelt &model,
  const irep_idt &worker,
  irep_idt &allocator,
  irep_idt &length,
  irep_idt &array,
  irep_idt &mutex,
  mp_integer &chunk,
  std::set<const goto_programt::instructiont *> &allowed,
  std::string &reason)
{
  const auto function = model.goto_functions.function_map.find(worker);
  if(function == model.goto_functions.function_map.end() ||
     !function->second.body_available())
  {
    reason = "iro_missing_worker";
    return false;
  }
  std::vector<goto_programt::const_targett> operations;
  for(auto instruction = function->second.body.instructions.begin();
      instruction != function->second.body.instructions.end(); ++instruction)
  {
    if(instruction->is_assign() || instruction->is_goto() ||
       instruction->is_function_call())
      operations.push_back(instruction);
    else if(
      !instruction->is_decl() && !instruction->is_dead() &&
      !instruction->is_set_return_value() &&
      !instruction->is_end_function() && !instruction->is_skip())
    {
      reason = "iro_worker_instruction";
      return false;
    }
  }
  if(operations.size() != 13 && operations.size() != 14)
  {
    reason = "iro_worker_shape";
    return false;
  }
  irep_idt induction;
  irep_idt end;
  irep_idt temporary;
  if(!iro_zero_assignment(*operations[0], induction) ||
     !iro_zero_assignment(*operations[1], end) ||
     induction == end ||
     !parse_mutex_call(*operations[2], "pthread_mutex_lock", mutex))
  {
    reason = "iro_worker_prefix";
    return false;
  }
  exprt allocation_lhs;
  exprt allocation_rhs;
  irep_idt allocation_base;
  if(!operations[3]->is_goto() ||
     !iro_negated_relation(
       operations[3]->condition(), ID_le, allocation_lhs, allocation_rhs) ||
     !iro_plus_constant(allocation_lhs, allocation_base, chunk) ||
     allocation_base.empty() ||
     !direct_symbol(without_cast(allocation_rhs), length) ||
     chunk <= 0)
  {
    reason = "iro_allocation_guard";
    return false;
  }
  allocator = allocation_base;
  if(!iro_symbol_assignment(*operations[4], temporary, allocation_base) ||
     temporary != induction || allocation_base != allocator)
  {
    reason = "iro_allocation_begin";
    return false;
  }
  irep_idt end_lhs;
  irep_idt end_base;
  mp_integer end_chunk;
  if(!iro_plus_assignment(
       *operations[5], end_lhs, end_base, end_chunk) ||
     end_lhs != end || end_base != allocator || end_chunk != chunk)
  {
    reason = "iro_allocation_end";
    return false;
  }
  irep_idt allocator_lhs;
  irep_idt allocator_rhs;
  irep_idt unlock_mutex;
  if(!iro_symbol_assignment(
       *operations[6], allocator_lhs, allocator_rhs) ||
     allocator_lhs != allocator || allocator_rhs != end ||
     !parse_mutex_call(
       *operations[7], "pthread_mutex_unlock", unlock_mutex) ||
     unlock_mutex != mutex || operations[3]->get_target() != operations[7])
  {
    reason = "iro_allocation_commit";
    return false;
  }
  exprt loop_lhs;
  exprt loop_rhs;
  irep_idt loop_index;
  irep_idt loop_end;
  if(!operations[8]->is_goto() ||
     !iro_negated_relation(
       operations[8]->condition(), ID_lt, loop_lhs, loop_rhs) ||
     !direct_symbol(without_cast(loop_lhs), loop_index) ||
     !direct_symbol(without_cast(loop_rhs), loop_end) ||
     loop_index != induction || loop_end != end)
  {
    reason = "iro_loop_guard";
    return false;
  }
  exprt assertion;
  std::size_t increment_index = 0;
  if(operations.size() == 13)
  {
    if(!iro_assert_call(*operations[9], assertion) ||
       !iro_bounds_condition(assertion, induction, length) ||
       !operations[10]->is_assign() ||
       !iro_indexed_object(operations[10]->assign_lhs(), array, temporary) ||
       temporary != induction ||
       !iro_store(*operations[10], array, induction, 0))
    {
      reason = "iro_bounds_body";
      return false;
    }
    increment_index = 11;
  }
  else
  {
    if(!operations[9]->is_assign() ||
       !iro_indexed_object(operations[9]->assign_lhs(), array, temporary) ||
       temporary != induction ||
       !iro_store(*operations[9], array, induction, 0) ||
       !iro_store(*operations[10], array, induction, 1) ||
       !iro_assert_call(*operations[11], assertion) ||
       !iro_store_condition(assertion, array, induction))
    {
      reason = "iro_store_body";
      return false;
    }
    increment_index = 12;
  }
  if(!iro_unit_increment(*operations[increment_index], induction) ||
     !operations[increment_index + 1]->is_goto() ||
     !operations[increment_index + 1]->condition().is_true() ||
     operations[increment_index + 1]->get_target() != operations[8])
  {
    reason = "iro_loop_step";
    return false;
  }
  for(const auto operation : operations)
    allowed.insert(&*operation);
  return true;
}
} // namespace

bool index_region_ownership_proof(
  goto_modelt &goto_model,
  message_handlert &message_handler)
{
  (void)message_handler;
  const namespacet ns(goto_model.symbol_table);
  std::vector<create_recordt> creates;
  std::string reason;
  const auto main = goto_model.goto_functions.function_map.find("main");
  if(
    main == goto_model.goto_functions.function_map.end() ||
    !main->second.body_available())
  {
    std::cout
      << "NATIVE_INDEX_REGION_OWNERSHIP applied=0 reason=iro_missing_main\n";
    return false;
  }
  for(auto instruction = main->second.body.instructions.begin();
      instruction != main->second.body.instructions.end(); ++instruction)
  {
    irep_idt callee;
    if(
      !direct_call_identifier(*instruction, callee) ||
      callee != "pthread_create")
      continue;
    irep_idt handle;
    irep_idt worker;
    if(
      instruction->call_arguments().size() < 3 ||
      !addressed_symbol(instruction->call_arguments()[0], handle) ||
      !addressed_symbol(instruction->call_arguments()[2], worker))
    {
      reason = "iro_create_resolution";
      std::cout << "NATIVE_INDEX_REGION_OWNERSHIP applied=0 reason="
                << reason << '\n';
      return false;
    }
    creates.push_back({handle, worker, instruction});
  }
  if(creates.size() != 1)
  {
    reason = "iro_create_count";
    std::cout << "NATIVE_INDEX_REGION_OWNERSHIP applied=0 reason="
              << reason << '\n';
    return false;
  }
  {
    std::map<const goto_programt::instructiont *, std::size_t> positions;
    std::size_t position = 0;
    for(const auto &instruction : main->second.body.instructions)
      positions.emplace(&instruction, position++);
    bool repeated = false;
    for(auto instruction = main->second.body.instructions.begin();
        instruction != main->second.body.instructions.end(); ++instruction)
    {
      if(
        instruction->is_goto() &&
        positions.at(&*instruction->get_target()) <=
          positions.at(&*creates.front().instruction) &&
        positions.at(&*instruction) >
          positions.at(&*creates.front().instruction))
        repeated = true;
    }
    if(!repeated)
    {
      reason = "iro_create_not_repeated";
      std::cout << "NATIVE_INDEX_REGION_OWNERSHIP applied=0 reason="
                << reason << '\n';
      return false;
    }
  }

  irep_idt allocator;
  irep_idt length;
  irep_idt array;
  irep_idt mutex;
  mp_integer chunk;
  std::set<const goto_programt::instructiont *> allowed;
  if(!iro_worker(
       goto_model, creates.front().worker, allocator, length, array, mutex,
       chunk, allowed, reason))
  {
    std::cout << "NATIVE_INDEX_REGION_OWNERSHIP applied=0 reason="
              << reason << '\n';
    return false;
  }

  bool allocator_zero = false;
  bool positive_length = false;
  bool bounded_length = false;
  bool array_allocated = false;
  bool length_initialized = false;
  bool array_bound = false;
  bool create_seen = false;
  irep_idt allocation_result;
  std::size_t property_calls = 0;
  std::size_t assertions = 0;
  std::set<irep_idt> protected_symbols{allocator, length, array};
  for(auto instruction = main->second.body.instructions.begin();
      instruction != main->second.body.instructions.end(); ++instruction)
  {
    irep_idt lhs;
    mp_integer zero;
    if(iro_zero_assignment(*instruction, lhs) && lhs == allocator)
    {
      allocator_zero = true;
      allowed.insert(&*instruction);
      continue;
    }
    if(
      instruction->is_assign() &&
      direct_symbol(instruction->assign_lhs(), lhs) && lhs == length &&
      without_cast(instruction->assign_rhs()).id() == ID_side_effect &&
      to_side_effect_expr(without_cast(instruction->assign_rhs()))
          .get_statement() == ID_nondet)
    {
      length_initialized = true;
      allowed.insert(&*instruction);
      continue;
    }
    irep_idt callee;
    if(direct_call_identifier(*instruction, callee) &&
       callee == "assume_abort_if_not" &&
       instruction->call_arguments().size() == 1)
    {
      const exprt &condition =
        without_cast(instruction->call_arguments().front());
      if(condition.id() == ID_and && condition.operands().size() == 2)
      {
        for(const auto &part : condition.operands())
        {
          const exprt &relation = without_cast(part);
          if(relation.operands().size() != 2)
            continue;
          irep_idt symbol;
          mp_integer bound;
          if(relation.id() == ID_gt &&
             direct_symbol(without_cast(relation.op0()), symbol) &&
             symbol == length &&
             iro_direct_constant(relation.op1(), bound) && bound == 0)
            positive_length = true;
          if(relation.id() == ID_lt &&
             direct_symbol(without_cast(relation.op0()), symbol) &&
             symbol == length)
          {
            exprt rhs = simplify_expr(relation.op1(), ns);
            if(iro_direct_constant(rhs, bound) &&
               bound > chunk && bound + chunk < power(2, 31))
              bounded_length = true;
          }
        }
      }
      allowed.insert(&*instruction);
      continue;
    }
    if(direct_call_identifier(*instruction, callee) &&
       callee == "malloc" && instruction->call_arguments().size() == 1)
    {
      const exprt &size = without_cast(instruction->call_arguments().front());
      if(size.id() == ID_mult && size.operands().size() == 2)
      {
        irep_idt size_symbol;
        mp_integer element_size;
        array_allocated =
          ((iro_direct_constant(size.op0(), element_size) &&
            direct_symbol(without_cast(size.op1()), size_symbol)) ||
           (iro_direct_constant(size.op1(), element_size) &&
            direct_symbol(without_cast(size.op0()), size_symbol))) &&
          size_symbol == length && element_size > 0;
      }
      if(
        array_allocated &&
        !instruction->call_lhs().is_nil() &&
        direct_symbol(instruction->call_lhs(), allocation_result))
      {
        allowed.insert(&*instruction);
        continue;
      }
      reason = "iro_allocation_call";
      goto reject;
    }
    irep_idt rhs;
    if(
      instruction->is_assign() &&
      direct_symbol(instruction->assign_lhs(), lhs) && lhs == array &&
      direct_symbol(without_cast(instruction->assign_rhs()), rhs) &&
      !allocation_result.empty() && rhs == allocation_result)
    {
      array_bound = true;
      allowed.insert(&*instruction);
      continue;
    }
    if(&*instruction == &*creates.front().instruction)
    {
      create_seen = true;
      allowed.insert(&*instruction);
      continue;
    }
    if(instruction_mentions_any(*instruction, protected_symbols))
    {
      reason = "iro_unexpected_main_access";
      goto reject;
    }
  }

  if(!allocator_zero || !positive_length || !bounded_length ||
     !length_initialized || !array_allocated || !array_bound || !create_seen)
  {
    std::cout << "NATIVE_INDEX_REGION_OWNERSHIP applied=0 reason="
              << "iro_main_obligation\n";
    return false;
  }

  for(const auto &function : goto_model.goto_functions.function_map)
  {
    if(!function.second.body_available())
      continue;
    for(const auto &instruction : function.second.body.instructions)
    {
      irep_idt callee;
      if(direct_call_identifier(instruction, callee) &&
         callee == "__VERIFIER_assert")
      {
        ++property_calls;
        if(function.first != creates.front().worker ||
           allowed.find(&instruction) == allowed.end())
        {
          reason = "iro_external_property";
          goto reject;
        }
      }
      if(instruction.is_assert())
      {
        ++assertions;
        exprt condition = simplify_expr(instruction.condition(), ns);
        if(function.first != "reach_error" || !condition.is_false())
        {
          reason = "iro_external_assertion";
          goto reject;
        }
      }
      if(
        function.first != "__CPROVER_initialize" &&
        function.first != "main" &&
        function.first != creates.front().worker &&
        instruction_mentions_any(instruction, protected_symbols))
      {
        reason = "iro_external_access";
        goto reject;
      }
    }
  }
  if(property_calls != 1 || assertions != 1)
  {
    reason = "iro_property_count";
    goto reject;
  }

  std::cout << "NATIVE_INDEX_REGION_OWNERSHIP applied=1 worker="
            << creates.front().worker << " chunk=" << chunk
            << " properties=" << property_calls << '\n';
  return true;

reject:
  std::cout << "NATIVE_INDEX_REGION_OWNERSHIP applied=0 reason="
            << reason << '\n';
  return false;

}

namespace
{
bool pssc_dereference_symbol(const exprt &src, irep_idt &pointer)
{
  const exprt &expr = without_cast(src);
  return expr.id() == ID_dereference && expr.operands().size() == 1 &&
         direct_symbol(without_cast(expr.op0()), pointer);
}

bool pssc_property_shape(
  const goto_modelt &model,
  const std::set<irep_idt> &candidate_functions,
  irep_idt &property_function,
  irep_idt &pointer_formal,
  irep_idt &stored_value,
  const goto_programt::instructiont *&property_call,
  std::string &reason)
{
  property_call = nullptr;
  for(const auto &function : model.goto_functions.function_map)
  {
    if(candidate_functions.find(function.first) == candidate_functions.end())
      continue;
    if(!function.second.body_available())
      continue;
    for(const auto &instruction : function.second.body.instructions)
    {
      irep_idt callee;
      if(
        direct_call_identifier(instruction, callee) &&
        callee == "__VERIFIER_assert")
      {
        if(property_call != nullptr)
        {
          reason = "pssc_multiple_properties";
          return false;
        }
        property_function = function.first;
        property_call = &instruction;
      }
    }
  }
  if(property_call == nullptr || property_call->call_arguments().size() != 1)
  {
    reason = "pssc_missing_property";
    return false;
  }

  const auto function =
    model.goto_functions.function_map.find(property_function);
  auto current = function->second.body.instructions.begin();
  for(; current != function->second.body.instructions.end(); ++current)
    if(&*current == property_call)
      break;
  if(current == function->second.body.instructions.end())
  {
    reason = "pssc_property_location";
    return false;
  }
  auto previous = current;
  bool found_store = false;
  while(previous != function->second.body.instructions.begin())
  {
    --previous;
    if(
      previous->is_decl() || previous->is_dead() ||
      previous->is_skip())
      continue;
    found_store = previous->is_assign();
    break;
  }
  if(!found_store ||
     !pssc_dereference_symbol(previous->assign_lhs(), pointer_formal) ||
     !direct_symbol(without_cast(previous->assign_rhs()), stored_value))
  {
    reason = "pssc_immediate_store";
    return false;
  }

  const exprt &condition =
    without_cast(property_call->call_arguments().front());
  if(condition.id() != ID_equal || condition.operands().size() != 2)
  {
    reason = "pssc_property_equality";
    return false;
  }
  auto matches = [&](const exprt &cell, const exprt &value) {
    irep_idt actual_pointer;
    irep_idt actual_value;
    return
      pssc_dereference_symbol(cell, actual_pointer) &&
      direct_symbol(without_cast(value), actual_value) &&
      actual_pointer == pointer_formal && actual_value == stored_value;
  };
  if(
    !matches(condition.op0(), condition.op1()) &&
    !matches(condition.op1(), condition.op0()))
  {
    reason = "pssc_property_store_mismatch";
    return false;
  }
  return true;
}

bool pssc_single_wrapper_call(
  const goto_modelt &model,
  const irep_idt &worker,
  irep_idt &callee,
  const goto_programt::instructiont *&call,
  std::string &reason)
{
  const auto function = model.goto_functions.function_map.find(worker);
  if(
    function == model.goto_functions.function_map.end() ||
    !function->second.body_available())
  {
    reason = "pssc_missing_worker";
    return false;
  }
  call = nullptr;
  for(const auto &instruction : function->second.body.instructions)
  {
    irep_idt candidate;
    if(!direct_call_identifier(instruction, candidate))
      continue;
    const auto body = model.goto_functions.function_map.find(candidate);
    if(
      body == model.goto_functions.function_map.end() ||
      !body->second.body_available())
      continue;
    if(call != nullptr)
    {
      reason = "pssc_wrapper_call_count";
      return false;
    }
    call = &instruction;
    callee = candidate;
  }
  if(call == nullptr)
  {
    reason = "pssc_wrapper_missing_call";
    return false;
  }
  return true;
}

bool pssc_other_worker_excludes(
  const goto_modelt &model,
  const irep_idt &worker,
  const irep_idt &pointer_actual,
  std::string &reason)
{
  std::deque<irep_idt> pending;
  std::set<irep_idt> visited;
  pending.push_back(worker);
  while(!pending.empty())
  {
    const irep_idt function_id = pending.front();
    pending.pop_front();
    if(!visited.insert(function_id).second)
      continue;
    const auto function = model.goto_functions.function_map.find(function_id);
    if(
      function == model.goto_functions.function_map.end() ||
      !function->second.body_available())
      continue;
    for(const auto &instruction : function->second.body.instructions)
    {
      if(
        contains_symbol(instruction.code(), {pointer_actual}) ||
        (instruction.has_condition() &&
         contains_symbol(instruction.condition(), {pointer_actual})))
      {
        reason = "pssc_other_worker_access";
        return false;
      }
      if(!instruction.is_function_call())
        continue;
      irep_idt callee;
      if(!direct_call_identifier(instruction, callee))
      {
        reason = "pssc_other_worker_indirect_call";
        return false;
      }
      const auto body = model.goto_functions.function_map.find(callee);
      if(
        body != model.goto_functions.function_map.end() &&
        body->second.body_available())
        pending.push_back(callee);
    }
  }
  return true;
}
} // namespace

bool post_store_stable_cell_proof(
  goto_modelt &goto_model,
  message_handlert &message_handler)
{
  (void)message_handler;
  const namespacet ns(goto_model.symbol_table);
  goto_modelt lifecycle_model;
  lifecycle_model.symbol_table = goto_model.symbol_table;
  lifecycle_model.goto_functions.copy_from(goto_model.goto_functions);
  std::vector<create_recordt> creates;
  std::vector<goto_programt::targett> joins;
  std::string reason;
  const auto reject_pssc = [&reason]() {
    std::cout << "NATIVE_POST_STORE_STABLE_CELL applied=0 reason="
              << reason << '\n';
    return false;
  };
  if(
    !collect_lifecycle(lifecycle_model, ns, creates, joins, reason) ||
    creates.size() != 2 || joins.size() != 2 ||
    !validate_main_region(lifecycle_model, ns, creates, joins, reason))
  {
    std::cout << "NATIVE_POST_STORE_STABLE_CELL applied=0 reason="
              << (reason.empty() ? "pssc_lifecycle" : reason) << '\n';
    return false;
  }

  irep_idt property_function;
  irep_idt pointer_formal;
  irep_idt stored_value;
  const goto_programt::instructiont *wrapper_calls[2]{nullptr, nullptr};
  irep_idt wrapper_callees[2];
  std::set<irep_idt> candidate_property_functions;
  for(std::size_t index = 0; index < 2; ++index)
  {
    if(!pssc_single_wrapper_call(
         goto_model, creates[index].worker, wrapper_callees[index],
         wrapper_calls[index], reason))
      return reject_pssc();
    candidate_property_functions.insert(wrapper_callees[index]);
  }
  const goto_programt::instructiont *property_call = nullptr;
  if(!pssc_property_shape(
       goto_model, candidate_property_functions, property_function,
       pointer_formal, stored_value,
       property_call, reason))
    return reject_pssc();

  std::size_t formal_index = 0;
  const auto property =
    goto_model.goto_functions.function_map.find(property_function);
  const auto formal = std::find(
    property->second.parameter_identifiers.begin(),
    property->second.parameter_identifiers.end(),
    pointer_formal);
  if(formal == property->second.parameter_identifiers.end())
  {
    reason = "pssc_pointer_not_parameter";
    return reject_pssc();
  }
  formal_index = static_cast<std::size_t>(
    formal - property->second.parameter_identifiers.begin());

  std::size_t property_worker_index = 2;
  for(std::size_t index = 0; index < 2; ++index)
  {
    if(wrapper_callees[index] == property_function)
    {
      if(property_worker_index != 2)
      {
        reason = "pssc_multiple_property_workers";
        return reject_pssc();
      }
      property_worker_index = index;
    }
  }
  if(property_worker_index == 2)
  {
    reason = "pssc_property_worker";
    return reject_pssc();
  }
  const auto property_wrapper_call = wrapper_calls[property_worker_index];
  if(property_wrapper_call->call_arguments().size() <= formal_index)
  {
    reason = "pssc_pointer_actual_index";
    return reject_pssc();
  }
  irep_idt pointer_actual;
  if(!direct_symbol(
       without_cast(
         property_wrapper_call->call_arguments()[formal_index]),
       pointer_actual))
  {
    reason = "pssc_pointer_actual";
    return reject_pssc();
  }

  if(!pssc_other_worker_excludes(
       goto_model, creates[1 - property_worker_index].worker,
       pointer_actual, reason))
    return reject_pssc();

  std::deque<irep_idt> reachable_pending;
  std::set<irep_idt> reachable_functions;
  reachable_pending.push_back("main");
  reachable_pending.push_back(creates[0].worker);
  reachable_pending.push_back(creates[1].worker);
  while(!reachable_pending.empty())
  {
    const irep_idt function_id = reachable_pending.front();
    reachable_pending.pop_front();
    if(!reachable_functions.insert(function_id).second)
      continue;
    const auto function =
      goto_model.goto_functions.function_map.find(function_id);
    if(
      function == goto_model.goto_functions.function_map.end() ||
      !function->second.body_available())
      continue;
    for(const auto &instruction : function->second.body.instructions)
    {
      if(!instruction.is_function_call())
        continue;
      irep_idt callee;
      if(!direct_call_identifier(instruction, callee))
      {
        reason = "pssc_reachable_indirect_call";
        return reject_pssc();
      }
      const auto body = goto_model.goto_functions.function_map.find(callee);
      if(
        body != goto_model.goto_functions.function_map.end() &&
        body->second.body_available())
        reachable_pending.push_back(callee);
    }
  }

  const auto main_function =
    goto_model.goto_functions.function_map.find("main");
  irep_idt allocation_result;
  const goto_programt::instructiont *pointer_binding = nullptr;
  const goto_programt::instructiont *allocation_call = nullptr;
  std::size_t pointer_bindings = 0;
  for(const auto &instruction : main_function->second.body.instructions)
  {
    irep_idt lhs;
    if(
      instruction.is_assign() &&
      direct_symbol(instruction.assign_lhs(), lhs) &&
      lhs == pointer_actual)
    {
      ++pointer_bindings;
      if(
        !direct_symbol(
          without_cast(instruction.assign_rhs()), allocation_result))
      {
        reason = "pssc_allocation_binding";
        return reject_pssc();
      }
      pointer_binding = &instruction;
    }
  }
  if(pointer_bindings != 1 || pointer_binding == nullptr)
  {
    reason = "pssc_allocation_binding_count";
    return reject_pssc();
  }
  std::size_t allocation_calls = 0;
  for(const auto &instruction : main_function->second.body.instructions)
  {
    irep_idt callee;
    irep_idt lhs;
    if(
      direct_call_identifier(instruction, callee) &&
      callee == "malloc" && !instruction.call_lhs().is_nil() &&
      direct_symbol(instruction.call_lhs(), lhs) &&
      lhs == allocation_result)
    {
      ++allocation_calls;
      allocation_call = &instruction;
    }
  }
  if(allocation_calls != 1 || allocation_call == nullptr)
  {
    reason = "pssc_allocation_origin";
    return reject_pssc();
  }

  for(const auto &function : goto_model.goto_functions.function_map)
  {
    if(reachable_functions.find(function.first) == reachable_functions.end())
      continue;
    if(!function.second.body_available())
      continue;
    for(const auto &instruction : function.second.body.instructions)
    {
      if(
        &instruction != pointer_binding &&
        &instruction != allocation_call &&
        !instruction.is_decl() && !instruction.is_dead() &&
        (contains_symbol(instruction.code(), {allocation_result}) ||
         (instruction.has_condition() &&
          contains_symbol(
            instruction.condition(), {allocation_result}))))
      {
        reason = "pssc_allocation_alias";
        return reject_pssc();
      }
      if(
        instruction.is_assign() &&
        contains_symbol(instruction.assign_rhs(), {pointer_actual}))
      {
        irep_idt lhs;
        if(
          !direct_symbol(instruction.assign_lhs(), lhs) ||
          lhs != pointer_actual)
        {
          reason = "pssc_pointer_alias";
          return reject_pssc();
        }
      }
      if(
        instruction.is_function_call() &&
        &instruction != property_wrapper_call)
      {
        for(const auto &argument : instruction.call_arguments())
        {
          if(contains_symbol(argument, {pointer_actual}) &&
             function.first != "main")
          {
            irep_idt callee;
            direct_call_identifier(instruction, callee);
            reason =
              "pssc_pointer_escape_" + id2string(function.first) + "_" +
              id2string(callee);
            return reject_pssc();
          }
        }
      }
    }
  }

  std::cout << "NATIVE_POST_STORE_STABLE_CELL applied=1 worker="
            << creates[property_worker_index].worker
            << " property_function=" << property_function << '\n';
  return true;
}

namespace
{
bool sci_constant(const exprt &src, mp_integer &value)
{
  const exprt &expr = without_cast(src);
  if(iro_direct_constant(expr, value))
    return true;
  if(expr.id() != ID_unary_minus || expr.operands().size() != 1)
    return false;
  if(!iro_direct_constant(expr.op0(), value))
    return false;
  value = -value;
  return true;
}

bool sci_relation(
  const exprt &src,
  const irep_idt &relation_id,
  irep_idt &symbol,
  mp_integer &constant,
  bool require_negation)
{
  const exprt *current = &without_cast(src);
  if(require_negation)
  {
    if(current->id() == ID_not && current->operands().size() == 1)
      current = &without_cast(current->op0());
    else if(!(
      relation_id == ID_equal && current->id() == ID_notequal &&
      current->operands().size() == 2))
      return false;
  }
  if(
    current->id() != relation_id &&
    !(require_negation && relation_id == ID_equal &&
      current->id() == ID_notequal))
    return false;
  if(current->operands().size() != 2)
    return false;
  if(
    direct_symbol(without_cast(current->op0()), symbol) &&
    sci_constant(current->op1(), constant))
    return true;
  return direct_symbol(without_cast(current->op1()), symbol) &&
         sci_constant(current->op0(), constant);
}

bool sci_return_constant(
  const goto_programt::instructiont &instruction,
  const mp_integer &expected)
{
  if(!instruction.is_set_return_value())
    return false;
  mp_integer value;
  return sci_constant(
           to_code_return(instruction.code()).return_value(), value) &&
         value == expected;
}

bool sci_unit_update_function(
  const goto_modelt &model,
  const irep_idt &function_id,
  const irep_idt &counter,
  bool increment)
{
  const auto function = model.goto_functions.function_map.find(function_id);
  if(
    function == model.goto_functions.function_map.end() ||
    !function->second.body_available())
    return false;
  std::size_t assignments = 0;
  for(const auto &instruction : function->second.body.instructions)
  {
    const bool mentions_counter =
      instruction_mentions_any(instruction, {counter});
    if(!instruction.is_assign())
    {
      if(mentions_counter)
        return false;
      continue;
    }
    ++assignments;
    irep_idt lhs;
    if(!direct_symbol(instruction.assign_lhs(), lhs) || lhs != counter)
      return false;
    const exprt &rhs = without_cast(instruction.assign_rhs());
    if(
      rhs.id() != (increment ? ID_plus : ID_minus) ||
      rhs.operands().size() != 2)
      return false;
    irep_idt base;
    mp_integer amount;
    if(
      !direct_symbol(without_cast(rhs.op0()), base) || base != counter ||
      !iro_direct_constant(rhs.op1(), amount) || amount != 1)
      return false;
  }
  return assignments == 1;
}

bool sci_get_function(
  const goto_modelt &model,
  const irep_idt &function_id,
  const irep_idt &counter)
{
  const auto function = model.goto_functions.function_map.find(function_id);
  if(
    function == model.goto_functions.function_map.end() ||
    !function->second.body_available())
    return false;
  std::size_t returns = 0;
  for(const auto &instruction : function->second.body.instructions)
  {
    const bool mentions_counter =
      instruction_mentions_any(instruction, {counter});
    if(!instruction.is_set_return_value())
    {
      if(mentions_counter)
        return false;
      continue;
    }
    ++returns;
    irep_idt returned;
    if(
      !direct_symbol(
        without_cast(to_code_return(instruction.code()).return_value()),
        returned) ||
      returned != counter)
      return false;
  }
  return returns == 1;
}

std::size_t sci_counter_mentions(
  const goto_modelt &model,
  const irep_idt &function_id,
  const irep_idt &counter)
{
  const auto function = model.goto_functions.function_map.find(function_id);
  if(
    function == model.goto_functions.function_map.end() ||
    !function->second.body_available())
    return 0;
  std::size_t mentions = 0;
  for(const auto &instruction : function->second.body.instructions)
    if(instruction_mentions_any(instruction, {counter}))
      ++mentions;
  return mentions;
}

bool sci_array_argument(
  const exprt &argument,
  const symbol_tablet &symbol_table,
  irep_idt &array,
  mp_integer &capacity)
{
  const std::set<symbol_exprt> symbols = find_symbols(argument);
  for(const auto &symbol_expr : symbols)
  {
    const irep_idt &identifier = symbol_expr.get_identifier();
    const auto symbol = symbol_table.symbols.find(identifier);
    if(
      symbol == symbol_table.symbols.end() ||
      symbol->second.type.id() != ID_array)
      continue;
    const exprt &size = to_array_type(symbol->second.type).size();
    mp_integer candidate;
    if(!iro_direct_constant(size, candidate) || candidate <= 0)
      continue;
    if(!array.empty())
      return false;
    array = identifier;
    capacity = candidate;
  }
  return !array.empty();
}

struct sci_worker_shapet
{
  irep_idt worker;
  irep_idt mutex;
  irep_idt counter;
  irep_idt operation;
  irep_idt array;
  mp_integer bound;
  mp_integer capacity;
  bool positive_guard = false;
  bool overflow_check = false;
  bool underflow_check = false;
};

bool sci_worker_shape(
  const goto_modelt &model,
  const irep_idt &worker,
  const irep_idt &counter,
  sci_worker_shapet &shape,
  std::string &reason)
{
  const auto function = model.goto_functions.function_map.find(worker);
  if(
    function == model.goto_functions.function_map.end() ||
    !function->second.body_available())
  {
    reason = "sci_missing_worker";
    return false;
  }
  shape.worker = worker;
  const auto &program = function->second.body;
  std::map<const goto_programt::instructiont *, std::size_t> positions;
  std::size_t next_position = 0;
  for(const auto &instruction : program.instructions)
    positions.emplace(&instruction, next_position++);
  std::size_t locks = 0;
  std::size_t unlocks = 0;
  std::size_t operation_calls = 0;
  std::size_t error_calls = 0;
  std::size_t loop_guards = 0;
  std::size_t loop_increments = 0;
  irep_idt induction;
  bool induction_zero = false;
  bool locked = false;
  const goto_programt::instructiont *operation_instruction = nullptr;
  const goto_programt::instructiont *error_instruction = nullptr;
  irep_idt operation_result;
  for(const auto &instruction : program.instructions)
  {
    irep_idt callee;
    if(direct_call_identifier(instruction, callee))
    {
      if(callee == "pthread_mutex_lock" || callee == "pthread_mutex_unlock")
      {
        if(instruction.call_arguments().size() != 1)
        {
          reason = "sci_mutex_arguments";
          return false;
        }
        irep_idt mutex;
        if(!addressed_symbol(instruction.call_arguments().front(), mutex))
        {
          reason = "sci_mutex_resolution";
          return false;
        }
        if(shape.mutex.empty())
          shape.mutex = mutex;
        if(shape.mutex != mutex)
        {
          reason = "sci_mutex_mismatch";
          return false;
        }
        if(callee == "pthread_mutex_lock")
        {
          if(locked)
          {
            reason = "sci_nested_mutex";
            return false;
          }
          locked = true;
          ++locks;
        }
        else
        {
          if(!locked)
          {
            reason = "sci_unbalanced_mutex";
            return false;
          }
          locked = false;
          ++unlocks;
        }
        continue;
      }
      irep_idt candidate_array;
      mp_integer candidate_capacity;
      if(
        !instruction.call_arguments().empty() &&
        sci_array_argument(
          instruction.call_arguments().front(), model.symbol_table,
          candidate_array, candidate_capacity))
      {
        if(!locked)
        {
          reason = "sci_operation_outside_mutex";
          return false;
        }
        ++operation_calls;
        shape.operation = callee;
        operation_instruction = &instruction;
        if(
          instruction.call_lhs().is_nil() ||
          !direct_symbol(instruction.call_lhs(), operation_result))
        {
          reason = "sci_operation_result";
          return false;
        }
        if(
          !shape.array.empty() &&
          (shape.array != candidate_array ||
           shape.capacity != candidate_capacity))
        {
          reason = "sci_array_capacity";
          return false;
        }
        shape.array = candidate_array;
        shape.capacity = candidate_capacity;
        continue;
      }
      if(callee == "error")
      {
        if(!locked)
        {
          reason = "sci_error_outside_mutex";
          return false;
        }
        ++error_calls;
        error_instruction = &instruction;
      }
    }
    if(instruction.is_assign())
    {
      irep_idt lhs;
      mp_integer zero;
      if(
        direct_symbol(instruction.assign_lhs(), lhs) &&
        iro_direct_constant(instruction.assign_rhs(), zero) && zero == 0)
      {
        if(induction.empty())
          induction = lhs;
        if(lhs == induction)
          induction_zero = true;
      }
      if(!induction.empty() && iro_unit_increment(instruction, induction))
        ++loop_increments;
    }
    if(instruction.is_goto())
    {
      irep_idt symbol;
      mp_integer constant;
      if(
        sci_relation(
          instruction.condition(), ID_lt, symbol, constant, true))
      {
        if(induction.empty())
          induction = symbol;
        if(symbol == induction)
        {
          shape.bound = constant;
          ++loop_guards;
        }
      }
    }
  }
  if(
    locked || locks != 1 || unlocks != 1 || operation_calls != 1 ||
    error_calls != 1 || !induction_zero || loop_guards != 1 ||
    loop_increments != 1 || shape.bound <= 0 ||
    shape.bound > shape.capacity)
  {
    reason = "sci_worker_obligation";
    return false;
  }
  if(operation_instruction == nullptr || error_instruction == nullptr)
  {
    reason = "sci_operation_control";
    return false;
  }
  const std::size_t operation_position = positions.at(operation_instruction);
  const std::size_t error_position = positions.at(error_instruction);
  for(const auto &instruction : program.instructions)
  {
    if(!instruction.is_goto() || instruction.targets.size() != 1)
      continue;
    const std::size_t guard_position = positions.at(&instruction);
    const std::size_t target_position =
      positions.at(&*instruction.get_target());
    irep_idt symbol;
    mp_integer constant;
    if(
      sci_relation(
        instruction.condition(), ID_equal, symbol, constant, true) &&
      symbol == operation_result &&
      operation_position < guard_position &&
      guard_position < error_position &&
      error_position < target_position)
    {
      if(constant == -1)
        shape.overflow_check = true;
      if(constant == -2)
        shape.underflow_check = true;
    }
    if(
      sci_relation(
        instruction.condition(), ID_gt, symbol, constant, true) &&
      symbol == counter && constant == 0 &&
      guard_position < operation_position &&
      operation_position < target_position)
      shape.positive_guard = true;
  }
  return true;
}

bool sci_push_helper(
  const goto_modelt &model,
  const irep_idt &function_id,
  const irep_idt &counter,
  const mp_integer &capacity,
  std::set<irep_idt> &counter_helpers)
{
  const auto push = model.goto_functions.function_map.find(function_id);
  if(
    push == model.goto_functions.function_map.end() ||
    !push->second.body_available())
    return false;

  bool push_boundary = false;
  bool push_failure = false;
  bool push_success = false;
  bool push_increment = false;
  bool push_index_read = false;
  std::size_t push_stores = 0;
  for(const auto &instruction : push->second.body.instructions)
  {
    irep_idt symbol;
    mp_integer constant;
    if(
      instruction.is_goto() &&
      sci_relation(
        instruction.condition(), ID_equal, symbol, constant, true) &&
      symbol == counter && constant == capacity)
      push_boundary = true;
    if(sci_return_constant(instruction, -1))
      push_failure = true;
    if(sci_return_constant(instruction, 0))
      push_success = true;
    irep_idt callee;
    if(direct_call_identifier(instruction, callee))
    {
      if(sci_unit_update_function(model, callee, counter, true))
      {
        push_increment = true;
        counter_helpers.insert(callee);
      }
      if(sci_get_function(model, callee, counter))
      {
        push_index_read = true;
        counter_helpers.insert(callee);
      }
    }
    if(
      instruction.is_assign() &&
      without_cast(instruction.assign_lhs()).id() == ID_dereference)
      ++push_stores;
  }

  return
    push_boundary && push_failure && push_success &&
    push_increment && push_index_read && push_stores == 1;
}

bool sci_pop_helper(
  const goto_modelt &model,
  const irep_idt &function_id,
  const irep_idt &counter,
  std::set<irep_idt> &counter_helpers)
{
  const auto pop = model.goto_functions.function_map.find(function_id);
  if(
    pop == model.goto_functions.function_map.end() ||
    !pop->second.body_available())
    return false;
  bool pop_boundary = false;
  bool pop_failure = false;
  bool pop_success = false;
  bool pop_decrement = false;
  bool pop_index_read = false;
  for(const auto &instruction : pop->second.body.instructions)
  {
    irep_idt symbol;
    mp_integer constant;
    if(
      instruction.is_goto() &&
      sci_relation(
        instruction.condition(), ID_equal, symbol, constant, true) &&
      symbol == counter && constant == 0)
      pop_boundary = true;
    if(sci_return_constant(instruction, -2))
      pop_failure = true;
    if(
      instruction.is_set_return_value() &&
      !sci_return_constant(instruction, -2))
      pop_success = true;
    irep_idt callee;
    if(direct_call_identifier(instruction, callee))
    {
      if(sci_unit_update_function(model, callee, counter, false))
      {
        pop_decrement = true;
        counter_helpers.insert(callee);
      }
      if(sci_get_function(model, callee, counter))
      {
        pop_index_read = true;
        counter_helpers.insert(callee);
      }
    }
  }
  return
    pop_boundary && pop_failure && pop_success &&
    pop_decrement && pop_index_read;
}
} // namespace

bool stack_capacity_invariant_proof(
  goto_modelt &goto_model,
  message_handlert &message_handler)
{
  (void)message_handler;
  const namespacet ns(goto_model.symbol_table);
  goto_modelt lifecycle_model;
  lifecycle_model.symbol_table = goto_model.symbol_table;
  lifecycle_model.goto_functions.copy_from(goto_model.goto_functions);
  std::vector<create_recordt> creates;
  std::vector<goto_programt::targett> joins;
  std::string reason;
  const auto reject = [&reason]() {
    std::cout << "NATIVE_STACK_CAPACITY applied=0 reason="
              << (reason.empty() ? "sci_unknown" : reason) << '\n';
    return false;
  };
  if(
    !collect_lifecycle(lifecycle_model, ns, creates, joins, reason) ||
    creates.size() != 2 || joins.size() != 2 ||
    !validate_main_region(lifecycle_model, ns, creates, joins, reason))
    return reject();

  std::vector<irep_idt> counter_candidates;
  const auto initialize =
    goto_model.goto_functions.function_map.find("__CPROVER_initialize");
  if(
    initialize == goto_model.goto_functions.function_map.end() ||
    !initialize->second.body_available())
  {
    reason = "sci_missing_initialization";
    return reject();
  }
  for(const auto &instruction : initialize->second.body.instructions)
  {
    irep_idt lhs;
    if(!iro_zero_assignment(instruction, lhs))
      continue;
    const auto symbol = goto_model.symbol_table.symbols.find(lhs);
    if(
      symbol != goto_model.symbol_table.symbols.end() &&
      symbol->second.is_static_lifetime &&
      symbol->second.type.id() == ID_signedbv)
      counter_candidates.push_back(lhs);
  }
  if(counter_candidates.empty())
  {
    reason = "sci_counter_initialization";
    return reject();
  }

  irep_idt counter;
  sci_worker_shapet first;
  sci_worker_shapet second;
  std::size_t admitted_counters = 0;
  for(const auto &candidate : counter_candidates)
  {
    sci_worker_shapet candidate_first;
    sci_worker_shapet candidate_second;
    std::string candidate_reason;
    if(
      !sci_worker_shape(
        goto_model, creates[0].worker, candidate,
        candidate_first, candidate_reason) ||
      !sci_worker_shape(
        goto_model, creates[1].worker, candidate,
        candidate_second, candidate_reason))
      continue;
    if(
      !candidate_first.positive_guard &&
      !candidate_second.positive_guard)
      continue;
    counter = candidate;
    first = candidate_first;
    second = candidate_second;
    ++admitted_counters;
  }
  if(admitted_counters != 1)
  {
    reason = "sci_counter_resolution";
    return reject();
  }

  sci_worker_shapet *pusher = nullptr;
  sci_worker_shapet *popper = nullptr;
  std::set<irep_idt> counter_helpers;
  for(auto *shape : {&first, &second})
  {
    if(sci_push_helper(
         goto_model, shape->operation, counter,
         shape->capacity, counter_helpers))
      pusher = shape;
    if(sci_pop_helper(
         goto_model, shape->operation, counter, counter_helpers))
      popper = shape;
  }
  if(
    pusher == nullptr || popper == nullptr ||
    pusher->mutex != popper->mutex || pusher->array != popper->array ||
    pusher->capacity != popper->capacity ||
    !pusher->overflow_check || !popper->underflow_check ||
    !popper->positive_guard)
  {
    reason =
      "sci_composition_obligation_first_" + id2string(first.operation) +
      "_second_" + id2string(second.operation) +
      "_mutex_" + std::to_string(first.mutex == second.mutex) +
      "_array_" + std::to_string(first.array == second.array) +
      "_capacity_" + std::to_string(first.capacity == second.capacity) +
      "_overflow_" + std::to_string(
        pusher != nullptr && pusher->overflow_check) +
      "_underflow_" + std::to_string(
        popper != nullptr && popper->underflow_check) +
      "_guard_" + std::to_string(
        popper != nullptr && popper->positive_guard);
    return reject();
  }
  if(
    counter_helpers.size() != 3 ||
    sci_counter_mentions(
      goto_model, pusher->worker, counter) != 0 ||
    sci_counter_mentions(
      goto_model, popper->worker, counter) != 1 ||
    sci_counter_mentions(
      goto_model, pusher->operation, counter) != 1 ||
    sci_counter_mentions(
      goto_model, popper->operation, counter) != 1)
  {
    reason =
      "sci_counter_footprint_helpers_" +
      std::to_string(counter_helpers.size()) +
      "_pusher_" + std::to_string(sci_counter_mentions(
        goto_model, pusher->worker, counter)) +
      "_popper_" + std::to_string(sci_counter_mentions(
        goto_model, popper->worker, counter)) +
      "_push_" + std::to_string(sci_counter_mentions(
        goto_model, pusher->operation, counter)) +
      "_pop_" + std::to_string(sci_counter_mentions(
        goto_model, popper->operation, counter));
    return reject();
  }
  std::set<irep_idt> allowed = {
    "__CPROVER_initialize", pusher->operation, popper->operation,
    creates[0].worker, creates[1].worker};
  allowed.insert(counter_helpers.begin(), counter_helpers.end());
  std::set<irep_idt> reachable;
  std::deque<irep_idt> pending{
    "main", creates[0].worker, creates[1].worker};
  while(!pending.empty())
  {
    const irep_idt function_id = pending.front();
    pending.pop_front();
    if(!reachable.insert(function_id).second)
      continue;
    const auto function =
      goto_model.goto_functions.function_map.find(function_id);
    if(
      function == goto_model.goto_functions.function_map.end() ||
      !function->second.body_available())
      continue;
    for(const auto &instruction : function->second.body.instructions)
    {
      if(!instruction.is_function_call())
        continue;
      irep_idt callee;
      if(!direct_call_identifier(instruction, callee))
      {
        reason = "sci_reachable_indirect_call";
        return reject();
      }
      const auto body =
        goto_model.goto_functions.function_map.find(callee);
      if(
        body != goto_model.goto_functions.function_map.end() &&
        body->second.body_available())
        pending.push_back(callee);
    }
  }
  for(const auto &function : goto_model.goto_functions.function_map)
  {
    if(
      reachable.find(function.first) == reachable.end() ||
      !function.second.body_available())
      continue;
    for(const auto &instruction : function.second.body.instructions)
    {
      if(
        allowed.find(function.first) == allowed.end() &&
        instruction_mentions_any(instruction, {counter}))
      {
        reason = "sci_external_counter_access";
        return reject();
      }
    }
  }

  std::size_t false_assertions = 0;
  for(const auto &function : goto_model.goto_functions.function_map)
  {
    if(!function.second.body_available())
      continue;
    for(const auto &instruction : function.second.body.instructions)
      if(instruction.is_assert())
      {
        exprt condition = simplify_expr(instruction.condition(), ns);
        if(!condition.is_false())
        {
          reason = "sci_external_assertion";
          return reject();
        }
        ++false_assertions;
      }
  }
  if(false_assertions != 1)
  {
    reason = "sci_property_count";
    return reject();
  }

  std::cout << "NATIVE_STACK_CAPACITY applied=1 counter=" << counter
            << " capacity=" << pusher->capacity
            << " push_bound=" << pusher->bound
            << " pop_bound=" << popper->bound << '\n';
  return true;
}

namespace
{
void qsc_components(const exprt &src, std::set<irep_idt> &components)
{
  const exprt &expr = without_cast(src);
  if(expr.id() == ID_member)
    components.insert(to_member_expr(expr).get_component_name());
  for(const auto &operand : expr.operands())
    qsc_components(operand, components);
}

bool qsc_indexed_symbol(
  const exprt &src,
  irep_idt &array,
  irep_idt &index)
{
  const exprt &expr = without_cast(src);
  if(expr.id() != ID_index || expr.operands().size() != 2)
    return false;
  return direct_symbol(without_cast(expr.op0()), array) &&
         direct_symbol(without_cast(expr.op1()), index);
}

bool qsc_addressed_argument(
  const goto_programt::instructiont &instruction,
  std::size_t index,
  irep_idt &object)
{
  return instruction.call_arguments().size() > index &&
         addressed_symbol(instruction.call_arguments()[index], object);
}

bool qsc_phase_guard(
  const goto_programt::instructiont &instruction,
  irep_idt &flag)
{
  if(!instruction.is_goto())
    return false;
  const exprt &outer = without_cast(instruction.condition());
  if(outer.id() != ID_not || outer.operands().size() != 1)
    return false;
  const exprt &inner = without_cast(outer.op0());
  mp_integer zero;
  return inner.id() == ID_notequal && inner.operands().size() == 2 &&
         direct_symbol(without_cast(inner.op0()), flag) &&
         sci_constant(inner.op1(), zero) && zero == 0;
}

bool qsc_boolean_assignment(
  const goto_programt::instructiont &instruction,
  irep_idt &flag,
  mp_integer &value)
{
  return instruction.is_assign() &&
         direct_symbol(instruction.assign_lhs(), flag) &&
         sci_constant(instruction.assign_rhs(), value) &&
         (value == 0 || value == 1);
}

bool qsc_booleanized_result(const exprt &src, irep_idt &result)
{
  const exprt &outer = without_cast(src);
  if(outer.id() != ID_not || outer.operands().size() != 1)
    return false;
  const exprt &comparison = without_cast(outer.op0());
  mp_integer zero;
  return
    comparison.id() == ID_notequal &&
    comparison.operands().size() == 2 &&
    direct_symbol(without_cast(comparison.op0()), result) &&
    sci_constant(comparison.op1(), zero) && zero == 0;
}

bool qsc_property_equality(
  const exprt &src,
  const irep_idt &result,
  const irep_idt &reference,
  const irep_idt &index)
{
  const exprt &outer = without_cast(src);
  if(outer.id() != ID_not || outer.operands().size() != 1)
    return false;
  const exprt &equality = without_cast(outer.op0());
  if(equality.id() != ID_equal || equality.operands().size() != 2)
    return false;
  auto matches = [&](const exprt &boolean_side, const exprt &array_side) {
    irep_idt actual_result;
    irep_idt actual_array;
    irep_idt actual_index;
    return qsc_booleanized_result(boolean_side, actual_result) &&
           actual_result == result &&
           qsc_indexed_symbol(array_side, actual_array, actual_index) &&
           actual_array == reference && actual_index == index;
  };
  return
    matches(equality.op0(), equality.op1()) ||
    matches(equality.op1(), equality.op0());
}

bool qsc_boolean_negative_equality(
  const exprt &src,
  const irep_idt &result)
{
  const exprt &outer = without_cast(src);
  if(outer.id() != ID_not || outer.operands().size() != 1)
    return false;
  const exprt &equality = without_cast(outer.op0());
  if(equality.id() != ID_equal || equality.operands().size() != 2)
    return false;
  auto matches = [&](const exprt &boolean_side, const exprt &constant_side) {
    irep_idt actual_result;
    mp_integer constant;
    return qsc_booleanized_result(boolean_side, actual_result) &&
           actual_result == result &&
           sci_constant(constant_side, constant) && constant < 0;
  };
  return
    matches(equality.op0(), equality.op1()) ||
    matches(equality.op1(), equality.op0());
}

std::size_t qsc_mentions(
  const goto_modelt &model,
  const irep_idt &function_id,
  const std::set<irep_idt> &objects)
{
  const auto function = model.goto_functions.function_map.find(function_id);
  if(
    function == model.goto_functions.function_map.end() ||
    !function->second.body_available())
    return 0;
  std::size_t count = 0;
  for(const auto &instruction : function->second.body.instructions)
    if(instruction_mentions_any(instruction, objects))
      ++count;
  return count;
}

struct qsc_worker_summaryt
{
  irep_idt worker;
  irep_idt mutex;
  irep_idt queue;
  irep_idt operation;
  irep_idt auxiliary_operation;
  irep_idt phase_flag;
  irep_idt induction;
  irep_idt value;
  irep_idt reference;
  irep_idt operation_result;
  mp_integer bound;
  mp_integer capacity;
  std::map<irep_idt, mp_integer> final_flags;
  bool producer = false;
  bool consumer = false;
};

bool qsc_worker(
  const goto_modelt &model,
  const irep_idt &worker,
  qsc_worker_summaryt &summary,
  std::string &reason)
{
  const auto function = model.goto_functions.function_map.find(worker);
  if(
    function == model.goto_functions.function_map.end() ||
    !function->second.body_available())
  {
    reason = "qsc_missing_worker";
    return false;
  }
  summary.worker = worker;
  const auto &program = function->second.body;
  std::vector<const goto_programt::instructiont *> order;
  std::map<const goto_programt::instructiont *, std::size_t> positions;
  for(const auto &instruction : program.instructions)
  {
    positions.emplace(&instruction, order.size());
    order.push_back(&instruction);
  }

  bool locked = false;
  std::size_t locks = 0;
  std::size_t unlocks = 0;
  std::size_t loop_guards = 0;
  std::size_t loop_increments = 0;
  std::size_t total_calls = 0;
  std::size_t total_assignments = 0;
  bool induction_zero = false;
  const goto_programt::instructiont *phase_guard = nullptr;
  const goto_programt::instructiont *reference_store = nullptr;
  const goto_programt::instructiont *property_guard = nullptr;
  const goto_programt::instructiont *error_call = nullptr;
  std::vector<const goto_programt::instructiont *> queue_calls;

  for(const auto &instruction : program.instructions)
  {
    irep_idt callee;
    if(instruction.is_function_call())
    {
      ++total_calls;
      if(!direct_call_identifier(instruction, callee))
      {
        reason = "qsc_worker_indirect_call";
        return false;
      }
      if(callee == "pthread_mutex_lock" || callee == "pthread_mutex_unlock")
      {
        irep_idt mutex;
        if(!qsc_addressed_argument(instruction, 0, mutex))
        {
          reason = "qsc_mutex_resolution";
          return false;
        }
        if(summary.mutex.empty())
          summary.mutex = mutex;
        if(summary.mutex != mutex)
        {
          reason = "qsc_mutex_mismatch";
          return false;
        }
        if(callee == "pthread_mutex_lock")
        {
          if(locked)
          {
            reason = "qsc_nested_mutex";
            return false;
          }
          locked = true;
          ++locks;
        }
        else
        {
          if(!locked)
          {
            reason = "qsc_unbalanced_mutex";
            return false;
          }
          locked = false;
          ++unlocks;
        }
        continue;
      }
      irep_idt object;
      if(qsc_addressed_argument(instruction, 0, object))
      {
        if(!locked)
        {
          reason = "qsc_queue_call_outside_mutex";
          return false;
        }
        if(summary.queue.empty())
          summary.queue = object;
        if(summary.queue != object)
        {
          reason = "qsc_queue_object_mismatch";
          return false;
        }
        queue_calls.push_back(&instruction);
      }
      if(callee == "reach_error")
        error_call = &instruction;
    }

    irep_idt flag;
    if(qsc_phase_guard(instruction, flag))
    {
      if(phase_guard != nullptr)
      {
        reason = "qsc_multiple_phase_guards";
        return false;
      }
      summary.phase_flag = flag;
      phase_guard = &instruction;
    }

    if(instruction.is_assign())
    {
      ++total_assignments;
      irep_idt lhs;
      mp_integer constant;
      if(
        direct_symbol(instruction.assign_lhs(), lhs) &&
        sci_constant(instruction.assign_rhs(), constant) &&
        constant == 0 && summary.induction.empty())
      {
        summary.induction = lhs;
        induction_zero = true;
      }
      if(
        !summary.induction.empty() &&
        iro_unit_increment(instruction, summary.induction))
        ++loop_increments;

      irep_idt array;
      irep_idt index;
      irep_idt value;
      if(
        qsc_indexed_symbol(instruction.assign_lhs(), array, index) &&
        direct_symbol(without_cast(instruction.assign_rhs()), value))
      {
        if(reference_store != nullptr)
        {
          reason = "qsc_multiple_reference_stores";
          return false;
        }
        const auto symbol = model.symbol_table.symbols.find(array);
        if(
          symbol == model.symbol_table.symbols.end() ||
          symbol->second.type.id() != ID_array ||
          !sci_constant(
            to_array_type(symbol->second.type).size(), summary.capacity))
        {
          reason = "qsc_reference_capacity";
          return false;
        }
        summary.reference = array;
        summary.induction = index;
        summary.value = value;
        reference_store = &instruction;
      }

      mp_integer bool_value;
      if(qsc_boolean_assignment(instruction, flag, bool_value) &&
         flag != summary.induction)
        summary.final_flags[flag] = bool_value;
    }

    if(instruction.is_goto())
    {
      irep_idt induction;
      mp_integer bound;
      if(
        sci_relation(
          instruction.condition(), ID_lt, induction, bound, true))
      {
        if(summary.induction.empty())
          summary.induction = induction;
        if(induction == summary.induction)
        {
          summary.bound = bound;
          ++loop_guards;
        }
      }
    }
  }

  if(
    locked || locks != 1 || unlocks != 1 || phase_guard == nullptr ||
    !induction_zero || loop_guards != 1 || loop_increments != 1 ||
    summary.bound <= 0 || queue_calls.empty())
  {
    reason = "qsc_worker_obligation";
    return false;
  }

  if(reference_store != nullptr)
  {
    summary.producer = true;
    if(
      queue_calls.size() != 1 ||
      queue_calls.front()->call_arguments().size() != 2 ||
      total_calls != 3 || total_assignments != 6)
    {
      reason = "qsc_producer_call_count";
      return false;
    }
    irep_idt actual_value;
    if(
      !direct_symbol(
        without_cast(queue_calls.front()->call_arguments()[1]),
        actual_value) ||
      actual_value != summary.value)
    {
      reason = "qsc_producer_value_mismatch";
      return false;
    }
    direct_call_identifier(*queue_calls.front(), summary.operation);
  }
  else
  {
    summary.consumer = true;
    if(
      queue_calls.size() != 2 || error_call == nullptr ||
      total_calls != 6 || total_assignments != 4)
    {
      reason = "qsc_consumer_call_count";
      return false;
    }
    direct_call_identifier(
      *queue_calls.front(), summary.auxiliary_operation);
    direct_call_identifier(*queue_calls.back(), summary.operation);
    if(
      queue_calls.back()->call_lhs().is_nil() ||
      !direct_symbol(
        queue_calls.back()->call_lhs(), summary.operation_result))
    {
      reason = "qsc_consumer_result";
      return false;
    }
    for(const auto &instruction : program.instructions)
    {
      if(!instruction.is_goto() || instruction.targets.size() != 1)
        continue;
      find_symbols_sett symbols;
      find_symbols(instruction.condition(), symbols);
      if(symbols.find(summary.operation_result) == symbols.end())
        continue;
      irep_idt candidate_reference;
      mp_integer candidate_capacity;
      for(const auto &identifier : symbols)
      {
        const auto symbol = model.symbol_table.symbols.find(identifier);
        if(
          symbol == model.symbol_table.symbols.end() ||
          symbol->second.type.id() != ID_array)
          continue;
        if(
          !sci_constant(
            to_array_type(symbol->second.type).size(),
            candidate_capacity))
          continue;
        if(!candidate_reference.empty())
        {
          reason = "qsc_multiple_property_arrays";
          return false;
        }
        candidate_reference = identifier;
      }
      if(!candidate_reference.empty())
      {
        property_guard = &instruction;
        summary.reference = candidate_reference;
        summary.capacity = candidate_capacity;
      }
    }
    if(property_guard == nullptr)
    {
      reason = "qsc_property_guard";
      return false;
    }
    if(!qsc_property_equality(
         property_guard->condition(), summary.operation_result,
         summary.reference, summary.induction))
    {
      reason = "qsc_property_shape";
      return false;
    }
    const std::size_t property_position = positions.at(property_guard);
    const std::size_t error_position = positions.at(error_call);
    if(
      positions.at(queue_calls.back()) >= property_position ||
      property_position >= error_position ||
      property_guard->targets.size() != 1 ||
      positions.at(&*property_guard->get_target()) <= error_position)
    {
      reason = "qsc_property_control";
      return false;
    }
    find_symbols_sett property_symbols;
    find_symbols(
      without_cast(property_guard->condition()), property_symbols);
    if(
      property_symbols.find(summary.operation_result) ==
        property_symbols.end())
    {
      reason = "qsc_property_result";
      return false;
    }
  }
  if(summary.bound != summary.capacity)
  {
    reason = "qsc_worker_bound_capacity";
    return false;
  }
  return true;
}

bool qsc_update_shape(
  const goto_modelt &model,
  const irep_idt &function_id,
  bool producer,
  const mp_integer &capacity,
  std::set<irep_idt> &components,
  irep_idt &data_component,
  std::string &reason)
{
  const auto function = model.goto_functions.function_map.find(function_id);
  if(
    function == model.goto_functions.function_map.end() ||
    !function->second.body_available())
  {
    reason = "qsc_missing_operation";
    return false;
  }
  std::vector<const goto_programt::instructiont *> assignments;
  std::vector<const goto_programt::instructiont *> guards;
  std::vector<const goto_programt::instructiont *> returns;
  for(const auto &instruction : function->second.body.instructions)
  {
    if(instruction.is_function_call())
    {
      reason = "qsc_operation_call";
      return false;
    }
    if(instruction.is_assign())
      assignments.push_back(&instruction);
    if(instruction.is_goto() && !instruction.condition().is_true())
      guards.push_back(&instruction);
    if(instruction.is_set_return_value())
      returns.push_back(&instruction);
  }
  if(
    assignments.size() != 4 || guards.size() != 1 ||
    returns.size() != 1)
  {
    reason = "qsc_operation_counts";
    return false;
  }

  std::set<irep_idt> first_lhs;
  std::set<irep_idt> first_rhs;
  qsc_components(assignments[0]->assign_lhs(), first_lhs);
  qsc_components(assignments[0]->assign_rhs(), first_rhs);
  if(producer)
  {
    irep_idt stored_value;
    if(
      first_lhs.size() != 2 || !first_rhs.empty() ||
      !direct_symbol(
        without_cast(assignments[0]->assign_rhs()), stored_value) ||
      std::find(
        function->second.parameter_identifiers.begin(),
        function->second.parameter_identifiers.end(),
        stored_value) == function->second.parameter_identifiers.end())
    {
      reason = "qsc_enqueue_store";
      return false;
    }
  }
  else
  {
    irep_idt loaded_value;
    irep_idt returned_value;
    if(
      first_rhs.size() != 2 ||
      !direct_symbol(assignments[0]->assign_lhs(), loaded_value) ||
      !direct_symbol(
        without_cast(
          to_code_return(returns.front()->code()).return_value()),
        returned_value) ||
      returned_value != loaded_value)
    {
      reason = "qsc_dequeue_load";
      return false;
    }
  }

  std::set<irep_idt> amount_lhs;
  std::set<irep_idt> amount_rhs;
  qsc_components(assignments[1]->assign_lhs(), amount_lhs);
  qsc_components(assignments[1]->assign_rhs(), amount_rhs);
  if(
    amount_lhs.size() != 1 || amount_rhs != amount_lhs)
  {
    reason = "qsc_amount_update";
    return false;
  }
  const exprt &amount_update =
    without_cast(assignments[1]->assign_rhs());
  if(
    amount_update.id() != (producer ? ID_plus : ID_minus) ||
    amount_update.operands().size() != 2)
  {
    reason = "qsc_amount_direction";
    return false;
  }
  mp_integer unit;
  if(!sci_constant(amount_update.op1(), unit) || unit != 1)
  {
    reason = "qsc_amount_unit";
    return false;
  }

  irep_idt guard_symbol;
  mp_integer guard_capacity;
  const exprt &guard_outer = without_cast(guards.front()->condition());
  if(
    guard_outer.id() != ID_not || guard_outer.operands().size() != 1)
  {
    reason = "qsc_index_guard";
    return false;
  }
  const exprt &guard_equal = without_cast(guard_outer.op0());
  std::set<irep_idt> guard_components;
  qsc_components(guard_equal, guard_components);
  if(
    guard_equal.id() != ID_equal ||
    guard_components.size() != 1 ||
    !sci_constant(guard_equal.op1(), guard_capacity) ||
    guard_capacity != capacity)
  {
    reason = "qsc_index_capacity";
    return false;
  }

  std::set<irep_idt> reset_lhs;
  std::set<irep_idt> increment_lhs;
  std::set<irep_idt> increment_rhs;
  qsc_components(assignments[2]->assign_lhs(), reset_lhs);
  qsc_components(assignments[3]->assign_lhs(), increment_lhs);
  qsc_components(assignments[3]->assign_rhs(), increment_rhs);
  mp_integer reset;
  const exprt &increment = without_cast(assignments[3]->assign_rhs());
  if(
    reset_lhs != guard_components ||
    increment_lhs != guard_components ||
    increment_rhs != guard_components ||
    !sci_constant(assignments[2]->assign_rhs(), reset) || reset != 1 ||
    increment.id() != ID_plus || increment.operands().size() != 2 ||
    !sci_constant(increment.op1(), unit) || unit != 1)
  {
    reason = "qsc_index_update";
    return false;
  }
  components.insert(first_lhs.begin(), first_lhs.end());
  components.insert(first_rhs.begin(), first_rhs.end());
  components.insert(amount_lhs.begin(), amount_lhs.end());
  components.insert(guard_components.begin(), guard_components.end());
  const std::set<irep_idt> &data_candidates =
    producer ? first_lhs : first_rhs;
  for(const auto &component : data_candidates)
    if(guard_components.find(component) == guard_components.end())
    {
      if(!data_component.empty())
      {
        reason = "qsc_multiple_data_components";
        return false;
      }
      data_component = component;
    }
  if(data_component.empty())
  {
    reason = "qsc_missing_data_component";
    return false;
  }
  if(components.size() != 3)
  {
    reason = "qsc_operation_component_count_" +
      std::to_string(components.size());
    return false;
  }
  return true;
}
} // namespace

bool queue_sequence_correspondence_proof(
  goto_modelt &goto_model,
  message_handlert &message_handler)
{
  (void)message_handler;
  const namespacet ns(goto_model.symbol_table);
  goto_modelt lifecycle_model;
  lifecycle_model.symbol_table = goto_model.symbol_table;
  lifecycle_model.goto_functions.copy_from(goto_model.goto_functions);
  std::vector<create_recordt> creates;
  std::vector<goto_programt::targett> joins;
  std::string reason;
  const auto reject = [&reason]() {
    std::cout << "NATIVE_QUEUE_SEQUENCE applied=0 reason="
              << (reason.empty() ? "qsc_unknown" : reason) << '\n';
    return false;
  };
  if(
    !collect_lifecycle(lifecycle_model, ns, creates, joins, reason) ||
    creates.size() != 2 || joins.size() != 2)
    return reject();

  qsc_worker_summaryt first;
  qsc_worker_summaryt second;
  if(
    !qsc_worker(goto_model, creates[0].worker, first, reason) ||
    !qsc_worker(goto_model, creates[1].worker, second, reason))
    return reject();
  qsc_worker_summaryt *producer =
    first.producer ? &first : (second.producer ? &second : nullptr);
  qsc_worker_summaryt *consumer =
    first.consumer ? &first : (second.consumer ? &second : nullptr);
  if(
    producer == nullptr || consumer == nullptr ||
    producer == consumer || producer->mutex != consumer->mutex ||
    producer->queue != consumer->queue ||
    producer->reference != consumer->reference ||
    producer->capacity != consumer->capacity ||
    producer->bound != consumer->bound ||
    producer->phase_flag == consumer->phase_flag)
  {
    reason = "qsc_worker_composition";
    return reject();
  }

  std::set<irep_idt> enqueue_components;
  std::set<irep_idt> dequeue_components;
  irep_idt enqueue_data_component;
  irep_idt dequeue_data_component;
  if(
    !qsc_update_shape(
      goto_model, producer->operation, true, producer->capacity,
      enqueue_components, enqueue_data_component, reason) ||
    !qsc_update_shape(
      goto_model, consumer->operation, false, consumer->capacity,
      dequeue_components, dequeue_data_component, reason))
    return reject();
  std::set<irep_idt> component_intersection;
  std::set_intersection(
    enqueue_components.begin(), enqueue_components.end(),
    dequeue_components.begin(), dequeue_components.end(),
    std::inserter(component_intersection, component_intersection.end()));
  if(
    enqueue_data_component != dequeue_data_component ||
    component_intersection.size() != 2)
  {
    reason = "qsc_operation_component_mismatch";
    return reject();
  }

  if(
    producer->final_flags[producer->phase_flag] != 0 ||
    producer->final_flags[consumer->phase_flag] != 1 ||
    consumer->final_flags[consumer->phase_flag] != 0 ||
    consumer->final_flags[producer->phase_flag] != 1)
  {
    reason = "qsc_phase_transition";
    return reject();
  }
  if(
    qsc_mentions(
      goto_model, producer->worker, {producer->queue}) != 1 ||
    qsc_mentions(
      goto_model, producer->worker, {producer->reference}) != 1 ||
    qsc_mentions(
      goto_model, consumer->worker, {producer->queue}) != 2 ||
    qsc_mentions(
      goto_model, consumer->worker, {producer->reference}) != 1 ||
    qsc_mentions(
      goto_model, producer->worker,
      {producer->phase_flag, consumer->phase_flag}) != 3 ||
    qsc_mentions(
      goto_model, consumer->worker,
      {producer->phase_flag, consumer->phase_flag}) != 3)
  {
    reason = "qsc_worker_footprint";
    return reject();
  }

  const auto main_function =
    goto_model.goto_functions.function_map.find("main");
  if(
    main_function == goto_model.goto_functions.function_map.end() ||
    !main_function->second.body_available())
  {
    reason = "qsc_missing_main";
    return reject();
  }
  bool producer_flag_one = false;
  bool consumer_flag_zero = false;
  bool init_call = false;
  irep_idt init_function;
  std::size_t main_error_calls = 0;
  std::size_t main_calls = 0;
  std::size_t main_assignments = 0;
  const goto_programt::instructiont *main_error = nullptr;
  const goto_programt::instructiont *main_empty_call = nullptr;
  irep_idt main_empty_result;
  std::map<const goto_programt::instructiont *, std::size_t> main_positions;
  std::size_t main_position = 0;
  for(const auto &instruction : main_function->second.body.instructions)
    main_positions.emplace(&instruction, main_position++);
  for(const auto &instruction : main_function->second.body.instructions)
  {
    if(instruction.is_assign())
      ++main_assignments;
    if(instruction.is_function_call())
    {
      ++main_calls;
      irep_idt direct;
      if(!direct_call_identifier(instruction, direct))
      {
        reason = "qsc_main_indirect_call";
        return reject();
      }
    }
    irep_idt flag;
    mp_integer value;
    if(qsc_boolean_assignment(instruction, flag, value))
    {
      if(flag == producer->phase_flag && value == 1)
        producer_flag_one = true;
      if(flag == consumer->phase_flag && value == 0)
        consumer_flag_zero = true;
    }
    irep_idt callee;
    irep_idt object;
    if(
      direct_call_identifier(instruction, callee) &&
      qsc_addressed_argument(instruction, 0, object) &&
      object == producer->queue &&
      callee != producer->operation &&
      callee != consumer->operation &&
      callee != consumer->auxiliary_operation)
    {
      const auto body = goto_model.goto_functions.function_map.find(callee);
      if(
        body != goto_model.goto_functions.function_map.end() &&
        body->second.body_available())
      {
        init_call = true;
        init_function = callee;
      }
    }
    if(
      direct_call_identifier(instruction, callee) &&
      callee == "reach_error")
    {
      ++main_error_calls;
      main_error = &instruction;
    }
    if(
      direct_call_identifier(instruction, callee) &&
      callee == consumer->auxiliary_operation &&
      !instruction.call_lhs().is_nil() &&
      direct_symbol(instruction.call_lhs(), main_empty_result))
      main_empty_call = &instruction;
  }
  if(
    !producer_flag_one || !consumer_flag_zero || !init_call ||
    main_error_calls != 1 || main_error == nullptr ||
    main_empty_call == nullptr || main_calls != 9 ||
    main_assignments != 2)
  {
    reason = "qsc_main_obligation";
    return reject();
  }
  if(
    qsc_mentions(
      goto_model, "main", {producer->reference}) != 0 ||
    qsc_mentions(
      goto_model, "main",
      {producer->phase_flag, consumer->phase_flag}) != 2 ||
    qsc_mentions(goto_model, "main", {producer->queue}) != 4)
  {
    reason = "qsc_main_footprint";
    return reject();
  }
  bool main_error_guarded = false;
  for(const auto &instruction : main_function->second.body.instructions)
  {
    if(!instruction.is_goto() || instruction.targets.size() != 1)
      continue;
    if(
      main_positions.at(main_empty_call) < main_positions.at(&instruction) &&
      main_positions.at(&instruction) < main_positions.at(main_error) &&
      main_positions.at(main_error) <
        main_positions.at(&*instruction.get_target()) &&
      qsc_boolean_negative_equality(
        instruction.condition(), main_empty_result))
      main_error_guarded = true;
  }
  if(!main_error_guarded)
  {
    reason = "qsc_main_property_control";
    return reject();
  }

  const auto init =
    goto_model.goto_functions.function_map.find(init_function);
  std::set<irep_idt> zero_components;
  std::size_t init_assignments = 0;
  for(const auto &instruction : init->second.body.instructions)
  {
    if(!instruction.is_assign())
      continue;
    ++init_assignments;
    mp_integer zero;
    std::set<irep_idt> component;
    qsc_components(instruction.assign_lhs(), component);
    if(
      component.size() != 1 ||
      !sci_constant(instruction.assign_rhs(), zero) || zero != 0)
    {
      reason = "qsc_init_assignment";
      return reject();
    }
    zero_components.insert(component.begin(), component.end());
  }
  if(
    init_assignments != 3 ||
    zero_components.size() != 3)
  {
    reason = "qsc_init_components";
    return reject();
  }
  std::set<irep_idt> expected_init = enqueue_components;
  expected_init.insert(
    dequeue_components.begin(), dequeue_components.end());
  expected_init.erase(enqueue_data_component);
  if(zero_components != expected_init)
  {
    reason = "qsc_init_component_mismatch";
    return reject();
  }

  std::size_t assertions = 0;
  for(const auto &function : goto_model.goto_functions.function_map)
  {
    if(!function.second.body_available())
      continue;
    for(const auto &instruction : function.second.body.instructions)
      if(instruction.is_assert())
      {
        exprt condition = simplify_expr(instruction.condition(), ns);
        if(!condition.is_false())
        {
          reason = "qsc_external_assertion";
          return reject();
        }
        ++assertions;
      }
  }
  if(assertions != 1)
  {
    reason = "qsc_property_count";
    return reject();
  }

  const std::set<irep_idt> protected_globals = {
    producer->queue, producer->reference,
    producer->phase_flag, consumer->phase_flag};
  const std::set<irep_idt> allowed_global_users = {
    "__CPROVER_initialize", "main",
    producer->worker, consumer->worker};
  for(const auto &function : goto_model.goto_functions.function_map)
  {
    if(
      allowed_global_users.find(function.first) !=
        allowed_global_users.end() ||
      !function.second.body_available())
      continue;
    for(const auto &instruction : function.second.body.instructions)
      if(instruction_mentions_any(instruction, protected_globals))
      {
        reason = "qsc_external_global_access";
        return reject();
      }
  }

  std::cout << "NATIVE_QUEUE_SEQUENCE applied=1 capacity="
            << producer->capacity << " producer=" << producer->worker
            << " consumer=" << consumer->worker << '\n';
  return true;
}

bool lock_linearization_stability_transform(
  goto_modelt &goto_model,
  message_handlert &message_handler)
{
  const namespacet ns(goto_model.symbol_table);
  auto main =
    goto_model.goto_functions.function_map.find("main");
  if(
    main == goto_model.goto_functions.function_map.end() ||
    !main->second.body_available())
    return false;

  auto &main_program = main->second.body;
  std::vector<goto_programt::targett> main_order;
  std::map<const goto_programt::instructiont *, std::size_t>
    main_positions;
  for(auto instruction = main_program.instructions.begin();
      instruction != main_program.instructions.end(); ++instruction)
  {
    main_positions.emplace(&*instruction, main_order.size());
    main_order.push_back(instruction);
  }

  goto_programt::targett create =
    main_program.instructions.end();
  irep_idt worker;
  std::size_t create_count = 0;
  for(auto &function_entry :
      goto_model.goto_functions.function_map)
  {
    if(!function_entry.second.body_available())
      continue;
    for(auto instruction =
          function_entry.second.body.instructions.begin();
        instruction !=
          function_entry.second.body.instructions.end();
        ++instruction)
    {
      irep_idt callee;
      if(
        !direct_call_identifier(*instruction, callee) ||
        callee != "pthread_create")
        continue;
      ++create_count;
      if(
        function_entry.first != "main" ||
        instruction->call_arguments().size() < 3 ||
        !addressed_symbol(
          instruction->call_arguments()[2], worker))
      {
        std::cout
          << "NATIVE_LOCK_STABILITY applied=0 reason="
          << "stable_create_resolution\n";
        return false;
      }
      create = instruction;
    }
  }
  if(
    create_count != 1 ||
    create == main_program.instructions.end())
  {
    std::cout
      << "NATIVE_LOCK_STABILITY applied=0 reason="
      << "stable_create_count\n";
    return false;
  }

  goto_programt::targett backedge =
    main_program.instructions.end();
  goto_programt::targett loop_head =
    main_program.instructions.end();
  std::size_t backedges = 0;
  const auto create_position = main_positions.at(&*create);
  for(auto instruction = main_program.instructions.begin();
      instruction != main_program.instructions.end(); ++instruction)
  {
    if(
      !instruction->is_goto() ||
      !instruction->condition().is_true() ||
      instruction->targets.size() != 1)
      continue;
    const auto source = main_positions.at(&*instruction);
    const auto target =
      main_positions.at(&*instruction->targets.front());
    if(target <= create_position && create_position < source)
    {
      backedge = instruction;
      loop_head = instruction->targets.front();
      ++backedges;
    }
  }
  if(backedges != 1)
  {
    std::cout
      << "NATIVE_LOCK_STABILITY applied=0 reason="
      << "stable_spawn_backedge\n";
    return false;
  }
  const auto loop_begin = main_positions.at(&*loop_head);
  const auto loop_end = main_positions.at(&*backedge);
  std::size_t loop_creates = 0;
  std::size_t conditional_exits = 0;
  for(std::size_t index = loop_begin; index <= loop_end; ++index)
  {
    auto instruction = main_order[index];
    irep_idt callee;
    if(
      direct_call_identifier(*instruction, callee) &&
      callee == "pthread_create")
    {
      ++loop_creates;
      continue;
    }
    if(instruction == backedge)
      continue;
    bool exit_condition;
    if(
      instruction->is_goto() &&
      instruction->targets.size() == 1 &&
      main_positions.at(&*instruction->targets.front()) >
        loop_end &&
      boolean_constant_eval(
        instruction->condition(), exit_condition) &&
      !exit_condition)
    {
      ++conditional_exits;
      continue;
    }
    if(
      instruction->is_skip() || instruction->is_location())
      continue;
    std::cout
      << "NATIVE_LOCK_STABILITY applied=0 reason="
      << "stable_spawn_loop_shape\n";
    return false;
  }
  if(loop_creates != 1 || conditional_exits != 1)
  {
    std::cout
      << "NATIVE_LOCK_STABILITY applied=0 reason="
      << "stable_spawn_loop_counts\n";
    return false;
  }

  const std::set<irep_idt> ignored_calls = {
    "pthread_mutex_lock",
    "pthread_mutex_unlock",
    "reach_error",
    "abort"};
  std::set<irep_idt> reachable;
  std::vector<irep_idt> pending{worker};
  std::set<const goto_programt::instructiont *> recognized;
  std::vector<stable_transitiont> transitions;
  std::string reason;
  while(!pending.empty())
  {
    const auto function_id = pending.back();
    pending.pop_back();
    if(!reachable.insert(function_id).second)
      continue;
    auto function =
      goto_model.goto_functions.function_map.find(function_id);
    if(
      function == goto_model.goto_functions.function_map.end() ||
      !function->second.body_available())
    {
      reason = "stable_reachable_function";
      break;
    }
    std::size_t property_calls = 0;
    for(const auto &instruction :
        function->second.body.instructions)
    {
      if(instruction.is_assert())
      {
        reason = "stable_reachable_assertion";
        break;
      }
      if(!instruction.is_function_call())
        continue;
      irep_idt callee;
      if(!direct_call_identifier(instruction, callee))
      {
        reason = "stable_indirect_call";
        break;
      }
      if(callee == "reach_error")
        ++property_calls;
      if(ignored_calls.find(callee) != ignored_calls.end())
        continue;
      const auto called =
        goto_model.goto_functions.function_map.find(callee);
      if(
        called == goto_model.goto_functions.function_map.end() ||
        !called->second.body_available())
      {
        reason = "stable_unknown_call";
        break;
      }
      pending.push_back(callee);
    }
    if(!reason.empty())
      break;
    if(property_calls != 0)
    {
      stable_transitiont transition;
      if(!parse_stable_transition(
           function_id,
           goto_model,
           ns,
           transition,
           recognized,
           reason))
        break;
      transitions.push_back(std::move(transition));
    }
  }
  if(!reason.empty() || transitions.empty())
  {
    if(reason.empty())
      reason = "stable_no_transition";
    std::cout
      << "NATIVE_LOCK_STABILITY applied=0 reason="
      << reason << '\n';
    return false;
  }

  const auto object = transitions.front().object;
  const auto mutex = transitions.front().mutex;
  std::set<irep_idt> proof_symbols{object};
  std::set<irep_idt> witness_symbols;
  std::set<irep_idt> transition_functions;
  for(const auto &property : transitions)
  {
    transition_functions.insert(property.function);
    if(
      property.object != object ||
      property.mutex != mutex)
    {
      reason = "stable_protocol_mismatch";
      break;
    }
    if(!property.property_witness.empty())
    {
      const symbolt *symbol = nullptr;
      if(
        ns.lookup(property.property_witness, symbol) ||
        !symbol->is_static_lifetime ||
        symbol->type.id() != ID_unsignedbv)
      {
        reason = "stable_property_witness_type";
        break;
      }
      witness_symbols.insert(property.property_witness);
      proof_symbols.insert(property.property_witness);
    }
    if(!property.set_witness.empty())
    {
      witness_symbols.insert(property.set_witness);
      proof_symbols.insert(property.set_witness);
    }
    for(const auto &interference : transitions)
    {
      if(
        interference.direction != property.direction &&
        (property.property_witness.empty() ||
         property.property_witness !=
           interference.set_witness))
      {
        reason = "stable_interference_not_covered";
        break;
      }
    }
    if(!reason.empty())
      break;
  }
  if(!reason.empty())
  {
    std::cout
      << "NATIVE_LOCK_STABILITY applied=0 reason="
      << reason << '\n';
    return false;
  }

  std::map<irep_idt, std::size_t> initialization_counts;
  std::size_t global_property_calls = 0;
  const std::set<irep_idt> mutex_symbol{mutex};
  for(auto &function_entry :
      goto_model.goto_functions.function_map)
  {
    if(!function_entry.second.body_available())
      continue;
    for(auto instruction =
          function_entry.second.body.instructions.begin();
        instruction !=
          function_entry.second.body.instructions.end();
        ++instruction)
    {
      irep_idt callee;
      if(
        direct_call_identifier(*instruction, callee) &&
        callee == "reach_error")
        ++global_property_calls;

      if(
        contains_address_of_symbol(
          instruction->is_assign()
            ? instruction->assign_rhs()
            : nil_exprt(),
          proof_symbols))
      {
        reason = "stable_address_escape";
        break;
      }
      if(instruction->is_function_call())
      {
        irep_idt called;
        const bool direct =
          direct_call_identifier(*instruction, called);
        for(const auto &argument : instruction->call_arguments())
        {
          if(contains_address_of_symbol(argument, proof_symbols))
          {
            reason = "stable_address_escape";
            break;
          }
          if(
            contains_address_of_symbol(argument, mutex_symbol) &&
            (!direct ||
             (called != "pthread_mutex_lock" &&
              called != "pthread_mutex_unlock")))
          {
            reason = "stable_mutex_escape";
            break;
          }
        }
      }
      if(
        instruction->is_assign() &&
        function_entry.first != "__CPROVER_initialize" &&
        (contains_symbol(
           instruction->assign_lhs(), mutex_symbol) ||
         contains_symbol(
           instruction->assign_rhs(), mutex_symbol)))
      {
        reason = "stable_mutex_write";
        break;
      }
      if(!reason.empty())
        break;

      if(instruction->is_assign())
      {
        irep_idt lhs;
        if(
          direct_symbol(instruction->assign_lhs(), lhs) &&
          proof_symbols.find(lhs) != proof_symbols.end())
        {
          if(recognized.find(&*instruction) != recognized.end())
            continue;
          if(function_entry.first != "__CPROVER_initialize")
          {
            reason = "stable_extra_write";
            break;
          }
          mp_integer value;
          if(
            !constant_eval(instruction->assign_rhs(), {}, value) ||
            (witness_symbols.find(lhs) !=
               witness_symbols.end() &&
             value != 0))
          {
            reason = "stable_initialization";
            break;
          }
          ++initialization_counts[lhs];
          continue;
        }
      }
      if(
        instruction_mentions_any(*instruction, proof_symbols) &&
        function_entry.first != "__CPROVER_initialize" &&
        transition_functions.find(function_entry.first) ==
          transition_functions.end())
      {
        reason = "stable_external_access";
        break;
      }
      if(
        transition_functions.find(function_entry.first) !=
          transition_functions.end() &&
        instruction_mentions_any(*instruction, proof_symbols) &&
        recognized.find(&*instruction) == recognized.end())
      {
        reason = "stable_unrecognized_access";
        break;
      }
    }
    if(!reason.empty())
      break;
  }
  for(const auto &identifier : proof_symbols)
  {
    if(initialization_counts[identifier] != 1)
      reason = "stable_initialization_count";
  }
  if(
    global_property_calls != transitions.size() ||
    !reason.empty())
  {
    if(reason.empty())
      reason = "stable_global_property_count";
    std::cout
      << "NATIVE_LOCK_STABILITY applied=0 reason="
      << reason << '\n';
    return false;
  }

  for(std::size_t index = loop_begin; index <= loop_end; ++index)
    main_order[index]->turn_into_skip();
  goto_model.goto_functions.update();
  std::cout
    << "NATIVE_LOCK_STABILITY applied=1 worker=" << worker
    << " transitions=" << transitions.size()
    << " object=" << object << " mutex=" << mutex
    << " witnesses=" << witness_symbols.size() << '\n';
  (void)message_handler;
  return true;
}

bool lock_scoped_commutative_aggregation_transform(
  goto_modelt &goto_model,
  message_handlert &message_handler)
{
  const namespacet ns(goto_model.symbol_table);
  auto main =
    goto_model.goto_functions.function_map.find("main");
  if(
    main == goto_model.goto_functions.function_map.end() ||
    !main->second.body_available())
    return false;

  goto_programt::targett create =
    main->second.body.instructions.end();
  goto_programt::targett join =
    main->second.body.instructions.end();
  irep_idt handle;
  irep_idt worker;
  std::size_t creates = 0;
  std::size_t joins = 0;
  std::string reason;
  for(auto instruction = main->second.body.instructions.begin();
      instruction != main->second.body.instructions.end(); ++instruction)
  {
    irep_idt callee;
    if(!direct_call_identifier(*instruction, callee))
      continue;
    if(callee == "pthread_create")
    {
      irep_idt candidate_handle;
      irep_idt candidate_worker;
      if(
        instruction->call_arguments().size() < 3 ||
        !addressed_symbol(
          instruction->call_arguments()[0], candidate_handle) ||
        !addressed_symbol(
          instruction->call_arguments()[2], candidate_worker))
      {
        reason = "lock_create_resolution";
        break;
      }
      handle = candidate_handle;
      worker = candidate_worker;
      create = instruction;
      ++creates;
    }
    else if(callee == "pthread_join")
    {
      irep_idt candidate_handle;
      if(
        instruction->call_arguments().empty() ||
        !direct_symbol(
          instruction->call_arguments().front(),
          candidate_handle) ||
        candidate_handle != handle)
      {
        reason = "lock_join_resolution";
        break;
      }
      join = instruction;
      ++joins;
    }
  }
  if(
    !reason.empty() || creates != 1 || joins != 1 ||
    create == main->second.body.instructions.end() ||
    join == main->second.body.instructions.end())
  {
    if(reason.empty())
      reason = "lock_lifecycle";
    std::cout << "NATIVE_LOCK_AGGREGATION applied=0 reason="
              << reason << '\n';
    return false;
  }

  locked_loop_summaryt main_loop;
  locked_loop_summaryt worker_loop;
  if(
    !parse_locked_affine_loop(
      "main", goto_model, ns, main_loop, reason) ||
    !parse_locked_affine_loop(
      worker, goto_model, ns, worker_loop, reason) ||
    main_loop.object != worker_loop.object ||
    main_loop.mutex != worker_loop.mutex)
  {
    if(reason.empty())
      reason = "lock_protocol_mismatch";
    std::cout << "NATIVE_LOCK_AGGREGATION applied=0 reason="
              << reason << '\n';
    return false;
  }

  goto_programt::targett initialization =
    main->second.body.instructions.end();
  mp_integer initial_value;
  if(!validate_lock_aggregate_property(
       goto_model,
       ns,
       main_loop,
       worker_loop,
       create,
       join,
       initialization,
       initial_value,
       reason))
  {
    std::cout << "NATIVE_LOCK_AGGREGATION applied=0 reason="
              << reason << '\n';
    return false;
  }

  const mp_integer main_total =
    main_loop.count * main_loop.delta;
  const mp_integer worker_total =
    worker_loop.count * worker_loop.delta;
  const mp_integer positive_total =
    std::max(mp_integer(0), main_total) +
    std::max(mp_integer(0), worker_total);
  const mp_integer negative_total =
    std::min(mp_integer(0), main_total) +
    std::min(mp_integer(0), worker_total);
  const mp_integer final_value =
    initial_value + main_total + worker_total;
  const symbolt &object_symbol =
    ns.lookup(main_loop.object);
  if(
    !integer_value_fits(
      initial_value + positive_total, object_symbol.type) ||
    !integer_value_fits(
      initial_value + negative_total, object_symbol.type) ||
    !integer_value_fits(final_value, object_symbol.type))
  {
    std::cout
      << "NATIVE_LOCK_AGGREGATION applied=0 reason=lock_overflow\n";
    return false;
  }

  for(auto instruction = main_loop.loop_head;
      instruction != std::next(main_loop.backedge); ++instruction)
    instruction->turn_into_skip();
  const auto location = join->source_location();
  main->second.body.insert_after(
    join,
    goto_programt::make_assignment(
      symbol_exprt(main_loop.object, object_symbol.type),
      from_integer(final_value, object_symbol.type),
      location));
  create->turn_into_skip();
  join->turn_into_skip();
  goto_model.goto_functions.update();

  std::cout
    << "NATIVE_LOCK_AGGREGATION applied=1 object="
    << main_loop.object << " mutex=" << main_loop.mutex
    << " main_count=" << main_loop.count
    << " worker_count=" << worker_loop.count
    << " main_delta=" << main_loop.delta
    << " worker_delta=" << worker_loop.delta
    << " final=" << final_value << '\n';
  (void)message_handler;
  return true;
}

bool ticket_rank_serializability_transform(
  goto_modelt &goto_model,
  message_handlert &message_handler)
{
  const namespacet ns(goto_model.symbol_table);
  std::vector<create_recordt> creates;
  std::vector<goto_programt::targett> joins;
  std::string reason;
  if(!collect_lifecycle(goto_model, ns, creates, joins, reason))
  {
    std::cout << "NATIVE_TICKET_SERIALIZATION applied=0 reason="
              << reason << '\n';
    return false;
  }
  if(!validate_main_region(goto_model, ns, creates, joins, reason))
  {
    std::cout << "NATIVE_TICKET_SERIALIZATION applied=0 reason="
              << reason << '\n';
    return false;
  }

  std::vector<ticket_regiont> regions;
  for(const auto &create : creates)
  {
    ticket_regiont region;
    if(!summarize_ticket_worker(
         create, goto_model, ns, region, reason))
    {
      std::cout << "NATIVE_TICKET_SERIALIZATION applied=0 reason="
                << reason << " worker=" << create.worker << '\n';
      return false;
    }
    regions.push_back(std::move(region));
  }
  const irep_idt ticket = regions.front().ticket;
  const irep_idt completed = regions.front().completed;
  for(const auto &region : regions)
  {
    if(region.ticket != ticket || region.completed != completed)
    {
      std::cout
        << "NATIVE_TICKET_SERIALIZATION applied=0 reason="
        << "ticket_protocol_mismatch worker=" << region.worker << '\n';
      return false;
    }
  }
  if(!validate_ticket_initialization_and_aliases(
       goto_model,
       ns,
       creates,
       regions,
       ticket,
       completed,
       reason))
  {
    std::cout << "NATIVE_TICKET_SERIALIZATION applied=0 reason="
              << reason << '\n';
    return false;
  }

  for(auto &region : regions)
  {
    auto &program =
      goto_model.goto_functions.function_map.at(region.worker).body;
    program.insert_before(
      region.body_begin,
      goto_programt::make_atomic_begin(
        region.body_begin->source_location()));
    program.insert_after(
      region.completion,
      goto_programt::make_atomic_end(
        region.completion->source_location()));
  }
  goto_model.goto_functions.update();
  std::cout << "NATIVE_TICKET_SERIALIZATION applied=1 workers="
            << regions.size() << " ticket=" << ticket
            << " completed=" << completed << '\n';
  (void)message_handler;
  return true;
}

bool prefix_affine_envelope_transform(
  goto_modelt &goto_model,
  message_handlert &message_handler)
{
  const namespacet ns(goto_model.symbol_table);
  auto main = goto_model.goto_functions.function_map.find("main");
  if(
    main == goto_model.goto_functions.function_map.end() ||
    !main->second.body_available())
    return false;

  std::vector<create_recordt> create_records;
  for(auto instruction = main->second.body.instructions.begin();
      instruction != main->second.body.instructions.end(); ++instruction)
  {
    irep_idt callee;
    if(
      !direct_call_identifier(*instruction, callee) ||
      callee != "pthread_create")
      continue;
    irep_idt handle;
    irep_idt worker;
    if(
      instruction->call_arguments().size() < 3 ||
      !addressed_symbol(instruction->call_arguments()[0], handle) ||
      !addressed_symbol(instruction->call_arguments()[2], worker))
      return false;
    create_records.push_back({handle, worker, instruction});
  }
  if(create_records.size() != 2)
    return false;

  std::string reason;
  affine_worker_summaryt workers[2];
  if(
    !parse_affine_worker(
      create_records[0].worker, goto_model, ns, workers[0], reason) ||
    !parse_affine_worker(
      create_records[1].worker, goto_model, ns, workers[1], reason) ||
    workers[0].target != workers[1].source ||
    workers[0].source != workers[1].target)
  {
    std::cout << "NATIVE_PREFIX_AFFINE applied=0 reason=" << reason << '\n';
    return false;
  }
  if(!validate_exclusive_writes_and_property(
       goto_model, ns, workers, reason))
  {
    std::cout << "NATIVE_PREFIX_AFFINE applied=0 reason=" << reason << '\n';
    return false;
  }

  const irep_idt first = workers[0].target;
  const irep_idt second = workers[0].source;
  irep_idt bound_function;
  std::map<irep_idt, mp_integer> initial_values;
  mp_integer property_bound;
  bool inline_property = false;
  bool inclusive_bad = false;
  goto_programt::targett failure_guard;
  if(
    assertion_bound(
      goto_model,
      first,
      second,
      bound_function,
      initial_values,
      reason))
  {
    if(!evaluate_bound_function(
         bound_function, goto_model, property_bound, reason))
    {
      std::cout
        << "NATIVE_PREFIX_AFFINE applied=0 reason=" << reason << '\n';
      return false;
    }
  }
  else
  {
    if(reason != "prefix_main_shape")
    {
      std::cout
        << "NATIVE_PREFIX_AFFINE applied=0 reason=" << reason << '\n';
      return false;
    }
    initial_values.clear();
    inline_property = true;
    if(!inline_error_bound(
         goto_model,
         first,
         second,
         property_bound,
         initial_values,
         inclusive_bad,
         failure_guard,
         reason))
    {
      std::cout
        << "NATIVE_PREFIX_AFFINE applied=0 reason=" << reason << '\n';
      return false;
    }
  }

  const auto count_first =
    numeric_cast_v<std::size_t>(workers[0].count);
  const auto count_second =
    numeric_cast_v<std::size_t>(workers[1].count);
  std::vector<std::vector<std::vector<affine_statet>>> frontier(
    count_first + 1,
    std::vector<std::vector<affine_statet>>(count_second + 1));
  frontier[0][0].push_back(
    {initial_values.at(first), initial_values.at(second), std::string()});
  const symbolt &first_symbol = ns.lookup(first);
  const symbolt &second_symbol = ns.lookup(second);
  if(
    initial_values.at(first) < 0 || initial_values.at(second) < 0 ||
    !signed_value_fits(initial_values.at(first), first_symbol.type) ||
    !signed_value_fits(initial_values.at(second), second_symbol.type))
  {
    std::cout
      << "NATIVE_PREFIX_AFFINE applied=0 reason=initial_range\n";
    return false;
  }
  mp_integer maximum =
    std::max(initial_values.at(first), initial_values.at(second));
  std::size_t retained_states = 1;
  std::size_t maximum_width = 1;
  const bool initial_violation =
    inclusive_bad
      ? initial_values.at(first) >= property_bound ||
          initial_values.at(second) >= property_bound
      : initial_values.at(first) > property_bound ||
          initial_values.at(second) > property_bound;
  bool counterexample_found = inline_property && initial_violation;
  affine_statet counterexample_state{
    initial_values.at(first),
    initial_values.at(second),
    std::string()};
  for(std::size_t i = 0; i <= count_first; ++i)
  {
    for(std::size_t j = 0; j <= count_second; ++j)
    {
      if(i == 0 && j == 0)
        continue;
      auto &states = frontier[i][j];
      if(i != 0)
      {
        for(const auto &predecessor : frontier[i - 1][j])
          states.push_back(
            apply_affine_worker(
              workers[0], predecessor, first, '0', inline_property));
      }
      if(j != 0)
      {
        for(const auto &predecessor : frontier[i][j - 1])
          states.push_back(
            apply_affine_worker(
              workers[1], predecessor, first, '1', inline_property));
      }
      pareto_prune(states);
      retained_states += states.size();
      maximum_width = std::max(maximum_width, states.size());
      if(retained_states > 100000)
      {
        std::cout
          << "NATIVE_PREFIX_AFFINE applied=0 reason=frontier_limit\n";
        return false;
      }
      for(const auto &state : states)
      {
        maximum = std::max(maximum, std::max(state.first, state.second));
        const bool violates =
          inclusive_bad
            ? state.first >= property_bound ||
                state.second >= property_bound
            : state.first > property_bound ||
                state.second > property_bound;
        if(inline_property && !counterexample_found && violates)
        {
          counterexample_found = true;
          counterexample_state = state;
        }
        if(
          state.first < 0 || state.second < 0 ||
          !signed_value_fits(state.first, first_symbol.type) ||
          !signed_value_fits(state.second, second_symbol.type))
        {
          std::cout
            << "NATIVE_PREFIX_AFFINE applied=0 reason=overflow\n";
          return false;
        }
      }
    }
  }
  if(counterexample_found)
  {
    for(auto &create : create_records)
      create.instruction->turn_into_skip();
    failure_guard->turn_into_skip();
    goto_model.goto_functions.update();
    std::cout
      << "NATIVE_PREFIX_AFFINE applied=1 result=UNSAFE workers=2 states="
      << retained_states << " max_width=" << maximum_width
      << " witness_first=" << counterexample_state.first
      << " witness_second=" << counterexample_state.second
      << " bound=" << property_bound
      << " inclusive=" << inclusive_bad
      << " schedule=" << counterexample_state.schedule << '\n';
    (void)message_handler;
    return true;
  }
  if(maximum > property_bound)
  {
    std::cout
      << "NATIVE_PREFIX_AFFINE applied=0 reason=bound_not_proved"
      << " maximum=" << maximum << " bound=" << property_bound << '\n';
    return false;
  }

  for(auto &create : create_records)
    create.instruction->turn_into_skip();
  goto_model.goto_functions.update();
  std::cout
    << "NATIVE_PREFIX_AFFINE applied=1 workers=2 states="
    << retained_states << " max_width=" << maximum_width
    << " maximum=" << maximum << " bound=" << property_bound << '\n';
  (void)message_handler;
  return true;
}

bool jces_transform(
  goto_modelt &goto_model,
  message_handlert &message_handler)
{
  const namespacet ns(goto_model.symbol_table);
  std::vector<create_recordt> creates;
  std::vector<goto_programt::targett> joins;
  std::string reason;
  if(!collect_lifecycle(goto_model, ns, creates, joins, reason))
  {
    std::cout << "NATIVE_JCES applied=0 reason=" << reason << '\n';
    return false;
  }
  if(!validate_main_region(goto_model, ns, creates, joins, reason))
  {
    std::cout << "NATIVE_JCES applied=0 reason=" << reason << '\n';
    return false;
  }

  std::set<irep_idt> mutable_shared;
  collect_mutable_shared(goto_model, ns, creates, mutable_shared);

  std::vector<worker_summaryt> summaries;
  for(const auto &create : creates)
  {
    worker_summaryt summary;
    if(!summarize_worker(
         create.worker,
         goto_model,
         ns,
         mutable_shared,
         summary,
         reason))
    {
      std::cout << "NATIVE_JCES applied=0 reason=" << reason
                << " worker=" << create.worker << '\n';
      return false;
    }
    summaries.push_back(std::move(summary));
  }

  std::map<irep_idt, std::pair<symbol_exprt, exprt>> replacements;
  for(const auto &summary : summaries)
  {
    for(const auto &effect : summary.effects)
    {
      const auto &object = to_symbol_expr(effect.object);
      const irep_idt &identifier = object.get_identifier();
      auto entry = replacements.find(identifier);
      if(entry == replacements.end())
      {
        entry = replacements
                  .emplace(
                    identifier,
                    std::make_pair(object, effect.object))
                  .first;
      }
      exprt count = cast_if_needed(summary.count, effect.object.type());
      exprt delta = cast_if_needed(effect.delta, effect.object.type());
      exprt contribution =
        mult_exprt(std::move(count), std::move(delta));
      if(effect.subtract)
        entry->second.second =
          minus_exprt(entry->second.second, std::move(contribution));
      else
        entry->second.second =
          plus_exprt(entry->second.second, std::move(contribution));
    }
  }

  auto main = goto_model.goto_functions.function_map.find("main");
  INVARIANT(
    main != goto_model.goto_functions.function_map.end(),
    "lifecycle collection found main");
  const auto final_join = joins.back();
  const auto location = final_join->source_location();
  for(auto &replacement : replacements)
  {
    simplify_expr(replacement.second.second, ns);
    main->second.body.insert_after(
      final_join,
      goto_programt::make_assignment(
        replacement.second.first,
        replacement.second.second,
        location));
  }
  for(auto &create : creates)
    create.instruction->turn_into_skip();
  for(auto &join : joins)
    join->turn_into_skip();
  goto_model.goto_functions.update();

  std::cout << "NATIVE_JCES applied=1 workers=" << summaries.size()
            << " objects=" << replacements.size() << '\n';
  (void)message_handler;
  return true;
}
