/*******************************************************************\

Module: Join-Scoped Compositional Effect Summary

\*******************************************************************/

#include "jces_analysis.h"

#include <goto-programs/goto_model.h>

#include <util/arith_tools.h>
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
#include <iostream>
#include <iterator>
#include <map>
#include <set>
#include <string>
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
} // namespace

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
