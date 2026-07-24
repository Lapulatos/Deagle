/*******************************************************************\

Module: CAS Linearization Stability

\*******************************************************************/

#include "cas_stability_analysis.h"

#include <goto-programs/goto_model.h>

#include <util/arith_tools.h>
#include <util/bitvector_types.h>
#include <util/expr_util.h>
#include <util/message.h>
#include <util/namespace.h>
#include <util/pointer_expr.h>
#include <util/std_code.h>
#include <util/std_expr.h>

#include <iostream>
#include <map>
#include <set>
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

bool addressed_id(const exprt &src, irep_idt &identifier)
{
  const exprt &expr = strip(src);
  if(expr.id() != ID_address_of)
    return false;
  return symbol_id(to_address_of_expr(expr).object(), identifier);
}

bool dereferenced_id(const exprt &src, irep_idt &identifier)
{
  const exprt &expr = strip(src);
  if(expr.id() != ID_dereference)
    return false;
  return symbol_id(to_dereference_expr(expr).pointer(), identifier);
}

bool call_id(
  const goto_programt::instructiont &instruction,
  irep_idt &identifier)
{
  if(!instruction.is_function_call())
    return false;
  return symbol_id(instruction.call_function(), identifier);
}

bool integer_constant(const exprt &src, mp_integer &value)
{
  const exprt &expr = strip(src);
  if(expr.id() == ID_constant)
    return !to_integer(to_constant_expr(expr), value);
  if(
    (expr.id() == ID_plus || expr.id() == ID_minus) &&
    expr.operands().size() == 2)
  {
    mp_integer lhs;
    mp_integer rhs;
    if(
      !integer_constant(expr.op0(), lhs) ||
      !integer_constant(expr.op1(), rhs))
      return false;
    value =
      expr.id() == ID_plus ? lhs + rhs : lhs - rhs;
    return true;
  }
  return false;
}

bool zero(const exprt &expr)
{
  mp_integer value;
  return integer_constant(expr, value) && value == 0;
}

bool one(const exprt &expr)
{
  mp_integer value;
  return integer_constant(expr, value) && value == 1;
}

bool contains_id(
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
    if(contains_id(operand, identifiers))
      return true;
  }
  return false;
}

bool contains_address(
  const exprt &expr,
  const std::set<irep_idt> &identifiers)
{
  if(expr.id() == ID_address_of)
  {
    irep_idt identifier;
    if(
      addressed_id(expr, identifier) &&
      identifiers.find(identifier) != identifiers.end())
      return true;
  }
  for(const auto &operand : expr.operands())
  {
    if(contains_address(operand, identifiers))
      return true;
  }
  return false;
}

bool mentions(
  const goto_programt::instructiont &instruction,
  const std::set<irep_idt> &identifiers)
{
  if(instruction.is_assign())
    return
      contains_id(instruction.assign_lhs(), identifiers) ||
      contains_id(instruction.assign_rhs(), identifiers);
  if(instruction.is_goto() || instruction.is_assume() ||
     instruction.is_assert())
    return contains_id(instruction.condition(), identifiers);
  if(instruction.is_function_call())
  {
    for(const auto &argument : instruction.call_arguments())
    {
      if(contains_id(argument, identifiers))
        return true;
    }
  }
  if(instruction.is_set_return_value())
    return contains_id(instruction.return_value(), identifiers);
  return false;
}

bool shared_unsigned(
  const irep_idt &identifier,
  const namespacet &ns)
{
  const symbolt *symbol = nullptr;
  return
    !ns.lookup(identifier, symbol) &&
    symbol->is_static_lifetime && !symbol->is_type &&
    symbol->type.id() == ID_unsignedbv;
}

bool local_unsigned_like(
  const irep_idt &identifier,
  const typet &type,
  const namespacet &ns)
{
  const symbolt *symbol = nullptr;
  return
    !ns.lookup(identifier, symbol) &&
    !symbol->is_static_lifetime &&
    symbol->type == type;
}

bool parse_nonzero(
  const exprt &src,
  irep_idt &identifier)
{
  const exprt &expr = strip(src);
  if(expr.id() != ID_notequal || expr.operands().size() != 2)
    return false;
  return
    (symbol_id(expr.op0(), identifier) && zero(expr.op1())) ||
    (symbol_id(expr.op1(), identifier) && zero(expr.op0()));
}

bool parse_relation(
  const exprt &src,
  irep_idt &object,
  irep_idt &snapshot,
  irep_idt &witness,
  int &direction)
{
  const exprt &expr = strip(src);
  const auto parse_comparison =
    [&](const exprt &candidate) -> bool
    {
      const exprt &comparison = strip(candidate);
      if(
        (comparison.id() != ID_gt &&
         comparison.id() != ID_lt) ||
        comparison.operands().size() != 2 ||
        !symbol_id(comparison.op0(), object) ||
        !symbol_id(comparison.op1(), snapshot))
        return false;
      direction = comparison.id() == ID_gt ? 1 : -1;
      return true;
    };
  if(parse_comparison(expr))
  {
    witness.clear();
    return true;
  }
  if(expr.id() != ID_or || expr.operands().size() != 2)
    return false;
  return
    (parse_nonzero(expr.op0(), witness) &&
     parse_comparison(expr.op1())) ||
    (parse_nonzero(expr.op1(), witness) &&
     parse_comparison(expr.op0()));
}

bool boolean_constant(const exprt &src, bool &value)
{
  const exprt &expr = strip(src);
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
    if(!boolean_constant(expr.op0(), value))
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
      !integer_constant(expr.op0(), lhs) ||
      !integer_constant(expr.op1(), rhs))
      return false;
    value =
      expr.id() == ID_equal ? lhs == rhs : lhs != rhs;
    return true;
  }
  return false;
}

bool parse_result_test(
  const exprt &src,
  const irep_idt &result)
{
  const exprt &expr = strip(src);
  if(expr.id() != ID_equal || expr.operands().size() != 2)
    return false;
  irep_idt candidate;
  return
    (symbol_id(expr.op0(), candidate) &&
     candidate == result && zero(expr.op1())) ||
    (symbol_id(expr.op1(), candidate) &&
     candidate == result && zero(expr.op0()));
}

struct propertyt
{
  irep_idt function;
  irep_idt object;
  irep_idt snapshot;
  irep_idt witness;
  int direction = 0;
  goto_programt::targett guard;
  goto_programt::targett error;
};

bool parse_property_function(
  const irep_idt &function_id,
  goto_modelt &model,
  const namespacet &ns,
  propertyt &property,
  std::set<const goto_programt::instructiont *> &recognized,
  std::string &reason,
  const bool strict_body)
{
  auto function = model.goto_functions.function_map.find(function_id);
  if(
    function == model.goto_functions.function_map.end() ||
    !function->second.body_available())
  {
    reason = "cas_property_function";
    return false;
  }
  auto &program = function->second.body;
  std::vector<goto_programt::targett> order;
  std::map<const goto_programt::instructiont *, std::size_t> position;
  for(auto instruction = program.instructions.begin();
      instruction != program.instructions.end(); ++instruction)
  {
    position.emplace(&*instruction, order.size());
    order.push_back(instruction);
  }
  goto_programt::targett error = program.instructions.end();
  std::size_t errors = 0;
  for(auto instruction = program.instructions.begin();
      instruction != program.instructions.end(); ++instruction)
  {
    irep_idt callee;
    if(call_id(*instruction, callee) && callee == "reach_error")
    {
      error = instruction;
      ++errors;
    }
  }
  if(errors != 1 || position.at(&*error) == 0)
  {
    reason = "cas_property_count";
    return false;
  }
  auto guard = order[position.at(&*error) - 1];
  if(
    !guard->is_goto() || guard->targets.size() != 1 ||
    !parse_relation(
      guard->condition(),
      property.object,
      property.snapshot,
      property.witness,
      property.direction) ||
    !shared_unsigned(property.object, ns))
  {
    reason = "cas_property_schema";
    return false;
  }
  const symbolt *object_symbol = nullptr;
  ns.lookup(property.object, object_symbol);
  if(
    !local_unsigned_like(
      property.snapshot, object_symbol->type, ns))
  {
    reason = "cas_property_snapshot";
    return false;
  }
  int atomic_depth = 0;
  for(std::size_t index = 0;
      index < position.at(&*guard); ++index)
  {
    if(order[index]->is_atomic_begin())
      ++atomic_depth;
    else if(order[index]->is_atomic_end())
      --atomic_depth;
  }
  if(atomic_depth <= 0)
  {
    reason = "cas_property_atomic";
    return false;
  }
  for(const auto &instruction : program.instructions)
  {
    if(strict_body && instruction.is_assign())
    {
      reason = "cas_property_write";
      return false;
    }
    if(
      strict_body &&
      instruction.is_goto() && &instruction != &*guard)
    {
      reason = "cas_property_control";
      return false;
    }
  }
  if(strict_body)
  {
    const symbolt &function_symbol = ns.lookup(function_id);
    const auto &parameters =
      to_code_type(function_symbol.type).parameters();
    if(
      parameters.size() != 1 ||
      parameters.front().get_identifier() != property.snapshot)
    {
      reason = "cas_property_parameter";
      return false;
    }
  }
  property.function = function_id;
  property.guard = guard;
  property.error = error;
  recognized.insert(&*guard);
  recognized.insert(&*error);
  return true;
}

struct cas_transitiont
{
  irep_idt function;
  irep_idt cas_function;
  irep_idt property_function;
  irep_idt object;
  irep_idt snapshot;
  irep_idt desired;
  irep_idt result;
  irep_idt set_witness;
  irep_idt property_witness;
  int direction = 0;
  goto_programt::targett cas_call;
  goto_programt::targett property_call;
};

bool parse_desired_assignment(
  const goto_programt::instructiont &instruction,
  const irep_idt &desired,
  const irep_idt &snapshot,
  int &direction)
{
  if(!instruction.is_assign())
    return false;
  irep_idt lhs;
  if(!symbol_id(instruction.assign_lhs(), lhs) ||
     lhs != desired)
    return false;
  const exprt &rhs = strip(instruction.assign_rhs());
  if(
    (rhs.id() != ID_plus && rhs.id() != ID_minus) ||
    rhs.operands().size() != 2)
    return false;
  irep_idt source;
  if(
    !symbol_id(rhs.op0(), source) || source != snapshot ||
    !one(rhs.op1()))
    return false;
  direction = rhs.id() == ID_plus ? 1 : -1;
  return true;
}

bool parse_transition(
  const irep_idt &function_id,
  goto_modelt &model,
  const namespacet &ns,
  cas_transitiont &transition,
  propertyt &property,
  std::set<const goto_programt::instructiont *> &recognized,
  std::string &reason)
{
  auto function = model.goto_functions.function_map.find(function_id);
  auto &program = function->second.body;
  std::vector<goto_programt::targett> order;
  std::map<const goto_programt::instructiont *, std::size_t> position;
  for(auto instruction = program.instructions.begin();
      instruction != program.instructions.end(); ++instruction)
  {
    position.emplace(&*instruction, order.size());
    order.push_back(instruction);
  }

  goto_programt::targett cas_call = program.instructions.end();
  std::size_t cas_calls = 0;
  for(auto instruction = program.instructions.begin();
      instruction != program.instructions.end(); ++instruction)
  {
    irep_idt callee;
    if(
      !call_id(*instruction, callee) ||
      instruction->call_arguments().size() < 4 ||
      instruction->call_arguments().size() > 5)
      continue;
    irep_idt object;
    irep_idt snapshot;
    irep_idt desired;
    irep_idt result;
    if(
      !addressed_id(instruction->call_arguments()[0], object) ||
      !shared_unsigned(object, ns) ||
      !symbol_id(instruction->call_arguments()[1], snapshot) ||
      !symbol_id(instruction->call_arguments()[2], desired) ||
      !addressed_id(instruction->call_arguments()[3], result))
      continue;
    transition.cas_function = callee;
    transition.object = object;
    transition.snapshot = snapshot;
    transition.desired = desired;
    transition.result = result;
    transition.set_witness.clear();
    if(
      instruction->call_arguments().size() == 5 &&
      !addressed_id(
        instruction->call_arguments()[4],
        transition.set_witness))
    {
      reason = "cas_witness_argument";
      return false;
    }
    cas_call = instruction;
    ++cas_calls;
  }
  if(cas_calls != 1)
  {
    reason = "cas_call_count";
    return false;
  }
  const symbolt *object_symbol = nullptr;
  ns.lookup(transition.object, object_symbol);
  if(
    !local_unsigned_like(
      transition.snapshot, object_symbol->type, ns) ||
    !local_unsigned_like(
      transition.desired, object_symbol->type, ns) ||
    !local_unsigned_like(
      transition.result, object_symbol->type, ns))
  {
    reason = "cas_local_types";
    return false;
  }

  goto_programt::targett snapshot_assignment =
    program.instructions.end();
  goto_programt::targett desired_assignment =
    program.instructions.end();
  std::size_t snapshots = 0;
  std::size_t desireds = 0;
  for(auto instruction = program.instructions.begin();
      instruction != program.instructions.end(); ++instruction)
  {
    if(!instruction->is_assign())
      continue;
    irep_idt lhs;
    irep_idt rhs;
    if(
      symbol_id(instruction->assign_lhs(), lhs) &&
      lhs == transition.snapshot &&
      symbol_id(instruction->assign_rhs(), rhs) &&
      rhs == transition.object)
    {
      snapshot_assignment = instruction;
      ++snapshots;
    }
    int direction = 0;
    if(parse_desired_assignment(
         *instruction,
         transition.desired,
         transition.snapshot,
         direction))
    {
      desired_assignment = instruction;
      transition.direction = direction;
      ++desireds;
    }
  }
  if(snapshots != 1 || desireds != 1)
  {
    reason = "cas_dataflow";
    return false;
  }
  const auto snapshot_position =
    position.at(&*snapshot_assignment);
  const auto desired_position =
    position.at(&*desired_assignment);
  const auto cas_position = position.at(&*cas_call);
  if(
    snapshot_position == 0 ||
    snapshot_position + 1 >= order.size() ||
    !order[snapshot_position - 1]->is_atomic_begin() ||
    !order[snapshot_position + 1]->is_atomic_end() ||
    !(snapshot_position < desired_position &&
      desired_position < cas_position))
  {
    reason = "cas_snapshot_atomic";
    return false;
  }

  bool boundary_guard = false;
  goto_programt::targett boundary_guard_instruction =
    program.instructions.end();
  for(std::size_t index = snapshot_position + 1;
      index < desired_position; ++index)
  {
    auto instruction = order[index];
    if(
      !instruction->is_goto() ||
      instruction->targets.size() != 1 ||
      instruction->targets.front() != desired_assignment)
      continue;
    const exprt &condition = instruction->condition();
    if(condition.id() != ID_not ||
       condition.operands().size() != 1)
      continue;
    const exprt &equality = strip(condition.op0());
    if(
      equality.id() != ID_equal ||
      equality.operands().size() != 2)
      continue;
    irep_idt guarded;
    mp_integer boundary_value;
    if(
      symbol_id(equality.op0(), guarded) &&
      guarded == transition.snapshot &&
      integer_constant(equality.op1(), boundary_value) &&
      ((transition.direction > 0 && boundary_value == -1) ||
       (transition.direction < 0 && boundary_value == 0)))
    {
      boundary_guard = true;
      boundary_guard_instruction = instruction;
    }
  }
  if(!boundary_guard)
  {
    reason = "cas_boundary_guard";
    return false;
  }
  std::set<std::size_t> pending;
  std::set<std::size_t> visited;
  pending.insert(position.at(&*boundary_guard_instruction) + 1);
  while(!pending.empty())
  {
    const auto index = *pending.begin();
    pending.erase(pending.begin());
    if(!visited.insert(index).second)
      continue;
    if(index == desired_position)
    {
      reason = "cas_boundary_bypass";
      return false;
    }
    auto instruction = order[index];
    if(instruction->is_end_function())
      continue;
    if(instruction->is_goto())
    {
      for(const auto &target : instruction->targets)
        pending.insert(position.at(&*target));
      if(
        !instruction->condition().is_true() &&
        index + 1 < order.size())
        pending.insert(index + 1);
    }
    else if(index + 1 < order.size())
      pending.insert(index + 1);
  }
  for(std::size_t index = desired_position;
      index < cas_position; ++index)
  {
    if(order[index]->is_goto())
    {
      reason = "cas_prelinearization_control";
      return false;
    }
  }

  goto_programt::targett retry = program.instructions.end();
  std::size_t retries = 0;
  for(std::size_t index = cas_position + 1;
      index < order.size(); ++index)
  {
    auto instruction = order[index];
    if(
      instruction->is_goto() &&
      instruction->targets.size() == 1 &&
      parse_result_test(
        instruction->condition(), transition.result) &&
      position.at(&*instruction->targets.front()) + 1 ==
        snapshot_position)
    {
      retry = instruction;
      ++retries;
    }
  }
  if(retries != 1)
  {
    reason = "cas_retry_guard";
    return false;
  }

  const auto retry_position = position.at(&*retry);
  if(retry_position != cas_position + 1)
  {
    reason = "cas_retry_dominance";
    return false;
  }
  goto_programt::targett property_call =
    program.instructions.end();
  irep_idt property_function;
  for(std::size_t index = retry_position + 1;
      index < order.size(); ++index)
  {
    irep_idt callee;
    if(call_id(*order[index], callee))
    {
      if(callee == "abort" || callee == "reach_error")
        continue;
      property_call = order[index];
      property_function = callee;
      break;
    }
  }

  if(property_call != program.instructions.end())
  {
    irep_idt actual_snapshot;
    if(
      property_call->call_arguments().size() != 1 ||
      !symbol_id(
        property_call->call_arguments().front(),
        actual_snapshot) ||
      actual_snapshot != transition.snapshot ||
      !parse_property_function(
        property_function,
        model,
        ns,
        property,
        recognized,
        reason,
        true))
      return false;
    transition.property_function = property_function;
  }
  else
  {
    if(!parse_property_function(
         function_id,
         model,
         ns,
         property,
         recognized,
         reason,
         false))
      return false;
    transition.property_function = function_id;
    if(position.at(&*property.guard) <= retry_position)
    {
      reason = "cas_property_before_success";
      return false;
    }
  }
  if(
    property.object != transition.object ||
    (property_call == program.instructions.end() &&
     property.snapshot != transition.snapshot) ||
    property.direction != transition.direction)
  {
    reason = "cas_property_mismatch";
    return false;
  }

  for(const auto &instruction : program.instructions)
  {
    if(
      instruction.is_goto() &&
      position.at(&*instruction.get_target()) <
        position.at(&instruction) &&
      &instruction != &*retry)
    {
      reason = "cas_extra_loop";
      return false;
    }
    if(
      instruction.is_assert())
    {
      reason = "cas_reachable_assertion";
      return false;
    }
  }
  transition.function = function_id;
  transition.property_witness = property.witness;
  transition.cas_call = cas_call;
  transition.property_call = property_call;
  recognized.insert(&*snapshot_assignment);
  recognized.insert(&*desired_assignment);
  recognized.insert(&*cas_call);
  recognized.insert(&*retry);
  if(property_call != program.instructions.end())
    recognized.insert(&*property_call);
  return true;
}

struct cas_protocolt
{
  irep_idt object_pointer;
  irep_idt expected;
  irep_idt desired;
  irep_idt result_pointer;
  irep_idt flag_pointer;
};

bool validate_cas_helper(
  const irep_idt &function_id,
  const std::size_t argument_count,
  goto_modelt &model,
  const namespacet &ns,
  cas_protocolt &protocol,
  std::string &reason)
{
  auto function = model.goto_functions.function_map.find(function_id);
  if(
    function == model.goto_functions.function_map.end() ||
    !function->second.body_available())
  {
    reason = "cas_helper_missing";
    return false;
  }
  const symbolt &function_symbol = ns.lookup(function_id);
  const auto &parameters =
    to_code_type(function_symbol.type).parameters();
  if(parameters.size() != argument_count)
  {
    reason = "cas_helper_arity";
    return false;
  }
  protocol.object_pointer = parameters[0].get_identifier();
  protocol.expected = parameters[1].get_identifier();
  protocol.desired = parameters[2].get_identifier();
  protocol.result_pointer = parameters[3].get_identifier();
  if(argument_count == 5)
    protocol.flag_pointer = parameters[4].get_identifier();

  auto &program = function->second.body;
  std::vector<goto_programt::targett> order;
  std::map<const goto_programt::instructiont *, std::size_t> position;
  for(auto instruction = program.instructions.begin();
      instruction != program.instructions.end(); ++instruction)
  {
    position.emplace(&*instruction, order.size());
    order.push_back(instruction);
  }
  int depth = 0;
  bool equality_guard = false;
  goto_programt::targett failure = program.instructions.end();
  std::size_t object_writes = 0;
  std::size_t result_one = 0;
  std::size_t result_zero = 0;
  std::size_t flag_writes = 0;
  std::size_t success_exits = 0;
  for(std::size_t index = 0; index < order.size(); ++index)
  {
    auto instruction = order[index];
    if(instruction->is_atomic_begin())
    {
      ++depth;
      continue;
    }
    if(instruction->is_atomic_end())
    {
      --depth;
      continue;
    }
    if(
      instruction->is_decl() || instruction->is_dead() ||
      instruction->is_skip() || instruction->is_location() ||
      instruction->is_end_function())
      continue;
    if(depth != 1)
    {
      reason = "cas_helper_atomic";
      return false;
    }
    if(instruction->is_goto())
    {
      const exprt &condition = instruction->condition();
      if(
        condition.id() == ID_not &&
        condition.operands().size() == 1)
      {
        const exprt &equal = strip(condition.op0());
        irep_idt pointer;
        irep_idt expected;
        if(
          equal.id() == ID_equal &&
          equal.operands().size() == 2 &&
          dereferenced_id(equal.op0(), pointer) &&
          pointer == protocol.object_pointer &&
          symbol_id(equal.op1(), expected) &&
          expected == protocol.expected &&
          instruction->targets.size() == 1)
        {
          equality_guard = true;
          failure = instruction->targets.front();
          continue;
        }
      }
      if(instruction->condition().is_true())
      {
        if(
          failure == program.instructions.end() ||
          index >= position.at(&*failure) ||
          instruction->targets.size() != 1 ||
          !instruction->targets.front()->is_atomic_end() ||
          position.at(&*instruction->targets.front()) <=
            position.at(&*failure))
        {
          reason = "cas_helper_success_exit";
          return false;
        }
        ++success_exits;
        continue;
      }
      reason = "cas_helper_control";
      return false;
    }
    if(!instruction->is_assign())
    {
      reason = "cas_helper_effect";
      return false;
    }
    irep_idt pointer;
    if(!dereferenced_id(instruction->assign_lhs(), pointer))
    {
      reason = "cas_helper_lhs";
      return false;
    }
    if(pointer == protocol.object_pointer)
    {
      if(
        failure == program.instructions.end() ||
        index >= position.at(&*failure))
      {
        reason = "cas_helper_update_branch";
        return false;
      }
      irep_idt desired;
      if(
        !symbol_id(instruction->assign_rhs(), desired) ||
        desired != protocol.desired)
      {
        reason = "cas_helper_update";
        return false;
      }
      ++object_writes;
    }
    else if(pointer == protocol.result_pointer)
    {
      if(one(instruction->assign_rhs()))
      {
        if(
          failure == program.instructions.end() ||
          index >= position.at(&*failure))
        {
          reason = "cas_helper_success_result_branch";
          return false;
        }
        ++result_one;
      }
      else if(zero(instruction->assign_rhs()))
      {
        if(failure == program.instructions.end() ||
           position.at(&*failure) != index)
        {
          reason = "cas_helper_failure_target";
          return false;
        }
        ++result_zero;
      }
      else
      {
        reason = "cas_helper_result";
        return false;
      }
    }
    else if(
      argument_count == 5 &&
      pointer == protocol.flag_pointer &&
      one(instruction->assign_rhs()))
    {
      if(
        failure == program.instructions.end() ||
        index >= position.at(&*failure))
      {
        reason = "cas_helper_flag_branch";
        return false;
      }
      ++flag_writes;
    }
    else
    {
      reason = "cas_helper_extra_write";
      return false;
    }
  }
  if(
    depth != 0 || !equality_guard ||
    object_writes != 1 || result_one != 1 ||
    result_zero != 1 || success_exits != 1 ||
    (argument_count == 5 ? flag_writes != 1
                         : flag_writes != 0))
  {
    reason = "cas_helper_shape";
    return false;
  }
  return true;
}

bool parse_spawn_loop(
  goto_modelt &model,
  irep_idt &worker,
  std::vector<goto_programt::targett> &loop,
  std::string &reason)
{
  auto main =
    model.goto_functions.function_map.find("main");
  if(
    main == model.goto_functions.function_map.end() ||
    !main->second.body_available())
  {
    reason = "cas_main";
    return false;
  }
  auto &program = main->second.body;
  std::vector<goto_programt::targett> order;
  std::map<const goto_programt::instructiont *, std::size_t> position;
  goto_programt::targett create = program.instructions.end();
  std::size_t creates = 0;
  for(auto instruction = program.instructions.begin();
      instruction != program.instructions.end(); ++instruction)
  {
    position.emplace(&*instruction, order.size());
    order.push_back(instruction);
    irep_idt callee;
    if(
      call_id(*instruction, callee) &&
      callee == "pthread_create")
    {
      if(
        instruction->call_arguments().size() < 3 ||
        !addressed_id(
          instruction->call_arguments()[2], worker))
      {
        reason = "cas_create_resolution";
        return false;
      }
      create = instruction;
      ++creates;
    }
  }
  if(creates != 1)
  {
    reason = "cas_create_count";
    return false;
  }
  std::size_t global_creates = 0;
  for(const auto &function : model.goto_functions.function_map)
  {
    if(!function.second.body_available())
      continue;
    for(const auto &instruction : function.second.body.instructions)
    {
      irep_idt callee;
      if(
        call_id(instruction, callee) &&
        callee == "pthread_create")
        ++global_creates;
    }
  }
  if(global_creates != 1)
  {
    reason = "cas_global_create_count";
    return false;
  }
  goto_programt::targett backedge = program.instructions.end();
  std::size_t backedges = 0;
  const auto create_position = position.at(&*create);
  for(auto instruction = program.instructions.begin();
      instruction != program.instructions.end(); ++instruction)
  {
    if(
      instruction->is_goto() &&
      instruction->condition().is_true() &&
      instruction->targets.size() == 1 &&
      position.at(&*instruction->targets.front()) <=
        create_position &&
      create_position < position.at(&*instruction))
    {
      backedge = instruction;
      ++backedges;
    }
  }
  if(backedges != 1)
  {
    reason = "cas_spawn_backedge";
    return false;
  }
  const auto begin = position.at(&*backedge->targets.front());
  const auto end = position.at(&*backedge);
  std::size_t exits = 0;
  for(std::size_t index = begin; index <= end; ++index)
  {
    auto instruction = order[index];
    if(instruction == create || instruction == backedge ||
       instruction->is_skip() || instruction->is_location())
    {
      loop.push_back(instruction);
      continue;
    }
    if(!instruction->is_goto())
    {
      reason = "cas_spawn_loop_shape";
      return false;
    }
    const exprt &condition = instruction->condition();
    bool condition_value = true;
    const bool false_guard =
      boolean_constant(condition, condition_value) &&
      !condition_value;
    if(
      instruction->targets.size() == 1 &&
      position.at(&*instruction->targets.front()) > end &&
      (condition.is_false() || false_guard))
    {
      ++exits;
      loop.push_back(instruction);
      continue;
    }
    reason = "cas_spawn_loop_shape";
    return false;
  }
  if(exits != 1)
  {
    reason = "cas_spawn_exit";
    return false;
  }
  return true;
}
} // namespace

bool cas_linearization_stability_transform(
  goto_modelt &goto_model,
  message_handlert &message_handler)
{
  const namespacet ns(goto_model.symbol_table);
  irep_idt worker;
  std::vector<goto_programt::targett> spawn_loop;
  std::string reason;
  if(!parse_spawn_loop(
       goto_model, worker, spawn_loop, reason))
  {
    std::cout << "NATIVE_CAS_STABILITY applied=0 reason="
              << reason << '\n';
    return false;
  }

  std::set<irep_idt> reachable;
  std::vector<irep_idt> pending{worker};
  std::set<irep_idt> ignored{
    "abort", "reach_error", "pthread_mutex_lock",
    "pthread_mutex_unlock"};
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
      reason = "cas_reachable_function";
      break;
    }
    for(const auto &instruction :
        function->second.body.instructions)
    {
      if(!instruction.is_function_call())
        continue;
      irep_idt callee;
      if(!call_id(instruction, callee))
      {
        reason = "cas_indirect_call";
        break;
      }
      if(ignored.find(callee) != ignored.end())
        continue;
      const auto called =
        goto_model.goto_functions.function_map.find(callee);
      if(
        called == goto_model.goto_functions.function_map.end() ||
        !called->second.body_available())
      {
        reason = "cas_unknown_call";
        break;
      }
      pending.push_back(callee);
    }
    if(!reason.empty())
      break;
  }
  if(!reason.empty())
  {
    std::cout << "NATIVE_CAS_STABILITY applied=0 reason="
              << reason << '\n';
    return false;
  }
  for(const auto &function_id : reachable)
  {
    const auto &program =
      goto_model.goto_functions.function_map.at(function_id).body;
    for(const auto &instruction : program.instructions)
    {
      if(instruction.is_assert())
      {
        std::cout
          << "NATIVE_CAS_STABILITY applied=0 reason="
          << "cas_reachable_assertion\n";
        return false;
      }
    }
  }

  std::vector<cas_transitiont> transitions;
  std::vector<propertyt> properties;
  std::set<const goto_programt::instructiont *> recognized;
  for(const auto &function_id : reachable)
  {
    auto &program =
      goto_model.goto_functions.function_map.at(function_id).body;
    bool candidate = false;
    for(const auto &instruction : program.instructions)
    {
      if(
        instruction.is_function_call() &&
        instruction.call_arguments().size() >= 4 &&
        instruction.call_arguments().size() <= 5)
      {
        irep_idt object;
        if(
          addressed_id(
            instruction.call_arguments()[0], object) &&
          shared_unsigned(object, ns))
          candidate = true;
      }
    }
    if(!candidate)
      continue;
    cas_transitiont transition;
    propertyt property;
    if(!parse_transition(
         function_id,
         goto_model,
         ns,
         transition,
         property,
         recognized,
         reason))
    {
      std::cout
        << "NATIVE_CAS_STABILITY applied=0 reason="
        << reason << " function=" << function_id << '\n';
      return false;
    }
    transitions.push_back(std::move(transition));
    properties.push_back(std::move(property));
  }
  if(transitions.empty())
  {
    std::cout
      << "NATIVE_CAS_STABILITY applied=0 reason=cas_no_transition\n";
    return false;
  }

  const auto cas_function = transitions.front().cas_function;
  const auto object = transitions.front().object;
  const auto argument_count =
    transitions.front().set_witness.empty() ? 4u : 5u;
  for(const auto &transition : transitions)
  {
    if(
      transition.cas_function != cas_function ||
      transition.object != object ||
      transition.cas_call->call_arguments().size() !=
        argument_count)
    {
      std::cout
        << "NATIVE_CAS_STABILITY applied=0 reason="
        << "cas_protocol_mismatch\n";
      return false;
    }
  }
  cas_protocolt protocol;
  if(!validate_cas_helper(
       cas_function,
       argument_count,
       goto_model,
       ns,
       protocol,
       reason))
  {
    std::cout << "NATIVE_CAS_STABILITY applied=0 reason="
              << reason << '\n';
    return false;
  }

  std::set<irep_idt> proof_symbols{object};
  std::set<irep_idt> witnesses;
  std::set<irep_idt> transition_functions;
  std::set<irep_idt> property_functions;
  std::set<irep_idt> property_helpers;
  std::size_t expected_property_helper_calls = 0;
  for(std::size_t index = 0;
      index < transitions.size(); ++index)
  {
    const auto &property = properties[index];
    const auto &transition = transitions[index];
    transition_functions.insert(transition.function);
    property_functions.insert(transition.property_function);
    if(transition.property_function != transition.function)
    {
      property_helpers.insert(transition.property_function);
      ++expected_property_helper_calls;
    }
    if(!transition.set_witness.empty())
    {
      if(!shared_unsigned(transition.set_witness, ns))
      {
        reason = "cas_set_witness_type";
        break;
      }
      witnesses.insert(transition.set_witness);
      proof_symbols.insert(transition.set_witness);
    }
    if(!property.witness.empty())
    {
      if(!shared_unsigned(property.witness, ns))
      {
        reason = "cas_property_witness_type";
        break;
      }
      witnesses.insert(property.witness);
      proof_symbols.insert(property.witness);
    }
    for(const auto &interference : transitions)
    {
      if(
        interference.direction != property.direction &&
        (property.witness.empty() ||
         property.witness != interference.set_witness))
      {
        reason = "cas_interference_not_covered";
        break;
      }
    }
    if(!reason.empty())
      break;
  }
  if(!reason.empty())
  {
    std::cout << "NATIVE_CAS_STABILITY applied=0 reason="
              << reason << '\n';
    return false;
  }

  std::size_t cas_calls = 0;
  std::size_t property_calls = 0;
  std::size_t property_helper_calls = 0;
  std::map<irep_idt, std::size_t> initializations;
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
      if(call_id(*instruction, callee))
      {
        if(callee == cas_function)
        {
          ++cas_calls;
          if(
            recognized.find(&*instruction) ==
              recognized.end())
          {
            reason = "cas_external_call";
            break;
          }
        }
        if(callee == "reach_error")
          ++property_calls;
        if(property_helpers.find(callee) != property_helpers.end())
        {
          ++property_helper_calls;
          if(
            recognized.find(&*instruction) ==
              recognized.end())
          {
            reason = "cas_external_property_call";
            break;
          }
        }
      }
      if(instruction->is_assign())
      {
        irep_idt lhs;
        if(
          symbol_id(instruction->assign_lhs(), lhs) &&
          proof_symbols.find(lhs) != proof_symbols.end())
        {
          if(function_entry.first != "__CPROVER_initialize")
          {
            reason = "cas_extra_write";
            break;
          }
          mp_integer value;
          if(
            !integer_constant(
              instruction->assign_rhs(), value) ||
            (witnesses.find(lhs) != witnesses.end() &&
             value != 0))
          {
            reason = "cas_initialization";
            break;
          }
          ++initializations[lhs];
        }
      }
      if(instruction->is_function_call())
      {
        const bool validated_cas =
          recognized.find(&*instruction) != recognized.end() &&
          callee == cas_function;
        for(const auto &argument :
            instruction->call_arguments())
        {
          if(
            contains_address(argument, proof_symbols) &&
            !validated_cas)
          {
            reason = "cas_address_escape";
            break;
          }
        }
      }
      if(!reason.empty())
        break;
      if(
        mentions(*instruction, proof_symbols) &&
        function_entry.first != "__CPROVER_initialize" &&
        function_entry.first != cas_function &&
        transition_functions.find(function_entry.first) ==
          transition_functions.end() &&
        property_functions.find(function_entry.first) ==
          property_functions.end())
      {
        reason = "cas_external_access";
        break;
      }
    }
    if(!reason.empty())
      break;
  }
  for(const auto &identifier : proof_symbols)
  {
    if(initializations[identifier] != 1)
      reason = "cas_initialization_count";
  }
  if(
    !reason.empty() ||
    cas_calls != transitions.size() ||
    property_calls != properties.size() ||
    property_helper_calls != expected_property_helper_calls)
  {
    if(reason.empty())
      reason = "cas_global_coverage";
    std::cout << "NATIVE_CAS_STABILITY applied=0 reason="
              << reason << '\n';
    return false;
  }

  for(auto instruction : spawn_loop)
    instruction->turn_into_skip();
  goto_model.goto_functions.update();
  std::cout << "NATIVE_CAS_STABILITY applied=1 worker="
            << worker << " transitions=" << transitions.size()
            << " object=" << object
            << " witnesses=" << witnesses.size() << '\n';
  (void)message_handler;
  return true;
}
