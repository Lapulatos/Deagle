/*******************************************************************\

Module: Lower finite pointer writes to explicit GOTO branches

\*******************************************************************/

#include "lower_finite_pointer_writes.h"

#include "goto_program_dereference.h"
#include "value_set_analysis.h"

#include <util/arith_tools.h>
#include <util/byte_operators.h>
#include <util/expr_util.h>
#include <util/namespace.h>
#include <util/replace_expr.h>
#include <util/std_expr.h>

#include <goto-programs/goto_model.h>

#include <algorithm>
#include <vector>

namespace
{
struct guarded_lvaluet
{
  exprt guard;
  exprt lhs;
};

bool contains_invalid_object(const exprt &expr)
{
  if(expr.get_bool(ID_C_invalid_object))
    return true;

  return std::any_of(
    expr.operands().begin(),
    expr.operands().end(),
    [](const exprt &operand) { return contains_invalid_object(operand); });
}

unsigned branch_order(const exprt &lhs)
{
  if(contains_invalid_object(lhs))
    return 3;
  if(
    lhs.id() == ID_index &&
    to_index_expr(lhs).index().is_constant())
    return 0;
  if(
    lhs.id() == ID_byte_extract_little_endian ||
    lhs.id() == ID_byte_extract_big_endian)
    return 2;
  return 1;
}

bool contains_expr(const exprt &haystack, const exprt &needle)
{
  if(haystack == needle)
    return true;

  return std::any_of(
    haystack.operands().begin(),
    haystack.operands().end(),
    [&needle](const exprt &operand) {
      return contains_expr(operand, needle);
    });
}

bool contains_constant_static_array_index(
  const exprt &expr,
  const namespacet &ns)
{
  if(expr.id() == ID_index)
  {
    const auto &index = to_index_expr(expr);
    if(
      index.index().is_constant() &&
      ns.follow(index.array().type()).id() == ID_array)
      return true;
  }

  return std::any_of(
    expr.operands().begin(),
    expr.operands().end(),
    [&ns](const exprt &operand) {
      return contains_constant_static_array_index(operand, ns);
    });
}

bool find_dereferenced_object_type(const exprt &expr, typet &type)
{
  if(expr.id() == ID_dereference)
  {
    type = expr.type();
    return true;
  }
  if(expr.id() == ID_member)
    return find_dereferenced_object_type(
      to_member_expr(expr).struct_op(), type);
  if(expr.id() == ID_index)
    return find_dereferenced_object_type(to_index_expr(expr).array(), type);
  if(expr.id() == ID_typecast)
    return find_dereferenced_object_type(to_typecast_expr(expr).op(), type);
  return false;
}

bool has_matching_small_static_array(
  const typet &object_type,
  const goto_modelt &goto_model,
  const namespacet &ns,
  std::size_t maximum_alternatives)
{
  const typet followed_object_type = ns.follow(object_type);
  for(const auto &symbol_pair : goto_model.symbol_table.symbols)
  {
    const typet &type = ns.follow(symbol_pair.second.type);
    if(type.id() != ID_array)
      continue;
    const auto &array_type = to_array_type(type);
    const auto size = numeric_cast<std::size_t>(array_type.size());
    if(
      size.has_value() && *size >= 2 &&
      *size <= maximum_alternatives &&
      ns.follow(array_type.element_type()) == followed_object_type)
      return true;
  }
  return false;
}

bool has_syntactic_finite_array_read_modify_write(
  const goto_modelt &goto_model,
  const namespacet &ns,
  std::size_t maximum_alternatives)
{
  for(const auto &function_entry : goto_model.goto_functions.function_map)
  {
    for(const auto &instruction : function_entry.second.body.instructions)
    {
      if(
        !instruction.is_assign() ||
        !has_subexpr(instruction.assign_lhs(), ID_dereference) ||
        !contains_expr(instruction.assign_rhs(), instruction.assign_lhs()))
        continue;

      typet object_type;
      if(
        find_dereferenced_object_type(
          instruction.assign_lhs(), object_type) &&
        has_matching_small_static_array(
          object_type,
          goto_model,
          ns,
          std::min<std::size_t>(maximum_alternatives, 8)))
        return true;
    }
  }
  return false;
}

bool is_direct_lvalue(const exprt &expr)
{
  if(has_subexpr(expr, ID_dereference) || has_subexpr(expr, ID_if))
    return false;

  if(expr.id() == ID_symbol)
    return true;

  if(expr.id() == ID_member)
    return is_direct_lvalue(to_member_expr(expr).struct_op());

  if(expr.id() == ID_index)
    return is_direct_lvalue(to_index_expr(expr).array());

  if(expr.id() == ID_typecast)
    return is_direct_lvalue(to_typecast_expr(expr).op());

  if(
    expr.id() == ID_byte_extract_little_endian ||
    expr.id() == ID_byte_extract_big_endian)
    return is_direct_lvalue(to_byte_extract_expr(expr).op());

  return false;
}

bool flatten_conditional_lvalue(
  const exprt &expr,
  const exprt &guard,
  std::vector<guarded_lvaluet> &result,
  std::size_t maximum_alternatives,
  const namespacet &ns)
{
  if(result.size() >= maximum_alternatives)
    return false;

  if(expr.id() == ID_if)
  {
    const auto &if_expr = to_if_expr(expr);
    return flatten_conditional_lvalue(
             if_expr.true_case(),
             make_and(guard, if_expr.cond()),
             result,
             maximum_alternatives,
             ns) &&
           flatten_conditional_lvalue(
             if_expr.false_case(),
             make_and(guard, not_exprt(if_expr.cond())),
             result,
             maximum_alternatives,
             ns);
  }

  if(expr.id() == ID_member)
  {
    const auto &member = to_member_expr(expr);
    std::vector<guarded_lvaluet> bases;
    if(!flatten_conditional_lvalue(
         member.struct_op(), guard, bases, maximum_alternatives, ns))
      return false;

    for(auto &base : bases)
    {
      if(result.size() >= maximum_alternatives)
        return false;
      result.push_back(
        {std::move(base.guard),
         member_exprt(
           std::move(base.lhs), member.get_component_name(), member.type())});
    }
    return true;
  }

  if(expr.id() == ID_index)
  {
    const auto &index = to_index_expr(expr);
    const typet &array_type = ns.follow(index.array().type());
    if(!index.index().is_constant() && array_type.id() == ID_array)
    {
      const auto size =
        numeric_cast<std::size_t>(to_array_type(array_type).size());
      if(!size.has_value() || *size < 2 || *size > maximum_alternatives ||
         result.size() + *size > maximum_alternatives ||
         !is_direct_lvalue(index.array()))
        return false;

      for(std::size_t i = 0; i < *size; ++i)
      {
        const exprt concrete_index = from_integer(i, index.index().type());
        result.push_back(
          {make_and(guard, equal_exprt(index.index(), concrete_index)),
           index_exprt(index.array(), concrete_index, index.type())});
      }
      return true;
    }
  }

  if(!is_direct_lvalue(expr))
    return false;

  result.push_back({guard, expr});
  return true;
}

bool lower_assignment(
  const irep_idt &function_id,
  goto_programt &program,
  goto_programt::targett target,
  const namespacet &ns,
  value_setst &value_sets,
  std::size_t maximum_alternatives)
{
  if(!target->is_assign() || !has_subexpr(target->assign_lhs(), ID_dereference))
    return false;

  exprt resolved_lhs = target->assign_lhs();
  dereference(function_id, target, resolved_lhs, ns, value_sets);

  std::vector<guarded_lvaluet> alternatives;
  const bool flattened = flatten_conditional_lvalue(
    resolved_lhs,
    true_exprt(),
    alternatives,
    maximum_alternatives,
    ns);
  if(!flattened ||
     alternatives.size() < 2 || alternatives.size() > maximum_alternatives)
    return false;

  std::stable_sort(
    alternatives.begin(),
    alternatives.end(),
    [](const guarded_lvaluet &lhs, const guarded_lvaluet &rhs) {
      return branch_order(lhs.lhs) < branch_order(rhs.lhs);
    });

  const source_locationt location = target->source_location();
  const exprt rhs = target->assign_rhs();

  goto_programt replacement;
  exprt::operandst exhaustive_guards;
  exhaustive_guards.reserve(alternatives.size());
  for(const auto &alternative : alternatives)
    exhaustive_guards.push_back(alternative.guard);
  replacement.add(goto_programt::make_assumption(
    disjunction(exhaustive_guards), location));

  for(const auto &alternative : alternatives)
  {
    exprt branch_rhs = rhs;
    replace_expr(target->assign_lhs(), alternative.lhs, branch_rhs);

    goto_programt guarded_assignment;
    guarded_assignment.add(goto_programt::make_assignment(
      alternative.lhs, std::move(branch_rhs), location));
    auto join_instruction = goto_programt::make_skip(location);
    join_instruction.code_nonconst().set("#finite_pointer_write_join", true);
    const auto join = guarded_assignment.add(std::move(join_instruction));
    replacement.add(
      goto_programt::make_goto(
        join, not_exprt(alternative.guard), location));
    replacement.destructive_append(guarded_assignment);
  }

  *target = goto_programt::make_skip(location);
  program.insert_before_swap(target, replacement);
  return true;
}

bool is_finite_array_read_modify_write(
  const irep_idt &function_id,
  goto_programt::targett target,
  const namespacet &ns,
  value_setst &value_sets,
  std::size_t maximum_alternatives)
{
  if(
    !target->is_assign() ||
    !has_subexpr(target->assign_lhs(), ID_dereference) ||
    !contains_expr(target->assign_rhs(), target->assign_lhs()))
    return false;

  exprt resolved_lhs = target->assign_lhs();
  dereference(function_id, target, resolved_lhs, ns, value_sets);

  std::vector<guarded_lvaluet> alternatives;
  if(
    !flatten_conditional_lvalue(
      resolved_lhs,
      true_exprt(),
      alternatives,
      maximum_alternatives,
      ns) ||
    alternatives.size() < 2 ||
    alternatives.size() > maximum_alternatives)
    return false;

  return std::count_if(
           alternatives.begin(),
           alternatives.end(),
           [&ns](const guarded_lvaluet &alternative) {
             return contains_constant_static_array_index(
               alternative.lhs, ns);
           }) >= 2;
}
} // namespace

std::size_t lower_finite_pointer_writes(
  goto_modelt &goto_model,
  std::size_t maximum_alternatives)
{
  const namespacet ns(goto_model.symbol_table);
  if(!has_syntactic_finite_array_read_modify_write(
       goto_model, ns, maximum_alternatives))
    return 0;

  value_set_analysist value_set_analysis(ns);
  value_set_analysis(goto_model.goto_functions);

  bool admitted = false;
  for(auto &function_entry : goto_model.goto_functions.function_map)
  {
    auto &program = function_entry.second.body;
    for(auto target = program.instructions.begin();
        target != program.instructions.end(); ++target)
    {
      if(is_finite_array_read_modify_write(
           function_entry.first,
           target,
           ns,
           value_set_analysis,
           maximum_alternatives))
      {
        admitted = true;
        break;
      }
    }
    if(admitted)
      break;
  }

  if(!admitted)
    return 0;

  std::size_t lowered = 0;
  for(auto &function_entry : goto_model.goto_functions.function_map)
  {
    auto &program = function_entry.second.body;
    for(auto target = program.instructions.begin();
        target != program.instructions.end(); ++target)
    {
      if(lower_assignment(
           function_entry.first,
           program,
           target,
           ns,
           value_set_analysis,
           maximum_alternatives))
        ++lowered;
    }
  }

  goto_model.goto_functions.update();
  return lowered;
}
