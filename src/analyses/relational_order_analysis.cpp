/*******************************************************************\

Module: Relational Order-Law Certificates

\*******************************************************************/

#include "relational_order_analysis.h"

#include <goto-programs/goto_model.h>

#include <util/arith_tools.h>
#include <util/expr_util.h>
#include <util/message.h>
#include <util/namespace.h>
#include <util/pointer_expr.h>
#include <util/std_code.h>
#include <util/std_expr.h>
#include <util/symbol.h>

#include <algorithm>
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
  return
    expr.id() == ID_address_of &&
    symbol_id(to_address_of_expr(expr).object(), identifier);
}

bool call_id(
  const goto_programt::instructiont &instruction,
  irep_idt &identifier)
{
  return
    instruction.is_function_call() &&
    symbol_id(instruction.call_function(), identifier);
}

bool integer_constant(const exprt &src, mp_integer &value)
{
  const exprt &expr = strip(src);
  if(
    expr.id() == ID_constant &&
    !to_integer(to_constant_expr(expr), value))
    return true;
  if(expr.id() == ID_unary_minus && expr.operands().size() == 1)
  {
    mp_integer operand;
    if(integer_constant(expr.op0(), operand))
    {
      value = -operand;
      return true;
    }
  }
  return false;
}

bool value_is(const exprt &expr, const mp_integer &expected)
{
  mp_integer value;
  return integer_constant(expr, value) && value == expected;
}

bool is_named(const irep_idt &identifier, const std::string &suffix)
{
  const std::string name = id2string(identifier);
  return
    name == suffix ||
    (name.size() > suffix.size() &&
     name.compare(name.size() - suffix.size(), suffix.size(), suffix) == 0);
}

bool is_create(const irep_idt &identifier)
{
  return is_named(identifier, "pthread_create");
}

bool is_join(const irep_idt &identifier)
{
  return is_named(identifier, "pthread_join");
}

bool is_assume(const irep_idt &identifier)
{
  return
    is_named(identifier, "assume_abort_if_not") ||
    is_named(identifier, "__CPROVER_assume");
}

bool is_reach_error(const irep_idt &identifier)
{
  return
    is_named(identifier, "reach_error") ||
    is_named(identifier, "__VERIFIER_error");
}

const symbolt *lookup(const irep_idt &identifier, const namespacet &ns)
{
  const symbolt *symbol = nullptr;
  return ns.lookup(identifier, symbol) ? nullptr : symbol;
}

bool shared_object(const irep_idt &identifier, const namespacet &ns)
{
  const symbolt *symbol = lookup(identifier, ns);
  return
    symbol != nullptr && symbol->is_static_lifetime && !symbol->is_type &&
    symbol->type.id() != ID_code;
}

bool signed_shared(const irep_idt &identifier, const namespacet &ns)
{
  const symbolt *symbol = lookup(identifier, ns);
  return
    symbol != nullptr && symbol->is_static_lifetime && !symbol->is_type &&
    symbol->type.id() == ID_signedbv;
}

bool pointer_shared(const irep_idt &identifier, const namespacet &ns)
{
  const symbolt *symbol = lookup(identifier, ns);
  return
    symbol != nullptr && symbol->is_static_lifetime && !symbol->is_type &&
    symbol->type.id() == ID_pointer &&
    to_pointer_type(symbol->type).base_type().id() == ID_signedbv;
}

bool indexed_value(
  const exprt &src,
  irep_idt &array,
  irep_idt &index)
{
  const exprt &expr = strip(src);
  if(expr.id() != ID_dereference)
    return false;
  const exprt &pointer = strip(to_dereference_expr(expr).pointer());
  if(pointer.id() != ID_plus || pointer.operands().size() != 2)
    return false;
  return
    (symbol_id(pointer.op0(), array) && symbol_id(pointer.op1(), index)) ||
    (symbol_id(pointer.op1(), array) && symbol_id(pointer.op0(), index));
}

bool binary_symbols(
  const exprt &src,
  const irep_idt &relation,
  irep_idt &left,
  irep_idt &right)
{
  const exprt &expr = strip(src);
  return
    expr.id() == relation && expr.operands().size() == 2 &&
    symbol_id(expr.op0(), left) && symbol_id(expr.op1(), right);
}

bool relation_to_zero(
  const exprt &src,
  const irep_idt &relation,
  irep_idt &symbol)
{
  const exprt &expr = strip(src);
  return
    expr.id() == relation && expr.operands().size() == 2 &&
    symbol_id(expr.op0(), symbol) && value_is(expr.op1(), 0);
}

bool flatten_relation_terms(
  const exprt &src,
  const irep_idt &operator_id,
  std::vector<exprt> &terms)
{
  const exprt &expr = strip(src);
  if(expr.id() == operator_id)
  {
    for(const auto &operand : expr.operands())
    {
      if(!flatten_relation_terms(operand, operator_id, terms))
        return false;
    }
  }
  else
    terms.push_back(expr);
  return true;
}

bool same_pair(
  const irep_idt &left_a,
  const irep_idt &right_a,
  const irep_idt &left_b,
  const irep_idt &right_b)
{
  return left_a == left_b && right_a == right_b;
}

struct objectt
{
  irep_idt scalar;
  irep_idt array;
  irep_idt length;

  bool operator==(const objectt &other) const
  {
    return
      scalar == other.scalar && array == other.array &&
      length == other.length;
  }
};

struct comparatort
{
  irep_idt worker;
  irep_idt result;
  objectt left;
  objectt right;
  bool has_scalar;
};

struct prefix_comparatort
{
  irep_idt worker;
  irep_idt result;
  objectt left;
  objectt right;
};

struct lifecyclet
{
  std::vector<irep_idt> workers;
  std::map<irep_idt, irep_idt> handles;
  const goto_programt::instructiont *first_create;
  const goto_programt::instructiont *last_join;
  std::vector<const goto_programt::instructiont *> post_assumptions;
  const goto_programt::instructiont *error_call;

  lifecyclet()
    : first_create(nullptr), last_join(nullptr), error_call(nullptr)
  {
  }
};

bool lifecycle(
  const goto_modelt &model,
  const namespacet &ns,
  lifecyclet &result,
  std::string &reason)
{
  const auto main = model.goto_functions.function_map.find(ID_main);
  if(
    main == model.goto_functions.function_map.end() ||
    !main->second.body_available())
  {
    reason = "main";
    return false;
  }

  std::set<irep_idt> workers;
  std::set<irep_idt> joined;
  bool joining = false;
  bool in_phase = false;
  bool after_phase = false;
  for(const auto &instruction : main->second.body.instructions)
  {
    irep_idt callee;
    const bool direct_call = call_id(instruction, callee);
    if(direct_call && is_create(callee))
    {
      if(
        joining || instruction.call_arguments().size() != 4 ||
        !value_is(instruction.call_arguments()[1], 0) ||
        !value_is(instruction.call_arguments()[3], 0))
      {
        reason = "create_shape";
        return false;
      }
      irep_idt handle;
      irep_idt worker;
      if(
        !addressed_id(instruction.call_arguments()[0], handle) ||
        !addressed_id(instruction.call_arguments()[2], worker) ||
        result.handles.find(handle) != result.handles.end() ||
        !workers.insert(worker).second)
      {
        reason = "create_resolution";
        return false;
      }
      const symbolt *worker_symbol = lookup(worker, ns);
      if(worker_symbol == nullptr || worker_symbol->type.id() != ID_code)
      {
        reason = "worker_symbol";
        return false;
      }
      result.handles.emplace(handle, worker);
      result.workers.push_back(worker);
      if(result.first_create == nullptr)
        result.first_create = &instruction;
      in_phase = true;
      continue;
    }
    if(direct_call && is_join(callee))
    {
      joining = true;
      irep_idt handle;
      if(
        instruction.call_arguments().size() != 2 ||
        !symbol_id(instruction.call_arguments()[0], handle) ||
        result.handles.find(handle) == result.handles.end() ||
        !joined.insert(handle).second)
      {
        reason = "join_resolution";
        return false;
      }
      result.last_join = &instruction;
      continue;
    }

    if(in_phase && result.last_join != nullptr)
    {
      in_phase = false;
      after_phase = true;
    }
    if(in_phase)
    {
      if(!instruction.is_skip() && !instruction.is_location())
      {
        reason = "main_phase_effect";
        return false;
      }
      continue;
    }
    if(!after_phase)
      continue;
    if(direct_call && is_assume(callee))
    {
      if(
        result.error_call != nullptr ||
        instruction.call_arguments().size() != 1)
      {
        reason = "post_assume";
        return false;
      }
      result.post_assumptions.push_back(&instruction);
    }
    else if(direct_call && is_reach_error(callee))
    {
      if(result.error_call != nullptr)
      {
        reason = "multiple_errors";
        return false;
      }
      result.error_call = &instruction;
    }
    else if(
      !instruction.is_skip() && !instruction.is_location() &&
      !instruction.is_dead() && !instruction.is_set_return_value() &&
      !instruction.is_end_function())
    {
      reason = "post_effect";
      return false;
    }
  }

  if(
    (result.workers.size() != 2 && result.workers.size() != 3) ||
    joined.size() != result.handles.size() ||
    result.first_create == nullptr || result.last_join == nullptr ||
    result.error_call == nullptr || result.post_assumptions.empty())
  {
    reason = "incomplete_lifecycle";
    return false;
  }
  for(const auto &worker : result.workers)
  {
    const auto function = model.goto_functions.function_map.find(worker);
    if(
      function == model.goto_functions.function_map.end() ||
      !function->second.body_available())
    {
      reason = "worker_body";
      return false;
    }
  }
  return true;
}

bool pair_loop_guard(
  const exprt &src,
  irep_idt &index,
  irep_idt &left_length,
  irep_idt &right_length)
{
  const exprt &condition = strip(src);
  if(condition.id() != ID_not || condition.operands().size() != 1)
    return false;
  const exprt &conjunction = strip(condition.op0());
  if(conjunction.id() != ID_and || conjunction.operands().size() != 2)
    return false;
  irep_idt index_a;
  irep_idt index_b;
  if(
    !binary_symbols(
      conjunction.op0(), ID_lt, index_a, left_length) ||
    !binary_symbols(
      conjunction.op1(), ID_lt, index_b, right_length) ||
    index_a != index_b)
    return false;
  index = index_a;
  return true;
}

bool mismatch_guard(
  const exprt &src,
  const irep_idt &index,
  irep_idt &left_array,
  irep_idt &right_array)
{
  const exprt &condition = strip(src);
  if(condition.id() != ID_not || condition.operands().size() != 1)
    return false;
  const exprt &different = strip(condition.op0());
  if(different.id() != ID_notequal || different.operands().size() != 2)
    return false;
  irep_idt left_index;
  irep_idt right_index;
  return
    indexed_value(different.op0(), left_array, left_index) &&
    indexed_value(different.op1(), right_array, right_index) &&
    left_index == index && right_index == index;
}

bool equality_exit_guard(
  const exprt &src,
  const irep_idt &index,
  irep_idt &left_array,
  irep_idt &right_array)
{
  const exprt &condition = strip(src);
  if(condition.id() != ID_not || condition.operands().size() != 1)
    return false;
  const exprt &equal = strip(condition.op0());
  if(equal.id() != ID_equal || equal.operands().size() != 2)
    return false;
  irep_idt left_index;
  irep_idt right_index;
  return
    indexed_value(equal.op0(), left_array, left_index) &&
    indexed_value(equal.op1(), right_array, right_index) &&
    left_index == index && right_index == index;
}

bool unit_increment(
  const exprt &src,
  const irep_idt &index)
{
  const exprt &expr = strip(src);
  if(expr.id() != ID_plus || expr.operands().size() != 2)
    return false;
  irep_idt candidate;
  return
    (symbol_id(expr.op0(), candidate) && candidate == index &&
     value_is(expr.op1(), 1)) ||
    (symbol_id(expr.op1(), candidate) && candidate == index &&
     value_is(expr.op0(), 1));
}

bool element_sign(
  const exprt &src,
  const irep_idt &index,
  irep_idt &left_array,
  irep_idt &right_array)
{
  const exprt &expr = strip(src);
  if(expr.id() != ID_if || expr.operands().size() != 3)
    return false;
  const exprt &condition = strip(expr.op0());
  if(
    condition.id() != ID_lt || condition.operands().size() != 2 ||
    !value_is(expr.op1(), -1) || !value_is(expr.op2(), 1))
    return false;
  irep_idt left_index;
  irep_idt right_index;
  return
    indexed_value(condition.op0(), left_array, left_index) &&
    indexed_value(condition.op1(), right_array, right_index) &&
    left_index == index && right_index == index;
}

bool scalar_sign(
  const exprt &src,
  irep_idt &left,
  irep_idt &right)
{
  const exprt &expr = strip(src);
  if(
    expr.id() != ID_if || expr.operands().size() != 3 ||
    !value_is(expr.op1(), 1) || !value_is(expr.op2(), -1))
    return false;
  return binary_symbols(expr.op0(), ID_gt, left, right);
}

bool difference(
  const exprt &src,
  irep_idt &left,
  irep_idt &right)
{
  return binary_symbols(src, ID_minus, left, right);
}

bool local_symbol(
  const irep_idt &identifier,
  const namespacet &ns)
{
  const symbolt *symbol = lookup(identifier, ns);
  return symbol != nullptr && !symbol->is_static_lifetime;
}

bool truth_guard(
  const exprt &src,
  irep_idt &identifier)
{
  const exprt &expr = strip(src);
  return
    expr.id() == ID_notequal && expr.operands().size() == 2 &&
    symbol_id(expr.op0(), identifier) && value_is(expr.op1(), 0);
}

bool negated_symbol_equality(
  const exprt &src,
  irep_idt &left,
  irep_idt &right)
{
  const exprt &expr = strip(src);
  return
    expr.id() == ID_not && expr.operands().size() == 1 &&
    binary_symbols(expr.op0(), ID_equal, left, right);
}

bool zero_relation(
  const exprt &src,
  const irep_idt &relation,
  const irep_idt &identifier)
{
  irep_idt candidate;
  return
    relation_to_zero(src, relation, candidate) &&
    candidate == identifier;
}

bool checked_subtraction_bound(
  const exprt &src,
  const irep_idt &left,
  const irep_idt &right,
  bool lower)
{
  const exprt &expr = strip(src);
  if(expr.id() != ID_or || expr.operands().size() != 2)
    return false;
  auto matches = [&](const exprt &sign_src, const exprt &bound_src) {
    if(
      !zero_relation(
        sign_src, lower ? ID_le : ID_ge, right))
      return false;
    const exprt &bound = strip(bound_src);
    if(
      bound.id() != (lower ? ID_ge : ID_le) ||
      bound.operands().size() != 2)
      return false;
    irep_idt lhs;
    if(!symbol_id(bound.op0(), lhs) || lhs != left)
      return false;
    const exprt &rhs = strip(bound.op1());
    if(
      rhs.id() != (lower ? ID_minus : ID_plus) ||
      rhs.operands().size() != 2)
      return false;
    irep_idt rhs_symbol;
    return
      symbol_id(rhs.op0(), rhs_symbol) && rhs_symbol == right &&
      value_is(
        rhs.op1(),
        lower ? power(2, 31) : power(2, 31) - 1);
  };
  return
    matches(expr.op0(), expr.op1()) ||
    matches(expr.op1(), expr.op0());
}

bool checked_subtraction_helper(
  const irep_idt &callee,
  const goto_modelt &model,
  const namespacet &ns)
{
  const symbolt *symbol = lookup(callee, ns);
  const auto function = model.goto_functions.function_map.find(callee);
  if(
    symbol == nullptr || symbol->type.id() != ID_code ||
    function == model.goto_functions.function_map.end() ||
    !function->second.body_available())
    return false;
  const auto &parameters = to_code_type(symbol->type).parameters();
  if(parameters.size() != 2)
    return false;
  const irep_idt left = parameters[0].get_identifier();
  const irep_idt right = parameters[1].get_identifier();
  if(left.empty() || right.empty())
    return false;

  bool lower = false;
  bool upper = false;
  bool result = false;
  std::size_t assumptions = 0;
  for(const auto &instruction : function->second.body.instructions)
  {
    irep_idt called;
    if(call_id(instruction, called) && is_assume(called))
    {
      ++assumptions;
      if(instruction.call_arguments().size() != 1)
        return false;
      const exprt &condition = instruction.call_arguments().front();
      if(checked_subtraction_bound(condition, left, right, true))
        lower = true;
      else if(checked_subtraction_bound(condition, left, right, false))
        upper = true;
      else
        return false;
    }
    else if(instruction.is_set_return_value())
    {
      irep_idt result_left;
      irep_idt result_right;
      result =
        difference(
          instruction.return_value(), result_left, result_right) &&
        result_left == left && result_right == right;
      if(!result)
        return false;
    }
    else if(
      instruction.is_assign() || instruction.is_function_call() ||
      instruction.is_goto() || instruction.is_assert() ||
      instruction.is_start_thread() || instruction.is_end_thread() ||
      instruction.is_atomic_begin() || instruction.is_atomic_end())
      return false;
  }
  return assumptions == 2 && lower && upper && result;
}

bool analyze_array_comparator(
  const irep_idt &worker,
  const goto_programt &program,
  const goto_modelt &model,
  const namespacet &ns,
  comparatort &result,
  std::string &reason)
{
  reason.clear();
  std::set<irep_idt> shared_writes;
  std::size_t backward_gotos = 0;
  std::size_t calls = 0;
  irep_idt index;
  irep_idt left_length;
  irep_idt right_length;
  irep_idt left_array;
  irep_idt right_array;
  irep_idt mismatch_left_array;
  irep_idt mismatch_right_array;
  irep_idt difference_left_length;
  irep_idt difference_right_length;
  bool loop_guard = false;
  bool mismatch = false;
  bool index_zero = false;
  bool increment = false;
  bool length_sign = false;
  bool element_difference = false;

  for(const auto &instruction : program.instructions)
  {
    if(instruction.is_goto())
    {
      if(
        instruction.get_target()->location_number <
        instruction.location_number)
        ++backward_gotos;
      irep_idt candidate_index;
      irep_idt candidate_left;
      irep_idt candidate_right;
      if(
        pair_loop_guard(
          instruction.condition(),
          candidate_index,
          candidate_left,
          candidate_right))
      {
        if(loop_guard)
        {
          reason = "multiple_loop_guards";
          return false;
        }
        loop_guard = true;
        index = candidate_index;
        left_length = candidate_left;
        right_length = candidate_right;
      }
    }
  }
  if(backward_gotos != 1 || !loop_guard)
  {
    reason = "array_control";
    return false;
  }

  for(const auto &instruction : program.instructions)
  {
    if(instruction.is_goto())
    {
      irep_idt candidate_left;
      irep_idt candidate_right;
      if(
        mismatch_guard(
          instruction.condition(), index, candidate_left, candidate_right))
      {
        if(mismatch)
        {
          reason = "multiple_mismatch";
          return false;
        }
        mismatch = true;
        mismatch_left_array = candidate_left;
        mismatch_right_array = candidate_right;
      }
      continue;
    }
    if(instruction.is_function_call())
    {
      ++calls;
      irep_idt callee;
      irep_idt lhs;
      irep_idt call_left_array;
      irep_idt call_left_index;
      irep_idt call_right_array;
      irep_idt call_right_index;
      if(
        !call_id(instruction, callee) ||
        !symbol_id(instruction.call_lhs(), lhs) ||
        instruction.call_arguments().size() != 2 ||
        !indexed_value(
          instruction.call_arguments()[0],
          call_left_array,
          call_left_index) ||
        !indexed_value(
          instruction.call_arguments()[1],
          call_right_array,
          call_right_index) ||
        call_left_index != index || call_right_index != index ||
        (mismatch &&
         call_left_array != mismatch_left_array &&
         call_left_array != mismatch_right_array) ||
        (mismatch &&
         call_right_array != mismatch_left_array &&
         call_right_array != mismatch_right_array) ||
        call_left_array == call_right_array ||
        !checked_subtraction_helper(callee, model, ns))
      {
        reason = "checked_difference";
        return false;
      }
      element_difference = true;
      left_array = call_left_array;
      right_array = call_right_array;
      if(result.result.empty())
        result.result = lhs;
      else if(result.result != lhs)
      {
        reason = "result_mismatch";
        return false;
      }
      shared_writes.insert(lhs);
      continue;
    }
    if(!instruction.is_assign())
      continue;
    irep_idt lhs;
    if(!symbol_id(instruction.assign_lhs(), lhs))
    {
      reason = "array_nonsymbol_write";
      return false;
    }
    if(shared_object(lhs, ns))
      shared_writes.insert(lhs);
    if(lhs == index && value_is(instruction.assign_rhs(), 0))
      index_zero = true;
    if(lhs == index && unit_increment(instruction.assign_rhs(), index))
      increment = true;
    irep_idt diff_left;
    irep_idt diff_right;
    if(difference(instruction.assign_rhs(), diff_left, diff_right))
    {
      if(length_sign)
      {
        reason = "multiple_length_signs";
        return false;
      }
      length_sign = true;
      difference_left_length = diff_left;
      difference_right_length = diff_right;
      if(result.result.empty())
        result.result = lhs;
      else if(result.result != lhs)
      {
        reason = "result_mismatch";
        return false;
      }
    }
    else if(
      lhs != index && lhs != result.result && shared_object(lhs, ns))
    {
      reason = "unexpected_shared_write";
      return false;
    }
  }

  if(
    calls != 1 || !mismatch || !index_zero || !increment ||
    !length_sign || !element_difference ||
    shared_writes.size() != 1 ||
    shared_writes.find(result.result) == shared_writes.end() ||
    !pointer_shared(left_array, ns) || !pointer_shared(right_array, ns) ||
    !signed_shared(left_length, ns) || !signed_shared(right_length, ns) ||
    !signed_shared(result.result, ns))
  {
    reason = "array_shape";
    return false;
  }
  const irep_idt expected_left_length =
    left_array == mismatch_left_array ? left_length : right_length;
  const irep_idt expected_right_length =
    right_array == mismatch_left_array ? left_length : right_length;
  if(
    difference_left_length != expected_left_length ||
    difference_right_length != expected_right_length)
  {
    reason = "length_direction";
    return false;
  }
  left_length = expected_left_length;
  right_length = expected_right_length;
  result.worker = worker;
  result.left = {irep_idt(), left_array, left_length};
  result.right = {irep_idt(), right_array, right_length};
  result.has_scalar = false;
  return true;
}

bool analyze_prefix_comparator(
  const irep_idt &worker,
  const goto_programt &program,
  const namespacet &ns,
  prefix_comparatort &result,
  std::string &reason)
{
  reason.clear();
  std::size_t backward_gotos = 0;
  std::size_t calls = 0;
  std::set<irep_idt> shared_writes;
  irep_idt index;
  irep_idt left_length;
  irep_idt right_length;
  irep_idt left_array;
  irep_idt right_array;
  bool loop_guard = false;
  bool mismatch = false;
  bool increment = false;

  for(const auto &instruction : program.instructions)
  {
    if(instruction.is_function_call())
      ++calls;
    if(!instruction.is_goto())
      continue;
    if(
      instruction.get_target()->location_number <
      instruction.location_number)
      ++backward_gotos;
    irep_idt candidate_index;
    irep_idt candidate_left;
    irep_idt candidate_right;
    if(
      pair_loop_guard(
        instruction.condition(),
        candidate_index,
        candidate_left,
        candidate_right))
    {
      if(loop_guard)
      {
        reason = "multiple_loop_guards";
        return false;
      }
      loop_guard = true;
      index = candidate_index;
      left_length = candidate_left;
      right_length = candidate_right;
    }
  }
  if(calls != 0 || backward_gotos != 1 || !loop_guard)
  {
    reason = "prefix_control";
    return false;
  }

  for(const auto &instruction : program.instructions)
  {
    if(instruction.is_goto())
    {
      irep_idt candidate_left;
      irep_idt candidate_right;
      if(
        equality_exit_guard(
          instruction.condition(), index, candidate_left, candidate_right))
      {
        if(mismatch)
        {
          reason = "multiple_mismatch";
          return false;
        }
        mismatch = true;
        left_array = candidate_left;
        right_array = candidate_right;
      }
      continue;
    }
    if(!instruction.is_assign())
      continue;
    irep_idt lhs;
    if(!symbol_id(instruction.assign_lhs(), lhs))
    {
      reason = "prefix_nonsymbol_write";
      return false;
    }
    if(shared_object(lhs, ns))
      shared_writes.insert(lhs);
    if(lhs == index && unit_increment(instruction.assign_rhs(), index))
      increment = true;
    else if(shared_object(lhs, ns))
    {
      reason = "prefix_shared_write";
      return false;
    }
  }

  if(!mismatch)
    reason = "prefix_mismatch";
  else if(!increment)
    reason = "prefix_increment";
  else if(index.empty())
    reason = "prefix_index";
  else if(shared_writes.size() != 1 || shared_writes.count(index) != 1)
    reason = "prefix_write_set";
  else if(!signed_shared(index, ns))
    reason = "prefix_result_type";
  else if(
    !pointer_shared(left_array, ns) || !pointer_shared(right_array, ns))
    reason = "prefix_array_type";
  else if(
    !signed_shared(left_length, ns) || !signed_shared(right_length, ns))
    reason = "prefix_length_type";
  if(!reason.empty())
    return false;
  result.worker = worker;
  result.result = index;
  result.left = {irep_idt(), left_array, left_length};
  result.right = {irep_idt(), right_array, right_length};
  return true;
}

bool analyze_word_comparator(
  const irep_idt &worker,
  const goto_programt &program,
  const namespacet &ns,
  comparatort &result,
  std::string &reason)
{
  reason.clear();
  std::set<irep_idt> shared_writes;
  std::size_t backward_gotos = 0;
  std::size_t conditional_gotos = 0;
  std::size_t calls = 0;
  irep_idt index;
  irep_idt left_length;
  irep_idt right_length;
  irep_idt left_array;
  irep_idt right_array;
  irep_idt diff_left;
  irep_idt diff_right;
  irep_idt scalar_left;
  irep_idt scalar_right;
  bool index_zero = false;
  bool increment = false;
  bool loop_guard = false;
  bool mismatch = false;
  bool sign = false;
  bool length_sign = false;
  bool scalar_result = false;
  const goto_programt::instructiont *loop_guard_instruction = nullptr;
  const goto_programt::instructiont *backedge_instruction = nullptr;
  const goto_programt::instructiont *mismatch_instruction = nullptr;
  const goto_programt::instructiont *index_zero_instruction = nullptr;
  const goto_programt::instructiont *increment_instruction = nullptr;
  const goto_programt::instructiont *sign_instruction = nullptr;
  const goto_programt::instructiont *length_instruction = nullptr;
  const goto_programt::instructiont *scalar_instruction = nullptr;
  std::map<irep_idt, const goto_programt::instructiont *> local_zero;
  std::map<irep_idt, const goto_programt::instructiont *> local_one;

  for(auto instruction = program.instructions.begin();
      instruction != program.instructions.end(); ++instruction)
  {
    if(instruction->is_function_call())
      ++calls;
    if(instruction->is_goto())
    {
      if(instruction->get_target()->location_number <
         instruction->location_number)
      {
        ++backward_gotos;
        backedge_instruction = &*instruction;
      }
      if(!instruction->condition().is_true())
      {
        ++conditional_gotos;
        irep_idt candidate_index;
        irep_idt candidate_left;
        irep_idt candidate_right;
        if(
          pair_loop_guard(
            instruction->condition(),
            candidate_index,
            candidate_left,
            candidate_right))
        {
          if(loop_guard)
          {
            reason = "multiple_loop_guards";
            return false;
          }
          loop_guard = true;
          loop_guard_instruction = &*instruction;
          index = candidate_index;
          left_length = candidate_left;
          right_length = candidate_right;
        }
      }
    }
  }
  if(calls != 0 || backward_gotos != 1 || !loop_guard)
  {
    reason = "word_control";
    return false;
  }

  for(const auto &instruction : program.instructions)
  {
    if(instruction.is_goto())
    {
      irep_idt candidate_left;
      irep_idt candidate_right;
      if(
        mismatch_guard(
          instruction.condition(), index, candidate_left, candidate_right))
      {
        if(mismatch)
        {
          reason = "multiple_mismatch";
          return false;
        }
        mismatch = true;
        mismatch_instruction = &instruction;
        left_array = candidate_left;
        right_array = candidate_right;
      }
      continue;
    }
    if(!instruction.is_assign())
      continue;
    irep_idt lhs;
    if(!symbol_id(instruction.assign_lhs(), lhs))
    {
      reason = "word_nonsymbol_write";
      return false;
    }
    if(shared_object(lhs, ns))
      shared_writes.insert(lhs);
    if(lhs == index && value_is(instruction.assign_rhs(), 0))
    {
      index_zero = true;
      index_zero_instruction = &instruction;
    }
    if(lhs == index && unit_increment(instruction.assign_rhs(), index))
    {
      increment = true;
      increment_instruction = &instruction;
    }
    if(local_symbol(lhs, ns) && value_is(instruction.assign_rhs(), 0))
      local_zero[lhs] = &instruction;
    if(local_symbol(lhs, ns) && value_is(instruction.assign_rhs(), 1))
      local_one[lhs] = &instruction;

    irep_idt candidate_left;
    irep_idt candidate_right;
    if(
      element_sign(
        instruction.assign_rhs(),
        index,
        candidate_left,
        candidate_right))
    {
      if(sign || (mismatch &&
         !same_pair(
           left_array, right_array, candidate_left, candidate_right)))
      {
        reason = "element_sign";
        return false;
      }
      sign = true;
      sign_instruction = &instruction;
      left_array = candidate_left;
      right_array = candidate_right;
      result.result = lhs;
    }
    else if(
      difference(
        instruction.assign_rhs(), candidate_left, candidate_right))
    {
      if(length_sign)
      {
        reason = "multiple_length_signs";
        return false;
      }
      length_sign = true;
      length_instruction = &instruction;
      diff_left = candidate_left;
      diff_right = candidate_right;
      if(result.result.empty())
        result.result = lhs;
      else if(result.result != lhs)
      {
        reason = "result_mismatch";
        return false;
      }
    }
    else if(
      scalar_sign(
        instruction.assign_rhs(), candidate_left, candidate_right))
    {
      if(scalar_result)
      {
        reason = "multiple_scalar_signs";
        return false;
      }
      scalar_result = true;
      scalar_instruction = &instruction;
      scalar_left = candidate_left;
      scalar_right = candidate_right;
      if(result.result.empty())
        result.result = lhs;
      else if(result.result != lhs)
      {
        reason = "result_mismatch";
        return false;
      }
    }
    else if(
      lhs != index && lhs != result.result && shared_object(lhs, ns))
    {
      reason = "unexpected_shared_write";
      return false;
    }
  }

  if(
    !index_zero || !increment || !mismatch || !sign || !length_sign ||
    diff_left != left_length || diff_right != right_length ||
    left_array.empty() || right_array.empty() ||
    !pointer_shared(left_array, ns) || !pointer_shared(right_array, ns) ||
    !signed_shared(left_length, ns) || !signed_shared(right_length, ns) ||
    !signed_shared(result.result, ns) ||
    shared_writes.size() != 1 ||
    shared_writes.find(result.result) == shared_writes.end())
  {
    reason = "word_shape";
    return false;
  }
  if(
    scalar_result &&
    (!signed_shared(scalar_left, ns) || !signed_shared(scalar_right, ns)))
  {
    reason = "scalar_type";
    return false;
  }
  if(!scalar_result && conditional_gotos < 3)
  {
    reason = "word_branch_count";
    return false;
  }

  irep_idt stop;
  const goto_programt::instructiont *stop_zero = nullptr;
  const goto_programt::instructiont *stop_one = nullptr;
  const goto_programt::instructiont *stop_guard = nullptr;
  const goto_programt::instructiont *scalar_guard = nullptr;
  for(const auto &entry : local_zero)
  {
    const auto one = local_one.find(entry.first);
    if(one == local_one.end())
      continue;
    if(!stop.empty())
    {
      reason = "ambiguous_stop";
      return false;
    }
    stop = entry.first;
    stop_zero = entry.second;
    stop_one = one->second;
  }
  for(const auto &instruction : program.instructions)
  {
    if(!instruction.is_goto())
      continue;
    irep_idt guarded;
    if(truth_guard(instruction.condition(), guarded) && guarded == stop)
    {
      if(stop_guard != nullptr)
      {
        reason = "multiple_stop_guards";
        return false;
      }
      stop_guard = &instruction;
    }
    irep_idt guard_left;
    irep_idt guard_right;
    if(
      scalar_result &&
      negated_symbol_equality(
        instruction.condition(), guard_left, guard_right) &&
      guard_left == scalar_left && guard_right == scalar_right)
      scalar_guard = &instruction;
  }
  if(
    stop.empty() || stop_zero == nullptr || stop_one == nullptr ||
    stop_guard == nullptr || loop_guard_instruction == nullptr ||
    backedge_instruction == nullptr || mismatch_instruction == nullptr ||
    index_zero_instruction == nullptr || increment_instruction == nullptr ||
    sign_instruction == nullptr || length_instruction == nullptr)
  {
    reason = "word_cfg_nodes";
    return false;
  }
  if(
    !(stop_zero->location_number < index_zero_instruction->location_number &&
      index_zero_instruction->location_number <
        loop_guard_instruction->location_number &&
      loop_guard_instruction->location_number <
        mismatch_instruction->location_number &&
      mismatch_instruction->location_number < sign_instruction->location_number &&
      sign_instruction->location_number < stop_one->location_number &&
      stop_one->location_number < increment_instruction->location_number &&
      increment_instruction->location_number <
        backedge_instruction->location_number &&
      backedge_instruction->location_number < stop_guard->location_number &&
      stop_guard->location_number < length_instruction->location_number))
  {
    reason = "word_cfg_order";
    return false;
  }
  if(
    &*mismatch_instruction->get_target() != increment_instruction ||
    &*backedge_instruction->get_target() != loop_guard_instruction ||
    stop_guard->get_target()->location_number <=
      length_instruction->location_number)
  {
    reason = "word_cfg_targets";
    return false;
  }
  bool mismatch_exit = false;
  for(const auto &instruction : program.instructions)
  {
    if(
      instruction.is_goto() && instruction.condition().is_true() &&
      instruction.location_number > stop_one->location_number &&
      instruction.location_number < increment_instruction->location_number &&
      instruction.get_target()->location_number >
        backedge_instruction->location_number &&
      instruction.get_target()->location_number <=
        stop_guard->location_number)
      mismatch_exit = true;
  }
  if(!mismatch_exit)
  {
    reason = "word_mismatch_exit";
    return false;
  }
  if(scalar_result)
  {
    if(
      scalar_guard == nullptr || scalar_instruction == nullptr ||
      &*scalar_guard->get_target() != scalar_instruction ||
      scalar_instruction->location_number <= length_instruction->location_number)
    {
      reason = "word_scalar_cfg";
      return false;
    }
  }

  result.worker = worker;
  result.left = {scalar_result ? scalar_left : irep_idt(), left_array,
                 left_length};
  result.right = {scalar_result ? scalar_right : irep_idt(), right_array,
                  right_length};
  result.has_scalar = scalar_result;
  return true;
}

bool exact_error_sink(
  const goto_modelt &model,
  std::string &reason)
{
  std::size_t assertions = 0;
  for(const auto &entry : model.goto_functions.function_map)
  {
    for(const auto &instruction : entry.second.body.instructions)
    {
      if(!instruction.is_assert())
        continue;
      ++assertions;
      if(!instruction.condition().is_false())
      {
        reason = "nonfalse_assertion";
        return false;
      }
    }
  }
  if(assertions != 1)
  {
    reason = assertions == 0 ? "missing_assertion" : "multiple_assertions";
    return false;
  }
  return true;
}

bool helper_assumes_nonnegative(
  const irep_idt &callee,
  const goto_modelt &model,
  const namespacet &ns)
{
  const symbolt *symbol = lookup(callee, ns);
  const auto function = model.goto_functions.function_map.find(callee);
  if(
    symbol == nullptr || symbol->type.id() != ID_code ||
    function == model.goto_functions.function_map.end() ||
    !function->second.body_available())
    return false;
  const auto &parameters = to_code_type(symbol->type).parameters();
  if(parameters.size() != 1 || parameters.front().get_identifier().empty())
    return false;
  const irep_idt parameter = parameters.front().get_identifier();
  for(const auto &instruction : function->second.body.instructions)
  {
    irep_idt assume;
    if(
      !call_id(instruction, assume) || !is_assume(assume) ||
      instruction.call_arguments().size() != 1)
      continue;
    const exprt &condition = strip(instruction.call_arguments().front());
    irep_idt candidate;
    if(
      condition.id() == ID_ge && condition.operands().size() == 2 &&
      symbol_id(condition.op0(), candidate) && candidate == parameter &&
      value_is(condition.op1(), 0))
      return true;
  }
  return false;
}

bool nonnegative_lengths(
  const goto_modelt &model,
  const lifecyclet &life,
  const std::vector<comparatort> &comparators,
  std::string &reason)
{
  std::set<std::pair<irep_idt, irep_idt>> required;
  for(const auto &comparator : comparators)
  {
    required.emplace(comparator.left.array, comparator.left.length);
    required.emplace(comparator.right.array, comparator.right.length);
  }
  std::set<std::pair<irep_idt, irep_idt>> established;
  const namespacet ns(model.symbol_table);
  const auto &main = model.goto_functions.function_map.at(ID_main).body;
  for(const auto &instruction : main.instructions)
  {
    if(&instruction == life.first_create)
      break;
    if(!instruction.is_function_call() || instruction.call_lhs().is_nil())
      continue;
    irep_idt callee;
    irep_idt array;
    irep_idt length;
    if(
      !call_id(instruction, callee) ||
      !symbol_id(instruction.call_lhs(), array) ||
      instruction.call_arguments().size() != 1 ||
      !symbol_id(instruction.call_arguments().front(), length) ||
      required.find({array, length}) == required.end() ||
      !helper_assumes_nonnegative(callee, model, ns))
      continue;
    established.emplace(array, length);
  }
  if(established != required)
  {
    reason = "length_nonnegative";
    return false;
  }
  return true;
}

bool nonnegative_prefix_lengths(
  const goto_modelt &model,
  const lifecyclet &life,
  const std::vector<prefix_comparatort> &comparators,
  std::string &reason)
{
  std::vector<comparatort> converted;
  for(const auto &prefix : comparators)
  {
    comparatort comparator;
    comparator.worker = prefix.worker;
    comparator.result = prefix.result;
    comparator.left = prefix.left;
    comparator.right = prefix.right;
    comparator.has_scalar = false;
    converted.push_back(comparator);
  }
  return nonnegative_lengths(model, life, converted, reason);
}

bool prefix_results_zero(
  const goto_modelt &model,
  const lifecyclet &life,
  const std::vector<prefix_comparatort> &comparators,
  std::string &reason)
{
  std::set<irep_idt> required;
  for(const auto &comparator : comparators)
    required.insert(comparator.result);
  std::set<irep_idt> zero;
  for(const auto &entry : model.goto_functions.function_map)
  {
    const bool before_main_create = entry.first == ID_main;
    const bool initializer =
      id2string(entry.first).find("start") != std::string::npos ||
      id2string(entry.first).find("initialize") != std::string::npos;
    if(!before_main_create && !initializer)
      continue;
    for(const auto &instruction : entry.second.body.instructions)
    {
      if(before_main_create && &instruction == life.first_create)
        break;
      if(!instruction.is_assign())
        continue;
      irep_idt lhs;
      if(
        !symbol_id(instruction.assign_lhs(), lhs) ||
        required.find(lhs) == required.end())
        continue;
      if(!value_is(instruction.assign_rhs(), 0))
      {
        reason = "prefix_initialization";
        return false;
      }
      zero.insert(lhs);
    }
  }
  if(zero != required)
  {
    reason = "prefix_initialization";
    return false;
  }
  return true;
}

bool negated_pair(
  const exprt &src,
  const irep_idt &left_relation,
  const irep_idt &right_relation,
  irep_idt &left_result,
  irep_idt &right_result)
{
  const exprt &expr = strip(src);
  if(expr.id() != ID_not || expr.operands().size() != 1)
    return false;
  const exprt &conjunction = strip(expr.op0());
  if(conjunction.id() != ID_and || conjunction.operands().size() != 2)
    return false;
  return
    relation_to_zero(
      conjunction.op0(), left_relation, left_result) &&
    relation_to_zero(
      conjunction.op1(), right_relation, right_result);
}

bool symmetry_property(
  const lifecyclet &life,
  const std::vector<comparatort> &comparators)
{
  if(comparators.size() != 2 || life.post_assumptions.size() != 3)
    return false;
  const auto &first = comparators[0];
  const auto &second = comparators[1];
  if(
    first.has_scalar != second.has_scalar ||
    !(first.left == second.right) || !(first.right == second.left))
    return false;

  bool negative_positive = false;
  bool positive_negative = false;
  bool zero_zero = false;
  for(const auto *assumption : life.post_assumptions)
  {
    const exprt &condition = assumption->call_arguments().front();
    irep_idt left;
    irep_idt right;
    if(negated_pair(condition, ID_lt, ID_gt, left, right))
      negative_positive =
        left == first.result && right == second.result;
    else if(negated_pair(condition, ID_gt, ID_lt, left, right))
      positive_negative =
        left == first.result && right == second.result;
    else if(negated_pair(condition, ID_equal, ID_equal, left, right))
      zero_zero = left == first.result && right == second.result;
    else
      return false;
  }
  return negative_positive && positive_negative && zero_zero;
}

const comparatort *by_result(
  const std::vector<comparatort> &comparators,
  const irep_idt &result)
{
  for(const auto &comparator : comparators)
  {
    if(comparator.result == result)
      return &comparator;
  }
  return nullptr;
}

bool transitivity_property(
  const lifecyclet &life,
  const std::vector<comparatort> &comparators)
{
  if(comparators.size() != 3 || life.post_assumptions.size() != 1)
    return false;
  std::vector<exprt> terms;
  flatten_relation_terms(
    life.post_assumptions.front()->call_arguments().front(), ID_and, terms);
  if(terms.size() != 3)
    return false;
  irep_idt positive_a;
  irep_idt positive_b;
  irep_idt nonpositive;
  if(
    !relation_to_zero(terms[0], ID_gt, positive_a) ||
    !relation_to_zero(terms[1], ID_gt, positive_b) ||
    !relation_to_zero(terms[2], ID_le, nonpositive))
    return false;
  const comparatort *xy = by_result(comparators, positive_a);
  const comparatort *yz = by_result(comparators, positive_b);
  const comparatort *xz = by_result(comparators, nonpositive);
  if(xy == nullptr || yz == nullptr || xz == nullptr)
    return false;
  return
    xy->has_scalar == yz->has_scalar &&
    yz->has_scalar == xz->has_scalar &&
    xy->right == yz->left && xy->left == xz->left &&
    yz->right == xz->right;
}

bool boolean_sign_difference(
  const exprt &src,
  const irep_idt &relation,
  irep_idt &left,
  irep_idt &right)
{
  const exprt &expr = strip(src);
  if(expr.id() != ID_notequal || expr.operands().size() != 2)
    return false;
  return
    relation_to_zero(expr.op0(), relation, left) &&
    relation_to_zero(expr.op1(), relation, right);
}

bool substitution_property(
  const lifecyclet &life,
  const std::vector<comparatort> &comparators)
{
  if(comparators.size() != 3 || life.post_assumptions.size() != 2)
    return false;
  irep_idt equal_result;
  const exprt &equality =
    strip(life.post_assumptions[0]->call_arguments().front());
  if(
    equality.id() != ID_equal || equality.operands().size() != 2 ||
    !symbol_id(equality.op0(), equal_result) ||
    !value_is(equality.op1(), 0))
    return false;
  const exprt &difference =
    strip(life.post_assumptions[1]->call_arguments().front());
  if(difference.id() != ID_or || difference.operands().size() != 2)
    return false;
  irep_idt positive_left;
  irep_idt positive_right;
  irep_idt negative_left;
  irep_idt negative_right;
  if(
    !boolean_sign_difference(
      difference.op0(), ID_gt, positive_left, positive_right) ||
    !boolean_sign_difference(
      difference.op1(), ID_lt, negative_left, negative_right) ||
    positive_left != negative_left ||
    positive_right != negative_right)
    return false;
  const comparatort *xy = by_result(comparators, equal_result);
  const comparatort *xz = by_result(comparators, positive_left);
  const comparatort *yz = by_result(comparators, positive_right);
  if(xy == nullptr || xz == nullptr || yz == nullptr)
    return false;
  return
    xy->has_scalar == xz->has_scalar &&
    xz->has_scalar == yz->has_scalar &&
    xy->left == xz->left && xy->right == yz->left &&
    xz->right == yz->right;
}

bool prefix_relation(
  const exprt &src,
  bool negated,
  irep_idt &index,
  objectt &left,
  objectt &right)
{
  const exprt *condition = &strip(src);
  if(negated)
  {
    if(condition->id() != ID_not || condition->operands().size() != 1)
      return false;
    condition = &strip(condition->op0());
  }
  if(condition->id() != ID_or || condition->operands().size() != 2)
    return false;
  const exprt &finished = strip(condition->op0());
  const exprt &mismatch = strip(condition->op1());
  irep_idt left_length;
  if(
    finished.id() != ID_equal || finished.operands().size() != 2 ||
    !symbol_id(finished.op0(), index) ||
    !symbol_id(finished.op1(), left_length) ||
    mismatch.id() != ID_and || mismatch.operands().size() != 2)
    return false;
  irep_idt mismatch_index;
  irep_idt right_length;
  if(
    !binary_symbols(
      mismatch.op0(), ID_lt, mismatch_index, right_length) ||
    mismatch_index != index)
    return false;
  const exprt &element_order = strip(mismatch.op1());
  if(element_order.id() != ID_le || element_order.operands().size() != 2)
    return false;
  irep_idt left_array;
  irep_idt left_index;
  irep_idt right_array;
  irep_idt right_index;
  if(
    !indexed_value(element_order.op0(), left_array, left_index) ||
    !indexed_value(element_order.op1(), right_array, right_index) ||
    left_index != index || right_index != index)
    return false;
  left = {irep_idt(), left_array, left_length};
  right = {irep_idt(), right_array, right_length};
  return true;
}

const prefix_comparatort *prefix_by_result(
  const std::vector<prefix_comparatort> &comparators,
  const irep_idt &result)
{
  for(const auto &comparator : comparators)
  {
    if(comparator.result == result)
      return &comparator;
  }
  return nullptr;
}

bool prefix_transitivity_property(
  const lifecyclet &life,
  const std::vector<prefix_comparatort> &comparators)
{
  if(comparators.size() != 3 || life.post_assumptions.size() != 3)
    return false;
  struct relationt
  {
    irep_idt result;
    objectt left;
    objectt right;
  };
  std::vector<relationt> positive;
  relationt negative;
  for(std::size_t i = 0; i < life.post_assumptions.size(); ++i)
  {
    relationt relation;
    if(!prefix_relation(
         life.post_assumptions[i]->call_arguments().front(),
         i == 2,
         relation.result,
         relation.left,
         relation.right))
      return false;
    if(i == 2)
      negative = relation;
    else
      positive.push_back(relation);
  }
  const auto *xy = prefix_by_result(comparators, positive[0].result);
  const auto *yz = prefix_by_result(comparators, positive[1].result);
  const auto *xz = prefix_by_result(comparators, negative.result);
  if(
    xy == nullptr || yz == nullptr || xz == nullptr ||
    !(xy->left == positive[0].left) ||
    !(xy->right == positive[0].right) ||
    !(yz->left == positive[1].left) ||
    !(yz->right == positive[1].right) ||
    !(xz->left == negative.left) ||
    !(xz->right == negative.right))
    return false;
  return
    xy->right == yz->left && xy->left == xz->left &&
    yz->right == xz->right;
}

} // namespace

bool relational_order_law_proof(
  const goto_modelt &goto_model,
  message_handlert &message_handler)
{
  messaget log(message_handler);
  const namespacet ns(goto_model.symbol_table);
  lifecyclet life;
  std::string reason;
  if(
    !lifecycle(goto_model, ns, life, reason) ||
    !exact_error_sink(goto_model, reason))
  {
    std::cout << "NATIVE_RELATIONAL_ORDER applied=0 reason="
              << reason << '\n';
    return false;
  }

  std::vector<comparatort> comparators;
  bool word_mode = true;
  bool comparator_mode = true;
  for(const auto &worker : life.workers)
  {
    comparatort comparator;
    const auto &program =
      goto_model.goto_functions.function_map.at(worker).body;
    if(!analyze_word_comparator(
         worker, program, ns, comparator, reason))
    {
      word_mode = false;
      comparators.clear();
      break;
    }
    comparators.push_back(comparator);
  }
  if(!word_mode)
  {
    for(const auto &worker : life.workers)
    {
      comparatort comparator;
      const auto &program =
        goto_model.goto_functions.function_map.at(worker).body;
      if(!analyze_array_comparator(
           worker, program, goto_model, ns, comparator, reason))
      {
        comparator_mode = false;
        comparators.clear();
        break;
      }
      comparators.push_back(comparator);
    }
  }
  if(!comparator_mode)
  {
    std::vector<prefix_comparatort> prefixes;
    for(const auto &worker : life.workers)
    {
      prefix_comparatort prefix;
      const auto &program =
        goto_model.goto_functions.function_map.at(worker).body;
      if(!analyze_prefix_comparator(worker, program, ns, prefix, reason))
      {
        std::cout << "NATIVE_RELATIONAL_ORDER applied=0 reason="
                  << reason << '\n';
        return false;
      }
      prefixes.push_back(prefix);
    }
    if(
      !nonnegative_prefix_lengths(goto_model, life, prefixes, reason) ||
      !prefix_results_zero(goto_model, life, prefixes, reason))
    {
      std::cout << "NATIVE_RELATIONAL_ORDER applied=0 reason="
                << reason << '\n';
      return false;
    }
    if(!prefix_transitivity_property(life, prefixes))
    {
      std::cout << "NATIVE_RELATIONAL_ORDER applied=0 reason=property\n";
      return false;
    }
    std::cout
      << "NATIVE_RELATIONAL_ORDER applied=1 rule=prefix_transitivity\n";
    return true;
  }

  if(!nonnegative_lengths(goto_model, life, comparators, reason))
  {
    std::cout << "NATIVE_RELATIONAL_ORDER applied=0 reason="
              << reason << '\n';
    return false;
  }

  const char *rule = nullptr;
  if(symmetry_property(life, comparators))
    rule = "lexicographic_symmetry";
  else if(transitivity_property(life, comparators))
    rule = "lexicographic_transitivity";
  else if(substitution_property(life, comparators))
    rule = "lexicographic_substitution";
  if(rule == nullptr)
  {
    std::cout << "NATIVE_RELATIONAL_ORDER applied=0 reason=property\n";
    return false;
  }

  log.debug() << "proved relational order law " << rule
              << messaget::eom;
  std::cout << "NATIVE_RELATIONAL_ORDER applied=1 rule=" << rule << '\n';
  return true;
}
