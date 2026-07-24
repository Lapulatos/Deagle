/*******************************************************************\

Module: Predicate-Stable Linearization

\*******************************************************************/

#include "predicate_stability_analysis.h"

#include <goto-programs/goto_model.h>

#include <util/arith_tools.h>
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
  return
    expr.id() == ID_address_of &&
    symbol_id(to_address_of_expr(expr).object(), identifier);
}

bool dereferenced_id(const exprt &src, irep_idt &identifier)
{
  const exprt &expr = strip(src);
  return
    expr.id() == ID_dereference &&
    symbol_id(to_dereference_expr(expr).pointer(), identifier);
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
  return
    expr.id() == ID_constant &&
    !to_integer(to_constant_expr(expr), value);
}

bool value_is(const exprt &expr, const mp_integer &expected)
{
  mp_integer value;
  return integer_constant(expr, value) && value == expected;
}

bool zero(const exprt &expr)
{
  return value_is(expr, 0);
}

bool one(const exprt &expr)
{
  return value_is(expr, 1);
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

bool parse_equal_zero(
  const exprt &src,
  irep_idt &identifier,
  bool &equal)
{
  const exprt &expr = strip(src);
  if(expr.id() == ID_not && expr.operands().size() == 1)
  {
    if(!parse_equal_zero(expr.op0(), identifier, equal))
      return false;
    equal = !equal;
    return true;
  }
  if(
    (expr.id() != ID_equal && expr.id() != ID_notequal) ||
    expr.operands().size() != 2)
    return false;
  if(
    (symbol_id(expr.op0(), identifier) && zero(expr.op1())) ||
    (symbol_id(expr.op1(), identifier) && zero(expr.op0())))
  {
    equal = expr.id() == ID_equal;
    return true;
  }
  return false;
}

bool parse_symbol_truth(
  const exprt &src,
  irep_idt &identifier,
  bool &positive)
{
  const exprt &expr = strip(src);
  if(symbol_id(expr, identifier))
  {
    positive = true;
    return true;
  }
  if(expr.id() == ID_not && expr.operands().size() == 1)
  {
    if(!symbol_id(strip(expr.op0()), identifier))
      return false;
    positive = false;
    return true;
  }
  bool equal = false;
  if(parse_equal_zero(expr, identifier, equal))
  {
    positive = !equal;
    return true;
  }
  return false;
}

bool contains_address(
  const exprt &expr,
  const irep_idt &identifier)
{
  irep_idt candidate;
  if(
    expr.id() == ID_address_of &&
    addressed_id(expr, candidate) &&
    candidate == identifier)
    return true;
  for(const auto &operand : expr.operands())
  {
    if(contains_address(operand, identifier))
      return true;
  }
  return false;
}

bool shared_scalar(
  const irep_idt &identifier,
  const namespacet &ns)
{
  const symbolt *symbol = nullptr;
  return
    !ns.lookup(identifier, symbol) &&
    symbol->is_static_lifetime && !symbol->is_type &&
    (symbol->type.id() == ID_signedbv ||
     symbol->type.id() == ID_unsignedbv);
}

struct program_indext
{
  std::vector<goto_programt::targett> order;
  std::map<const goto_programt::instructiont *, std::size_t> position;

  explicit program_indext(goto_programt &program)
  {
    for(auto instruction = program.instructions.begin();
        instruction != program.instructions.end(); ++instruction)
    {
      position.emplace(&*instruction, order.size());
      order.push_back(instruction);
    }
  }
};

bool parse_spawn_loop(
  goto_modelt &model,
  irep_idt &worker,
  std::vector<goto_programt::targett> &loop,
  std::string &reason)
{
  auto main = model.goto_functions.function_map.find("main");
  if(
    main == model.goto_functions.function_map.end() ||
    !main->second.body_available())
  {
    reason = "predicate_main";
    return false;
  }
  auto &program = main->second.body;
  program_indext index(program);
  goto_programt::targett create = program.instructions.end();
  std::size_t creates = 0;
  for(auto instruction : index.order)
  {
    irep_idt callee;
    if(call_id(*instruction, callee) && callee == "pthread_create")
    {
      if(
        instruction->call_arguments().size() < 3 ||
        !addressed_id(instruction->call_arguments()[2], worker))
      {
        reason = "predicate_create_resolution";
        return false;
      }
      create = instruction;
      ++creates;
    }
  }
  if(creates != 1)
  {
    reason = "predicate_create_count";
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
      if(call_id(instruction, callee) && callee == "pthread_create")
        ++global_creates;
    }
  }
  if(global_creates != 1)
  {
    reason = "predicate_global_create_count";
    return false;
  }
  const auto create_position = index.position.at(&*create);
  goto_programt::targett backedge = program.instructions.end();
  std::size_t backedges = 0;
  for(auto instruction : index.order)
  {
    if(
      instruction->is_goto() &&
      instruction->condition().is_true() &&
      instruction->targets.size() == 1 &&
      index.position.at(&*instruction->targets.front()) <=
        create_position &&
      create_position < index.position.at(&*instruction))
    {
      backedge = instruction;
      ++backedges;
    }
  }
  if(backedges != 1)
  {
    reason = "predicate_spawn_backedge";
    return false;
  }
  const auto begin =
    index.position.at(&*backedge->targets.front());
  const auto end = index.position.at(&*backedge);
  std::size_t exits = 0;
  for(std::size_t position = begin; position <= end; ++position)
  {
    auto instruction = index.order[position];
    if(
      instruction == create || instruction == backedge ||
      instruction->is_skip() || instruction->is_location())
    {
      loop.push_back(instruction);
      continue;
    }
    bool false_guard = false;
    if(
      instruction->is_goto() &&
      instruction->targets.size() == 1 &&
      index.position.at(&*instruction->targets.front()) > end &&
      boolean_constant(
        instruction->condition(), false_guard) &&
      !false_guard)
    {
      ++exits;
      loop.push_back(instruction);
      continue;
    }
    reason = "predicate_spawn_loop_shape";
    return false;
  }
  if(exits != 1)
  {
    reason = "predicate_spawn_exit";
    return false;
  }
  return true;
}

bool parse_return_predicate(
  const irep_idt &function_id,
  goto_modelt &model,
  const namespacet &ns,
  irep_idt &object,
  std::string &reason)
{
  auto function =
    model.goto_functions.function_map.find(function_id);
  if(
    function == model.goto_functions.function_map.end() ||
    !function->second.body_available())
  {
    reason = "predicate_empty_function";
    return false;
  }
  auto &program = function->second.body;
  program_indext index(program);
  std::size_t guards = 0;
  std::size_t return_one = 0;
  std::size_t return_zero = 0;
  goto_programt::targett guard = program.instructions.end();
  goto_programt::targett one_return = program.instructions.end();
  goto_programt::targett zero_return = program.instructions.end();
  for(auto instruction : index.order)
  {
    if(instruction->is_goto())
    {
      irep_idt candidate;
      bool equal = true;
      if(
        parse_equal_zero(
          instruction->condition(), candidate, equal) &&
        !equal)
      {
        object = candidate;
        guard = instruction;
        ++guards;
      }
    }
    if(instruction->is_set_return_value())
    {
      if(one(instruction->return_value()))
      {
        one_return = instruction;
        ++return_one;
      }
      else if(zero(instruction->return_value()))
      {
        zero_return = instruction;
        ++return_zero;
      }
    }
  }
  if(
    guards != 1 || return_one != 1 || return_zero != 1 ||
    !shared_scalar(object, ns) ||
    guard->targets.size() != 1 ||
    index.position.at(&*one_return) >=
      index.position.at(&*zero_return) ||
    index.position.at(&*guard->targets.front()) !=
      index.position.at(&*zero_return))
  {
    reason = "predicate_empty_schema";
    return false;
  }
  return true;
}

struct propertyt
{
  irep_idt function;
  irep_idt object;
  irep_idt result_parameter;
  goto_programt::targett error;
};

bool parse_helper_property(
  const irep_idt &function_id,
  goto_modelt &model,
  const namespacet &ns,
  propertyt &property,
  std::string &reason)
{
  auto function =
    model.goto_functions.function_map.find(function_id);
  if(
    function == model.goto_functions.function_map.end() ||
    !function->second.body_available())
    return false;
  const auto &parameters =
    to_code_type(ns.lookup(function_id).type).parameters();
  if(parameters.size() != 1)
    return false;
  property.result_parameter = parameters.front().get_identifier();
  auto &program = function->second.body;
  program_indext index(program);
  goto_programt::targett error = program.instructions.end();
  std::size_t errors = 0;
  for(auto instruction : index.order)
  {
    irep_idt callee;
    if(call_id(*instruction, callee) && callee == "reach_error")
    {
      error = instruction;
      ++errors;
    }
  }
  if(errors != 1 || index.position.at(&*error) == 0)
    return false;
  auto guard = index.order[index.position.at(&*error) - 1];
  irep_idt safe;
  bool positive = false;
  if(
    !guard->is_goto() || guard->targets.size() != 1 ||
    !parse_symbol_truth(guard->condition(), safe, positive) ||
    !positive ||
    index.position.at(&*guard->targets.front()) <=
      index.position.at(&*error))
  {
    reason = "predicate_property_polarity";
    return false;
  }
  goto_programt::targett predicate_call =
    program.instructions.end();
  irep_idt predicate_result;
  irep_idt predicate_function;
  std::size_t predicate_calls = 0;
  std::size_t safe_true = 0;
  std::size_t safe_from_predicate = 0;
  std::size_t result_guards = 0;
  int depth = 0;
  int error_depth = 0;
  for(auto instruction : index.order)
  {
    if(instruction->is_atomic_begin())
      ++depth;
    else if(instruction->is_atomic_end())
      --depth;
    if(instruction == error)
      error_depth = depth;
    irep_idt callee;
    if(call_id(*instruction, callee))
    {
      irep_idt lhs;
      if(symbol_id(instruction->call_lhs(), lhs))
      {
        predicate_call = instruction;
        predicate_result = lhs;
        predicate_function = callee;
        ++predicate_calls;
      }
    }
    if(instruction->is_assign())
    {
      irep_idt lhs;
      if(
        symbol_id(instruction->assign_lhs(), lhs) &&
        lhs == safe)
      {
        if(instruction->assign_rhs().is_true())
          ++safe_true;
        else
        {
          const exprt &rhs = strip(instruction->assign_rhs());
          const exprt *condition = &rhs;
          if(
            rhs.id() == ID_if &&
            rhs.operands().size() == 3 &&
            rhs.op1().is_true() && rhs.op2().is_false())
            condition = &rhs.op0();
          irep_idt candidate;
          bool equal = false;
          if(
            parse_equal_zero(
              *condition, candidate, equal) &&
            equal && candidate == predicate_result)
            ++safe_from_predicate;
        }
      }
    }
    if(instruction->is_goto())
    {
      irep_idt candidate;
      bool truth = false;
      if(
        parse_symbol_truth(
          instruction->condition(), candidate, truth) &&
        candidate == property.result_parameter && truth)
        ++result_guards;
    }
  }
  if(
    depth != 0 || error_depth <= 0 ||
    predicate_calls != 1 || safe_true != 1 ||
    safe_from_predicate != 1 || result_guards != 1)
  {
    reason = "predicate_property_schema";
    return false;
  }
  if(!parse_return_predicate(
       predicate_function,
       model,
       ns,
       property.object,
       reason))
    return false;
  property.function = function_id;
  property.error = error;
  return true;
}

bool parse_direct_property(
  const irep_idt &function_id,
  goto_modelt &model,
  const namespacet &ns,
  propertyt &property,
  std::string &reason)
{
  auto function =
    model.goto_functions.function_map.find(function_id);
  auto &program = function->second.body;
  program_indext index(program);
  goto_programt::targett error = program.instructions.end();
  std::size_t errors = 0;
  for(auto instruction : index.order)
  {
    irep_idt callee;
    if(call_id(*instruction, callee) && callee == "reach_error")
    {
      error = instruction;
      ++errors;
    }
  }
  if(errors != 1 || index.position.at(&*error) == 0)
  {
    reason = "predicate_direct_property_count";
    return false;
  }
  auto guard = index.order[index.position.at(&*error) - 1];
  bool equal = true;
  if(
    !guard->is_goto() || guard->targets.size() != 1 ||
    !parse_equal_zero(
      guard->condition(), property.object, equal) ||
    equal || !shared_scalar(property.object, ns) ||
    index.position.at(&*guard->targets.front()) <=
      index.position.at(&*error))
  {
    reason = "predicate_direct_property_schema";
    return false;
  }
  int depth = 0;
  int error_depth = 0;
  bool lock_active = false;
  irep_idt lock;
  for(std::size_t position = 0;
      position <= index.position.at(&*error); ++position)
  {
    auto instruction = index.order[position];
    if(instruction->is_atomic_begin())
      ++depth;
    else if(instruction->is_atomic_end())
      --depth;
    irep_idt callee;
    if(call_id(*instruction, callee))
    {
      irep_idt candidate;
      if(
        callee == "pthread_mutex_lock" &&
        instruction->call_arguments().size() == 1 &&
        addressed_id(
          instruction->call_arguments().front(), candidate))
      {
        lock_active = true;
        lock = candidate;
      }
      else if(
        callee == "pthread_mutex_unlock" &&
        instruction->call_arguments().size() == 1 &&
        addressed_id(
          instruction->call_arguments().front(), candidate) &&
        candidate == lock)
        lock_active = false;
    }
    if(instruction == error)
      error_depth = depth;
  }
  if(error_depth <= 0 && !lock_active)
  {
    reason = "predicate_direct_property_protection";
    return false;
  }
  property.function = function_id;
  property.error = error;
  property.result_parameter.clear();
  return true;
}

struct loopt
{
  irep_idt function;
  irep_idt update_function;
  irep_idt property_function;
  irep_idt result;
  bool result_property = false;
};

bool parse_iteration_loop(
  const irep_idt &function_id,
  goto_modelt &model,
  const namespacet &ns,
  loopt &loop,
  propertyt &property,
  std::string &reason)
{
  auto function =
    model.goto_functions.function_map.find(function_id);
  if(
    function == model.goto_functions.function_map.end() ||
    !function->second.body_available())
    return false;
  auto &program = function->second.body;
  program_indext index(program);
  goto_programt::targett backedge = program.instructions.end();
  std::size_t backedges = 0;
  for(auto instruction : index.order)
  {
    if(
      instruction->is_goto() &&
      instruction->targets.size() == 1 &&
      index.position.at(&*instruction->targets.front()) <
        index.position.at(&*instruction))
    {
      backedge = instruction;
      ++backedges;
    }
  }
  if(backedges != 1)
    return false;
  const auto begin =
    index.position.at(&*backedge->targets.front());
  const auto end = index.position.at(&*backedge);
  std::vector<goto_programt::targett> calls;
  for(std::size_t position = begin; position <= end; ++position)
  {
    if(index.order[position]->is_function_call())
      calls.push_back(index.order[position]);
  }
  goto_programt::targett property_call =
    program.instructions.end();
  std::size_t helper_properties = 0;
  for(auto call : calls)
  {
    irep_idt callee;
    call_id(*call, callee);
    propertyt candidate;
    std::string ignored;
    if(parse_helper_property(
         callee, model, ns, candidate, ignored))
    {
      property = candidate;
      property_call = call;
      loop.property_function = callee;
      ++helper_properties;
    }
  }
  if(helper_properties == 1)
  {
    if(
      property_call->call_arguments().size() != 1 ||
      !symbol_id(
        property_call->call_arguments().front(),
        loop.result))
    {
      reason = "predicate_property_actual";
      return false;
    }
    goto_programt::targett update_call =
      program.instructions.end();
    std::size_t updates = 0;
    for(auto call : calls)
    {
      irep_idt lhs;
      irep_idt callee;
      if(
        symbol_id(call->call_lhs(), lhs) &&
        lhs == loop.result &&
        call_id(*call, callee) &&
        callee != loop.property_function)
      {
        update_call = call;
        loop.update_function = callee;
        ++updates;
      }
    }
    if(
      updates != 1 ||
      index.position.at(&*update_call) >=
        index.position.at(&*property_call))
    {
      reason = "predicate_update_call";
      return false;
    }
    loop.result_property = true;
  }
  else if(helper_properties == 0)
  {
    if(!parse_direct_property(
         function_id, model, ns, property, reason))
      return false;
    std::size_t updates = 0;
    for(auto call : calls)
    {
      irep_idt callee;
      if(
        call_id(*call, callee) &&
        callee != "pthread_mutex_lock" &&
        callee != "pthread_mutex_unlock" &&
        callee != "reach_error" && callee != "abort" &&
        index.position.at(&*call) <
          index.position.at(&*property.error))
      {
        loop.update_function = callee;
        ++updates;
      }
    }
    if(updates != 1)
    {
      reason = "predicate_direct_update_call";
      return false;
    }
  }
  else
  {
    reason = "predicate_multiple_properties";
    return false;
  }
  loop.function = function_id;
  return true;
}

bool blocks_on_false(
  const irep_idt &callee,
  goto_modelt &model)
{
  auto function =
    model.goto_functions.function_map.find(callee);
  if(
    function == model.goto_functions.function_map.end() ||
    !function->second.body_available())
    return false;
  const namespacet ns(model.symbol_table);
  const auto &parameters =
    to_code_type(ns.lookup(callee).type).parameters();
  if(parameters.size() != 1)
    return false;
  const irep_idt parameter =
    parameters.front().get_identifier();
  auto &program = function->second.body;
  program_indext index(program);
  goto_programt::targett guard = program.instructions.end();
  goto_programt::targett abort_call =
    program.instructions.end();
  std::size_t guards = 0;
  std::size_t aborts = 0;
  for(auto candidate : index.order)
  {
    if(candidate->is_goto())
    {
      irep_idt tested;
      bool positive = false;
      if(
        parse_symbol_truth(
          candidate->condition(), tested, positive) &&
        tested == parameter && positive &&
        candidate->targets.size() == 1)
      {
        guard = candidate;
        ++guards;
      }
    }
    irep_idt nested;
    if(call_id(*candidate, nested) && nested == "abort")
    {
      abort_call = candidate;
      ++aborts;
    }
  }
  if(
    guards != 1 || aborts != 1 ||
    index.position.at(&*guard) >=
      index.position.at(&*abort_call) ||
    index.position.at(&*guard->targets.front()) <=
      index.position.at(&*abort_call))
    return false;
  auto abort_function =
    model.goto_functions.function_map.find("abort");
  if(
    abort_function ==
      model.goto_functions.function_map.end() ||
    !abort_function->second.body_available())
    return false;
  for(const auto &candidate :
      abort_function->second.body.instructions)
  {
    bool condition_value = true;
    if(
      candidate.is_assume() &&
      boolean_constant(
        candidate.condition(), condition_value) &&
      !condition_value)
      return true;
  }
  return false;
}

bool false_call(
  const goto_programt::instructiont &instruction,
  goto_modelt &model)
{
  irep_idt callee;
  return
    call_id(instruction, callee) &&
    instruction.call_arguments().size() == 1 &&
    zero(instruction.call_arguments().front()) &&
    blocks_on_false(callee, model);
}

bool parse_dereference_equal(
  const exprt &src,
  const irep_idt &pointer,
  const mp_integer &value)
{
  const exprt &expr = strip(src);
  if(
    expr.id() != ID_equal ||
    expr.operands().size() != 2)
    return false;
  irep_idt candidate;
  return
    (dereferenced_id(expr.op0(), candidate) &&
     candidate == pointer &&
     value_is(expr.op1(), value)) ||
    (dereferenced_id(expr.op1(), candidate) &&
     candidate == pointer &&
     value_is(expr.op0(), value));
}

bool parse_cas_equality_condition(
  const exprt &src,
  const irep_idt &object_pointer,
  const irep_idt &expected,
  bool &true_on_equal)
{
  const exprt &expr = strip(src);
  if(expr.id() == ID_not && expr.operands().size() == 1)
  {
    if(!parse_cas_equality_condition(
         expr.op0(), object_pointer, expected, true_on_equal))
      return false;
    true_on_equal = !true_on_equal;
    return true;
  }
  if(
    (expr.id() != ID_equal && expr.id() != ID_notequal) ||
    expr.operands().size() != 2)
    return false;
  irep_idt pointer;
  irep_idt compared;
  const bool operands_match =
    (dereferenced_id(expr.op0(), pointer) &&
     pointer == object_pointer &&
     symbol_id(expr.op1(), compared) &&
     compared == expected) ||
    (dereferenced_id(expr.op1(), pointer) &&
     pointer == object_pointer &&
     symbol_id(expr.op0(), compared) &&
     compared == expected);
  if(!operands_match)
    return false;
  true_on_equal = expr.id() == ID_equal;
  return true;
}

bool validate_flag_lock_function(
  const irep_idt &function_id,
  const mp_integer &required,
  const mp_integer &written,
  goto_modelt &model,
  const namespacet &ns)
{
  auto function =
    model.goto_functions.function_map.find(function_id);
  if(
    function == model.goto_functions.function_map.end() ||
    !function->second.body_available())
    return false;
  const auto &parameters =
    to_code_type(ns.lookup(function_id).type).parameters();
  if(parameters.size() != 1)
    return false;
  const irep_idt pointer =
    parameters.front().get_identifier();
  int depth = 0;
  std::size_t guards = 0;
  std::size_t writes = 0;
  for(const auto &instruction :
      function->second.body.instructions)
  {
    if(instruction.is_atomic_begin())
    {
      ++depth;
      continue;
    }
    if(instruction.is_atomic_end())
    {
      --depth;
      continue;
    }
    if(
      instruction.is_end_function() ||
      instruction.is_skip() ||
      instruction.is_location() ||
      instruction.is_decl() ||
      instruction.is_dead())
      continue;
    if(depth != 1)
      return false;
    if(instruction.is_assign())
    {
      irep_idt lhs;
      if(
        dereferenced_id(
          instruction.assign_lhs(), lhs) &&
        lhs == pointer &&
        value_is(instruction.assign_rhs(), written))
      {
        ++writes;
        continue;
      }
      return false;
    }
    irep_idt callee;
    if(
      call_id(instruction, callee) &&
      instruction.call_arguments().size() == 1 &&
      parse_dereference_equal(
        instruction.call_arguments().front(),
        pointer,
        required) &&
      blocks_on_false(callee, model))
    {
      ++guards;
      continue;
    }
    return false;
  }
  return depth == 0 && guards == 1 && writes == 1;
}

bool validate_cas_helper(
  const irep_idt &function_id,
  goto_modelt &model,
  const namespacet &ns,
  std::string &reason)
{
  auto function =
    model.goto_functions.function_map.find(function_id);
  if(
    function == model.goto_functions.function_map.end() ||
    !function->second.body_available())
  {
    reason = "predicate_cas_helper_missing";
    return false;
  }
  const auto &parameters =
    to_code_type(ns.lookup(function_id).type).parameters();
  if(parameters.size() != 4)
  {
    reason = "predicate_cas_helper_arity";
    return false;
  }
  const auto object_pointer = parameters[0].get_identifier();
  const auto expected = parameters[1].get_identifier();
  const auto desired = parameters[2].get_identifier();
  const auto result_pointer = parameters[3].get_identifier();
  auto &program = function->second.body;
  program_indext index(program);
  int depth = 0;
  std::size_t equality = 0;
  std::size_t object_writes = 0;
  std::size_t result_one = 0;
  std::size_t result_zero = 0;
  goto_programt::targett branch = program.instructions.end();
  bool branch_true_on_equal = false;
  std::size_t object_write_position = index.order.size();
  std::size_t result_one_position = index.order.size();
  std::size_t result_zero_position = index.order.size();
  for(auto instruction : index.order)
  {
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
      reason = "predicate_cas_atomic";
      return false;
    }
    if(instruction->is_goto())
    {
      if(instruction->condition().is_true())
        continue;
      bool true_on_equal = false;
      if(
        instruction->targets.size() == 1 &&
        parse_cas_equality_condition(
          instruction->condition(),
          object_pointer,
          expected,
          true_on_equal))
      {
        branch = instruction->targets.front();
        branch_true_on_equal = true_on_equal;
        ++equality;
        continue;
      }
      reason = "predicate_cas_control";
      return false;
    }
    if(!instruction->is_assign())
    {
      reason = "predicate_cas_effect";
      return false;
    }
    irep_idt pointer;
    if(!dereferenced_id(
         instruction->assign_lhs(), pointer))
    {
      reason = "predicate_cas_lhs";
      return false;
    }
    const auto position =
      index.position.at(&*instruction);
    if(pointer == object_pointer)
    {
      irep_idt source;
      if(
        !symbol_id(instruction->assign_rhs(), source) ||
        source != desired)
      {
        reason = "predicate_cas_update";
        return false;
      }
      object_write_position = position;
      ++object_writes;
    }
    else if(pointer == result_pointer)
    {
      if(one(instruction->assign_rhs()))
      {
        result_one_position = position;
        ++result_one;
      }
      else if(zero(instruction->assign_rhs()))
      {
        result_zero_position = position;
        ++result_zero;
      }
      else
      {
        reason = "predicate_cas_result";
        return false;
      }
    }
    else
    {
      reason = "predicate_cas_extra_write";
      return false;
    }
  }
  if(
    depth != 0 || equality != 1 ||
    object_writes != 1 || result_one != 1 ||
    result_zero != 1)
  {
    reason = "predicate_cas_shape";
    return false;
  }
  const auto branch_position =
    index.position.at(&*branch);
  const bool success_before_branch =
    object_write_position < branch_position &&
    result_one_position < branch_position;
  const bool failure_before_branch =
    result_zero_position < branch_position;
  const bool original_layout =
    success_before_branch && !failure_before_branch;
  const bool inverted_layout =
    !success_before_branch && failure_before_branch &&
    object_write_position >= branch_position &&
    result_one_position >= branch_position;
  if(
    (!original_layout && !inverted_layout) ||
    (branch_true_on_equal && !inverted_layout) ||
    (!branch_true_on_equal && !original_layout))
  {
    reason = "predicate_cas_branch_semantics";
    return false;
  }
  return true;
}

struct updatet
{
  irep_idt function;
  irep_idt object;
  irep_idt value;
  irep_idt cas_function;
  goto_programt::targett write;
  goto_programt::targett cas_call;
  bool cas = false;
};

bool validate_update(
  const loopt &loop,
  const propertyt &property,
  goto_modelt &model,
  const namespacet &ns,
  updatet &update,
  std::string &reason)
{
  auto function =
    model.goto_functions.function_map.find(
      loop.update_function);
  if(
    function == model.goto_functions.function_map.end() ||
    !function->second.body_available())
  {
    reason = "predicate_update_function";
    return false;
  }
  auto &program = function->second.body;
  program_indext index(program);
  update.function = loop.update_function;
  update.object = property.object;
  update.write = program.instructions.end();
  update.cas_call = program.instructions.end();
  std::size_t direct_writes = 0;
  std::size_t cas_calls = 0;
  for(auto instruction : index.order)
  {
    if(instruction->is_assign())
    {
      irep_idt lhs;
      irep_idt rhs;
      if(
        symbol_id(instruction->assign_lhs(), lhs) &&
        lhs == property.object)
      {
        if(!symbol_id(instruction->assign_rhs(), rhs))
        {
          reason = "predicate_update_value";
          return false;
        }
        update.value = rhs;
        update.write = instruction;
        ++direct_writes;
      }
    }
    irep_idt callee;
    if(
      call_id(*instruction, callee) &&
      instruction->call_arguments().size() == 4)
    {
      irep_idt object;
      irep_idt desired;
      if(
        addressed_id(
          instruction->call_arguments()[0], object) &&
        object == property.object &&
        symbol_id(
          instruction->call_arguments()[2], desired))
      {
        update.value = desired;
        update.cas_function = callee;
        update.cas_call = instruction;
        ++cas_calls;
      }
    }
  }
  if(direct_writes + cas_calls != 1)
  {
    reason = "predicate_update_count";
    return false;
  }
  update.cas = cas_calls == 1;
  const auto linearization =
    update.cas ? update.cas_call : update.write;
  const auto linearization_position =
    index.position.at(&*linearization);
  std::size_t nonzero_guards = 0;
  goto_programt::targett nonzero_guard =
    program.instructions.end();
  for(std::size_t position = 0;
      position < linearization_position; ++position)
  {
    auto instruction = index.order[position];
    if(
      !instruction->is_goto() ||
      instruction->targets.size() != 1)
      continue;
    irep_idt candidate;
    bool equal = true;
    if(
      parse_equal_zero(
        instruction->condition(), candidate, equal) &&
      !equal && candidate == update.value &&
      index.position.at(&*instruction->targets.front()) <=
        linearization_position)
    {
      nonzero_guard = instruction;
      ++nonzero_guards;
    }
  }
  if(nonzero_guards != 1)
  {
    reason = "predicate_nonzero_guard";
    return false;
  }
  const auto guard_position =
    index.position.at(&*nonzero_guard);
  bool failure_infeasible = false;
  bool failure_returns_zero = false;
  for(std::size_t position = guard_position + 1;
      position <
        index.position.at(&*nonzero_guard->targets.front());
      ++position)
  {
    auto instruction = index.order[position];
    if(false_call(*instruction, model))
      failure_infeasible = true;
    if(
      instruction->is_set_return_value() &&
      zero(instruction->return_value()))
      failure_returns_zero = true;
  }
  if(
    loop.result_property
      ? !failure_returns_zero
      : !failure_infeasible)
  {
    reason = "predicate_failure_path";
    return false;
  }
  if(update.cas)
  {
    if(!validate_cas_helper(
         update.cas_function, model, ns, reason))
      return false;
    irep_idt result;
    if(!addressed_id(
         update.cas_call->call_arguments()[3], result))
    {
      reason = "predicate_cas_actual";
      return false;
    }
    std::size_t success_guards = 0;
    for(std::size_t position =
          linearization_position + 1;
        position < index.order.size(); ++position)
    {
      auto instruction = index.order[position];
      if(!instruction->is_goto())
        continue;
      const exprt &condition = strip(instruction->condition());
      const exprt *candidate = &condition;
      if(
        condition.id() == ID_not &&
        condition.operands().size() == 1)
        candidate = &strip(condition.op0());
      if(
        candidate->id() == ID_equal &&
        candidate->operands().size() == 2)
      {
        irep_idt tested;
        if(
          symbol_id(candidate->op0(), tested) &&
          tested == result &&
          one(candidate->op1()))
          ++success_guards;
      }
      irep_idt tested;
      bool equal = false;
      if(
        parse_equal_zero(
          instruction->condition(), tested, equal) &&
        equal && tested == result)
        ++success_guards;
    }
    if(success_guards != 1)
    {
      reason = "predicate_cas_success_guard";
      return false;
    }
  }
  else
  {
    int depth = 0;
    bool protected_write = false;
    bool lock_active = false;
    irep_idt lock;
    for(std::size_t position = 0;
        position <= linearization_position; ++position)
    {
      auto instruction = index.order[position];
      if(instruction->is_atomic_begin())
        ++depth;
      else if(instruction->is_atomic_end())
        --depth;
      irep_idt callee;
      if(call_id(*instruction, callee))
      {
        irep_idt candidate;
        if(
          callee == "pthread_mutex_lock" &&
          instruction->call_arguments().size() == 1 &&
          addressed_id(
            instruction->call_arguments().front(),
            candidate))
        {
          lock_active = true;
          lock = candidate;
        }
        else if(
          callee == "pthread_mutex_unlock" &&
          instruction->call_arguments().size() == 1 &&
          addressed_id(
            instruction->call_arguments().front(),
            candidate) && candidate == lock)
          lock_active = false;
      }
      if(position == linearization_position)
        protected_write = depth > 0 || lock_active;
    }
    if(!protected_write)
    {
      reason = "predicate_update_protection";
      return false;
    }
  }
  std::size_t success_returns = 0;
  std::size_t success_returns_after_linearization = 0;
  for(std::size_t position = 0;
      position < index.order.size(); ++position)
  {
    auto instruction = index.order[position];
    if(
      instruction->is_set_return_value() &&
      one(instruction->return_value()))
    {
      ++success_returns;
      if(position > linearization_position)
        ++success_returns_after_linearization;
    }
  }
  if(
    loop.result_property &&
    (success_returns != 1 ||
     success_returns_after_linearization != 1))
  {
    reason = "predicate_success_result";
    return false;
  }
  return true;
}

bool validate_worker_initialization(
  const irep_idt &worker,
  const irep_idt &iteration,
  const irep_idt &object,
  goto_modelt &model,
  const namespacet &ns,
  std::set<irep_idt> &initializer_functions,
  std::string &reason)
{
  if(worker == iteration)
    return true;
  auto function =
    model.goto_functions.function_map.find(worker);
  auto &program = function->second.body;
  program_indext index(program);
  goto_programt::targett iteration_call =
    program.instructions.end();
  std::size_t iteration_calls = 0;
  for(auto instruction : index.order)
  {
    irep_idt callee;
    if(call_id(*instruction, callee) && callee == iteration)
    {
      iteration_call = instruction;
      ++iteration_calls;
    }
  }
  if(iteration_calls != 1)
  {
    reason = "predicate_worker_iteration";
    return false;
  }
  goto_programt::targett init_call =
    program.instructions.end();
  irep_idt init_function;
  std::size_t init_calls = 0;
  for(std::size_t position = 0;
      position < index.position.at(&*iteration_call);
      ++position)
  {
    auto instruction = index.order[position];
    irep_idt callee;
    if(!call_id(*instruction, callee))
      continue;
    auto called =
      model.goto_functions.function_map.find(callee);
    if(
      called == model.goto_functions.function_map.end() ||
      !called->second.body_available())
      continue;
    std::size_t zero_writes = 0;
    for(const auto &candidate :
        called->second.body.instructions)
    {
      irep_idt lhs;
      if(
        candidate.is_assign() &&
        symbol_id(candidate.assign_lhs(), lhs) &&
        lhs == object &&
        zero(candidate.assign_rhs()))
        ++zero_writes;
    }
    if(zero_writes == 1)
    {
      init_call = instruction;
      init_function = callee;
      ++init_calls;
    }
  }
  if(init_calls == 0)
    return true;
  if(init_calls != 1)
  {
    reason = "predicate_init_call";
    return false;
  }
  initializer_functions.insert(init_function);
  const auto init_position =
    index.position.at(&*init_call);
  irep_idt state;
  goto_programt::targett state_write =
    program.instructions.end();
  std::size_t state_guards = 0;
  std::size_t state_writes = 0;
  for(std::size_t position = 0;
      position < index.position.at(&*iteration_call);
      ++position)
  {
    auto instruction = index.order[position];
    if(instruction->is_goto())
    {
      irep_idt candidate;
      bool equal = false;
      if(
        parse_equal_zero(
          instruction->condition(), candidate, equal) &&
        equal &&
        instruction->targets.size() == 1 &&
        index.position.at(&*instruction->targets.front()) ==
          init_position)
      {
        state = candidate;
        ++state_guards;
      }
    }
    if(instruction->is_assign())
    {
      irep_idt lhs;
      if(
        symbol_id(instruction->assign_lhs(), lhs) &&
        lhs == state && one(instruction->assign_rhs()) &&
        position > init_position)
      {
        state_write = instruction;
        ++state_writes;
      }
    }
  }
  if(
    state_guards != 1 || state_writes != 1 ||
    !shared_scalar(state, ns) ||
    index.position.at(&*state_write) != init_position + 1)
  {
    reason = "predicate_init_state";
    return false;
  }
  irep_idt init_lock;
  irep_idt acquire_function;
  std::size_t acquires = 0;
  for(std::size_t position = 0;
      position < init_position; ++position)
  {
    auto instruction = index.order[position];
    irep_idt callee;
    irep_idt candidate;
    if(
      call_id(*instruction, callee) &&
      instruction->call_arguments().size() == 1 &&
      addressed_id(
        instruction->call_arguments().front(),
        candidate))
    {
      init_lock = candidate;
      acquire_function = callee;
      ++acquires;
    }
  }
  irep_idt release_function;
  std::size_t releases = 0;
  for(std::size_t position =
        index.position.at(&*state_write) + 1;
      position < index.position.at(&*iteration_call);
      ++position)
  {
    auto instruction = index.order[position];
    irep_idt callee;
    irep_idt candidate;
    if(
      call_id(*instruction, callee) &&
      instruction->call_arguments().size() == 1 &&
      addressed_id(
        instruction->call_arguments().front(),
        candidate) &&
      candidate == init_lock)
    {
      release_function = callee;
      ++releases;
    }
  }
  if(
    acquires != 1 || releases != 1 ||
    (acquire_function == "pthread_mutex_lock"
       ? release_function != "pthread_mutex_unlock"
       : acquire_function == release_function))
  {
    reason = "predicate_init_lock";
    return false;
  }
  if(
    acquire_function != "pthread_mutex_lock" &&
    (!validate_flag_lock_function(
       acquire_function, 0, 1, model, ns) ||
     !validate_flag_lock_function(
       release_function, 1, 0, model, ns)))
  {
    reason = "predicate_init_lock_semantics";
    return false;
  }
  return true;
}

bool global_coverage(
  const propertyt &property,
  const updatet &update,
  const std::set<irep_idt> &initializer_functions,
  goto_modelt &model,
  std::string &reason)
{
  std::size_t reach_errors = 0;
  std::size_t object_zero_writes = 0;
  std::size_t object_nonzero_writes = 0;
  std::size_t cas_calls = 0;
  for(auto &function_entry :
      model.goto_functions.function_map)
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
        if(callee == "reach_error")
          ++reach_errors;
        if(
          update.cas && callee == update.cas_function &&
          !instruction->call_arguments().empty())
        {
          irep_idt actual;
          if(
            addressed_id(
              instruction->call_arguments().front(),
              actual) &&
            actual == property.object)
          {
            if(&*instruction != &*update.cas_call)
            {
              reason = "predicate_external_cas";
              return false;
            }
            ++cas_calls;
          }
        }
        for(const auto &argument :
            instruction->call_arguments())
        {
          if(
            contains_address(argument, property.object) &&
            (!update.cas ||
             &*instruction != &*update.cas_call))
          {
            reason = "predicate_address_escape";
            return false;
          }
        }
      }
      if(instruction->is_assign())
      {
        irep_idt lhs;
        if(
          symbol_id(instruction->assign_lhs(), lhs) &&
          lhs == property.object)
        {
          if(
            function_entry.first == "__CPROVER_initialize" ||
            initializer_functions.find(function_entry.first) !=
              initializer_functions.end())
          {
            if(!zero(instruction->assign_rhs()))
            {
              reason = "predicate_initializer_value";
              return false;
            }
            ++object_zero_writes;
          }
          else if(&*instruction == &*update.write)
            ++object_nonzero_writes;
          else
          {
            reason = "predicate_external_write";
            return false;
          }
        }
      }
      if(
        instruction->is_assert() &&
        function_entry.first != "reach_error")
      {
        reason = "predicate_external_assertion";
        return false;
      }
    }
  }
  if(
    reach_errors != 1 ||
    object_zero_writes < 1 ||
    (update.cas ? cas_calls != 1
                : object_nonzero_writes != 1))
  {
    reason = "predicate_global_coverage";
    return false;
  }
  return true;
}
} // namespace

bool predicate_stable_linearization_transform(
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
    std::cout << "NATIVE_PREDICATE_STABILITY applied=0 reason="
              << reason << '\n';
    return false;
  }
  auto worker_function =
    goto_model.goto_functions.function_map.find(worker);
  if(
    worker_function ==
      goto_model.goto_functions.function_map.end() ||
    !worker_function->second.body_available())
  {
    std::cout
      << "NATIVE_PREDICATE_STABILITY applied=0 reason="
      << "predicate_worker\n";
    return false;
  }
  std::vector<irep_idt> candidates{worker};
  for(const auto &instruction :
      worker_function->second.body.instructions)
  {
    irep_idt callee;
    if(call_id(instruction, callee))
      candidates.push_back(callee);
  }
  loopt loop;
  propertyt property;
  std::size_t matches = 0;
  for(const auto &candidate : candidates)
  {
    loopt parsed_loop;
    propertyt parsed_property;
    std::string ignored;
    if(parse_iteration_loop(
         candidate,
         goto_model,
         ns,
         parsed_loop,
         parsed_property,
         ignored))
    {
      loop = parsed_loop;
      property = parsed_property;
      ++matches;
    }
  }
  if(matches != 1)
  {
    std::cout
      << "NATIVE_PREDICATE_STABILITY applied=0 reason="
      << "predicate_iteration_count\n";
    return false;
  }
  updatet update;
  if(!validate_update(
       loop, property, goto_model, ns, update, reason))
  {
    std::cout << "NATIVE_PREDICATE_STABILITY applied=0 reason="
              << reason << '\n';
    return false;
  }
  std::set<irep_idt> initializer_functions;
  if(!validate_worker_initialization(
       worker,
       loop.function,
       property.object,
       goto_model,
       ns,
       initializer_functions,
       reason) ||
     !global_coverage(
       property,
       update,
       initializer_functions,
       goto_model,
       reason))
  {
    std::cout << "NATIVE_PREDICATE_STABILITY applied=0 reason="
              << reason << '\n';
    return false;
  }
  for(auto instruction : spawn_loop)
    instruction->turn_into_skip();
  goto_model.goto_functions.update();
  std::cout << "NATIVE_PREDICATE_STABILITY applied=1 worker="
            << worker << " iteration=" << loop.function
            << " update=" << update.function
            << " object=" << property.object
            << " mode=" << (update.cas ? "cas" : "direct")
            << '\n';
  (void)message_handler;
  return true;
}
