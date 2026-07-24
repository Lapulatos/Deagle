/*******************************************************************\

Module: Join-Scoped Compositional Effect Summary

\*******************************************************************/

#include "jces_analysis.h"

#include <goto-programs/goto_model.h>

#include <util/arith_tools.h>
#include <util/bitvector_types.h>
#include <util/expr_util.h>
#include <util/message.h>
#include <util/namespace.h>
#include <util/pointer_expr.h>
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
} // namespace

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
