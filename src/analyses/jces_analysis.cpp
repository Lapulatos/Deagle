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
} // namespace

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
