/*******************************************************************\

Module: Lock-Boundary Ego-Thread Abstraction

\*******************************************************************/

#include "lock_ego_abstraction.h"

#include <goto-programs/goto_model.h>

#include <util/expr_util.h>
#include <util/namespace.h>
#include <util/pointer_expr.h>
#include <util/std_code.h>
#include <util/std_expr.h>
#include <util/std_types.h>
#include <util/symbol.h>

#include <algorithm>
#include <iostream>
#include <map>
#include <set>
#include <string>
#include <vector>

namespace
{
const exprt &without_cast(const exprt &expr)
{
  return skip_typecast(expr);
}

bool direct_symbol(const exprt &expr, irep_idt &identifier)
{
  const exprt &value = without_cast(expr);
  if(value.id() != ID_symbol)
    return false;
  identifier = to_symbol_expr(value).get_identifier();
  return true;
}

bool addressed_symbol(const exprt &expr, irep_idt &identifier)
{
  const exprt &value = without_cast(expr);
  if(value.id() != ID_address_of)
    return false;
  return direct_symbol(
    without_cast(to_address_of_expr(value).object()), identifier);
}

bool direct_call_identifier(
  const goto_programt::instructiont &instruction,
  irep_idt &identifier)
{
  return
    instruction.is_function_call() &&
    direct_symbol(instruction.call_function(), identifier);
}

bool is_zero(const exprt &expr)
{
  const exprt &value = without_cast(expr);
  return value.is_zero() ||
         (value.id() == ID_constant && value.get(ID_value) == "NULL");
}

bool parse_mutex_call(
  const goto_programt::instructiont &instruction,
  const irep_idt &expected,
  irep_idt &mutex)
{
  irep_idt callee;
  return
    direct_call_identifier(instruction, callee) &&
    callee == expected &&
    instruction.call_arguments().size() == 1 &&
    addressed_symbol(instruction.call_arguments().front(), mutex);
}

bool shared_symbol(
  const irep_idt &identifier,
  const namespacet &ns,
  const symbolt *&symbol)
{
  if(ns.lookup(identifier, symbol))
    return false;
  return
    symbol->is_static_lifetime && !symbol->is_type &&
    symbol->type.id() != ID_code;
}

void collect_symbols(const exprt &expr, std::set<irep_idt> &symbols)
{
  const exprt &value = without_cast(expr);
  if(value.id() == ID_symbol)
    symbols.insert(to_symbol_expr(value).get_identifier());
  for(const auto &operand : value.operands())
    collect_symbols(operand, symbols);
}

bool contains_pointer_access(const exprt &expr)
{
  const exprt &value = without_cast(expr);
  if(value.id() == ID_dereference || value.id() == ID_address_of)
    return true;
  for(const auto &operand : value.operands())
  {
    if(contains_pointer_access(operand))
      return true;
  }
  return false;
}

bool collect_shared_reads(
  const exprt &expr,
  int lock_depth,
  const irep_idt &mutex,
  const namespacet &ns,
  std::set<irep_idt> &outside_reads,
  std::string &reason)
{
  if(contains_pointer_access(expr))
  {
    reason = "unsupported_pointer_read";
    return false;
  }
  std::set<irep_idt> symbols;
  collect_symbols(expr, symbols);
  for(const auto &identifier : symbols)
  {
    const symbolt *symbol = nullptr;
    if(!shared_symbol(identifier, ns, symbol) || identifier == mutex)
      continue;
    if(symbol->type.id() == ID_pointer)
    {
      reason = "unsupported_shared_read";
      return false;
    }
    if(lock_depth == 0)
      outside_reads.insert(identifier);
  }
  return true;
}

struct spawn_loopt
{
  irep_idt worker;
  exprt argument;
  goto_programt::targett create;
  goto_programt::targett head;
  goto_programt::targett backedge;
};

bool collect_spawn_loop(
  goto_modelt &model,
  const namespacet &ns,
  spawn_loopt &spawn,
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

  auto &program = main->second.body;
  std::vector<goto_programt::targett> order;
  std::map<const goto_programt::instructiont *, std::size_t> positions;
  goto_programt::targett create = program.instructions.end();
  irep_idt worker;
  exprt argument;
  for(auto instruction = program.instructions.begin();
      instruction != program.instructions.end(); ++instruction)
  {
    positions.emplace(&*instruction, order.size());
    order.push_back(instruction);
    irep_idt callee;
    if(
      !direct_call_identifier(*instruction, callee) ||
      callee != "pthread_create")
      continue;
    if(create != program.instructions.end())
    {
      reason = "multiple_create_sites";
      return false;
    }
    if(
      instruction->call_arguments().size() != 4 ||
      !instruction->call_lhs().is_nil() ||
      !is_zero(instruction->call_arguments()[1]) ||
      !is_zero(instruction->call_arguments()[3]) ||
      !addressed_symbol(instruction->call_arguments()[2], worker))
    {
      reason = "create_shape";
      return false;
    }
    const symbolt *worker_symbol = nullptr;
    if(
      ns.lookup(worker, worker_symbol) ||
      worker_symbol->type.id() != ID_code)
    {
      reason = "worker_resolution";
      return false;
    }
    create = instruction;
    argument = instruction->call_arguments()[3];
  }
  if(create == program.instructions.end())
  {
    reason = "missing_create";
    return false;
  }

  const auto create_position = positions.at(&*create);
  goto_programt::targett head = program.instructions.end();
  goto_programt::targett backedge = program.instructions.end();
  std::size_t tightest_span = order.size() + 1;
  for(auto instruction = program.instructions.begin();
      instruction != program.instructions.end(); ++instruction)
  {
    if(
      !instruction->is_goto() ||
      instruction->targets.size() != 1)
      continue;
    const auto target = instruction->targets.front();
    const auto from = positions.at(&*instruction);
    const auto to = positions.at(&*target);
    if(to > create_position || from < create_position || to > from)
      continue;
    const auto span = from - to;
    if(span < tightest_span)
    {
      tightest_span = span;
      head = target;
      backedge = instruction;
    }
  }
  if(
    head == program.instructions.end() ||
    backedge == program.instructions.end() ||
    !backedge->condition().is_true())
  {
    reason = "unbounded_spawn_loop";
    return false;
  }

  const auto head_position = positions.at(&*head);
  const auto backedge_position = positions.at(&*backedge);
  for(std::size_t index = head_position;
      index <= backedge_position; ++index)
  {
    const auto instruction = order[index];
    if(instruction == create)
      continue;
    if(
      instruction->is_skip() || instruction->is_location() ||
      instruction->is_goto())
      continue;
    reason = "spawn_loop_effect";
    return false;
  }
  for(std::size_t index = backedge_position + 1;
      index < order.size(); ++index)
  {
    const auto instruction = order[index];
    if(
      instruction->is_skip() || instruction->is_location() ||
      instruction->is_end_function() ||
      instruction->is_set_return_value() || instruction->is_dead())
      continue;
    reason = "main_after_spawn";
    return false;
  }

  spawn = {worker, argument, create, head, backedge};
  return true;
}

struct worker_summaryt
{
  struct lock_recordt
  {
    irep_idt function;
    goto_programt::targett instruction;
  };

  struct write_recordt
  {
    irep_idt function;
    goto_programt::targett instruction;
    int lock_depth;
  };

  struct property_recordt
  {
    irep_idt function;
    goto_programt::targett condition_instruction;
    goto_programt::targett error_instruction;
    exprt safe_condition;
    int lock_depth;
    bool direct_assert;
  };

  irep_idt mutex;
  std::set<irep_idt> writes;
  std::set<irep_idt> outside_reads;
  std::vector<lock_recordt> locks;
  std::vector<write_recordt> write_records;
  std::vector<property_recordt> property_records;
  std::set<irep_idt> functions;
  std::map<irep_idt, int> entry_depths;
  std::set<irep_idt> visiting;
  std::size_t properties = 0;
};

bool analyze_function(
  const irep_idt &identifier,
  int entry_depth,
  goto_modelt &model,
  const namespacet &ns,
  worker_summaryt &summary,
  std::string &reason)
{
  const auto previous_depth = summary.entry_depths.find(identifier);
  if(previous_depth != summary.entry_depths.end())
  {
    if(previous_depth->second != entry_depth)
    {
      reason = "helper_entry_lock_mismatch";
      return false;
    }
    if(summary.visiting.find(identifier) != summary.visiting.end())
    {
      reason = "recursive_helper";
      return false;
    }
    return true;
  }
  if(!summary.visiting.insert(identifier).second)
  {
    reason = "recursive_helper";
    return false;
  }

  const auto function = model.goto_functions.function_map.find(identifier);
  if(
    function == model.goto_functions.function_map.end() ||
    !function->second.body_available())
  {
    reason = "missing_helper";
    return false;
  }
  summary.entry_depths.emplace(identifier, entry_depth);
  summary.functions.insert(identifier);

  auto &program = function->second.body;
  std::vector<goto_programt::targett> order;
  std::map<const goto_programt::instructiont *, int> depth_at;
  int lock_depth = entry_depth;
  for(auto instruction = program.instructions.begin();
      instruction != program.instructions.end(); ++instruction)
  {
    order.push_back(instruction);
    depth_at.emplace(&*instruction, lock_depth);
    irep_idt mutex;
    if(parse_mutex_call(*instruction, "pthread_mutex_lock", mutex))
    {
      if(
        lock_depth != 0 ||
        (!summary.mutex.empty() && summary.mutex != mutex))
      {
        reason = "lock_shape";
        return false;
      }
      summary.mutex = mutex;
      summary.locks.push_back({identifier, instruction});
      ++lock_depth;
      continue;
    }
    if(parse_mutex_call(*instruction, "pthread_mutex_unlock", mutex))
    {
      if(lock_depth != 1 || mutex != summary.mutex)
      {
        reason = "unlock_shape";
        return false;
      }
      --lock_depth;
      continue;
    }

    if(instruction->is_assign())
    {
      irep_idt lhs;
      if(!direct_symbol(instruction->assign_lhs(), lhs))
      {
        reason = "non_symbol_write";
        return false;
      }
      const symbolt *lhs_symbol = nullptr;
      if(shared_symbol(lhs, ns, lhs_symbol))
      {
        if(
          lock_depth != 1 ||
          lhs_symbol->type.id() == ID_pointer ||
          lhs_symbol->type.id() == ID_array)
        {
          reason = "unprotected_or_unstable_write";
          return false;
        }
        summary.writes.insert(lhs);
        summary.write_records.push_back(
          {identifier, instruction, lock_depth});
      }
      if(
        !collect_shared_reads(
          instruction->assign_rhs(),
          lock_depth,
          summary.mutex,
          ns,
          summary.outside_reads,
          reason))
        return false;
    }
    else if(
      instruction->is_goto() || instruction->is_assume() ||
      instruction->is_assert())
    {
      if(
        !collect_shared_reads(
          instruction->condition(),
          lock_depth,
          summary.mutex,
          ns,
          summary.outside_reads,
          reason))
        return false;
      if(instruction->is_assert())
      {
        summary.property_records.push_back(
          {
            identifier,
            instruction,
            instruction,
            instruction->condition(),
            lock_depth,
            true});
        ++summary.properties;
      }
    }
    else if(instruction->is_function_call())
    {
      irep_idt callee;
      if(!direct_call_identifier(*instruction, callee))
      {
        reason = "indirect_call";
        return false;
      }
      if(callee == "reach_error" || callee == "__VERIFIER_error")
      {
        if(instruction == program.instructions.begin())
        {
          reason = "unsupported_property_control";
          return false;
        }
        auto guard = instruction;
        --guard;
        if(
          !guard->is_goto() ||
          guard->targets.size() != 1 ||
          guard->condition().is_true())
        {
          reason = "unsupported_property_control";
          return false;
        }
        summary.property_records.push_back(
          {
            identifier,
            guard,
            instruction,
            guard->condition(),
            lock_depth,
            false});
        ++summary.properties;
      }
      else if(callee != "abort" && callee != "__assert_fail")
      {
        if(!instruction->call_lhs().is_nil())
        {
          reason = "helper_return_value";
          return false;
        }
        for(const auto &argument : instruction->call_arguments())
        {
          if(
            !collect_shared_reads(
              argument,
              lock_depth,
              summary.mutex,
              ns,
              summary.outside_reads,
              reason))
            return false;
        }
        if(
          !analyze_function(
            callee,
            lock_depth,
            model,
            ns,
            summary,
            reason))
          return false;
      }
    }
    else if(instruction->is_set_return_value())
    {
      if(
        !collect_shared_reads(
          instruction->return_value(),
          lock_depth,
          summary.mutex,
          ns,
          summary.outside_reads,
          reason))
        return false;
    }
    else if(
      instruction->is_atomic_begin() || instruction->is_atomic_end() ||
      instruction->is_other() || instruction->is_start_thread() ||
      instruction->is_end_thread() || instruction->is_throw() ||
      instruction->is_catch())
    {
      reason = "unsupported_worker_effect";
      return false;
    }
  }
  if(lock_depth != entry_depth)
  {
    reason = "helper_lock_lifecycle";
    return false;
  }

  for(const auto instruction : order)
  {
    if(!instruction->is_goto())
      continue;
    const int source_depth = depth_at.at(&*instruction);
    for(const auto target : instruction->targets)
    {
      const auto found = depth_at.find(&*target);
      if(found == depth_at.end() || found->second != source_depth)
      {
        reason = "control_crosses_lock";
        return false;
      }
    }
  }
  for(const auto &property : summary.property_records)
  {
    if(
      property.function != identifier ||
      property.direct_assert)
      continue;
    const auto &guard = *property.condition_instruction;
    const auto target = guard.targets.front();
    const auto target_position = std::find(order.begin(), order.end(), target);
    const auto error_position =
      std::find(order.begin(), order.end(), property.error_instruction);
    if(
      target_position == order.end() ||
      error_position == order.end() ||
      target_position <= error_position)
    {
      reason = "unsupported_property_control";
      return false;
    }
  }
  summary.visiting.erase(identifier);
  return true;
}

bool same_expr(const exprt &left, const exprt &right)
{
  return without_cast(left) == without_cast(right);
}

bool guarded_inflationary_write(
  const worker_summaryt::write_recordt &write,
  const irep_idt &shared,
  goto_modelt &model,
  const namespacet &ns,
  goto_programt::targett &guard,
  std::string &reason)
{
  if(write.lock_depth != 1)
  {
    reason = "monotone_write_outside_lock";
    return false;
  }
  auto &program =
    model.goto_functions.function_map.at(write.function).body;
  const auto assignment = write.instruction;
  if(assignment == program.instructions.begin())
  {
    reason = "monotone_write_guard";
    return false;
  }
  guard = assignment;
  --guard;
  auto after = assignment;
  ++after;
  if(
    !guard->is_goto() ||
    guard->targets.size() != 1 ||
    guard->targets.front() != after)
  {
    reason = "monotone_write_guard";
    return false;
  }

  irep_idt lhs;
  if(!direct_symbol(assignment->assign_lhs(), lhs) || lhs != shared)
  {
    reason = "monotone_write_shape";
    return false;
  }
  const symbolt *symbol = nullptr;
  if(
    !shared_symbol(shared, ns, symbol) ||
    symbol->type.id() != ID_signedbv ||
    assignment->assign_rhs().type().id() != ID_signedbv ||
    assignment->assign_rhs().type().get(ID_width) !=
      symbol->type.get(ID_width))
  {
    reason = "monotone_write_type";
    return false;
  }
  if(contains_pointer_access(assignment->assign_rhs()))
  {
    reason = "monotone_write_candidate";
    return false;
  }
  std::set<irep_idt> candidate_symbols;
  collect_symbols(assignment->assign_rhs(), candidate_symbols);
  for(const auto &identifier : candidate_symbols)
  {
    const symbolt *candidate_symbol = nullptr;
    if(shared_symbol(identifier, ns, candidate_symbol))
    {
      reason = "monotone_write_candidate";
      return false;
    }
  }

  const exprt &condition = without_cast(guard->condition());
  const exprt *comparison = &condition;
  if(
    condition.id() == ID_not &&
    condition.operands().size() == 1)
    comparison = &without_cast(condition.operands().front());
  if(
    comparison->id() == ID_gt &&
    comparison->operands().size() == 2 &&
    same_expr(comparison->operands()[0], assignment->assign_rhs()))
  {
    irep_idt rhs;
    if(
      direct_symbol(comparison->operands()[1], rhs) &&
      rhs == shared &&
      condition.id() == ID_not)
      return true;
  }
  if(
    comparison->id() == ID_le &&
    comparison->operands().size() == 2 &&
    same_expr(comparison->operands()[0], assignment->assign_rhs()))
  {
    irep_idt rhs;
    if(
      direct_symbol(comparison->operands()[1], rhs) &&
      rhs == shared &&
      condition.id() != ID_not)
      return true;
  }
  reason = "monotone_write_guard";
  return false;
}

bool stable_property(
  const worker_summaryt::property_recordt &property,
  const irep_idt &shared,
  const namespacet &ns,
  std::string &reason)
{
  const exprt &condition = without_cast(property.safe_condition);
  std::set<irep_idt> symbols;
  collect_symbols(condition, symbols);
  std::set<irep_idt> shared_symbols;
  for(const auto &identifier : symbols)
  {
    const symbolt *symbol = nullptr;
    if(shared_symbol(identifier, ns, symbol))
      shared_symbols.insert(identifier);
  }
  if(shared_symbols.empty())
    return true;
  if(
    shared_symbols.size() != 1 ||
    *shared_symbols.begin() != shared ||
    condition.id() != ID_le ||
    condition.operands().size() != 2)
  {
    reason = "unstable_property";
    return false;
  }
  irep_idt rhs;
  if(
    !direct_symbol(condition.operands()[1], rhs) ||
    rhs != shared ||
    contains_pointer_access(condition.operands()[0]))
  {
    reason = "unstable_property";
    return false;
  }
  std::set<irep_idt> bound_symbols;
  collect_symbols(condition.operands()[0], bound_symbols);
  for(const auto &identifier : bound_symbols)
  {
    const symbolt *symbol = nullptr;
    if(shared_symbol(identifier, ns, symbol))
    {
      reason = "unstable_property";
      return false;
    }
  }
  return true;
}

bool monotone_lock_rely(
  worker_summaryt &summary,
  goto_modelt &model,
  const namespacet &ns,
  std::string &reason)
{
  if(summary.writes.size() != 1 || summary.write_records.empty())
  {
    reason = "monotone_write_set";
    return false;
  }
  const irep_idt shared = *summary.writes.begin();
  std::set<const goto_programt::instructiont *> allowed_guards;
  std::set<const goto_programt::instructiont *> allowed_properties;
  for(const auto &write : summary.write_records)
  {
    goto_programt::targett guard;
    if(
      !guarded_inflationary_write(
        write, shared, model, ns, guard, reason))
      return false;
    allowed_guards.insert(&*guard);
  }
  for(const auto &property : summary.property_records)
  {
    if(!stable_property(property, shared, ns, reason))
      return false;
    std::set<irep_idt> property_symbols;
    collect_symbols(property.safe_condition, property_symbols);
    if(property_symbols.find(shared) != property_symbols.end())
      allowed_properties.insert(&*property.condition_instruction);
  }

  for(const auto &identifier : summary.functions)
  {
    const auto &program =
      model.goto_functions.function_map.at(identifier).body;
    for(const auto &instruction : program.instructions)
    {
      std::set<irep_idt> symbols;
      if(instruction.is_assign())
      {
        collect_symbols(instruction.assign_rhs(), symbols);
        irep_idt lhs;
        if(
          direct_symbol(instruction.assign_lhs(), lhs) &&
          lhs == shared)
          ;
        else
          collect_symbols(instruction.assign_lhs(), symbols);
      }
      else if(
        instruction.is_goto() || instruction.is_assume() ||
        instruction.is_assert())
        collect_symbols(instruction.condition(), symbols);
      else if(instruction.is_function_call())
      {
        for(const auto &argument : instruction.call_arguments())
          collect_symbols(argument, symbols);
      }
      else if(instruction.is_set_return_value())
        collect_symbols(instruction.return_value(), symbols);
      if(symbols.find(shared) == symbols.end())
        continue;
      const auto pointer = &instruction;
      if(
        allowed_guards.find(pointer) == allowed_guards.end() &&
        allowed_properties.find(pointer) == allowed_properties.end())
      {
        reason = "unsupported_monotone_read";
        return false;
      }
    }
  }
  return true;
}

bool analyze_worker(
  const irep_idt &worker,
  goto_modelt &model,
  const namespacet &ns,
  worker_summaryt &summary,
  std::string &reason)
{
  if(
    !analyze_function(
      worker, 0, model, ns, summary, reason))
    return false;
  if(!summary.visiting.empty())
  {
    reason = "recursive_helper";
    return false;
  }
  if(summary.locks.empty())
  {
    reason = "lock_lifecycle";
    return false;
  }
  if(summary.properties == 0)
  {
    reason = "missing_property";
    return false;
  }
  if(summary.writes.empty())
  {
    reason = "missing_environment_write";
    return false;
  }
  for(const auto &entry : model.goto_functions.function_map)
  {
    if(!entry.second.body_available())
      continue;
    for(const auto &instruction : entry.second.body.instructions)
    {
      irep_idt callee;
      if(
        !direct_call_identifier(instruction, callee) ||
        callee == worker ||
        summary.functions.find(callee) == summary.functions.end())
        continue;
      if(summary.functions.find(entry.first) == summary.functions.end())
      {
        reason = "external_helper_caller";
        return false;
      }
    }
  }
  return true;
}
} // namespace

bool lock_boundary_ego_thread_abstraction_transform(
  goto_modelt &goto_model,
  message_handlert &message_handler)
{
  const namespacet ns(goto_model.symbol_table);
  spawn_loopt spawn;
  std::string reason;
  if(!collect_spawn_loop(goto_model, ns, spawn, reason))
  {
    std::cout << "NATIVE_LOCK_EGO_ABSTRACTION applied=0 reason="
              << reason << '\n';
    return false;
  }

  worker_summaryt summary;
  if(
    !analyze_worker(
      spawn.worker, goto_model, ns, summary, reason))
  {
    std::cout << "NATIVE_LOCK_EGO_ABSTRACTION applied=0 reason="
              << reason << " worker=" << spawn.worker << '\n';
    return false;
  }

  std::string monotone_reason;
  const bool monotone =
    monotone_lock_rely(
      summary, goto_model, ns, monotone_reason);
  if(!monotone)
  {
    for(const auto &property : summary.property_records)
    {
      if(property.lock_depth != 1)
      {
        reason = "unprotected_property";
        std::cout << "NATIVE_LOCK_EGO_ABSTRACTION applied=0 reason="
                  << reason << " worker=" << spawn.worker
                  << " monotone_reject=" << monotone_reason << '\n';
        return false;
      }
    }
    for(const auto &identifier : summary.outside_reads)
    {
      if(summary.writes.find(identifier) != summary.writes.end())
      {
        reason = "mutable_read_outside_lock";
        std::cout << "NATIVE_LOCK_EGO_ABSTRACTION applied=0 reason="
                  << reason << " worker=" << spawn.worker
                  << " monotone_reject=" << monotone_reason << '\n';
        return false;
      }
    }
    for(const auto &lock : summary.locks)
    {
      auto &program =
        goto_model.goto_functions.function_map.at(lock.function).body;
      for(const auto &identifier : summary.writes)
      {
        const symbolt &symbol = ns.lookup(identifier);
        program.insert_after(
          lock.instruction,
          goto_programt::make_assignment(
            symbol.symbol_expr(),
            side_effect_expr_nondett(
              symbol.type, lock.instruction->source_location()),
            lock.instruction->source_location()));
      }
    }
  }

  for(auto instruction = spawn.head;; ++instruction)
  {
    if(instruction != spawn.create)
      instruction->turn_into_skip();
    if(instruction == spawn.backedge)
      break;
  }
  const symbolt &worker_symbol = ns.lookup(spawn.worker);
  code_function_callt call(
    worker_symbol.symbol_expr(), {spawn.argument});
  call.add_source_location() = spawn.create->source_location();
  spawn.create->code_nonconst() = std::move(call);

  goto_model.goto_functions.update();
  std::cout << "NATIVE_LOCK_EGO_ABSTRACTION applied=1 worker="
            << spawn.worker << " mutex=" << summary.mutex
            << " locks=" << summary.locks.size()
            << " writes=" << summary.writes.size()
            << " functions=" << summary.functions.size()
            << " mode=" << (monotone ? "monotone" : "havoc");
  if(!monotone)
    std::cout << " monotone_reject=" << monotone_reason;
  std::cout << '\n';
  (void)message_handler;
  return true;
}
