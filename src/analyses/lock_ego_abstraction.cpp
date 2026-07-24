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

bool collect_shared_reads(
  const exprt &expr,
  int lock_depth,
  const irep_idt &mutex,
  const namespacet &ns,
  std::set<irep_idt> &outside_reads,
  std::string &reason)
{
  std::set<irep_idt> symbols;
  collect_symbols(expr, symbols);
  for(const auto &identifier : symbols)
  {
    const symbolt *symbol = nullptr;
    if(!shared_symbol(identifier, ns, symbol) || identifier == mutex)
      continue;
    if(
      symbol->type.id() == ID_pointer ||
      symbol->type.id() == ID_array ||
      symbol->type.get_bool(ID_C_volatile))
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
  irep_idt mutex;
  std::set<irep_idt> writes;
  std::vector<goto_programt::targett> locks;
};

bool analyze_worker(
  const irep_idt &worker,
  goto_modelt &model,
  const namespacet &ns,
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

  auto &program = function->second.body;
  std::vector<goto_programt::targett> order;
  std::map<const goto_programt::instructiont *, int> depth_at;
  int lock_depth = 0;
  std::size_t properties = 0;
  std::set<irep_idt> outside_reads;
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
      summary.locks.push_back(instruction);
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
          lhs_symbol->type.id() == ID_array ||
          lhs_symbol->type.get_bool(ID_C_volatile))
        {
          reason = "unprotected_or_unstable_write";
          return false;
        }
        summary.writes.insert(lhs);
      }
      if(
        !collect_shared_reads(
          instruction->assign_rhs(),
          lock_depth,
          summary.mutex,
          ns,
          outside_reads,
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
          outside_reads,
          reason))
        return false;
      if(instruction->is_assert())
      {
        if(lock_depth != 1)
        {
          reason = "unprotected_property";
          return false;
        }
        ++properties;
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
        if(lock_depth != 1)
        {
          reason = "unprotected_property";
          return false;
        }
        ++properties;
      }
      else if(callee != "abort" && callee != "__assert_fail")
      {
        reason = "worker_call";
        return false;
      }
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
  if(lock_depth != 0 || summary.locks.empty())
  {
    reason = "lock_lifecycle";
    return false;
  }
  if(properties == 0)
  {
    reason = "missing_property";
    return false;
  }
  if(summary.writes.empty())
  {
    reason = "missing_environment_write";
    return false;
  }
  for(const auto &identifier : outside_reads)
  {
    if(summary.writes.find(identifier) != summary.writes.end())
    {
      reason = "mutable_read_outside_lock";
      return false;
    }
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

  auto &worker_program =
    goto_model.goto_functions.function_map.at(spawn.worker).body;
  for(const auto lock : summary.locks)
  {
    for(const auto &identifier : summary.writes)
    {
      const symbolt &symbol = ns.lookup(identifier);
      worker_program.insert_after(
        lock,
        goto_programt::make_assignment(
          symbol.symbol_expr(),
          side_effect_expr_nondett(
            symbol.type, lock->source_location()),
          lock->source_location()));
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
            << " writes=" << summary.writes.size() << '\n';
  (void)message_handler;
  return true;
}
