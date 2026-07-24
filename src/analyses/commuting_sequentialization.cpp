/*******************************************************************\

Module: Join-Scoped Commuting Phase Sequentialization

\*******************************************************************/

#include "commuting_sequentialization.h"

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
#include <utility>
#include <vector>

namespace
{
struct create_recordt
{
  irep_idt handle;
  irep_idt worker;
  exprt argument;
  goto_programt::targett instruction;
};

struct join_recordt
{
  create_recordt *create;
  goto_programt::targett instruction;
};

struct effect_summaryt
{
  std::set<irep_idt> reads;
  std::set<irep_idt> writes;
};

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
  const exprt &object = without_cast(to_address_of_expr(value).object());
  return direct_symbol(object, identifier);
}

bool direct_call_identifier(
  const goto_programt::instructiont &instruction,
  irep_idt &identifier)
{
  if(!instruction.is_function_call())
    return false;
  return direct_symbol(instruction.call_function(), identifier);
}

bool is_zero(const exprt &expr)
{
  const exprt &value = without_cast(expr);
  return value.is_zero() ||
         (value.id() == ID_constant && value.get(ID_value) == "NULL");
}

bool shared_symbol(
  const irep_idt &identifier,
  const namespacet &ns,
  const symbolt *&symbol)
{
  if(ns.lookup(identifier, symbol))
    return false;
  return symbol->is_static_lifetime && !symbol->is_type &&
         symbol->type.id() != ID_code;
}

irep_idt memory_object(const irep_idt &base)
{
  return "$commuting-memory:" + id2string(base);
}

bool find_memory_base(
  const exprt &expr,
  const namespacet &ns,
  std::set<irep_idt> &bases)
{
  const exprt &value = without_cast(expr);
  if(value.id() == ID_symbol)
  {
    const auto &identifier = to_symbol_expr(value).get_identifier();
    const symbolt *symbol = nullptr;
    if(
      shared_symbol(identifier, ns, symbol) &&
      (symbol->type.id() == ID_pointer || symbol->type.id() == ID_array))
      bases.insert(identifier);
  }
  else if(value.id() == ID_address_of)
  {
    const exprt &object = without_cast(to_address_of_expr(value).object());
    if(object.id() == ID_symbol)
    {
      const auto &identifier = to_symbol_expr(object).get_identifier();
      const symbolt *symbol = nullptr;
      if(shared_symbol(identifier, ns, symbol))
        bases.insert(identifier);
    }
  }
  for(const auto &operand : value.operands())
    find_memory_base(operand, ns, bases);
  return bases.size() <= 1;
}

bool collect_reads(
  const exprt &expr,
  const namespacet &ns,
  effect_summaryt &summary,
  std::string &reason)
{
  const exprt &value = without_cast(expr);

  if(value.id() == ID_side_effect)
  {
    if(to_side_effect_expr(value).get_statement() != ID_nondet)
    {
      reason = "expression_side_effect";
      return false;
    }
    for(const auto &operand : value.operands())
    {
      if(!collect_reads(operand, ns, summary, reason))
        return false;
    }
    return true;
  }

  if(value.id() == ID_address_of)
  {
    reason = "address_escape";
    return false;
  }

  if(value.id() == ID_dereference || value.id() == ID_index)
  {
    const exprt &pointer =
      value.id() == ID_dereference
        ? to_dereference_expr(value).pointer()
        : value.op0();
    std::set<irep_idt> bases;
    if(!find_memory_base(pointer, ns, bases) || bases.size() != 1)
    {
      reason = "unresolved_read_base";
      return false;
    }
    summary.reads.insert(memory_object(*bases.begin()));
    for(const auto &operand : value.operands())
    {
      if(!collect_reads(operand, ns, summary, reason))
        return false;
    }
    return true;
  }

  if(value.id() == ID_symbol)
  {
    const auto &identifier = to_symbol_expr(value).get_identifier();
    const symbolt *symbol = nullptr;
    if(shared_symbol(identifier, ns, symbol))
    {
      if(symbol->type.get_bool(ID_C_volatile))
      {
        reason = "volatile_read";
        return false;
      }
      summary.reads.insert(identifier);
    }
    return true;
  }

  for(const auto &operand : value.operands())
  {
    if(!collect_reads(operand, ns, summary, reason))
      return false;
  }
  return true;
}

bool collect_write(
  const exprt &lhs,
  const namespacet &ns,
  effect_summaryt &summary,
  std::string &reason)
{
  const exprt &object = without_cast(lhs);
  if(object.id() != ID_symbol)
  {
    reason =
      object.id() == ID_dereference || object.id() == ID_index
        ? "pointer_write"
        : "non_symbol_write";
    return false;
  }

  const auto &identifier = to_symbol_expr(object).get_identifier();
  const symbolt *symbol = nullptr;
  if(!shared_symbol(identifier, ns, symbol))
    return true;
  if(
    symbol->type.id() == ID_pointer || symbol->type.id() == ID_array ||
    symbol->type.get_bool(ID_C_volatile))
  {
    reason = "unstable_shared_write";
    return false;
  }
  summary.writes.insert(identifier);
  return true;
}

bool forbidden_callee(const irep_idt &callee)
{
  const std::string name = id2string(callee);
  return name.find("pthread_") == 0 ||
         name.find("__atomic_") == 0 ||
         name.find("__sync_") == 0 ||
         name == "malloc" || name == "calloc" || name == "realloc" ||
         name == "free" || name == "alloca" ||
         name == "reach_error" || name == "__VERIFIER_error";
}

bool analyze_function(
  const irep_idt &identifier,
  const goto_modelt &model,
  const namespacet &ns,
  std::set<irep_idt> &visiting,
  std::map<irep_idt, effect_summaryt> &cache,
  effect_summaryt &summary,
  std::string &reason)
{
  const auto cached = cache.find(identifier);
  if(cached != cache.end())
  {
    summary.reads.insert(cached->second.reads.begin(), cached->second.reads.end());
    summary.writes.insert(
      cached->second.writes.begin(), cached->second.writes.end());
    return true;
  }
  if(!visiting.insert(identifier).second)
  {
    reason = "recursive_call_graph";
    return false;
  }

  const auto function = model.goto_functions.function_map.find(identifier);
  if(
    function == model.goto_functions.function_map.end() ||
    !function->second.body_available())
  {
    reason = "missing_function_body";
    visiting.erase(identifier);
    return false;
  }

  effect_summaryt local;
  for(const auto &instruction : function->second.body.instructions)
  {
    if(
      instruction.is_assert() || instruction.is_start_thread() ||
      instruction.is_end_thread() || instruction.is_atomic_begin() ||
      instruction.is_atomic_end() || instruction.is_other() ||
      instruction.is_throw() || instruction.is_catch())
    {
      reason = "unsupported_worker_instruction";
      visiting.erase(identifier);
      return false;
    }

    if(instruction.is_assign())
    {
      if(
        !collect_write(instruction.assign_lhs(), ns, local, reason) ||
        !collect_reads(instruction.assign_rhs(), ns, local, reason))
      {
        visiting.erase(identifier);
        return false;
      }
      continue;
    }

    if(instruction.is_function_call())
    {
      irep_idt callee;
      if(!direct_call_identifier(instruction, callee))
      {
        reason = "indirect_call";
        visiting.erase(identifier);
        return false;
      }
      for(const auto &argument : instruction.call_arguments())
      {
        if(!collect_reads(argument, ns, local, reason))
        {
          visiting.erase(identifier);
          return false;
        }
      }
      if(
        !instruction.call_lhs().is_nil() &&
        !collect_write(instruction.call_lhs(), ns, local, reason))
      {
        visiting.erase(identifier);
        return false;
      }
      if(callee == "abort" || callee == "__CPROVER_assume")
        continue;
      if(forbidden_callee(callee))
      {
        reason = "forbidden_call";
        visiting.erase(identifier);
        return false;
      }
      if(
        !analyze_function(
          callee, model, ns, visiting, cache, local, reason))
      {
        visiting.erase(identifier);
        return false;
      }
      continue;
    }

    if(instruction.has_condition())
    {
      if(!collect_reads(instruction.condition(), ns, local, reason))
      {
        visiting.erase(identifier);
        return false;
      }
    }
    if(
      instruction.is_set_return_value() &&
      !collect_reads(instruction.return_value(), ns, local, reason))
    {
      visiting.erase(identifier);
      return false;
    }
  }

  visiting.erase(identifier);
  cache.emplace(identifier, local);
  summary.reads.insert(local.reads.begin(), local.reads.end());
  summary.writes.insert(local.writes.begin(), local.writes.end());
  return true;
}

bool collect_phase(
  goto_modelt &model,
  const namespacet &ns,
  std::vector<create_recordt> &creates,
  std::vector<join_recordt> &joins,
  std::vector<irep_idt> &normalized_workers,
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

  std::map<irep_idt, std::size_t> handles;
  std::set<irep_idt> workers;
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
      if(
        join_seen || instruction->call_arguments().size() != 4 ||
        !instruction->call_lhs().is_nil() ||
        !is_zero(instruction->call_arguments()[1]) ||
        !is_zero(instruction->call_arguments()[3]))
      {
        reason = "create_shape";
        return false;
      }
      irep_idt handle;
      irep_idt worker;
      if(
        !addressed_symbol(instruction->call_arguments()[0], handle) ||
        !addressed_symbol(instruction->call_arguments()[2], worker) ||
        handles.find(handle) != handles.end() ||
        !workers.insert(worker).second)
      {
        reason = "create_resolution";
        return false;
      }
      const symbolt *handle_symbol = nullptr;
      const symbolt *worker_symbol = nullptr;
      if(
        ns.lookup(handle, handle_symbol) ||
        handle_symbol->is_static_lifetime ||
        ns.lookup(worker, worker_symbol) ||
        worker_symbol->type.id() != ID_code)
      {
        reason = "lifecycle_symbol";
        return false;
      }
      const auto &parameters =
        to_code_type(worker_symbol->type).parameters();
      if(
        parameters.size() != 1 ||
        parameters.front().type() !=
          instruction->call_arguments()[3].type())
      {
        reason = "worker_argument_type";
        return false;
      }
      handles.emplace(handle, creates.size());
      creates.push_back(
        {handle, worker, instruction->call_arguments()[3], instruction});
    }
    else if(callee == "pthread_join")
    {
      join_seen = true;
      irep_idt handle;
      if(
        instruction->call_arguments().size() != 2 ||
        !instruction->call_lhs().is_nil() ||
        !is_zero(instruction->call_arguments()[1]) ||
        !direct_symbol(instruction->call_arguments()[0], handle) ||
        handles.find(handle) == handles.end() ||
        !joined.insert(handle).second)
      {
        reason = "join_resolution";
        return false;
      }
      joins.push_back({&creates[handles.at(handle)], instruction});
    }
  }
  if(
    creates.empty() || joins.size() != creates.size() ||
    joined.size() != creates.size())
  {
    reason = "incomplete_lifecycle";
    return false;
  }

  const auto first_create = creates.front().instruction;
  const auto final_join = joins.back().instruction;
  bool in_region = false;
  bool after_region = false;
  std::size_t properties = 0;
  for(auto instruction = main->second.body.instructions.begin();
      instruction != main->second.body.instructions.end(); ++instruction)
  {
    if(instruction == first_create)
      in_region = true;
    if(in_region)
    {
      irep_idt callee;
      if(instruction->is_function_call())
      {
        if(
          !direct_call_identifier(*instruction, callee))
        {
          reason = "main_region_call";
          return false;
        }
        if(callee != "pthread_create" && callee != "pthread_join")
        {
          const auto worker =
            model.goto_functions.function_map.find(callee);
          if(
            !instruction->call_lhs().is_nil() ||
            instruction->call_arguments().size() != 1 ||
            !is_zero(instruction->call_arguments().front()) ||
            worker == model.goto_functions.function_map.end() ||
            !worker->second.body_available())
          {
            reason = "main_region_call";
            return false;
          }
          normalized_workers.push_back(callee);
        }
      }
      else if(
        !instruction->is_skip() && !instruction->is_location())
      {
        reason = "main_region_effect";
        return false;
      }
    }
    if(instruction == final_join)
    {
      in_region = false;
      after_region = true;
      continue;
    }
    irep_idt callee;
    const bool property_call =
      direct_call_identifier(*instruction, callee) &&
      (callee == "reach_error" || callee == "__VERIFIER_error");
    if(instruction->is_assert() || property_call)
    {
      if(!after_region)
      {
        reason = "property_before_join";
        return false;
      }
      ++properties;
    }
  }
  if(properties != 1)
  {
    reason = "property_count";
    return false;
  }
  return true;
}

bool disjoint(
  const std::set<irep_idt> &left,
  const std::set<irep_idt> &right)
{
  auto l = left.begin();
  auto r = right.begin();
  while(l != left.end() && r != right.end())
  {
    if(*l < *r)
      ++l;
    else if(*r < *l)
      ++r;
    else
      return false;
  }
  return true;
}
} // namespace

bool join_scoped_commuting_sequentialization_transform(
  goto_modelt &goto_model,
  message_handlert &message_handler)
{
  const namespacet ns(goto_model.symbol_table);
  std::vector<create_recordt> creates;
  std::vector<join_recordt> joins;
  std::vector<irep_idt> normalized_workers;
  std::string reason;
  if(
    !collect_phase(
      goto_model, ns, creates, joins, normalized_workers, reason))
  {
    std::cout
      << "NATIVE_COMMUTING_SEQUENTIALIZATION applied=0 reason="
      << reason << '\n';
    return false;
  }

  std::vector<irep_idt> workers;
  for(const auto &create : creates)
    workers.push_back(create.worker);
  workers.insert(
    workers.end(), normalized_workers.begin(), normalized_workers.end());
  std::vector<effect_summaryt> effects(workers.size());
  std::map<irep_idt, effect_summaryt> cache;
  for(std::size_t index = 0; index < workers.size(); ++index)
  {
    std::set<irep_idt> visiting;
    if(
      !analyze_function(
        workers[index],
        goto_model,
        ns,
        visiting,
        cache,
        effects[index],
        reason))
    {
      std::cout
        << "NATIVE_COMMUTING_SEQUENTIALIZATION applied=0 reason="
        << reason << " worker=" << workers[index] << '\n';
      return false;
    }
  }

  for(std::size_t first = 0; first < effects.size(); ++first)
  {
    for(std::size_t second = first + 1; second < effects.size(); ++second)
    {
      if(
        !disjoint(effects[first].writes, effects[second].writes) ||
        !disjoint(effects[first].writes, effects[second].reads) ||
        !disjoint(effects[second].writes, effects[first].reads))
      {
        std::cout
          << "NATIVE_COMMUTING_SEQUENTIALIZATION applied=0"
          << " reason=interference first=" << workers[first]
          << " second=" << workers[second] << '\n';
        return false;
      }
    }
  }

  for(auto &create : creates)
    create.instruction->turn_into_skip();
  for(auto &join : joins)
  {
    const auto symbol_entry =
      goto_model.symbol_table.symbols.find(join.create->worker);
    if(symbol_entry == goto_model.symbol_table.symbols.end())
    {
      std::cout
        << "NATIVE_COMMUTING_SEQUENTIALIZATION applied=0"
        << " reason=missing_worker_symbol\n";
      return false;
    }
    code_function_callt call(
      symbol_entry->second.symbol_expr(), {join.create->argument});
    call.add_source_location() = join.instruction->source_location();
    join.instruction->code_nonconst() = std::move(call);
  }
  goto_model.goto_functions.update();

  std::size_t reads = 0;
  std::size_t writes = 0;
  for(const auto &effect : effects)
  {
    reads += effect.reads.size();
    writes += effect.writes.size();
  }
  std::cout
    << "NATIVE_COMMUTING_SEQUENTIALIZATION applied=1 workers="
    << workers.size() << " residual=" << creates.size()
    << " reads=" << reads
    << " writes=" << writes << '\n';
  (void)message_handler;
  return true;
}
