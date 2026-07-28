/*******************************************************************\

Module: Homogeneous Thread-Local Cutoff

\*******************************************************************/

#include "thread_local_cutoff_analysis.h"

#include "natural_loops.h"

#include <goto-programs/goto_model.h>

#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/expr_util.h>
#include <util/find_symbols.h>
#include <util/namespace.h>
#include <util/pointer_expr.h>
#include <util/std_code.h>
#include <util/std_expr.h>
#include <util/symbol.h>

#include <algorithm>
#include <iostream>
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

bool direct_call(
  const goto_programt::instructiont &instruction,
  irep_idt &callee)
{
  return
    instruction.is_function_call() &&
    symbol_id(instruction.call_function(), callee);
}

bool zero_value(const exprt &src)
{
  const exprt &expr = strip(src);
  return expr.is_zero() ||
         (expr.id() == ID_constant && expr.get(ID_value) == "NULL");
}

bool address_of_symbol(const exprt &src, irep_idt &identifier)
{
  const exprt &expr = strip(src);
  return
    expr.id() == ID_address_of &&
    symbol_id(to_address_of_expr(expr).object(), identifier);
}

struct indexed_handlet
{
  irep_idt base;
  irep_idt index;
};

bool pointer_plus_index(
  const exprt &src,
  indexed_handlet &result)
{
  const exprt &expr = strip(src);
  if(expr.id() != ID_plus || expr.operands().size() != 2)
    return false;
  return
    symbol_id(expr.op0(), result.base) &&
    symbol_id(expr.op1(), result.index);
}

bool indexed_handle_object(
  const exprt &src,
  indexed_handlet &result)
{
  const exprt &expr = strip(src);
  if(expr.id() == ID_index && expr.operands().size() == 2)
  {
    return
      symbol_id(expr.op0(), result.base) &&
      symbol_id(expr.op1(), result.index);
  }
  if(expr.id() == ID_dereference && expr.operands().size() == 1)
    return pointer_plus_index(to_dereference_expr(expr).pointer(), result);
  return false;
}

bool create_handle(
  const exprt &src,
  indexed_handlet &result)
{
  const exprt &expr = strip(src);
  return
    expr.id() == ID_address_of &&
    indexed_handle_object(to_address_of_expr(expr).object(), result);
}

bool join_handle(
  const exprt &src,
  indexed_handlet &result)
{
  return indexed_handle_object(src, result);
}

bool unit_increment(
  const goto_programt::instructiont &instruction,
  const irep_idt &index)
{
  if(!instruction.is_assign())
    return false;
  irep_idt lhs;
  if(!symbol_id(instruction.assign_lhs(), lhs) || lhs != index)
    return false;
  const exprt &rhs = strip(instruction.assign_rhs());
  if(rhs.id() != ID_plus || rhs.operands().size() != 2)
    return false;
  const exprt &step_expr = strip(rhs.op1());
  if(step_expr.id() != ID_constant)
    return false;
  irep_idt first;
  mp_integer step;
  return
    symbol_id(rhs.op0(), first) && first == index &&
    !to_integer(to_constant_expr(step_expr), step) && step == 1;
}

struct lifecycle_loopt
{
  goto_programt::targett head;
  goto_programt::targett call;
  goto_programt::targett backedge;
  irep_idt index;
  exprt index_expr;
  exprt bound;
  indexed_handlet handle;
  irep_idt worker;
  exprt argument;
  bool create;
};

bool parse_loop_exit(
  goto_programt::targett head,
  irep_idt &index,
  exprt &index_expr,
  exprt &bound)
{
  if(!head->is_goto() || head->is_backwards_goto())
    return false;
  const exprt &condition = strip(head->condition());
  if(condition.id() != ID_not || condition.operands().size() != 1)
    return false;
  const exprt &continuation = strip(condition.op0());
  if(continuation.id() != ID_lt || continuation.operands().size() != 2)
    return false;
  if(!symbol_id(continuation.op0(), index))
    return false;
  index_expr = continuation.op0();
  bound = continuation.op1();
  return true;
}

bool analyze_lifecycle_loop(
  goto_programt &program,
  const natural_loops_mutablet::loop_mapt::value_type &entry,
  lifecycle_loopt &result,
  std::string &reason)
{
  result.head = entry.first;
  if(
    !parse_loop_exit(
      result.head, result.index, result.index_expr, result.bound))
  {
    reason = "loop_guard";
    return false;
  }

  std::size_t calls = 0;
  std::size_t increments = 0;
  std::size_t backedges = 0;
  for(const auto instruction : entry.second)
  {
    irep_idt callee;
    if(direct_call(*instruction, callee))
    {
      ++calls;
      result.call = instruction;
      const auto &arguments = instruction->call_arguments();
      if(callee == "pthread_create" && arguments.size() == 4)
      {
        result.create = true;
        if(
          !instruction->call_lhs().is_nil() ||
          !create_handle(arguments[0], result.handle) ||
          result.handle.index != result.index ||
          !zero_value(arguments[1]) ||
          !address_of_symbol(arguments[2], result.worker) ||
          !zero_value(arguments[3]))
        {
          reason = "create_shape";
          return false;
        }
        result.argument = arguments[3];
      }
      else if(callee == "pthread_join" && arguments.size() == 2)
      {
        result.create = false;
        if(
          !instruction->call_lhs().is_nil() ||
          !join_handle(arguments[0], result.handle) ||
          result.handle.index != result.index ||
          !zero_value(arguments[1]))
        {
          reason = "join_shape";
          return false;
        }
      }
      else
      {
        reason = "loop_call";
        return false;
      }
    }
    else if(instruction->is_assign())
    {
      irep_idt lhs;
      if(
        symbol_id(instruction->assign_lhs(), lhs) &&
        lhs == result.index)
      {
        if(unit_increment(*instruction, result.index))
          ++increments;
        else
        {
          reason = "index_update";
          return false;
        }
      }
      else
      {
        reason = "loop_assignment";
        return false;
      }
    }
    else if(instruction->is_backwards_goto())
    {
      if(instruction->get_target() != result.head)
      {
        reason = "loop_backedge_target";
        return false;
      }
      ++backedges;
      result.backedge = instruction;
    }
    else if(
      !instruction->is_goto() && !instruction->is_skip() &&
      !instruction->is_location())
    {
      reason = "loop_instruction";
      return false;
    }
  }
  if(calls != 1 || increments != 1 || backedges != 1)
  {
    reason = "loop_cardinality";
    return false;
  }

  std::size_t zero_initializations = 0;
  for(auto instruction = program.instructions.begin();
      instruction != result.head; ++instruction)
  {
    if(!instruction->is_assign())
      continue;
    irep_idt lhs;
    if(
      symbol_id(instruction->assign_lhs(), lhs) &&
      lhs == result.index && strip(instruction->assign_rhs()).is_zero())
      ++zero_initializations;
  }
  if(zero_initializations != 1)
  {
    reason = "index_initialization";
    return false;
  }
  return true;
}

bool immutable_key_initialization(
  const goto_programt &main,
  const irep_idt &key,
  goto_programt::const_targett create_head,
  std::string &reason)
{
  std::size_t key_creates = 0;
  for(auto instruction = main.instructions.begin();
      instruction != main.instructions.end(); ++instruction)
  {
    if(instruction->is_assign())
    {
      irep_idt lhs;
      if(symbol_id(instruction->assign_lhs(), lhs) && lhs == key)
      {
        reason = "key_write";
        return false;
      }
    }
    irep_idt callee;
    if(!direct_call(*instruction, callee))
      continue;
    if(callee == "pthread_key_create")
    {
      const auto &arguments = instruction->call_arguments();
      irep_idt candidate;
      if(
        instruction->location_number >= create_head->location_number ||
        arguments.size() != 2 ||
        !address_of_symbol(arguments[0], candidate) ||
        candidate != key || !zero_value(arguments[1]))
      {
        reason = "key_create";
        return false;
      }
      ++key_creates;
    }
    else if(callee == "pthread_key_delete")
    {
      reason = "key_delete";
      return false;
    }
  }
  if(key_creates != 1)
  {
    reason = "key_create_count";
    return false;
  }
  return true;
}

struct worker_summaryt
{
  std::set<irep_idt> tls_symbols;
  std::set<irep_idt> key_symbols;
  std::size_t properties = 0;
  std::size_t instructions = 0;
};

bool thread_local_value_address(
  const exprt &src,
  const namespacet &ns,
  std::set<irep_idt> &tls_symbols)
{
  const exprt &expr = strip(src);
  if(expr.id() != ID_address_of)
    return false;
  const exprt &object = strip(to_address_of_expr(expr).object());
  irep_idt identifier;
  if(!symbol_id(object, identifier))
    return false;
  const symbolt *symbol = nullptr;
  if(ns.lookup(identifier, symbol) || symbol->is_type)
    return false;
  if(symbol->is_static_lifetime)
  {
    if(!symbol->is_thread_local)
      return false;
    tls_symbols.insert(identifier);
  }
  return true;
}

bool call_storage_is_local(
  const goto_programt::instructiont &instruction,
  const namespacet &ns,
  worker_summaryt &summary,
  const std::set<irep_idt> &allowed_shared,
  std::string &reason)
{
  find_symbols_sett symbols;
  find_symbols(instruction.call_lhs(), symbols);
  for(const auto &argument : instruction.call_arguments())
    find_symbols(argument, symbols);
  for(const auto &identifier : symbols)
  {
    const symbolt *symbol = nullptr;
    if(
      ns.lookup(identifier, symbol) || symbol->is_type ||
      symbol->type.id() == ID_code || !symbol->is_static_lifetime)
      continue;
    if(symbol->is_thread_local)
      summary.tls_symbols.insert(identifier);
    else if(allowed_shared.count(identifier) == 0)
    {
      reason = "shared_call_state";
      return false;
    }
  }
  return true;
}

bool analyze_worker(
  const irep_idt &function,
  const goto_modelt &model,
  const namespacet &ns,
  std::set<irep_idt> &visiting,
  worker_summaryt &summary,
  std::string &reason)
{
  if(!visiting.insert(function).second)
  {
    reason = "worker_recursion";
    return false;
  }
  const auto function_entry =
    model.goto_functions.function_map.find(function);
  if(
    function_entry == model.goto_functions.function_map.end() ||
    !function_entry->second.body_available())
  {
    visiting.erase(function);
    reason = "worker_body";
    return false;
  }
  const auto &program = function_entry->second.body;
  natural_loopst loops;
  loops(program);
  if(!loops.loop_map.empty())
  {
    visiting.erase(function);
    reason = "worker_loop";
    return false;
  }

  for(const auto &instruction : program.instructions)
  {
    ++summary.instructions;
    if(instruction.is_start_thread() || instruction.is_end_thread())
    {
      visiting.erase(function);
      reason = "nested_thread";
      return false;
    }

    if(instruction.is_assert())
      ++summary.properties;

    irep_idt callee;
    if(direct_call(instruction, callee))
    {
      if(callee == "pthread_setspecific" || callee == "pthread_getspecific")
      {
        const auto &arguments = instruction.call_arguments();
        irep_idt key;
        if(arguments.empty() || !symbol_id(arguments[0], key))
        {
          visiting.erase(function);
          reason = "thread_key_argument";
          return false;
        }
        summary.key_symbols.insert(key);
        if(callee == "pthread_setspecific")
        {
          if(
            arguments.size() != 2 ||
            !thread_local_value_address(
              arguments[1], ns, summary.tls_symbols))
          {
            visiting.erase(function);
            reason = "thread_value_escape";
            return false;
          }
        }
        std::set<irep_idt> allowed_shared;
        allowed_shared.insert(key);
        if(
          !call_storage_is_local(
            instruction, ns, summary, allowed_shared, reason))
        {
          visiting.erase(function);
          return false;
        }
        continue;
      }

      const std::string callee_name = id2string(callee);
      if(
        callee_name.find("pthread_") == 0 ||
        callee_name.find("__CPROVER_") == 0 ||
        callee_name == "malloc" || callee_name == "calloc" ||
        callee_name == "realloc" || callee_name == "free")
      {
        visiting.erase(function);
        reason = "worker_builtin";
        return false;
      }
      if(
        !call_storage_is_local(
          instruction, ns, summary, {}, reason) ||
        !analyze_worker(
          callee, model, ns, visiting, summary, reason))
      {
        visiting.erase(function);
        return false;
      }
      continue;
    }

    if(
      instruction.is_function_call() ||
      (instruction.is_other() &&
       instruction.get_other().get_statement() != ID_expression))
    {
      visiting.erase(function);
      reason = "worker_instruction";
      return false;
    }

    if(instruction.is_assign())
    {
      find_symbols_sett lhs_symbols;
      find_symbols(instruction.assign_lhs(), lhs_symbols);
      for(const auto &identifier : lhs_symbols)
      {
        const symbolt *symbol = nullptr;
        if(
          !ns.lookup(identifier, symbol) &&
          symbol->is_static_lifetime && !symbol->is_type)
        {
          if(!symbol->is_thread_local)
          {
            visiting.erase(function);
            reason = "shared_write";
            return false;
          }
          summary.tls_symbols.insert(identifier);
        }
      }
    }

    find_symbols_sett symbols;
    instruction.apply(
      [&symbols](const exprt &expr) { find_symbols(expr, symbols); });
    for(const auto &identifier : symbols)
    {
      const symbolt *symbol = nullptr;
      if(
        ns.lookup(identifier, symbol) || symbol->is_type ||
        symbol->type.id() == ID_code || !symbol->is_static_lifetime)
        continue;
      if(symbol->is_thread_local)
        summary.tls_symbols.insert(identifier);
      else
      {
        visiting.erase(function);
        reason = "shared_read";
        return false;
      }
    }
  }
  visiting.erase(function);
  return true;
}

bool indexed_handle_use(
  const exprt &src,
  const irep_idt &handle)
{
  const exprt &expr = strip(src);
  if(expr.id() == ID_index && expr.operands().size() == 2)
  {
    irep_idt base;
    if(symbol_id(expr.op0(), base) && base == handle)
      return true;
  }
  if(expr.id() == ID_dereference && expr.operands().size() == 1)
  {
    const exprt &pointer =
      strip(to_dereference_expr(expr).pointer());
    if(pointer.id() == ID_plus && pointer.operands().size() == 2)
    {
      irep_idt base;
      if(symbol_id(pointer.op0(), base) && base == handle)
        return true;
    }
  }
  for(const auto &operand : expr.operands())
  {
    if(indexed_handle_use(operand, handle))
      return true;
  }
  return false;
}

bool main_non_observation(
  const goto_programt &main,
  const lifecycle_loopt &create,
  const lifecycle_loopt &join,
  const worker_summaryt &summary,
  std::string &reason)
{
  for(auto instruction = main.instructions.begin();
      instruction != main.instructions.end(); ++instruction)
  {
    const bool create_member =
      instruction->location_number >= create.head->location_number &&
      instruction->location_number <= create.backedge->location_number;
    const bool join_member =
      instruction->location_number >= join.head->location_number &&
      instruction->location_number <= join.backedge->location_number;

    bool observes_handle = false;
    instruction->apply([&](const exprt &expr) {
      observes_handle =
        observes_handle ||
        indexed_handle_use(expr, create.handle.base);
    });
    if(observes_handle && !create_member && !join_member)
    {
      reason = "handle_observation";
      return false;
    }

    find_symbols_sett symbols;
    instruction->apply(
      [&symbols](const exprt &expr) { find_symbols(expr, symbols); });
    for(const auto &tls : summary.tls_symbols)
    {
      if(symbols.count(tls) != 0)
      {
        reason = "main_tls_observation";
        return false;
      }
    }

    irep_idt callee;
    if(
      direct_call(*instruction, callee) &&
      (callee == "pthread_getspecific" ||
       callee == "pthread_setspecific" ||
       callee == "pthread_key_delete"))
    {
      const auto &arguments = instruction->call_arguments();
      irep_idt key;
      if(
        !arguments.empty() && symbol_id(arguments[0], key) &&
        summary.key_symbols.count(key) != 0)
      {
        reason = "main_key_observation";
        return false;
      }
    }
  }
  return true;
}

bool collect_lifecycle(
  goto_modelt &model,
  lifecycle_loopt &create,
  lifecycle_loopt &join,
  std::string &reason)
{
  const auto main_entry =
    model.goto_functions.function_map.find(ID_main);
  if(
    main_entry == model.goto_functions.function_map.end() ||
    !main_entry->second.body_available())
  {
    reason = "main";
    return false;
  }
  auto &program = main_entry->second.body;
  natural_loops_mutablet loops;
  loops(program);
  if(loops.loop_map.size() != 2)
  {
    reason = "main_loop_count";
    return false;
  }

  bool have_create = false;
  bool have_join = false;
  for(const auto &entry : loops.loop_map)
  {
    lifecycle_loopt candidate;
    if(!analyze_lifecycle_loop(program, entry, candidate, reason))
      return false;
    if(candidate.create)
    {
      if(have_create)
      {
        reason = "duplicate_create";
        return false;
      }
      create = candidate;
      have_create = true;
    }
    else
    {
      if(have_join)
      {
        reason = "duplicate_join";
        return false;
      }
      join = candidate;
      have_join = true;
    }
  }
  if(!have_create || !have_join)
  {
    reason = "lifecycle_calls";
    return false;
  }
  if(
    create.head->location_number >= join.head->location_number ||
    strip(create.bound) != strip(join.bound) ||
    create.handle.base != join.handle.base)
  {
    reason = "lifecycle_match";
    return false;
  }
  return true;
}

void restrict_to_one(lifecycle_loopt &loop)
{
  loop.backedge->turn_into_skip();
}

bool sequentialize_representative(
  goto_modelt &model,
  lifecycle_loopt &create,
  lifecycle_loopt &join,
  std::string &reason)
{
  const auto worker_symbol =
    model.symbol_table.symbols.find(create.worker);
  if(worker_symbol == model.symbol_table.symbols.end())
  {
    reason = "worker_symbol";
    return false;
  }
  code_function_callt call(
    worker_symbol->second.symbol_expr(), {create.argument});
  call.add_source_location() = create.call->source_location();
  create.call->code_nonconst() = std::move(call);
  join.call->turn_into_skip();
  restrict_to_one(create);
  restrict_to_one(join);
  return true;
}

struct tls_array_loopt
{
  goto_programt::targett head;
  goto_programt::targett action;
  goto_programt::targett backedge;
  irep_idt index;
  exprt bound;
  bool property = false;
};

bool dereference_index(
  const exprt &src,
  irep_idt &base,
  irep_idt &index)
{
  const exprt &expr = strip(src);
  if(expr.id() != ID_dereference || expr.operands().size() != 1)
    return false;
  const exprt &pointer =
    strip(to_dereference_expr(expr).pointer());
  return
    pointer.id() == ID_plus && pointer.operands().size() == 2 &&
    symbol_id(pointer.op0(), base) &&
    symbol_id(pointer.op1(), index);
}

bool zero_constant(const exprt &src)
{
  const exprt &expr = strip(src);
  if(expr.id() != ID_constant)
    return false;
  mp_integer value;
  return !to_integer(to_constant_expr(expr), value) && value == 0;
}

bool nonzero_constant(const exprt &src)
{
  const exprt &expr = strip(src);
  if(expr.id() != ID_constant)
    return false;
  mp_integer value;
  return !to_integer(to_constant_expr(expr), value) && value != 0;
}

bool nonnegative_assumption(
  const goto_programt::instructiont &instruction,
  const irep_idt &identifier)
{
  irep_idt callee;
  if(
    !direct_call(instruction, callee) ||
    callee != "assume_abort_if_not" ||
    instruction.call_arguments().size() != 1)
    return false;
  const exprt &condition =
    strip(instruction.call_arguments().front());
  if(
    condition.id() != ID_ge ||
    condition.operands().size() != 2)
    return false;
  irep_idt lhs;
  return
    symbol_id(condition.op0(), lhs) && lhs == identifier &&
    zero_constant(condition.op1());
}

bool analyze_tls_array_loop(
  const natural_loops_mutablet::loop_mapt::value_type &entry,
  const irep_idt &tls_pointer,
  tls_array_loopt &result,
  std::string &reason)
{
  exprt index_expr;
  result.head = entry.first;
  if(
    !parse_loop_exit(
      result.head, result.index, index_expr, result.bound))
  {
    reason = "tls_loop_guard";
    return false;
  }

  std::size_t actions = 0;
  std::size_t increments = 0;
  std::size_t backedges = 0;
  for(const auto instruction : entry.second)
  {
    irep_idt callee;
    if(direct_call(*instruction, callee))
    {
      if(
        callee != "__VERIFIER_assert" ||
        instruction->call_arguments().size() != 1)
      {
        reason = "tls_loop_call";
        return false;
      }
      const exprt &condition =
        strip(instruction->call_arguments().front());
      if(
        condition.id() != ID_equal ||
        condition.operands().size() != 2)
      {
        reason = "tls_property_relation";
        return false;
      }
      irep_idt base;
      irep_idt index;
      if(
        !dereference_index(condition.op0(), base, index) ||
        base != tls_pointer || index != result.index ||
        !zero_constant(condition.op1()))
      {
        reason = "tls_property_index";
        return false;
      }
      result.property = true;
      result.action = instruction;
      ++actions;
    }
    else if(instruction->is_assign())
    {
      irep_idt lhs;
      if(
        symbol_id(instruction->assign_lhs(), lhs) &&
        lhs == result.index)
      {
        if(!unit_increment(*instruction, result.index))
        {
          reason = "tls_loop_increment";
          return false;
        }
        ++increments;
      }
      else
      {
        irep_idt base;
        irep_idt index;
        if(
          !dereference_index(
            instruction->assign_lhs(), base, index) ||
          base != tls_pointer || index != result.index ||
          !nonzero_constant(instruction->assign_rhs()))
        {
          reason = "tls_loop_write";
          return false;
        }
        result.property = false;
        result.action = instruction;
        ++actions;
      }
    }
    else if(instruction->is_backwards_goto())
    {
      if(instruction->get_target() != result.head)
      {
        reason = "tls_loop_backedge_target";
        return false;
      }
      result.backedge = instruction;
      ++backedges;
    }
    else if(
      !instruction->is_goto() && !instruction->is_skip() &&
      !instruction->is_location())
    {
      reason = "tls_loop_instruction";
      return false;
    }
  }
  if(actions != 1 || increments != 1 || backedges != 1)
  {
    reason = "tls_loop_cardinality";
    return false;
  }
  return true;
}

bool dynamic_tls_worker(
  goto_modelt &model,
  const namespacet &ns,
  const irep_idt &worker_id,
  irep_idt &tls_pointer,
  std::string &reason)
{
  auto worker = model.goto_functions.function_map.find(worker_id);
  if(
    worker == model.goto_functions.function_map.end() ||
    !worker->second.body_available())
  {
    reason = "tls_worker";
    return false;
  }
  auto &program = worker->second.body;
  natural_loops_mutablet loops;
  loops(program);
  if(loops.loop_map.size() != 2)
  {
    reason = "tls_worker_loop_count";
    return false;
  }

  goto_programt::targett calloc_call = program.instructions.end();
  goto_programt::targett tls_assignment = program.instructions.end();
  goto_programt::targett free_call = program.instructions.end();
  irep_idt allocation_result;
  irep_idt length;
  std::size_t calloc_calls = 0;
  std::size_t free_calls = 0;
  std::size_t property_calls = 0;
  std::size_t tls_writes = 0;
  bool length_nonnegative = false;
  for(auto instruction = program.instructions.begin();
      instruction != program.instructions.end(); ++instruction)
  {
    irep_idt callee;
    if(direct_call(*instruction, callee))
    {
      if(callee == "calloc")
      {
        const auto &arguments = instruction->call_arguments();
        if(arguments.size() != 2)
        {
          reason = "tls_calloc_shape";
          return false;
        }
        const exprt &element_size_expr = strip(arguments[1]);
        mp_integer element_size;
        if(
          instruction->call_lhs().is_nil() ||
          !symbol_id(instruction->call_lhs(), allocation_result) ||
          !symbol_id(arguments[0], length) ||
          element_size_expr.id() != ID_constant ||
          to_integer(
            to_constant_expr(element_size_expr), element_size) ||
          element_size <= 0)
        {
          reason = "tls_calloc_shape";
          return false;
        }
        calloc_call = instruction;
        ++calloc_calls;
      }
      else if(callee == "free")
      {
        irep_idt freed;
        if(
          instruction->call_arguments().size() != 1 ||
          !symbol_id(instruction->call_arguments().front(), freed))
        {
          reason = "tls_free_shape";
          return false;
        }
        if(tls_pointer.empty())
          tls_pointer = freed;
        if(freed != tls_pointer)
        {
          reason = "tls_free_object";
          return false;
        }
        free_call = instruction;
        ++free_calls;
      }
      else if(callee == "__VERIFIER_assert")
        ++property_calls;
      else if(callee == "assume_abort_if_not")
      {
        // Checked after the allocation has identified the bound symbol.
      }
      else
      {
        reason = "tls_worker_call";
        return false;
      }
    }
    if(instruction->is_assign())
    {
      irep_idt lhs;
      irep_idt rhs;
      if(
        symbol_id(instruction->assign_lhs(), lhs))
      {
        const symbolt *symbol = nullptr;
        if(!ns.lookup(lhs, symbol) && symbol->is_static_lifetime)
        {
          if(!symbol->is_thread_local)
          {
            reason = "tls_shared_write";
            return false;
          }
          if(
            !symbol_id(instruction->assign_rhs(), rhs) ||
            rhs != allocation_result)
          {
            reason = "tls_pointer_assignment";
            return false;
          }
          if(tls_pointer.empty())
            tls_pointer = lhs;
          if(lhs != tls_pointer)
          {
            reason = "tls_pointer_count";
            return false;
          }
          tls_assignment = instruction;
          ++tls_writes;
        }
      }
    }
  }
  for(const auto &instruction : program.instructions)
    length_nonnegative =
      length_nonnegative ||
      (!length.empty() &&
       nonnegative_assumption(instruction, length));

  const symbolt *tls_symbol = nullptr;
  if(
    calloc_calls != 1 || free_calls != 1 || property_calls != 1 ||
    tls_writes != 1 || !length_nonnegative ||
    calloc_call == program.instructions.end() ||
    tls_assignment == program.instructions.end() ||
    free_call == program.instructions.end() ||
    ns.lookup(tls_pointer, tls_symbol) ||
    !tls_symbol->is_thread_local ||
    tls_symbol->type.id() != ID_pointer)
  {
    reason = "tls_worker_resources";
    return false;
  }

  std::vector<tls_array_loopt> summaries;
  for(const auto &entry : loops.loop_map)
  {
    tls_array_loopt summary;
    if(!analyze_tls_array_loop(
         entry, tls_pointer, summary, reason))
      return false;
    summaries.push_back(std::move(summary));
  }
  std::sort(
    summaries.begin(),
    summaries.end(),
    [](const tls_array_loopt &lhs, const tls_array_loopt &rhs) {
      return lhs.head->location_number < rhs.head->location_number;
    });
  irep_idt loop_bound;
  if(
    !summaries[0].property || summaries[1].property ||
    strip(summaries[0].bound) != strip(summaries[1].bound) ||
    !symbol_id(summaries[0].bound, loop_bound) ||
    loop_bound != length ||
    tls_assignment->location_number >=
      summaries[0].head->location_number ||
    summaries[0].backedge->location_number >=
      summaries[1].head->location_number ||
    summaries[1].backedge->location_number >=
      free_call->location_number)
  {
    reason = "tls_worker_order";
    return false;
  }

  const auto initialize =
    model.goto_functions.function_map.find("__CPROVER_initialize");
  if(
    initialize == model.goto_functions.function_map.end() ||
    !initialize->second.body_available())
  {
    reason = "tls_initialize";
    return false;
  }
  std::size_t null_initializations = 0;
  for(const auto &instruction : initialize->second.body.instructions)
  {
    irep_idt lhs;
    if(
      instruction.is_assign() &&
      symbol_id(instruction.assign_lhs(), lhs) &&
      lhs == tls_pointer &&
      zero_value(instruction.assign_rhs()))
      ++null_initializations;
  }
  if(null_initializations != 1)
  {
    reason = "tls_initial_value";
    return false;
  }
  return true;
}

std::vector<goto_programt::targett> semantic_instructions(
  goto_programt &program)
{
  std::vector<goto_programt::targett> result;
  for(auto instruction = program.instructions.begin();
      instruction != program.instructions.end(); ++instruction)
  {
    if(
      instruction->is_skip() || instruction->is_location() ||
      instruction->is_decl() || instruction->is_dead() ||
      instruction->is_set_return_value() ||
      instruction->is_end_function())
      continue;
    result.push_back(instruction);
  }
  return result;
}

bool pointer_integer(
  const exprt &src,
  mp_integer &value)
{
  const exprt &expr = strip(src);
  return
    expr.id() == ID_constant &&
    !to_integer(to_constant_expr(expr), value);
}

bool direct_dereference_symbol(
  const exprt &src,
  irep_idt &identifier)
{
  const exprt &expr = strip(src);
  return
    expr.id() == ID_dereference &&
    expr.operands().size() == 1 &&
    symbol_id(to_dereference_expr(expr).pointer(), identifier);
}

bool tls_destructor_shape(
  goto_modelt &model,
  irep_idt &key,
  irep_idt &destructor,
  irep_idt &worker_id,
  mp_integer &value,
  goto_programt::targett &key_create,
  goto_programt::targett &worker_setspecific,
  goto_programt::targett &worker_return,
  std::string &reason)
{
  auto main = model.goto_functions.function_map.find(ID_main);
  if(
    main == model.goto_functions.function_map.end() ||
    !main->second.body_available())
  {
    reason = "tls_dtor_main";
    return false;
  }
  auto main_semantic = semantic_instructions(main->second.body);
  if(main_semantic.size() != 9)
  {
    reason = "tls_dtor_main_count";
    return false;
  }

  irep_idt callee;
  if(
    !direct_call(*main_semantic[0], callee) ||
    callee != "pthread_key_create" ||
    main_semantic[0]->call_arguments().size() != 2 ||
    !address_of_symbol(
      main_semantic[0]->call_arguments()[0], key) ||
    !address_of_symbol(
      main_semantic[0]->call_arguments()[1], destructor) ||
    main_semantic[0]->call_lhs().is_nil())
  {
    reason = "tls_dtor_key_create";
    return false;
  }
  key_create = main_semantic[0];

  irep_idt key_result;
  irep_idt checked_result;
  if(
    !symbol_id(main_semantic[0]->call_lhs(), key_result) ||
    !main_semantic[1]->is_assign() ||
    !symbol_id(main_semantic[1]->assign_lhs(), checked_result) ||
    !symbol_id(main_semantic[1]->assign_rhs(), callee) ||
    callee != key_result ||
    !main_semantic[2]->is_goto() ||
    main_semantic[2]->targets.size() != 1 ||
    !direct_call(*main_semantic[3], callee) ||
    callee != "reach_error" ||
    main_semantic[2]->get_target()->location_number <=
      main_semantic[3]->location_number ||
    main_semantic[2]->get_target()->location_number >
      main_semantic[4]->location_number)
  {
    reason = "tls_dtor_key_result";
    return false;
  }
  const exprt &key_success = strip(main_semantic[2]->condition());
  irep_idt key_success_symbol;
  if(
    key_success.id() != ID_equal ||
    key_success.operands().size() != 2 ||
    !symbol_id(key_success.op0(), key_success_symbol) ||
    key_success_symbol != checked_result ||
    !zero_constant(key_success.op1()))
  {
    reason = "tls_dtor_key_success";
    return false;
  }

  irep_idt thread;
  irep_idt create_worker;
  irep_idt create_key;
  if(
    !direct_call(*main_semantic[4], callee) ||
    callee != "pthread_create" ||
    main_semantic[4]->call_arguments().size() != 4 ||
    !address_of_symbol(
      main_semantic[4]->call_arguments()[0], thread) ||
    !address_of_symbol(
      main_semantic[4]->call_arguments()[2], create_worker))
  {
    reason = "tls_dtor_create";
    return false;
  }
  const exprt &worker_argument =
    strip(main_semantic[4]->call_arguments()[3]);
  if(
    worker_argument.id() != ID_address_of ||
    !symbol_id(
      to_address_of_expr(worker_argument).object(), create_key) ||
    create_key != key)
  {
    reason = "tls_dtor_create_argument";
    return false;
  }
  worker_id = create_worker;

  if(
    !direct_call(*main_semantic[5], callee) ||
    callee != "pthread_setspecific" ||
    main_semantic[5]->call_arguments().size() != 2 ||
    !main_semantic[6]->is_goto() ||
    !direct_call(*main_semantic[7], callee) ||
    callee != "reach_error" ||
    main_semantic[6]->get_target() != main_semantic[8] ||
    !direct_call(*main_semantic[8], callee) ||
    callee != "pthread_join" ||
    main_semantic[8]->call_arguments().size() != 2)
  {
    reason = "tls_dtor_main_suffix";
    return false;
  }
  irep_idt main_specific_key;
  irep_idt joined_thread;
  if(
    !symbol_id(
      main_semantic[5]->call_arguments()[0], main_specific_key) ||
    main_specific_key != key ||
    !symbol_id(
      main_semantic[8]->call_arguments()[0], joined_thread) ||
    joined_thread != thread)
  {
    reason = "tls_dtor_main_correspondence";
    return false;
  }

  auto worker = model.goto_functions.function_map.find(worker_id);
  if(
    worker == model.goto_functions.function_map.end() ||
    !worker->second.body_available())
  {
    reason = "tls_dtor_worker";
    return false;
  }
  auto worker_semantic = semantic_instructions(worker->second.body);
  if(worker_semantic.size() != 5)
  {
    reason = "tls_dtor_worker_count";
    return false;
  }
  irep_idt local_key;
  irep_idt worker_argument_symbol;
  if(
    !worker_semantic[0]->is_assign() ||
    !symbol_id(worker_semantic[0]->assign_lhs(), local_key) ||
    !symbol_id(
      worker_semantic[0]->assign_rhs(), worker_argument_symbol) ||
    !direct_call(*worker_semantic[1], callee) ||
    callee != "pthread_setspecific" ||
    worker_semantic[1]->call_arguments().size() != 2)
  {
    reason = "tls_dtor_worker_prefix";
    return false;
  }
  irep_idt dereferenced_key;
  if(
    !direct_dereference_symbol(
      worker_semantic[1]->call_arguments()[0], dereferenced_key) ||
    dereferenced_key != local_key ||
    !pointer_integer(
      worker_semantic[1]->call_arguments()[1], value) ||
    value == 0)
  {
    reason = "tls_dtor_worker_value";
    return false;
  }
  worker_setspecific = worker_semantic[1];
  irep_idt worker_result;
  irep_idt worker_checked;
  if(
    worker_semantic[1]->call_lhs().is_nil() ||
    !symbol_id(
      worker_semantic[1]->call_lhs(), worker_result) ||
    !worker_semantic[2]->is_assign() ||
    !symbol_id(worker_semantic[2]->assign_lhs(), worker_checked) ||
    !symbol_id(worker_semantic[2]->assign_rhs(), callee) ||
    callee != worker_result ||
    !worker_semantic[3]->is_goto() ||
    !direct_call(*worker_semantic[4], callee) ||
    callee != "reach_error")
  {
    reason = "tls_dtor_worker_result";
    return false;
  }
  worker_return = worker_semantic[3]->get_target();
  if(worker_return == worker->second.body.instructions.end())
  {
    reason = "tls_dtor_worker_return";
    return false;
  }

  auto dtor = model.goto_functions.function_map.find(destructor);
  if(
    dtor == model.goto_functions.function_map.end() ||
    !dtor->second.body_available())
  {
    reason = "tls_dtor_body";
    return false;
  }
  auto dtor_semantic = semantic_instructions(dtor->second.body);
  if(
    dtor_semantic.size() != 3 ||
    !dtor_semantic[0]->is_assign() ||
    !dtor_semantic[1]->is_goto() ||
    dtor_semantic[1]->targets.size() != 1 ||
    !direct_call(*dtor_semantic[2], callee) ||
    callee != "reach_error" ||
    dtor_semantic[1]->get_target() ==
      dtor_semantic[2])
  {
    reason = "tls_dtor_property";
    return false;
  }
  irep_idt converted;
  irep_idt parameter;
  if(
    !symbol_id(dtor_semantic[0]->assign_lhs(), converted) ||
    !symbol_id(dtor_semantic[0]->assign_rhs(), parameter))
  {
    reason = "tls_dtor_conversion";
    return false;
  }
  const exprt &guard = strip(dtor_semantic[1]->condition());
  irep_idt guarded;
  mp_integer forbidden;
  if(
    guard.id() != ID_notequal ||
    guard.operands().size() != 2 ||
    !symbol_id(guard.op0(), guarded) ||
    guarded != converted ||
    !pointer_integer(guard.op1(), forbidden) ||
    forbidden != value)
  {
    reason = "tls_dtor_guard";
    return false;
  }
  return true;
}
} // namespace

bool tls_destructor_counterexample_transform(
  goto_modelt &goto_model,
  message_handlert &message_handler)
{
  irep_idt key;
  irep_idt destructor;
  irep_idt worker;
  mp_integer value;
  goto_programt::targett key_create;
  goto_programt::targett worker_setspecific;
  goto_programt::targett worker_return;
  std::string reason;
  if(
    !tls_destructor_shape(
      goto_model,
      key,
      destructor,
      worker,
      value,
      key_create,
      worker_setspecific,
      worker_return,
      reason))
  {
    std::cout
      << "NATIVE_TLS_DESTRUCTOR_COUNTEREXAMPLE applied=0 reason="
      << reason << '\n';
    return false;
  }

  const namespacet ns(goto_model.symbol_table);
  const symbolt &key_symbol = ns.lookup(key);
  const symbolt &destructor_symbol = ns.lookup(destructor);
  const exprt zero_key = from_integer(0, key_symbol.type);
  const auto key_location = key_create->source_location();
  auto &main =
    goto_model.goto_functions.function_map.at(ID_main).body;
  main.insert_before(
    key_create,
    goto_programt::make_assignment(
      key_symbol.symbol_expr(), zero_key, key_location));
  const exprt key_create_lhs = key_create->call_lhs();
  *key_create =
    goto_programt::make_assignment(
      key_create_lhs,
      from_integer(0, key_create_lhs.type()),
      key_location);

  const exprt worker_result_lhs =
    worker_setspecific->call_lhs();
  *worker_setspecific =
    goto_programt::make_assignment(
      worker_result_lhs,
      from_integer(0, worker_result_lhs.type()),
      worker_setspecific->source_location());
  const code_typet &destructor_type =
    to_code_type(destructor_symbol.type);
  INVARIANT(
    destructor_type.parameters().size() == 1,
    "accepted TLS destructor has one parameter");
  const exprt destructor_value =
    typecast_exprt::conditional_cast(
      from_integer(value, size_type()),
      destructor_type.parameters().front().type());
  code_function_callt destructor_call(
    destructor_symbol.symbol_expr(), {destructor_value});
  auto &worker_body =
    goto_model.goto_functions.function_map.at(worker).body;
  auto destructor_instruction =
    goto_programt::make_function_call(
      destructor_call, worker_return->source_location());
  worker_body.insert_before_swap(
    worker_return, destructor_instruction);
  goto_model.goto_functions.update();
  std::cout
    << "NATIVE_TLS_DESTRUCTOR_COUNTEREXAMPLE applied=1"
    << " worker=" << worker
    << " destructor=" << destructor
    << " value=" << value << '\n';
  (void)message_handler;
  return true;
}

bool dynamic_tls_calloc_zero_proof(
  goto_modelt &goto_model,
  message_handlert &message_handler)
{
  std::string reason;
  lifecycle_loopt create;
  lifecycle_loopt join;
  if(!collect_lifecycle(goto_model, create, join, reason))
  {
    std::cout
      << "NATIVE_DYNAMIC_TLS_CALLOC_ZERO applied=0 reason="
      << reason << '\n';
    return false;
  }
  const namespacet ns(goto_model.symbol_table);
  irep_idt tls_pointer;
  if(
    !dynamic_tls_worker(
      goto_model, ns, create.worker, tls_pointer, reason))
  {
    std::cout
      << "NATIVE_DYNAMIC_TLS_CALLOC_ZERO applied=0 reason="
      << reason << " worker=" << create.worker << '\n';
    return false;
  }

  bool thread_count_nonnegative = false;
  const auto &main =
    goto_model.goto_functions.function_map.at(ID_main).body;
  irep_idt thread_count;
  if(!symbol_id(create.bound, thread_count))
  {
    std::cout
      << "NATIVE_DYNAMIC_TLS_CALLOC_ZERO applied=0"
      << " reason=tls_thread_bound\n";
    return false;
  }
  for(const auto &instruction : main.instructions)
    thread_count_nonnegative =
      thread_count_nonnegative ||
      nonnegative_assumption(instruction, thread_count);
  if(!thread_count_nonnegative)
  {
    std::cout
      << "NATIVE_DYNAMIC_TLS_CALLOC_ZERO applied=0"
      << " reason=tls_thread_count\n";
    return false;
  }

  std::cout
    << "NATIVE_DYNAMIC_TLS_CALLOC_ZERO applied=1"
    << " worker=" << create.worker
    << " tls=" << tls_pointer
    << " thread_count=" << thread_count << '\n';
  (void)message_handler;
  return true;
}

bool homogeneous_thread_local_cutoff_transform(
  goto_modelt &goto_model,
  message_handlert &message_handler)
{
  (void)message_handler;
  std::string reason;
  lifecycle_loopt create;
  lifecycle_loopt join;
  if(!collect_lifecycle(goto_model, create, join, reason))
  {
    std::cout << "NATIVE_THREAD_LOCAL_CUTOFF applied=0 reason="
              << reason << '\n';
    return false;
  }

  const namespacet ns(goto_model.symbol_table);
  worker_summaryt summary;
  std::set<irep_idt> visiting;
  if(
    !analyze_worker(
      create.worker, goto_model, ns, visiting, summary, reason))
  {
    std::cout << "NATIVE_THREAD_LOCAL_CUTOFF applied=0 reason="
              << reason << " worker=" << create.worker << '\n';
    return false;
  }
  if(summary.properties == 0)
  {
    std::cout
      << "NATIVE_THREAD_LOCAL_CUTOFF applied=0 reason=worker_property\n";
    return false;
  }

  const auto &main =
    goto_model.goto_functions.function_map.at(ID_main).body;
  for(const auto &key : summary.key_symbols)
  {
    if(
      !immutable_key_initialization(
        main, key, create.head, reason))
    {
      std::cout << "NATIVE_THREAD_LOCAL_CUTOFF applied=0 reason="
                << reason << " key=" << key << '\n';
      return false;
    }
  }
  if(!main_non_observation(main, create, join, summary, reason))
  {
    std::cout << "NATIVE_THREAD_LOCAL_CUTOFF applied=0 reason="
              << reason << '\n';
    return false;
  }
  if(summary.tls_symbols.empty() && summary.key_symbols.empty())
  {
    std::cout
      << "NATIVE_THREAD_LOCAL_CUTOFF applied=0 reason=no_thread_local_state\n";
    return false;
  }

  if(
    !sequentialize_representative(
      goto_model, create, join, reason))
  {
    std::cout << "NATIVE_THREAD_LOCAL_CUTOFF applied=0 reason="
              << reason << '\n';
    return false;
  }
  goto_model.goto_functions.update();
  std::cout << "NATIVE_THREAD_LOCAL_CUTOFF applied=1 worker="
            << create.worker
            << " tls=" << summary.tls_symbols.size()
            << " keys=" << summary.key_symbols.size()
            << " properties=" << summary.properties
            << " instructions=" << summary.instructions << '\n';
  return true;
}
