/*******************************************************************\

Module: Homogeneous Thread-Local Cutoff

\*******************************************************************/

#include "thread_local_cutoff_analysis.h"

#include "natural_loops.h"

#include <goto-programs/goto_model.h>

#include <util/arith_tools.h>
#include <util/expr_util.h>
#include <util/find_symbols.h>
#include <util/namespace.h>
#include <util/pointer_expr.h>
#include <util/std_code.h>
#include <util/std_expr.h>
#include <util/symbol.h>

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
} // namespace

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
