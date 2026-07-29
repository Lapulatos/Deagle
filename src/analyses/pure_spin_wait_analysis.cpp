/*******************************************************************\

Module: Native Pure Spin-Wait Collapse

\*******************************************************************/

#include "jces_analysis.h"

#include <goto-programs/goto_inline.h>
#include <goto-programs/goto_model.h>

#include <util/arith_tools.h>
#include <util/expr_util.h>
#include <util/exit_codes.h>
#include <util/find_symbols.h>
#include <util/message.h>
#include <util/pointer_expr.h>
#include <util/simplify_expr.h>
#include <util/std_expr.h>
#include <util/symbol.h>

#include <algorithm>
#include <cstdlib>
#include <functional>
#include <iostream>
#include <iterator>
#include <map>
#include <set>
#include <string>
#include <vector>

namespace
{
bool direct_call_identifier(
  const goto_programt::instructiont &instruction,
  irep_idt &identifier)
{
  if(!instruction.is_function_call())
    return false;
  const exprt &function = skip_typecast(instruction.call_function());
  if(function.id() != ID_symbol)
    return false;
  identifier = to_symbol_expr(function).get_identifier();
  return true;
}
} // namespace

bool pure_spin_wait_dispatch(
  goto_modelt &goto_model,
  message_handlert &message_handler)
{
  bool empty_barrier_family =
    goto_model.symbol_table.symbols.find(
      "__CPROVER_deagle_empty_compiler_barrier") !=
    goto_model.symbol_table.symbols.end();
  if(!empty_barrier_family)
    return false;

  bool within_proof_budget = false;
  const bool transformed =
    pure_spin_wait_collapse_transform(
      goto_model,
      message_handler,
      empty_barrier_family,
      within_proof_budget);
  if(!transformed || !within_proof_budget)
  {
    std::cout
      << "NATIVE_PURE_SPIN_PROOF result=INCONCLUSIVE"
      << " reason=not_admitted\n"
      << "VERIFICATION INCONCLUSIVE\n";
    std::exit(CPROVER_EXIT_VERIFICATION_INCONCLUSIVE);
  }
  return true;
}


#if defined(__GNUC__)
__attribute__((cold))
#endif
bool pure_spin_wait_collapse_transform(
  goto_modelt &goto_model,
  message_handlert &message_handler,
  bool &empty_barrier_family,
  bool &within_proof_budget)
{
  struct candidatet
  {
    irep_idt function;
    goto_programt::targett backedge;
  };

  std::vector<candidatet> accepted_candidates;
  std::size_t marked_candidates = 0;
  std::size_t model_instructions = 0;
  within_proof_budget = false;
  empty_barrier_family =
    goto_model.symbol_table.symbols.find(
      "__CPROVER_deagle_empty_compiler_barrier") !=
    goto_model.symbol_table.symbols.end();
  if(!empty_barrier_family)
  {
    std::cout
      << "NATIVE_PURE_SPIN_COLLAPSE applied=0"
      << " empty_barrier=0 reason=no_empty_barrier\n";
    return false;
  }

  std::function<bool(const exprt &)> local_value_expression;
  local_value_expression = [&](const exprt &expression) -> bool
  {
    if(
      expression.id() == ID_dereference ||
      expression.id() == ID_index ||
      expression.id() == ID_member)
      return false;
    if(expression.id() == ID_symbol)
    {
      const auto symbol = goto_model.symbol_table.symbols.find(
        to_symbol_expr(expression).get_identifier());
      return
        symbol != goto_model.symbol_table.symbols.end() &&
        !symbol->second.is_static_lifetime;
    }
    for(const auto &operand : expression.operands())
    {
      if(!local_value_expression(operand))
        return false;
    }
    return true;
  };

  std::function<bool(
    const irep_idt &, std::set<irep_idt> &, std::size_t &)> read_only_callee;
  read_only_callee =
    [&](const irep_idt &root,
        std::set<irep_idt> &visiting,
        std::size_t &atomic_load_calls) -> bool
  {
    const std::string identifier = id2string(root);
    if(identifier.rfind("__atomic_load", 0) == 0)
    {
      ++atomic_load_calls;
      return true;
    }
    if(!visiting.insert(root).second)
      return false;
    const auto function =
      goto_model.goto_functions.function_map.find(root);
    if(
      function == goto_model.goto_functions.function_map.end() ||
      !function->second.body_available())
      return false;
    for(const auto &instruction : function->second.body.instructions)
    {
      if(instruction.is_assign())
      {
        if(
          instruction.assign_lhs().id() != ID_symbol ||
          !local_value_expression(instruction.assign_rhs()))
          return false;
        find_symbols_sett lhs_symbols;
        find_symbols(instruction.assign_lhs(), lhs_symbols);
        if(lhs_symbols.size() != 1)
          return false;
        const auto symbol =
          goto_model.symbol_table.symbols.find(*lhs_symbols.begin());
        if(
          symbol == goto_model.symbol_table.symbols.end() ||
          symbol->second.is_static_lifetime)
          return false;
      }
      else if(instruction.is_function_call())
      {
        irep_idt callee;
        if(
          !direct_call_identifier(instruction, callee) ||
          !read_only_callee(callee, visiting, atomic_load_calls))
          return false;
      }
      else if(
        instruction.is_goto() &&
        !local_value_expression(instruction.condition()))
        return false;
      else if(
        !instruction.is_goto() &&
        !instruction.is_decl() &&
        !instruction.is_dead() &&
        !instruction.is_skip() &&
        !instruction.is_location() &&
        !instruction.is_set_return_value() &&
        !instruction.is_end_function())
        return false;
    }
    visiting.erase(root);
    return true;
  };

  std::function<bool(const irep_idt &, std::set<irep_idt> &)>
    reaches_atomic_reservation;
  reaches_atomic_reservation =
    [&](const irep_idt &root, std::set<irep_idt> &visiting) -> bool
  {
    const std::string identifier = id2string(root);
    if(
      identifier.rfind("__atomic_fetch_add", 0) == 0 ||
      identifier.rfind("__atomic_add_fetch", 0) == 0)
      return true;
    if(!visiting.insert(root).second)
      return false;
    const auto function =
      goto_model.goto_functions.function_map.find(root);
    if(
      function == goto_model.goto_functions.function_map.end() ||
      !function->second.body_available())
      return false;
    for(const auto &instruction : function->second.body.instructions)
    {
      irep_idt callee;
      if(
        instruction.is_function_call() &&
        direct_call_identifier(instruction, callee) &&
        reaches_atomic_reservation(callee, visiting))
      {
        visiting.erase(root);
        return true;
      }
    }
    visiting.erase(root);
    return false;
  };

  auto reservation_dominates_call =
    [&](const goto_programt &program,
        goto_programt::const_targett target) -> bool
  {
    using statet =
      std::pair<const goto_programt::instructiont *, bool>;
    std::vector<std::pair<goto_programt::const_targett, bool>> worklist;
    std::set<statet> visited;
    worklist.push_back({program.instructions.begin(), false});
    bool reached_target = false;
    while(!worklist.empty())
    {
      const auto state = worklist.back();
      worklist.pop_back();
      const auto instruction = state.first;
      const bool reserved_before = state.second;
      if(
        !visited.insert({&*instruction, reserved_before}).second)
        continue;
      if(instruction == target)
      {
        reached_target = true;
        if(!reserved_before)
          return false;
        continue;
      }
      bool reserved_after = reserved_before;
      irep_idt callee;
      std::set<irep_idt> reservation_visiting;
      if(
        instruction->is_function_call() &&
        direct_call_identifier(*instruction, callee) &&
        reaches_atomic_reservation(callee, reservation_visiting))
        reserved_after = true;
      for(const auto &successor : program.get_successors(instruction))
        worklist.push_back({successor, reserved_after});
    }
    return reached_target;
  };

  std::function<bool(const irep_idt &, std::set<irep_idt> &)>
    all_call_paths_have_reservation;
  all_call_paths_have_reservation =
    [&](const irep_idt &root, std::set<irep_idt> &visiting) -> bool
  {
    if(!visiting.insert(root).second)
      return false;
    std::size_t direct_callers = 0;
    bool every_call_path_reserves = true;
    for(const auto &caller_entry : goto_model.goto_functions.function_map)
    {
      if(!caller_entry.second.body_available())
        continue;
      const auto &caller = caller_entry.second.body;
      for(auto call = caller.instructions.begin();
          call != caller.instructions.end(); ++call)
      {
        irep_idt callee;
        if(
          !call->is_function_call() ||
          !direct_call_identifier(*call, callee) ||
          callee != root)
          continue;
        ++direct_callers;
        bool prefix_reserves =
          reservation_dominates_call(caller, call);
        if(!prefix_reserves)
        {
          std::set<irep_idt> caller_visiting = visiting;
          prefix_reserves = all_call_paths_have_reservation(
            caller_entry.first, caller_visiting);
        }
        every_call_path_reserves =
          every_call_path_reserves && prefix_reserves;
      }
    }
    visiting.erase(root);
    return direct_callers != 0 && every_call_path_reserves;
  };

  auto inlined_failure_iteration_is_stuttering =
    [&](const irep_idt &function_id,
        const source_locationt &backedge_location,
        std::string &reason) -> bool
  {
    goto_modelt inlined_model;
    inlined_model.symbol_table = goto_model.symbol_table;
    inlined_model.goto_functions.copy_from(
      goto_model.goto_functions);
    goto_function_inline(
      inlined_model, function_id, message_handler, false, true);
    inlined_model.goto_functions.update();

    auto function =
      inlined_model.goto_functions.function_map.find(function_id);
    if(
      function == inlined_model.goto_functions.function_map.end() ||
      !function->second.body_available())
    {
      reason = "inline_function";
      return false;
    }
    auto &program = function->second.body;
    std::vector<goto_programt::targett> order;
    std::map<const goto_programt::instructiont *, std::size_t> position;
    for(auto instruction = program.instructions.begin();
        instruction != program.instructions.end(); ++instruction)
    {
      position.emplace(&*instruction, order.size());
      order.push_back(instruction);
    }

    goto_programt::targett matched = program.instructions.end();
    for(auto instruction = program.instructions.begin();
        instruction != program.instructions.end(); ++instruction)
    {
      if(
        !instruction->is_goto() ||
        !instruction->condition().is_true() ||
        instruction->targets.size() != 1 ||
        position.at(&*instruction->get_target()) >=
          position.at(&*instruction))
        continue;
      const auto &location = instruction->source_location();
      if(
        location.get_file() == backedge_location.get_file() &&
        location.get_line() == backedge_location.get_line())
      {
        if(matched != program.instructions.end())
        {
          reason = "inline_backedge_ambiguous";
          return false;
        }
        matched = instruction;
      }
    }
    if(matched == program.instructions.end())
    {
      reason = "inline_backedge_missing";
      return false;
    }

    const auto head = matched->get_target();

    struct statet
    {
      explicit statet(goto_programt::targett _instruction)
        : instruction(_instruction)
      {
      }

      goto_programt::targett instruction;
      std::set<irep_idt> live_locals;
      std::map<irep_idt, irep_idt> local_pointer_targets;
      std::map<irep_idt, exprt> values;
      std::vector<exprt> path_conditions;
      bool shared_write = false;
      std::size_t depth = 0;
    };

    const namespacet ns(inlined_model.symbol_table);
    std::function<exprt(
      const exprt &,
      const std::map<irep_idt, exprt> &,
      std::set<irep_idt> &)> evaluate;
    evaluate =
      [&](const exprt &source,
          const std::map<irep_idt, exprt> &values,
          std::set<irep_idt> &visiting) -> exprt
    {
      if(source.id() == ID_address_of)
      {
        const exprt &object =
          skip_typecast(to_address_of_expr(source).object());
        if(object.id() == ID_symbol)
        {
          const symbolt *symbol = nullptr;
          if(
            !ns.lookup(
              to_symbol_expr(object).get_identifier(), symbol) &&
            !symbol->is_static_lifetime)
            return source;
        }
      }
      if(source.id() == ID_symbol)
      {
        const irep_idt identifier =
          to_symbol_expr(source).get_identifier();
        const auto value = values.find(identifier);
        if(
          value != values.end() &&
          visiting.insert(identifier).second)
        {
          exprt result = evaluate(value->second, values, visiting);
          visiting.erase(identifier);
          return result;
        }
      }
      exprt result = source;
      for(auto &operand : result.operands())
        operand = evaluate(operand, values, visiting);
      simplify(result, ns);
      return result;
    };
    auto evaluated =
      [&](const exprt &source,
          const std::map<irep_idt, exprt> &values) -> exprt
    {
      std::set<irep_idt> visiting;
      return evaluate(source, values, visiting);
    };
    auto condition_value =
      [&](const exprt &source,
          const statet &state) -> int
    {
      const exprt value = evaluated(source, state.values);
      if(value.is_true())
        return 1;
      if(value.is_false())
        return 0;
      for(const auto &known : state.path_conditions)
      {
        if(value == known)
          return 1;
        exprt negated = not_exprt(known);
        simplify(negated, ns);
        if(value == negated)
          return 0;
      }
      return -1;
    };
    auto forget_local_value =
      [](statet &state, const irep_idt &identifier)
    {
      state.path_conditions.erase(
        std::remove_if(
          state.path_conditions.begin(),
          state.path_conditions.end(),
          [&](const exprt &condition)
          {
            const auto symbols = find_symbols(condition);
            return std::any_of(
              symbols.begin(),
              symbols.end(),
              [&](const symbol_exprt &symbol)
              {
                return symbol.get_identifier() == identifier;
              });
          }),
        state.path_conditions.end());
      for(auto value = state.values.begin();
          value != state.values.end();)
      {
        if(value->first == identifier)
        {
          ++value;
          continue;
        }
        const auto symbols = find_symbols(value->second);
        const bool depends =
          std::any_of(
            symbols.begin(),
            symbols.end(),
            [&](const symbol_exprt &symbol)
            {
              return symbol.get_identifier() == identifier;
            });
        if(depends)
          value = state.values.erase(value);
        else
          ++value;
      }
    };
    auto loop_carried_locals_are_unobserved =
      [&](const std::set<irep_idt> &locals) -> bool
    {
      using pendingt =
        std::pair<goto_programt::targett, std::set<irep_idt>>;
      std::vector<pendingt> pending;
      pending.emplace_back(head, locals);
      std::set<std::pair<std::size_t, std::set<irep_idt>>> seen;
      while(!pending.empty())
      {
        pendingt current = std::move(pending.back());
        pending.pop_back();
        auto instruction = current.first;
        auto remaining = std::move(current.second);
        if(instruction == matched || instruction->is_end_function())
          continue;
        if(!seen.emplace(
             position.at(&*instruction), remaining).second)
          continue;

        find_symbols_sett reads;
        if(instruction->is_assign())
        {
          find_symbols(instruction->assign_rhs(), reads);
          const exprt &lhs =
            skip_typecast(instruction->assign_lhs());
          if(lhs.id() != ID_symbol)
            find_symbols(lhs, reads);
        }
        else if(instruction->is_function_call())
        {
          find_symbols(instruction->call_function(), reads);
          for(const auto &argument : instruction->call_arguments())
            find_symbols(argument, reads);
        }
        else if(
          instruction->is_goto() || instruction->is_assume() ||
          instruction->is_assert())
          find_symbols(instruction->condition(), reads);
        else if(instruction->is_set_return_value())
          find_symbols(
            instruction->return_value(), reads);
        else if(instruction->is_other())
          find_symbols(instruction->code(), reads);

        for(const auto &identifier : reads)
        {
          if(remaining.find(identifier) != remaining.end())
            return false;
        }

        if(instruction->is_assign())
        {
          const exprt &lhs =
            skip_typecast(instruction->assign_lhs());
          if(lhs.id() == ID_symbol)
            remaining.erase(
              to_symbol_expr(lhs).get_identifier());
        }
        else if(instruction->is_dead())
          remaining.erase(
            instruction->dead_symbol().get_identifier());
        else if(
          instruction->is_function_call() &&
          instruction->call_lhs().id() == ID_symbol)
          remaining.erase(
            to_symbol_expr(instruction->call_lhs())
              .get_identifier());

        if(instruction->is_goto())
        {
          if(!instruction->condition().is_false())
            pending.emplace_back(
              instruction->get_target(), remaining);
          if(!instruction->condition().is_true())
            pending.emplace_back(
              std::next(instruction), remaining);
        }
        else
          pending.emplace_back(
            std::next(instruction), remaining);
      }
      return true;
    };

    std::vector<statet> worklist;
    worklist.emplace_back(head);
    std::size_t explored_states = 0;
    std::size_t backedge_paths = 0;
    std::size_t exit_paths = 0;
    while(!worklist.empty())
    {
      statet state = std::move(worklist.back());
      worklist.pop_back();
      if(++explored_states > 16384 ||
         state.depth > order.size() * 4)
      {
        reason = "inline_state_budget";
        return false;
      }
      if(state.instruction == matched)
      {
        ++backedge_paths;
        if(state.shared_write)
        {
          reason = "inline_failure_shared_write";
          return false;
        }
        if(!state.live_locals.empty())
        {
          if(!loop_carried_locals_are_unobserved(
               state.live_locals))
          {
            reason = "inline_loop_carried_local";
            return false;
          }
        }
        continue;
      }
      if(state.instruction->is_end_function())
      {
        ++exit_paths;
        continue;
      }

      auto instruction = state.instruction;
      if(instruction->is_assign())
      {
        const exprt &lhs = skip_typecast(instruction->assign_lhs());
        if(lhs.id() == ID_symbol)
        {
          const irep_idt identifier =
            to_symbol_expr(lhs).get_identifier();
          const symbolt *symbol = nullptr;
          if(
            ns.lookup(identifier, symbol) ||
            symbol->is_static_lifetime)
            state.shared_write = true;
          else
            state.live_locals.insert(identifier);
          forget_local_value(state, identifier);
          state.local_pointer_targets.erase(identifier);
          const exprt rhs =
            evaluated(instruction->assign_rhs(), state.values);
          const std::string identifier_text =
            id2string(identifier);
          const std::string weak_parameter = "::p_3";
          if(
            identifier_text.find(
              "__atomic_compare_exchange") !=
              std::string::npos &&
            identifier_text.size() >= weak_parameter.size() &&
            identifier_text.compare(
              identifier_text.size() - weak_parameter.size(),
              weak_parameter.size(),
              weak_parameter) == 0)
          {
            mp_integer weak;
            if(
              rhs.id() != ID_constant ||
              to_integer(to_constant_expr(rhs), weak) ||
              weak != 0)
            {
              reason = "inline_weak_compare_exchange";
              return false;
            }
          }
          state.values[identifier] = rhs;
          if(rhs.id() == ID_address_of)
          {
            const exprt &object =
              skip_typecast(to_address_of_expr(rhs).object());
            if(object.id() == ID_symbol)
            {
              const irep_idt target =
                to_symbol_expr(object).get_identifier();
              const symbolt *target_symbol = nullptr;
              if(
                !ns.lookup(target, target_symbol) &&
                !target_symbol->is_static_lifetime)
                state.local_pointer_targets.emplace(
                  identifier, target);
            }
          }
          else if(rhs.id() == ID_symbol)
          {
            const auto target = state.local_pointer_targets.find(
              to_symbol_expr(rhs).get_identifier());
            if(target != state.local_pointer_targets.end())
              state.local_pointer_targets.emplace(
                identifier, target->second);
          }
        }
        else if(lhs.id() == ID_dereference)
        {
          const exprt &pointer = skip_typecast(
            to_dereference_expr(lhs).pointer());
          if(pointer.id() != ID_symbol)
          {
            reason = "inline_shared_write";
            return false;
          }
          const auto target = state.local_pointer_targets.find(
            to_symbol_expr(pointer).get_identifier());
          if(target == state.local_pointer_targets.end())
            state.shared_write = true;
          else
          {
            forget_local_value(state, target->second);
            state.live_locals.insert(target->second);
            state.values[target->second] =
              evaluated(instruction->assign_rhs(), state.values);
          }
        }
        else
          state.shared_write = true;
      }
      else if(instruction->is_dead())
      {
        const irep_idt identifier =
          instruction->dead_symbol().get_identifier();
        state.live_locals.erase(identifier);
        state.local_pointer_targets.erase(identifier);
        state.values.erase(identifier);
      }
      else if(instruction->is_function_call())
      {
        irep_idt callee;
        if(!direct_call_identifier(*instruction, callee))
        {
          reason = "inline_indirect_call";
          return false;
        }
        const std::string identifier = id2string(callee);
        if(
          identifier.rfind("__atomic_load", 0) != 0 &&
          callee != "verification_spin_start" &&
          callee != "verification_spin_end")
        {
          reason = "inline_effect_call";
          return false;
        }
        if(instruction->call_lhs().id() == ID_symbol)
        {
          const irep_idt identifier =
            to_symbol_expr(instruction->call_lhs())
              .get_identifier();
          forget_local_value(state, identifier);
          state.live_locals.insert(identifier);
          state.values.erase(identifier);
        }
      }
      else if(
        instruction->is_assert() ||
        instruction->is_set_return_value() ||
        (!instruction->is_goto() &&
         !instruction->is_assume() &&
         !instruction->is_decl() &&
         !instruction->is_skip() &&
         !instruction->is_location() &&
         !instruction->is_atomic_begin() &&
         !instruction->is_atomic_end() &&
         !(instruction->is_other() &&
           instruction->code().get_statement() ==
             ID_expression)))
      {
        reason = "inline_effect";
        return false;
      }

      ++state.depth;
      if(instruction->is_assume())
      {
        const int value =
          condition_value(instruction->condition(), state);
        if(value == 0)
          continue;
        if(value < 0)
          state.path_conditions.push_back(
            evaluated(instruction->condition(), state.values));
      }
      if(instruction->is_goto())
      {
        if(instruction->targets.size() != 1)
        {
          reason = "inline_multi_target";
          return false;
        }
        const int value =
          condition_value(instruction->condition(), state);
        if(value != 0)
        {
          statet taken = state;
          if(value < 0)
            taken.path_conditions.push_back(
              evaluated(instruction->condition(), state.values));
          taken.instruction = instruction->get_target();
          worklist.push_back(std::move(taken));
        }
        if(value != 1)
        {
          statet fallthrough = state;
          if(value < 0)
          {
            exprt negated = not_exprt(
              evaluated(instruction->condition(), state.values));
            simplify(negated, ns);
            fallthrough.path_conditions.push_back(
              std::move(negated));
          }
          fallthrough.instruction = std::next(instruction);
          worklist.push_back(std::move(fallthrough));
        }
      }
      else
      {
        state.instruction = std::next(instruction);
        worklist.push_back(std::move(state));
      }
    }
    if(backedge_paths == 0 || exit_paths == 0)
    {
      reason = "inline_progress_shape";
      return false;
    }
    reason = "none";
    return true;
  };

  for(auto &function_entry : goto_model.goto_functions.function_map)
  {
    if(!function_entry.second.body_available())
      continue;
    auto &program = function_entry.second.body;
    model_instructions += program.instructions.size();
    std::map<const goto_programt::instructiont *, std::size_t> positions;
    std::size_t position = 0;
    for(const auto &instruction : program.instructions)
      positions.emplace(&instruction, position++);

    for(auto backedge = program.instructions.begin();
        backedge != program.instructions.end(); ++backedge)
    {
      if(
        !backedge->is_goto() ||
        !backedge->condition().is_true() ||
        backedge->targets.size() != 1 ||
        positions.at(&*backedge->get_target()) >= positions.at(&*backedge))
        continue;

      const auto head = backedge->get_target();
      std::size_t spin_start_calls = 0;
      std::size_t spin_end_calls = 0;
      std::size_t read_calls = 0;
      bool saw_exit = false;
      bool prior_reservation = false;
      bool accepted = true;
      std::string rejection = "none";
      for(auto instruction = program.instructions.begin();
          instruction != head; ++instruction)
      {
        irep_idt callee;
        std::set<irep_idt> visiting;
        if(
          instruction->is_function_call() &&
          direct_call_identifier(*instruction, callee) &&
          reaches_atomic_reservation(callee, visiting))
        {
          prior_reservation = true;
          break;
        }
      }
      if(!prior_reservation)
      {
        std::set<irep_idt> visiting;
        prior_reservation = all_call_paths_have_reservation(
          function_entry.first, visiting);
      }
      for(auto instruction = head;
          instruction != std::next(backedge); ++instruction)
      {
        if(instruction == backedge)
          continue;
        if(instruction->is_function_call())
        {
          irep_idt callee;
          if(!direct_call_identifier(*instruction, callee))
          {
            accepted = false;
            rejection = "indirect_call";
            break;
          }
          if(callee == "verification_spin_start")
          {
            ++spin_start_calls;
            continue;
          }
          if(callee == "verification_spin_end")
          {
            ++spin_end_calls;
            continue;
          }
          std::size_t atomic_load_calls = 0;
          std::set<irep_idt> visiting;
          const bool read_only =
            read_only_callee(callee, visiting, atomic_load_calls);
          if(
            !read_only ||
            atomic_load_calls != 1 ||
            instruction->call_lhs().id() != ID_symbol)
          {
            accepted = false;
            rejection = "non_read_call";
            break;
          }
          ++read_calls;
        }
        else if(instruction->is_assign())
        {
          if(instruction->assign_lhs().id() != ID_symbol)
          {
            accepted = false;
            rejection = "assignment_shape";
            break;
          }
          if(!local_value_expression(instruction->assign_rhs()))
          {
            accepted = false;
            rejection = "assignment_value";
            break;
          }
          find_symbols_sett lhs_symbols;
          find_symbols(instruction->assign_lhs(), lhs_symbols);
          if(lhs_symbols.size() != 1)
          {
            accepted = false;
            rejection = "assignment_lhs";
            break;
          }
          const auto symbol =
            goto_model.symbol_table.symbols.find(*lhs_symbols.begin());
          if(
            symbol == goto_model.symbol_table.symbols.end() ||
            symbol->second.is_static_lifetime)
          {
            accepted = false;
            rejection = "assignment_storage";
            break;
          }
        }
        else if(instruction->is_goto())
        {
          if(!local_value_expression(instruction->condition()))
          {
            accepted = false;
            rejection = "condition_value";
            break;
          }
          for(const auto &target : instruction->targets)
          {
            if(positions.at(&*target) > positions.at(&*backedge))
              saw_exit = true;
          }
        }
        else if(
          !instruction->is_decl() &&
          !instruction->is_dead() &&
          !instruction->is_skip() &&
          !instruction->is_location())
        {
          accepted = false;
          rejection = "instruction_effect";
          break;
        }
      }

      if(spin_start_calls != 0 || spin_end_calls != 0)
      {
        bool stuttering_retry = false;
        std::string stutter_reason = "not_checked";
        if(
          !accepted &&
          rejection == "non_read_call" &&
          spin_start_calls == 1)
        {
          stuttering_retry =
            inlined_failure_iteration_is_stuttering(
              function_entry.first,
              backedge->source_location(),
              stutter_reason);
        }
        const bool pure_read_admitted =
          accepted &&
          spin_start_calls == 1 &&
          spin_end_calls != 0 &&
          read_calls == 1 &&
          prior_reservation &&
          saw_exit;
        const bool admitted =
          pure_read_admitted || stuttering_retry;
        ++marked_candidates;
        std::cout
          << "NATIVE_PURE_SPIN_CANDIDATE function="
          << function_entry.first
          << " accepted=" << (admitted ? 1 : 0)
          << " reason=" << rejection
          << " starts=" << spin_start_calls
          << " ends=" << spin_end_calls
          << " reads=" << read_calls
          << " reservation=" << (prior_reservation ? 1 : 0)
          << " exit=" << (saw_exit ? 1 : 0)
          << " stuttering_retry="
          << (stuttering_retry ? 1 : 0)
          << " stutter_reason=" << stutter_reason << '\n';
        if(admitted)
          accepted_candidates.push_back(
            {function_entry.first, backedge});
      }
    }
  }

  if(
    marked_candidates == 0 ||
    accepted_candidates.size() != marked_candidates)
  {
    std::cout
      << "NATIVE_PURE_SPIN_COLLAPSE applied=0"
      << " marked=" << marked_candidates
      << " accepted=" << accepted_candidates.size()
      << " empty_barrier=" << (empty_barrier_family ? 1 : 0)
      << " instructions=" << model_instructions
      << " reason=global_single_spin\n";
    return false;
  }

  constexpr std::size_t proof_instruction_budget = 750;
  within_proof_budget = model_instructions <= proof_instruction_budget;
  for(auto &candidate : accepted_candidates)
  {
    candidate.backedge->condition_nonconst() = false_exprt();
    candidate.backedge->turn_into_assume();
  }
  goto_model.goto_functions.update();
  std::cout
    << "NATIVE_PURE_SPIN_COLLAPSE applied=1 loops="
    << accepted_candidates.size()
    << " functions=" << accepted_candidates.size()
    << " empty_barrier=" << (empty_barrier_family ? 1 : 0)
    << " instructions=" << model_instructions
    << " proof_budget=" << (within_proof_budget ? 1 : 0)
    << " function=" << accepted_candidates.front().function << '\n';
  (void)message_handler;
  return true;
}
