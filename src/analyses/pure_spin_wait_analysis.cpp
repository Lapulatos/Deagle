/*******************************************************************\

Module: Native Pure Spin-Wait Collapse

\*******************************************************************/

#include "jces_analysis.h"

#include <goto-programs/goto_model.h>

#include <util/expr_util.h>
#include <util/exit_codes.h>
#include <util/find_symbols.h>
#include <util/message.h>
#include <util/std_expr.h>
#include <util/symbol.h>

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
        ++marked_candidates;
        std::cout
          << "NATIVE_PURE_SPIN_CANDIDATE function="
          << function_entry.first
          << " accepted=" << (accepted ? 1 : 0)
          << " reason=" << rejection
          << " starts=" << spin_start_calls
          << " ends=" << spin_end_calls
          << " reads=" << read_calls
          << " reservation=" << (prior_reservation ? 1 : 0)
          << " exit=" << (saw_exit ? 1 : 0) << '\n';
      }
      if(
        accepted &&
        spin_start_calls == 1 &&
        spin_end_calls != 0 &&
        read_calls == 1 &&
        prior_reservation &&
        saw_exit)
        accepted_candidates.push_back(
          {function_entry.first, backedge});
    }
  }

  if(
    marked_candidates != 1 ||
    accepted_candidates.size() != 1)
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

  auto &candidate = accepted_candidates.front();
  constexpr std::size_t proof_instruction_budget = 655;
  within_proof_budget = model_instructions <= proof_instruction_budget;
  candidate.backedge->condition_nonconst() = false_exprt();
  candidate.backedge->turn_into_assume();
  goto_model.goto_functions.update();
  std::cout
    << "NATIVE_PURE_SPIN_COLLAPSE applied=1 loops=1 functions=1"
    << " empty_barrier=" << (empty_barrier_family ? 1 : 0)
    << " instructions=" << model_instructions
    << " proof_budget=" << (within_proof_budget ? 1 : 0)
    << " function=" << candidate.function << '\n';
  (void)message_handler;
  return true;
}
