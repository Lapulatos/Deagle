/*******************************************************************\

Module: Property-Directed Affine Relation Analysis

\*******************************************************************/

#include "property_directed_affine_analysis.h"

#include "natural_loops.h"

#include <goto-programs/goto_model.h>

#include <util/arith_tools.h>
#include <util/message.h>
#include <util/namespace.h>
#include <util/pointer_expr.h>
#include <util/rational.h>
#include <util/std_expr.h>
#include <util/symbol.h>

#include <iostream>
#include <functional>
#include <map>
#include <set>
#include <sstream>
#include <string>
#include <vector>

namespace
{
struct affine_formt
{
  std::map<irep_idt, mp_integer> coefficients;
  mp_integer constant = 0;

  void add(const affine_formt &other, const mp_integer &factor = 1)
  {
    constant += factor * other.constant;
    for(const auto &term : other.coefficients)
    {
      coefficients[term.first] += factor * term.second;
      if(coefficients[term.first] == 0)
        coefficients.erase(term.first);
    }
  }
};

const exprt &strip_casts(const exprt &src)
{
  const exprt *result = &src;
  while(result->id() == ID_typecast && result->operands().size() == 1)
    result = &result->op0();
  return *result;
}

bool symbol_identifier(const exprt &src, irep_idt &identifier)
{
  const exprt &expr = strip_casts(src);
  if(expr.id() != ID_symbol)
    return false;
  identifier = to_symbol_expr(expr).get_identifier();
  return true;
}

bool direct_call(
  const goto_programt::instructiont &instruction,
  irep_idt &identifier)
{
  return
    instruction.is_function_call() &&
    symbol_identifier(instruction.call_function(), identifier);
}

bool named_suffix(const irep_idt &identifier, const std::string &suffix)
{
  const std::string name = id2string(identifier);
  return
    name == suffix ||
    (name.size() > suffix.size() &&
     name.compare(name.size() - suffix.size(), suffix.size(), suffix) == 0);
}

bool integer_constant(const exprt &src, mp_integer &value)
{
  const exprt &expr = strip_casts(src);
  if(expr.id() == ID_constant && !to_integer(to_constant_expr(expr), value))
    return true;
  if(expr.id() == ID_unary_minus && expr.operands().size() == 1)
  {
    if(integer_constant(expr.op0(), value))
    {
      value = -value;
      return true;
    }
  }
  return false;
}

bool affine_expression(const exprt &src, affine_formt &result)
{
  const exprt &expr = strip_casts(src);
  irep_idt identifier;
  if(symbol_identifier(expr, identifier))
  {
    result.coefficients[identifier] = 1;
    return true;
  }

  mp_integer value;
  if(integer_constant(expr, value))
  {
    result.constant = value;
    return true;
  }

  if(
    (expr.id() == ID_plus || expr.id() == ID_minus) &&
    !expr.operands().empty())
  {
    affine_formt first;
    if(!affine_expression(expr.op0(), first))
      return false;
    result.add(first);
    for(std::size_t index = 1; index < expr.operands().size(); ++index)
    {
      affine_formt operand;
      if(!affine_expression(expr.operands()[index], operand))
        return false;
      result.add(operand, expr.id() == ID_minus ? -1 : 1);
    }
    return true;
  }

  if(expr.id() == ID_unary_minus && expr.operands().size() == 1)
  {
    affine_formt operand;
    if(!affine_expression(expr.op0(), operand))
      return false;
    result.add(operand, -1);
    return true;
  }

  if(expr.id() == ID_mult && expr.operands().size() == 2)
  {
    mp_integer factor;
    affine_formt operand;
    if(
      integer_constant(expr.op0(), factor) &&
      affine_expression(expr.op1(), operand))
    {
      result.add(operand, factor);
      return true;
    }
    if(
      integer_constant(expr.op1(), factor) &&
      affine_expression(expr.op0(), operand))
    {
      result.add(operand, factor);
      return true;
    }
  }

  return false;
}

bool bad_linear_disequality(
  const exprt &src,
  affine_formt &difference)
{
  const exprt &expr = strip_casts(src);
  if(expr.id() != ID_notequal || expr.operands().size() != 2)
    return false;
  affine_formt lhs;
  affine_formt rhs;
  if(
    !affine_expression(expr.op0(), lhs) ||
    !affine_expression(expr.op1(), rhs))
    return false;
  difference.add(lhs);
  difference.add(rhs, -1);
  return !difference.coefficients.empty();
}

bool shared_integer(
  const irep_idt &identifier,
  const namespacet &ns)
{
  const symbolt *symbol = nullptr;
  if(ns.lookup(identifier, symbol) || symbol == nullptr)
    return false;
  const irep_idt type = strip_casts(symbol_exprt(identifier, symbol->type))
                          .type()
                          .id();
  return
    symbol->is_static_lifetime && !symbol->is_type &&
    (type == ID_signedbv || type == ID_unsignedbv);
}

struct audit_statst
{
  std::set<irep_idt> workers;
  std::size_t creates = 0;
  std::size_t joins = 0;
  std::size_t loops = 0;
  std::size_t affine_assignments = 0;
  std::size_t nonlinear_assignments = 0;
  std::size_t indirect_assignments = 0;
  std::size_t unknown_calls = 0;
};

using deltavectort = std::map<irep_idt, mp_integer>;

bool translation_delta(
  const goto_programt::instructiont &instruction,
  const namespacet &ns,
  irep_idt &lhs,
  mp_integer &delta)
{
  if(
    !instruction.is_assign() ||
    !symbol_identifier(instruction.assign_lhs(), lhs) ||
    !shared_integer(lhs, ns))
    return false;
  affine_formt rhs;
  if(!affine_expression(instruction.assign_rhs(), rhs))
    return false;
  const auto self = rhs.coefficients.find(lhs);
  if(
    self == rhs.coefficients.end() || self->second != 1 ||
    rhs.coefficients.size() != 1)
    return false;
  delta = rhs.constant;
  return true;
}

bool permitted_loop_call(const goto_programt::instructiont &instruction)
{
  irep_idt callee;
  return
    direct_call(instruction, callee) &&
    (named_suffix(callee, "assume_abort_if_not") ||
     named_suffix(callee, "__VERIFIER_assume") ||
     named_suffix(callee, "__VERIFIER_atomic_begin") ||
     named_suffix(callee, "__VERIFIER_atomic_end"));
}

struct transition_systemt
{
  std::set<irep_idt> variables;
  std::vector<deltavectort> paths;
  std::size_t rejected_paths = 0;
  std::size_t explored_paths = 0;
};

bool enumerate_loop_paths(
  const goto_programt &program,
  const natural_loopst::natural_loopt &loop,
  goto_programt::const_targett head,
  const namespacet &ns,
  transition_systemt &system)
{
  const std::size_t path_limit = 256;
  const std::size_t depth_limit = loop.size() + 2;
  bool supported = true;

  std::function<void(
    goto_programt::const_targett,
    const deltavectort &,
    const std::set<goto_programt::const_targett> &,
    std::size_t)> visit;

  visit = [&](goto_programt::const_targett current,
              const deltavectort &incoming,
              const std::set<goto_programt::const_targett> &visited,
              std::size_t depth) {
    if(
      !supported || system.explored_paths >= path_limit ||
      depth > depth_limit)
    {
      supported = false;
      return;
    }
    if(current == head && depth != 0)
    {
      system.paths.push_back(incoming);
      ++system.explored_paths;
      return;
    }
    if(!loop.contains(current))
    {
      system.paths.push_back(incoming);
      ++system.explored_paths;
      return;
    }
    if(visited.find(current) != visited.end())
    {
      supported = false;
      return;
    }

    deltavectort delta = incoming;
    if(current->is_assign())
    {
      irep_idt lhs;
      if(symbol_identifier(current->assign_lhs(), lhs) &&
         shared_integer(lhs, ns))
      {
        mp_integer amount;
        if(!translation_delta(*current, ns, lhs, amount))
        {
          ++system.rejected_paths;
          supported = false;
          return;
        }
        delta[lhs] += amount;
        system.variables.insert(lhs);
      }
      else if(!symbol_identifier(current->assign_lhs(), lhs))
      {
        ++system.rejected_paths;
        supported = false;
        return;
      }
    }
    else if(current->is_function_call() && !permitted_loop_call(*current))
    {
      ++system.rejected_paths;
      supported = false;
      return;
    }

    std::set<goto_programt::const_targett> next_visited = visited;
    next_visited.insert(current);
    const auto successors = program.get_successors(current);
    if(successors.empty())
    {
      system.paths.push_back(delta);
      ++system.explored_paths;
      return;
    }
    for(const auto &successor : successors)
      visit(successor, delta, next_visited, depth + 1);
  };

  visit(head, deltavectort{}, {}, 0);
  return supported && system.explored_paths > 0;
}

bool extract_transition_system(
  const goto_modelt &model,
  const namespacet &ns,
  const std::set<irep_idt> &workers,
  transition_systemt &system)
{
  for(const auto &worker : workers)
  {
    const auto found = model.goto_functions.function_map.find(worker);
    if(
      found == model.goto_functions.function_map.end() ||
      !found->second.body_available())
      return false;
    const goto_programt &program = found->second.body;
    natural_loopst loops;
    loops(program);
    if(loops.loop_map.empty())
      return false;

    std::set<goto_programt::const_targett> loop_instructions;
    for(const auto &entry : loops.loop_map)
      loop_instructions.insert(entry.second.begin(), entry.second.end());

    for(auto instruction = program.instructions.begin();
        instruction != program.instructions.end(); ++instruction)
    {
      if(!instruction->is_assign())
        continue;
      irep_idt lhs;
      if(
        symbol_identifier(instruction->assign_lhs(), lhs) &&
        shared_integer(lhs, ns))
      {
        system.variables.insert(lhs);
        if(loop_instructions.find(instruction) == loop_instructions.end())
          return false;
      }
      else if(!symbol_identifier(instruction->assign_lhs(), lhs))
        return false;
    }

    for(const auto &entry : loops.loop_map)
    {
      for(const auto &instruction : entry.second)
      {
        if(
          instruction != entry.first &&
          loops.loop_map.find(instruction) != loops.loop_map.end())
          return false;
      }
      if(!enumerate_loop_paths(
           program, entry.second, entry.first, ns, system))
        return false;
    }
  }
  return !system.variables.empty() && !system.paths.empty();
}

bool solve_property_conservation(
  const affine_formt &property,
  const transition_systemt &system,
  std::map<irep_idt, rationalt> &solution)
{
  std::set<irep_idt> variable_set = system.variables;
  for(const auto &term : property.coefficients)
    variable_set.insert(term.first);
  std::vector<irep_idt> variables(variable_set.begin(), variable_set.end());
  std::map<irep_idt, std::size_t> index;
  for(std::size_t i = 0; i < variables.size(); ++i)
    index[variables[i]] = i;

  std::vector<std::vector<rationalt>> matrix;
  for(const auto &path : system.paths)
  {
    std::vector<rationalt> row(variables.size() + 1);
    bool nonzero = false;
    for(const auto &delta : path)
    {
      row[index.at(delta.first)] = rationalt(delta.second);
      nonzero = nonzero || delta.second != 0;
    }
    if(nonzero)
      matrix.push_back(row);
  }
  for(const auto &fixed : property.coefficients)
  {
    std::vector<rationalt> row(variables.size() + 1);
    row[index.at(fixed.first)] = rationalt(1);
    row.back() = rationalt(fixed.second);
    matrix.push_back(row);
  }
  if(matrix.empty())
    return false;

  std::vector<int> pivot_column;
  std::size_t pivot_row = 0;
  for(std::size_t column = 0;
      column < variables.size() && pivot_row < matrix.size();
      ++column)
  {
    std::size_t selected = pivot_row;
    while(selected < matrix.size() && matrix[selected][column].is_zero())
      ++selected;
    if(selected == matrix.size())
      continue;
    std::swap(matrix[pivot_row], matrix[selected]);
    const rationalt pivot = matrix[pivot_row][column];
    for(std::size_t j = column; j <= variables.size(); ++j)
      matrix[pivot_row][j] /= pivot;
    for(std::size_t row = 0; row < matrix.size(); ++row)
    {
      if(row == pivot_row || matrix[row][column].is_zero())
        continue;
      const rationalt factor = matrix[row][column];
      for(std::size_t j = column; j <= variables.size(); ++j)
        matrix[row][j] -= factor * matrix[pivot_row][j];
    }
    pivot_column.push_back(static_cast<int>(column));
    ++pivot_row;
  }

  for(const auto &row : matrix)
  {
    bool all_zero = true;
    for(std::size_t column = 0; column < variables.size(); ++column)
      all_zero = all_zero && row[column].is_zero();
    if(all_zero && !row.back().is_zero())
      return false;
  }

  std::vector<rationalt> values(variables.size());
  for(std::size_t row = 0; row < pivot_column.size(); ++row)
    values[static_cast<std::size_t>(pivot_column[row])] = matrix[row].back();
  for(std::size_t i = 0; i < variables.size(); ++i)
  {
    if(!values[i].is_zero())
      solution[variables[i]] = values[i];
  }
  return !solution.empty();
}

std::string coefficient_string(
  const std::map<irep_idt, rationalt> &coefficients)
{
  std::ostringstream out;
  bool first = true;
  for(const auto &term : coefficients)
  {
    if(!first)
      out << ';';
    first = false;
    out << term.first << ':' << term.second;
  }
  return out.str();
}

std::string affine_fact_string(const affine_formt &fact)
{
  std::ostringstream out;
  bool first = true;
  for(const auto &term : fact.coefficients)
  {
    if(!first)
      out << '+';
    first = false;
    out << term.second << '*' << term.first;
  }
  if(fact.constant != 0 || first)
  {
    if(!first)
      out << '+';
    out << fact.constant;
  }
  return out.str();
}

std::string affine_facts_string(
  const std::vector<affine_formt> &facts)
{
  std::ostringstream out;
  bool first = true;
  for(const auto &fact : facts)
  {
    if(!first)
      out << ';';
    first = false;
    out << affine_fact_string(fact);
  }
  return out.str();
}

bool lifecycle(
  const goto_modelt &model,
  audit_statst &stats,
  const goto_programt::instructiont *&first_create,
  const goto_programt::instructiont *&last_join)
{
  const auto main = model.goto_functions.function_map.find(ID_main);
  if(
    main == model.goto_functions.function_map.end() ||
    !main->second.body_available())
    return false;

  std::set<irep_idt> handles;
  std::set<irep_idt> joined_handles;
  bool joining = false;
  for(const auto &instruction : main->second.body.instructions)
  {
    irep_idt callee;
    if(!direct_call(instruction, callee))
      continue;
    if(named_suffix(callee, "pthread_create"))
    {
      if(joining || instruction.call_arguments().size() < 3)
        return false;
      const exprt &handle = strip_casts(instruction.call_arguments()[0]);
      const exprt &worker = strip_casts(instruction.call_arguments()[2]);
      irep_idt handle_id;
      irep_idt worker_id;
      if(
        handle.id() != ID_address_of ||
        worker.id() != ID_address_of ||
        !symbol_identifier(to_address_of_expr(handle).object(), handle_id) ||
        !symbol_identifier(to_address_of_expr(worker).object(), worker_id))
        return false;
      handles.insert(handle_id);
      stats.workers.insert(worker_id);
      if(first_create == nullptr)
        first_create = &instruction;
      ++stats.creates;
    }
    else if(named_suffix(callee, "pthread_join"))
    {
      if(instruction.call_arguments().empty())
        return false;
      irep_idt handle_id;
      if(
        !symbol_identifier(
          strip_casts(instruction.call_arguments()[0]), handle_id) ||
        handles.find(handle_id) == handles.end() ||
        !joined_handles.insert(handle_id).second)
        return false;
      joining = true;
      last_join = &instruction;
      ++stats.joins;
    }
  }
  return
    stats.creates > 0 && stats.creates == handles.size() &&
    stats.creates == stats.workers.size() &&
    stats.joins == handles.size() && joined_handles == handles &&
    last_join != nullptr;
}

void flatten_conjunction(
  const exprt &src,
  std::vector<exprt> &terms)
{
  const exprt &expr = strip_casts(src);
  if(expr.id() == ID_and)
  {
    for(const auto &operand : expr.operands())
      flatten_conjunction(operand, terms);
  }
  else
    terms.push_back(expr);
}

bool equality_form(const exprt &src, affine_formt &result)
{
  const exprt &expr = strip_casts(src);
  if(expr.id() != ID_equal || expr.operands().size() != 2)
    return false;
  affine_formt lhs;
  affine_formt rhs;
  if(
    !affine_expression(expr.op0(), lhs) ||
    !affine_expression(expr.op1(), rhs))
    return false;
  result.add(lhs);
  result.add(rhs, -1);
  return true;
}

std::size_t rational_rank(
  std::vector<std::vector<rationalt>> matrix)
{
  if(matrix.empty())
    return 0;
  const std::size_t columns = matrix.front().size();
  std::size_t pivot_row = 0;
  for(std::size_t column = 0;
      column < columns && pivot_row < matrix.size();
      ++column)
  {
    std::size_t selected = pivot_row;
    while(selected < matrix.size() && matrix[selected][column].is_zero())
      ++selected;
    if(selected == matrix.size())
      continue;
    std::swap(matrix[pivot_row], matrix[selected]);
    const rationalt pivot = matrix[pivot_row][column];
    for(std::size_t j = column; j < columns; ++j)
      matrix[pivot_row][j] /= pivot;
    for(std::size_t row = pivot_row + 1; row < matrix.size(); ++row)
    {
      if(matrix[row][column].is_zero())
        continue;
      const rationalt factor = matrix[row][column];
      for(std::size_t j = column; j < columns; ++j)
        matrix[row][j] -= factor * matrix[pivot_row][j];
    }
    ++pivot_row;
  }
  return pivot_row;
}

bool implied_by_equalities(
  const std::vector<affine_formt> &facts,
  const std::map<irep_idt, rationalt> &coefficients,
  const mp_integer &constant)
{
  std::set<irep_idt> variable_set;
  for(const auto &fact : facts)
    for(const auto &term : fact.coefficients)
      variable_set.insert(term.first);
  for(const auto &term : coefficients)
    variable_set.insert(term.first);
  std::vector<irep_idt> variables(variable_set.begin(), variable_set.end());
  std::map<irep_idt, std::size_t> index;
  for(std::size_t i = 0; i < variables.size(); ++i)
    index[variables[i]] = i;

  std::vector<std::vector<rationalt>> rows;
  for(const auto &fact : facts)
  {
    std::vector<rationalt> row(variables.size() + 1);
    for(const auto &term : fact.coefficients)
      row[index.at(term.first)] = rationalt(term.second);
    row.back() = rationalt(fact.constant);
    rows.push_back(row);
  }
  const std::size_t before = rational_rank(rows);
  std::vector<rationalt> target(variables.size() + 1);
  for(const auto &term : coefficients)
    target[index.at(term.first)] = term.second;
  target.back() = rationalt(constant);
  rows.push_back(target);
  return rational_rank(rows) == before;
}

bool initial_relation_established(
  const goto_modelt &model,
  const namespacet &ns,
  const goto_programt::instructiont *first_create,
  const std::map<irep_idt, rationalt> &coefficients,
  const mp_integer &constant,
  std::vector<affine_formt> *facts_output)
{
  const auto main = model.goto_functions.function_map.find(ID_main);
  if(
    main == model.goto_functions.function_map.end() ||
    first_create == nullptr)
    return false;

  std::vector<const goto_programt::instructiont *> prefix;
  std::map<irep_idt, std::size_t> last_assignment;
  for(const auto &instruction : main->second.body.instructions)
  {
    if(&instruction == first_create)
      break;
    prefix.push_back(&instruction);
    if(instruction.is_assign())
    {
      irep_idt lhs;
      if(symbol_identifier(instruction.assign_lhs(), lhs))
        last_assignment[lhs] = prefix.size() - 1;
    }
  }

  std::vector<affine_formt> facts;
  for(const auto &term : coefficients)
  {
    if(last_assignment.find(term.first) != last_assignment.end())
      continue;
    const symbolt *symbol = nullptr;
    if(
      !ns.lookup(term.first, symbol) && symbol != nullptr &&
      symbol->is_static_lifetime &&
      (symbol->type.id() == ID_signedbv ||
       symbol->type.id() == ID_unsignedbv))
    {
      affine_formt zero;
      zero.coefficients[term.first] = 1;
      facts.push_back(zero);
    }
  }

  for(std::size_t position = 0; position < prefix.size(); ++position)
  {
    const auto &instruction = *prefix[position];
    if(instruction.is_assign())
    {
      irep_idt lhs;
      if(
        !symbol_identifier(instruction.assign_lhs(), lhs) ||
        last_assignment[lhs] != position)
        continue;
      affine_formt rhs;
      if(!affine_expression(instruction.assign_rhs(), rhs))
        continue;
      bool stable_rhs = true;
      for(const auto &rhs_term : rhs.coefficients)
      {
        const auto assigned = last_assignment.find(rhs_term.first);
        if(
          assigned != last_assignment.end() &&
          assigned->second > position)
          stable_rhs = false;
      }
      if(!stable_rhs)
        continue;
      affine_formt fact;
      fact.coefficients[lhs] = 1;
      fact.add(rhs, -1);
      facts.push_back(fact);
    }
    else if(instruction.is_function_call())
    {
      irep_idt callee;
      if(
        direct_call(instruction, callee) &&
        (named_suffix(callee, "assume_abort_if_not") ||
         named_suffix(callee, "__VERIFIER_assume")) &&
        instruction.call_arguments().size() == 1)
      {
        std::vector<exprt> terms;
        flatten_conjunction(instruction.call_arguments()[0], terms);
        for(const auto &term : terms)
        {
          affine_formt fact;
          if(equality_form(term, fact))
            facts.push_back(fact);
        }
      }
    }
  }
  if(facts_output != nullptr)
    *facts_output = facts;
  return implied_by_equalities(facts, coefficients, constant);
}

bool rational_coefficients_to_affine(
  const std::map<irep_idt, rationalt> &coefficients,
  const mp_integer &constant,
  affine_formt &result)
{
  result.constant = constant;
  for(const auto &term : coefficients)
  {
    const mp_integer denominator = term.second.get_denominator();
    if(denominator != 1 && denominator != -1)
      return false;
    result.coefficients[term.first] =
      denominator == 1
        ? term.second.get_numerator()
        : -term.second.get_numerator();
  }
  return true;
}

bool same_affine_form(
  const affine_formt &left,
  const affine_formt &right)
{
  if(
    left.coefficients == right.coefficients &&
    left.constant == right.constant)
    return true;
  if(left.constant != -right.constant ||
     left.coefficients.size() != right.coefficients.size())
    return false;
  for(const auto &term : left.coefficients)
  {
    const auto found = right.coefficients.find(term.first);
    if(
      found == right.coefficients.end() ||
      term.second != -found->second)
      return false;
  }
  return true;
}

bool exact_initial_fact(
  const std::vector<affine_formt> &facts,
  const affine_formt &invariant)
{
  for(const auto &fact : facts)
    if(same_affine_form(fact, invariant))
      return true;
  return false;
}

bool every_path_preserves(
  const transition_systemt &system,
  const affine_formt &invariant)
{
  for(const auto &path : system.paths)
  {
    mp_integer change = 0;
    for(const auto &term : invariant.coefficients)
    {
      const auto found = path.find(term.first);
      if(found != path.end())
        change += term.second * found->second;
    }
    if(change != 0)
      return false;
  }
  return true;
}

bool common_bitvector_domain(
  const affine_formt &invariant,
  const namespacet &ns)
{
  irep_idt kind;
  std::size_t width = 0;
  for(const auto &term : invariant.coefficients)
  {
    const symbolt *symbol = nullptr;
    if(ns.lookup(term.first, symbol) || symbol == nullptr)
      return false;
    const typet &type = symbol->type;
    if(type.id() != ID_signedbv && type.id() != ID_unsignedbv)
      return false;
    const std::size_t current_width =
      type.id() == ID_signedbv
        ? to_signedbv_type(type).get_width()
        : to_unsignedbv_type(type).get_width();
    if(kind.empty())
    {
      kind = type.id();
      width = current_width;
    }
    else if(kind != type.id() || width != current_width)
      return false;
  }
  return !kind.empty();
}

bool permitted_main_certificate_call(const irep_idt &callee)
{
  return
    named_suffix(callee, "pthread_create") ||
    named_suffix(callee, "pthread_join") ||
    named_suffix(callee, "assume_abort_if_not") ||
    named_suffix(callee, "__VERIFIER_assume") ||
    named_suffix(callee, "reach_error");
}

bool certificate_boundary_call(const irep_idt &callee)
{
  return
    named_suffix(callee, "pthread_create") ||
    named_suffix(callee, "pthread_join") ||
    named_suffix(callee, "reach_error") ||
    named_suffix(callee, "__assert_fail") ||
    named_suffix(callee, "abort");
}

bool direct_certificate_coverage(
  const goto_modelt &model,
  const std::set<irep_idt> &workers,
  const goto_programt::instructiont *first_create,
  const affine_formt &invariant)
{
  if(first_create == nullptr)
    return false;
  std::set<irep_idt> relevant;
  for(const auto &term : invariant.coefficients)
    relevant.insert(term.first);

  std::set<irep_idt> reachable;
  std::vector<irep_idt> work;
  reachable.insert(ID_main);
  work.push_back(ID_main);
  for(const auto &worker : workers)
    if(reachable.insert(worker).second)
      work.push_back(worker);
  for(std::size_t index = 0; index < work.size(); ++index)
  {
    const auto found = model.goto_functions.function_map.find(work[index]);
    if(
      found == model.goto_functions.function_map.end() ||
      !found->second.body_available())
      continue;
    for(const auto &instruction : found->second.body.instructions)
    {
      irep_idt callee;
      if(
        direct_call(instruction, callee) &&
        !certificate_boundary_call(callee) &&
        model.goto_functions.function_map.find(callee) !=
          model.goto_functions.function_map.end() &&
        model.goto_functions.function_map.at(callee).body_available() &&
        reachable.insert(callee).second)
        work.push_back(callee);
    }
  }

  for(const auto &function : reachable)
  {
    const auto found = model.goto_functions.function_map.find(function);
    if(
      found == model.goto_functions.function_map.end() ||
      !found->second.body_available())
      continue;
    const bool main = function == ID_main;
    const bool worker = workers.find(function) != workers.end();
    bool after_create = false;
    for(const auto &instruction : found->second.body.instructions)
    {
      if(main && &instruction == first_create)
        after_create = true;
      if(main && after_create && instruction.is_goto())
        return false;
      if(instruction.is_assign())
      {
        irep_idt lhs;
        if(!symbol_identifier(instruction.assign_lhs(), lhs))
          return false;
        if(relevant.find(lhs) == relevant.end())
          continue;
        if(worker)
          continue;
        if(main && !after_create)
          continue;
        return false;
      }
      if(main && after_create && instruction.is_function_call())
      {
        irep_idt callee;
        if(
          !direct_call(instruction, callee) ||
          !permitted_main_certificate_call(callee))
          return false;
      }
    }
  }
  return true;
}

bool direct_conservation_certificate(
  const goto_modelt &model,
  const namespacet &ns,
  const audit_statst &stats,
  const goto_programt::instructiont *first_create,
  const affine_formt &property,
  const transition_systemt &transition_system,
  const std::map<irep_idt, rationalt> &coefficients,
  const std::vector<affine_formt> &initial_facts)
{
  affine_formt invariant;
  return
    rational_coefficients_to_affine(
      coefficients, property.constant, invariant) &&
    same_affine_form(invariant, property) &&
    exact_initial_fact(initial_facts, invariant) &&
    every_path_preserves(transition_system, invariant) &&
    common_bitvector_domain(invariant, ns) &&
    direct_certificate_coverage(
      model, stats.workers, first_create, invariant);
}

bool integer_combination(
  const std::vector<affine_formt> &facts,
  const affine_formt &target,
  std::vector<mp_integer> *multipliers_output)
{
  if(facts.empty())
    return false;
  std::set<irep_idt> variable_set;
  for(const auto &fact : facts)
    for(const auto &term : fact.coefficients)
      variable_set.insert(term.first);
  for(const auto &term : target.coefficients)
    variable_set.insert(term.first);
  std::vector<irep_idt> variables(variable_set.begin(), variable_set.end());

  std::vector<std::vector<rationalt>> matrix(
    variables.size() + 1,
    std::vector<rationalt>(facts.size() + 1));
  for(std::size_t row = 0; row < variables.size(); ++row)
  {
    for(std::size_t column = 0; column < facts.size(); ++column)
    {
      const auto found = facts[column].coefficients.find(variables[row]);
      if(found != facts[column].coefficients.end())
        matrix[row][column] = rationalt(found->second);
    }
    const auto target_term = target.coefficients.find(variables[row]);
    if(target_term != target.coefficients.end())
      matrix[row].back() = rationalt(target_term->second);
  }
  for(std::size_t column = 0; column < facts.size(); ++column)
    matrix.back()[column] = rationalt(facts[column].constant);
  matrix.back().back() = rationalt(target.constant);

  std::vector<std::size_t> pivot_columns;
  std::size_t pivot_row = 0;
  for(std::size_t column = 0;
      column < facts.size() && pivot_row < matrix.size();
      ++column)
  {
    std::size_t selected = pivot_row;
    while(selected < matrix.size() && matrix[selected][column].is_zero())
      ++selected;
    if(selected == matrix.size())
      continue;
    std::swap(matrix[pivot_row], matrix[selected]);
    const rationalt pivot = matrix[pivot_row][column];
    for(std::size_t j = column; j <= facts.size(); ++j)
      matrix[pivot_row][j] /= pivot;
    for(std::size_t row = 0; row < matrix.size(); ++row)
    {
      if(row == pivot_row || matrix[row][column].is_zero())
        continue;
      const rationalt factor = matrix[row][column];
      for(std::size_t j = column; j <= facts.size(); ++j)
        matrix[row][j] -= factor * matrix[pivot_row][j];
    }
    pivot_columns.push_back(column);
    ++pivot_row;
  }

  for(const auto &row : matrix)
  {
    bool zero = true;
    for(std::size_t column = 0; column < facts.size(); ++column)
      zero = zero && row[column].is_zero();
    if(zero && !row.back().is_zero())
      return false;
  }

  std::vector<mp_integer> multipliers(facts.size());
  for(std::size_t row = 0; row < pivot_columns.size(); ++row)
  {
    const mp_integer denominator =
      matrix[row].back().get_denominator();
    if(denominator != 1 && denominator != -1)
      return false;
    multipliers[pivot_columns[row]] =
      denominator == 1
        ? matrix[row].back().get_numerator()
        : -matrix[row].back().get_numerator();
  }

  affine_formt reconstructed;
  for(std::size_t index = 0; index < facts.size(); ++index)
    reconstructed.add(facts[index], multipliers[index]);
  if(
    reconstructed.coefficients != target.coefficients ||
    reconstructed.constant != target.constant)
    return false;
  if(multipliers_output != nullptr)
    *multipliers_output = multipliers;
  return true;
}

std::string integer_multipliers_string(
  const std::vector<mp_integer> &multipliers)
{
  std::ostringstream out;
  for(std::size_t index = 0; index < multipliers.size(); ++index)
  {
    if(index != 0)
      out << ':';
    out << multipliers[index];
  }
  return out.str();
}

bool canonical_lt_loop_guard(
  const exprt &src,
  irep_idt &induction,
  irep_idt &bound)
{
  const exprt &condition = strip_casts(src);
  if(condition.id() != ID_not || condition.operands().size() != 1)
    return false;
  const exprt &guard = strip_casts(condition.op0());
  if(guard.id() != ID_lt || guard.operands().size() != 2)
    return false;
  return
    symbol_identifier(guard.op0(), induction) &&
    symbol_identifier(guard.op1(), bound) &&
    induction != bound;
}

struct counted_loopt
{
  irep_idt worker;
  irep_idt induction;
  irep_idt bound;
};

struct lattice_audit_statst
{
  bool integer_invariant = false;
  bool integer_initial = false;
  bool preserved = false;
  bool common_domain = false;
  bool complete_coverage = false;
};

struct token_drain_audit_statst
{
  bool terminal_facts = false;
  bool unsigned_domain = false;
  bool closed_paths = false;
  bool guarded_updates = false;
  bool ordered_transfers = false;
  bool global_snapshot = false;
  bool property_discharged = false;
  std::set<irep_idt> resources;
  std::size_t token_paths = 0;
  std::size_t snapshot_workers = 0;
  std::size_t resource_updates = 0;
  std::size_t atomic_updates = 0;
  std::size_t negative_updates = 0;
  std::size_t guarded_negative_updates = 0;
  std::vector<mp_integer> property_multipliers;
};

bool unsigned_resource_domain(
  const std::set<irep_idt> &resources,
  const namespacet &ns)
{
  std::size_t width = 0;
  for(const auto &resource : resources)
  {
    const symbolt *symbol = nullptr;
    if(
      ns.lookup(resource, symbol) || symbol == nullptr ||
      !symbol->is_static_lifetime ||
      symbol->type.id() != ID_unsignedbv ||
      symbol->type.get_bool(ID_C_volatile))
      return false;
    const std::size_t current_width =
      to_unsignedbv_type(symbol->type).get_width();
    if(width == 0)
      width = current_width;
    else if(width != current_width)
      return false;
  }
  return !resources.empty() && width != 0;
}

bool token_closed_paths(
  const transition_systemt &system,
  const std::set<irep_idt> &resources,
  std::size_t &token_paths)
{
  for(const auto &path : system.paths)
  {
    std::size_t negative = 0;
    std::size_t positive = 0;
    for(const auto &resource : resources)
    {
      const auto found = path.find(resource);
      const mp_integer delta =
        found == path.end() ? mp_integer(0) : found->second;
      if(delta == -1)
        ++negative;
      else if(delta == 1)
        ++positive;
      else if(delta != 0)
        return false;
    }
    if(negative == 0 && positive == 0)
      continue;
    if(negative != 1 || positive > 1)
      return false;
    ++token_paths;
  }
  return token_paths > 0;
}

bool positive_resource_guard(
  const exprt &src,
  irep_idt &resource)
{
  const exprt &condition = strip_casts(src);
  if(condition.id() != ID_not || condition.operands().size() != 1)
    return false;
  const exprt &guard = strip_casts(condition.op0());
  if(guard.id() != ID_gt || guard.operands().size() != 2)
    return false;
  mp_integer zero;
  return
    symbol_identifier(guard.op0(), resource) &&
    integer_constant(guard.op1(), zero) && zero == 0;
}

bool instruction_inside_atomic(
  const goto_programt &program,
  goto_programt::const_targett target)
{
  std::size_t depth = 0;
  for(auto instruction = program.instructions.begin();
      instruction != program.instructions.end(); ++instruction)
  {
    if(instruction == target)
      return depth > 0;
    if(instruction->is_atomic_begin())
      ++depth;
    else if(instruction->is_atomic_end())
    {
      if(depth == 0)
        return false;
      --depth;
    }
  }
  return false;
}

bool exclusive_source_snapshot_guard(
  const goto_programt &program,
  const natural_loopst &loops,
  const natural_loopst::natural_loopt &loop,
  goto_programt::const_targett assignment,
  const irep_idt &resource,
  const std::set<irep_idt> &resources,
  const namespacet &ns);

bool guarded_resource_updates(
  const goto_modelt &model,
  const namespacet &ns,
  const std::set<irep_idt> &workers,
  const std::set<irep_idt> &resources,
  token_drain_audit_statst &drain_stats)
{
  std::map<irep_idt, std::size_t> negative_sites;
  for(const auto &worker : workers)
  {
    const auto found = model.goto_functions.function_map.find(worker);
    if(found == model.goto_functions.function_map.end())
      return false;
    for(const auto &instruction : found->second.body.instructions)
    {
      if(!instruction.is_assign())
        continue;
      irep_idt lhs;
      mp_integer delta;
      if(
        symbol_identifier(instruction.assign_lhs(), lhs) &&
        resources.find(lhs) != resources.end() &&
        translation_delta(instruction, ns, lhs, delta) &&
        delta == -1)
        ++negative_sites[lhs];
    }
  }

  for(const auto &worker : workers)
  {
    const auto found = model.goto_functions.function_map.find(worker);
    if(found == model.goto_functions.function_map.end())
      return false;
    const goto_programt &program = found->second.body;
    natural_loopst loops;
    loops(program);
    for(auto assignment = program.instructions.begin();
        assignment != program.instructions.end(); ++assignment)
    {
      if(!assignment->is_assign())
        continue;
      irep_idt lhs;
      if(
        !symbol_identifier(assignment->assign_lhs(), lhs) ||
        resources.find(lhs) == resources.end())
        continue;
      ++drain_stats.resource_updates;
      mp_integer delta;
      if(
        !translation_delta(*assignment, ns, lhs, delta) ||
        (delta != -1 && delta != 1))
        return false;
      if(!instruction_inside_atomic(program, assignment))
        return false;
      ++drain_stats.atomic_updates;
      if(delta == 1)
        continue;
      ++drain_stats.negative_updates;

      const natural_loopst::natural_loopt *containing = nullptr;
      for(const auto &entry : loops.loop_map)
      {
        if(entry.second.contains(assignment))
        {
          if(containing != nullptr)
            return false;
          containing = &entry.second;
        }
      }
      if(containing == nullptr)
        return false;

      bool guarded = false;
      for(const auto &candidate : *containing)
      {
        irep_idt guarded_resource;
        if(
          !candidate->is_goto() ||
          !positive_resource_guard(
            candidate->condition(), guarded_resource) ||
          guarded_resource != lhs ||
          candidate->get_target()->location_number <=
            assignment->location_number)
          continue;
        if(
          loops.get_dominator_info().dominates(
            candidate, assignment))
        {
          guarded = true;
          break;
        }
      }
      if(
        !guarded && negative_sites[lhs] == 1 &&
        exclusive_source_snapshot_guard(
          program,
          loops,
          *containing,
          assignment,
          lhs,
          resources,
          ns))
        guarded = true;
      if(!guarded)
        return false;
      ++drain_stats.guarded_negative_updates;
    }
  }
  return true;
}

bool collect_positive_resources(
  const exprt &src,
  std::set<irep_idt> &resources)
{
  const exprt &expr = strip_casts(src);
  if(expr.id() == ID_or && expr.operands().size() == 2)
    return
      collect_positive_resources(expr.op0(), resources) &&
      collect_positive_resources(expr.op1(), resources);
  if(expr.id() != ID_gt || expr.operands().size() != 2)
    return false;
  irep_idt resource;
  mp_integer zero;
  if(
    !symbol_identifier(expr.op0(), resource) ||
    !integer_constant(expr.op1(), zero) || zero != 0)
    return false;
  return resources.insert(resource).second;
}

bool same_atomic_region(
  const goto_programt &program,
  goto_programt::const_targett left,
  goto_programt::const_targett right)
{
  std::size_t depth = 0;
  std::size_t region = 0;
  std::size_t left_region = 0;
  std::size_t right_region = 0;
  for(auto instruction = program.instructions.begin();
      instruction != program.instructions.end(); ++instruction)
  {
    if(instruction->is_atomic_begin())
    {
      if(depth == 0)
        ++region;
      ++depth;
    }
    if(instruction == left && depth > 0)
      left_region = region;
    if(instruction == right && depth > 0)
      right_region = region;
    if(instruction->is_atomic_end())
    {
      if(depth == 0)
        return false;
      --depth;
    }
  }
  return left_region != 0 && left_region == right_region;
}

bool ordered_resource_transfers(
  const goto_modelt &model,
  const namespacet &ns,
  const std::set<irep_idt> &workers,
  const std::set<irep_idt> &resources)
{
  for(const auto &worker : workers)
  {
    const auto found = model.goto_functions.function_map.find(worker);
    if(found == model.goto_functions.function_map.end())
      return false;
    const goto_programt &program = found->second.body;
    natural_loopst loops;
    loops(program);
    for(const auto &entry : loops.loop_map)
    {
      std::map<irep_idt, std::size_t> assignments;
      std::vector<goto_programt::const_targett> increments;
      std::vector<goto_programt::const_targett> decrements;
      for(const auto &instruction : entry.second)
      {
        if(!instruction->is_assign())
          continue;
        irep_idt lhs;
        mp_integer delta;
        if(
          !symbol_identifier(instruction->assign_lhs(), lhs) ||
          resources.find(lhs) == resources.end() ||
          !translation_delta(*instruction, ns, lhs, delta))
          continue;
        if(++assignments[lhs] != 1)
          return false;
        if(delta == 1)
          increments.push_back(instruction);
        else if(delta == -1)
          decrements.push_back(instruction);
      }
      if(increments.empty())
        continue;
      if(increments.size() != 1 || decrements.size() != 1)
        return false;
      if(
        !same_atomic_region(
          program, increments.front(), decrements.front()) &&
        !loops.get_dominator_info().dominates(
          increments.front(), decrements.front()))
        return false;
    }
  }
  return true;
}

bool loop_boolean_guard(
  const exprt &src,
  irep_idt &condition_symbol)
{
  const exprt &condition = strip_casts(src);
  if(condition.id() != ID_not || condition.operands().size() != 1)
    return false;
  const exprt &truth = strip_casts(condition.op0());
  if(truth.id() != ID_notequal || truth.operands().size() != 2)
    return false;
  mp_integer zero;
  return
    symbol_identifier(truth.op0(), condition_symbol) &&
    integer_constant(truth.op1(), zero) && zero == 0;
}

bool clean_atomic_snapshot(
  const goto_programt &program,
  goto_programt::const_targett snapshot,
  const std::set<irep_idt> &resources)
{
  std::size_t depth = 0;
  std::size_t region = 0;
  std::size_t snapshot_region = 0;
  bool found = false;
  bool resource_write_in_region = false;
  for(auto instruction = program.instructions.begin();
      instruction != program.instructions.end(); ++instruction)
  {
    if(instruction->is_atomic_begin())
    {
      if(depth == 0)
      {
        ++region;
        resource_write_in_region = false;
      }
      ++depth;
    }
    if(
      depth > 0 && instruction != snapshot &&
      instruction->is_assign())
    {
      irep_idt lhs;
      if(
        symbol_identifier(instruction->assign_lhs(), lhs) &&
        resources.find(lhs) != resources.end())
        resource_write_in_region = true;
    }
    if(instruction == snapshot)
    {
      if(depth == 0 || resource_write_in_region)
        return false;
      snapshot_region = region;
      found = true;
    }
    if(instruction->is_atomic_end())
    {
      if(depth == 0)
        return false;
      --depth;
      if(found && region == snapshot_region && depth == 0)
        return !resource_write_in_region;
    }
  }
  return false;
}

bool exclusive_source_snapshot_guard(
  const goto_programt &program,
  const natural_loopst &loops,
  const natural_loopst::natural_loopt &loop,
  goto_programt::const_targett assignment,
  const irep_idt &resource,
  const std::set<irep_idt> &resources,
  const namespacet &ns)
{
  goto_programt::const_targett head = program.instructions.end();
  for(const auto &entry : loops.loop_map)
  {
    if(&entry.second == &loop)
    {
      head = entry.first;
      break;
    }
  }
  if(
    head == program.instructions.end() || !head->is_goto() ||
    !loops.get_dominator_info().dominates(head, assignment))
    return false;
  irep_idt condition_symbol;
  if(!loop_boolean_guard(head->condition(), condition_symbol))
    return false;

  std::set<irep_idt> singleton{resource};
  std::vector<goto_programt::const_targett> snapshots;
  for(auto instruction = program.instructions.begin();
      instruction != program.instructions.end(); ++instruction)
  {
    if(!instruction->is_assign())
      continue;
    irep_idt lhs;
    if(
      !symbol_identifier(instruction->assign_lhs(), lhs) ||
      lhs != condition_symbol)
      continue;
    std::set<irep_idt> observed;
    if(
      !collect_positive_resources(
        instruction->assign_rhs(), observed) ||
      observed != singleton ||
      !clean_atomic_snapshot(program, instruction, resources))
      return false;
    snapshots.push_back(instruction);
  }
  if(snapshots.size() != 2)
    return false;

  goto_programt::const_targett initial = program.instructions.end();
  goto_programt::const_targett refresh = program.instructions.end();
  for(const auto &snapshot : snapshots)
  {
    if(loop.contains(snapshot))
      refresh = snapshot;
    else if(snapshot->location_number < head->location_number)
      initial = snapshot;
  }
  if(
    initial == program.instructions.end() ||
    refresh == program.instructions.end())
    return false;
  if(
    !loops.get_dominator_info().dominates(
      initial, head))
    return false;
  if(
    !loops.get_dominator_info().dominates(
      assignment, refresh))
    return false;

  std::vector<goto_programt::const_targett> destination_increments;
  for(const auto &instruction : loop)
  {
    if(!instruction->is_assign())
      continue;
    irep_idt lhs;
    mp_integer delta;
    if(
      !symbol_identifier(instruction->assign_lhs(), lhs) ||
      resources.find(lhs) == resources.end() ||
      lhs == resource ||
      !translation_delta(*instruction, ns, lhs, delta))
      continue;
    if(delta == 1)
      destination_increments.push_back(instruction);
  }
  if(destination_increments.size() > 1)
    return false;
  if(
    destination_increments.size() == 1 &&
    !loops.get_dominator_info().dominates(
      destination_increments.front(), assignment))
    return false;

  for(const auto &instruction : loop)
  {
    if(
      instruction->is_backwards_goto() &&
      instruction->get_target() == head &&
      !loops.get_dominator_info().dominates(
        refresh, instruction))
      return false;
  }
  return true;
}

bool global_drain_snapshot(
  const goto_modelt &model,
  const std::set<irep_idt> &workers,
  const std::set<irep_idt> &resources,
  std::size_t &snapshot_workers)
{
  for(const auto &worker : workers)
  {
    const auto found = model.goto_functions.function_map.find(worker);
    if(found == model.goto_functions.function_map.end())
      return false;
    const goto_programt &program = found->second.body;
    natural_loopst loops;
    loops(program);
    bool worker_snapshot = false;
    for(const auto &entry : loops.loop_map)
    {
      irep_idt condition_symbol;
      if(
        !entry.first->is_goto() ||
        !loop_boolean_guard(
          entry.first->condition(), condition_symbol))
        continue;
      const auto exit = entry.first->get_target();
      if(entry.second.contains(exit))
        continue;

      bool closed_body = true;
      std::size_t exits = 0;
      std::size_t backedges = 0;
      for(const auto &instruction : entry.second)
      {
        for(const auto &successor : program.get_successors(instruction))
        {
          if(entry.second.contains(successor))
            continue;
          ++exits;
          if(instruction != entry.first || successor != exit)
            closed_body = false;
        }
        if(
          instruction->is_backwards_goto() &&
          instruction->get_target() == entry.first)
          ++backedges;
      }
      if(!closed_body || exits != 1 || backedges == 0)
        continue;

      std::vector<goto_programt::const_targett> assignments;
      for(auto instruction = program.instructions.begin();
          instruction != program.instructions.end(); ++instruction)
      {
        if(!instruction->is_assign())
          continue;
        irep_idt lhs;
        if(
          symbol_identifier(instruction->assign_lhs(), lhs) &&
          lhs == condition_symbol)
          assignments.push_back(instruction);
      }
      if(assignments.size() != 2)
        continue;

      goto_programt::const_targett initial = program.instructions.end();
      goto_programt::const_targett refresh = program.instructions.end();
      for(const auto &assignment : assignments)
      {
        std::set<irep_idt> observed;
        if(
          !collect_positive_resources(
            assignment->assign_rhs(), observed) ||
          observed != resources ||
          !clean_atomic_snapshot(
            program, assignment, resources))
        {
          initial = program.instructions.end();
          refresh = program.instructions.end();
          break;
        }
        if(entry.second.contains(assignment))
          refresh = assignment;
        else if(
          assignment->location_number <
          entry.first->location_number)
          initial = assignment;
      }
      if(
        initial == program.instructions.end() ||
        refresh == program.instructions.end())
        continue;
      if(
        !loops.get_dominator_info().dominates(
          initial, entry.first))
        continue;

      bool refreshes_all_backedges = true;
      for(const auto &instruction : entry.second)
      {
        if(
          instruction->is_backwards_goto() &&
          instruction->get_target() == entry.first &&
          !loops.get_dominator_info().dominates(
            refresh, instruction))
          refreshes_all_backedges = false;
      }
      if(!refreshes_all_backedges)
        continue;
      worker_snapshot = true;
      break;
    }
    if(worker_snapshot)
      ++snapshot_workers;
  }
  return snapshot_workers > 0;
}

bool token_drain_certificate(
  const goto_modelt &model,
  const namespacet &ns,
  const audit_statst &stats,
  const goto_programt::instructiont *first_create,
  const affine_formt &property,
  const transition_systemt &transition_system,
  const std::map<irep_idt, rationalt> &coefficients,
  const std::vector<affine_formt> &initial_facts,
  token_drain_audit_statst &drain_stats)
{
  affine_formt invariant;
  if(
    !rational_coefficients_to_affine(
      coefficients, property.constant, invariant) ||
    !integer_combination(initial_facts, invariant, nullptr) ||
    !every_path_preserves(transition_system, invariant))
    return false;

  for(const auto &term : invariant.coefficients)
  {
    if(
      property.coefficients.find(term.first) ==
        property.coefficients.end() &&
      transition_system.variables.find(term.first) !=
        transition_system.variables.end())
      drain_stats.resources.insert(term.first);
  }
  std::vector<affine_formt> join_facts{invariant};
  for(const auto &resource : drain_stats.resources)
  {
    affine_formt zero;
    zero.coefficients[resource] = 1;
    join_facts.push_back(zero);
  }
  drain_stats.terminal_facts =
    !drain_stats.resources.empty() &&
    integer_combination(
      join_facts,
      property,
      &drain_stats.property_multipliers);
  drain_stats.unsigned_domain =
    drain_stats.terminal_facts &&
    unsigned_resource_domain(drain_stats.resources, ns);
  drain_stats.closed_paths =
    drain_stats.unsigned_domain &&
    token_closed_paths(
      transition_system,
      drain_stats.resources,
      drain_stats.token_paths);
  drain_stats.guarded_updates =
    drain_stats.closed_paths &&
    guarded_resource_updates(
      model,
      ns,
      stats.workers,
      drain_stats.resources,
      drain_stats);
  drain_stats.ordered_transfers =
    drain_stats.guarded_updates &&
    ordered_resource_transfers(
      model, ns, stats.workers, drain_stats.resources);
  drain_stats.global_snapshot =
    drain_stats.ordered_transfers &&
    global_drain_snapshot(
      model,
      stats.workers,
      drain_stats.resources,
      drain_stats.snapshot_workers);

  drain_stats.property_discharged =
    drain_stats.global_snapshot &&
    common_bitvector_domain(invariant, ns) &&
    direct_certificate_coverage(
      model, stats.workers, first_create, invariant);
  return drain_stats.property_discharged;
}

std::string counted_loop_string(
  const std::vector<counted_loopt> &loops)
{
  std::ostringstream out;
  bool first = true;
  for(const auto &loop : loops)
  {
    if(!first)
      out << ';';
    first = false;
    out << loop.worker << ':' << loop.induction << ':' << loop.bound;
  }
  return out.str();
}

bool worker_assigns_symbol(
  const goto_modelt &model,
  const std::set<irep_idt> &workers,
  const irep_idt &symbol,
  const goto_programt::instructiont *except)
{
  for(const auto &worker : workers)
  {
    const auto found = model.goto_functions.function_map.find(worker);
    if(found == model.goto_functions.function_map.end())
      return true;
    for(const auto &instruction : found->second.body.instructions)
    {
      if(&instruction == except || !instruction.is_assign())
        continue;
      irep_idt lhs;
      if(
        symbol_identifier(instruction.assign_lhs(), lhs) &&
        lhs == symbol)
        return true;
    }
  }
  return false;
}

bool extract_counted_loops(
  const goto_modelt &model,
  const namespacet &ns,
  const std::set<irep_idt> &workers,
  std::vector<counted_loopt> &summaries)
{
  for(const auto &worker : workers)
  {
    const auto found = model.goto_functions.function_map.find(worker);
    if(found == model.goto_functions.function_map.end())
      return false;
    const goto_programt &program = found->second.body;
    natural_loopst loops;
    loops(program);
    for(const auto &entry : loops.loop_map)
    {
      irep_idt induction;
      irep_idt bound;
      if(
        !entry.first->is_goto() ||
        !canonical_lt_loop_guard(
          entry.first->condition(), induction, bound) ||
        !shared_integer(induction, ns) || !shared_integer(bound, ns))
        continue;
      const auto exit = entry.first->get_target();
      if(entry.second.contains(exit))
        continue;
      const auto head_successors = program.get_successors(entry.first);
      if(head_successors.size() != 2)
        continue;
      std::size_t inside_successors = 0;
      std::size_t outside_successors = 0;
      for(const auto &successor : head_successors)
      {
        if(entry.second.contains(successor))
          ++inside_successors;
        else if(successor == exit)
          ++outside_successors;
      }
      if(inside_successors != 1 || outside_successors != 1)
        continue;

      goto_programt::const_targett increment = program.instructions.end();
      std::size_t induction_assignments = 0;
      bool closed_body = true;
      for(const auto &instruction : entry.second)
      {
        for(const auto &successor : program.get_successors(instruction))
        {
          if(
            !entry.second.contains(successor) &&
            !(instruction == entry.first && successor == exit))
            closed_body = false;
        }
        if(!instruction->is_assign())
          continue;
        irep_idt lhs;
        if(
          symbol_identifier(instruction->assign_lhs(), lhs) &&
          lhs == induction)
        {
          ++induction_assignments;
          mp_integer delta;
          if(
            translation_delta(*instruction, ns, lhs, delta) &&
            delta == 1)
            increment = instruction;
        }
      }
      if(
        !closed_body || induction_assignments != 1 ||
        increment == program.instructions.end())
        continue;

      std::size_t backedges = 0;
      bool canonical_backedges = true;
      for(const auto &instruction : entry.second)
      {
        if(!instruction->is_backwards_goto())
          continue;
        if(instruction->get_target() != entry.first)
        {
          canonical_backedges = false;
          continue;
        }
        ++backedges;
        if(!loops.get_dominator_info().dominates(increment, instruction))
          canonical_backedges = false;
      }
      if(!canonical_backedges || backedges == 0)
        continue;
      if(
        worker_assigns_symbol(model, workers, induction, &*increment) ||
        worker_assigns_symbol(model, workers, bound, nullptr))
        continue;
      summaries.push_back({worker, induction, bound});
    }
  }
  return !summaries.empty();
}

bool property_discharged_by_counted_loops(
  const goto_modelt &model,
  const namespacet &ns,
  const audit_statst &stats,
  const goto_programt::instructiont *first_create,
  const affine_formt &property,
  const transition_systemt &transition_system,
  const std::map<irep_idt, rationalt> &coefficients,
  const std::vector<affine_formt> &initial_facts,
  const std::vector<counted_loopt> &counted_loops,
  std::size_t &equal_loop_pairs,
  std::vector<mp_integer> &property_multipliers,
  lattice_audit_statst &lattice_stats)
{
  affine_formt invariant;
  std::vector<mp_integer> base_multipliers;
  lattice_stats.integer_invariant =
    rational_coefficients_to_affine(
      coefficients, property.constant, invariant);
  lattice_stats.integer_initial =
    lattice_stats.integer_invariant &&
    integer_combination(initial_facts, invariant, &base_multipliers);
  lattice_stats.preserved =
    lattice_stats.integer_initial &&
    every_path_preserves(transition_system, invariant);
  if(!lattice_stats.preserved)
    return false;

  affine_formt relevant = invariant;
  for(const auto &loop : counted_loops)
  {
    relevant.coefficients[loop.induction] += 1;
    relevant.coefficients[loop.bound] += 1;
  }
  lattice_stats.common_domain = common_bitvector_domain(relevant, ns);
  lattice_stats.complete_coverage =
    lattice_stats.common_domain &&
    direct_certificate_coverage(
      model, stats.workers, first_create, relevant);
  if(!lattice_stats.complete_coverage)
    return false;

  std::vector<affine_formt> join_facts;
  join_facts.push_back(invariant);
  for(std::size_t left = 0; left < counted_loops.size(); ++left)
  {
    for(std::size_t right = left + 1;
        right < counted_loops.size();
        ++right)
    {
      if(counted_loops[left].worker == counted_loops[right].worker)
        continue;
      affine_formt equal_initial;
      equal_initial.coefficients[counted_loops[left].induction] = 1;
      equal_initial.coefficients[counted_loops[right].induction] = -1;
      affine_formt equal_bounds;
      equal_bounds.coefficients[counted_loops[left].bound] = 1;
      equal_bounds.coefficients[counted_loops[right].bound] = -1;
      if(
        !integer_combination(initial_facts, equal_initial, nullptr) ||
        !integer_combination(initial_facts, equal_bounds, nullptr))
        continue;
      ++equal_loop_pairs;
      join_facts.push_back(equal_initial);
    }
  }
  return
    equal_loop_pairs > 0 &&
    integer_combination(
      join_facts, property, &property_multipliers);
}

bool property_after_join(
  const goto_modelt &model,
  const goto_programt::instructiont *last_join,
  affine_formt &bad_difference)
{
  const auto main = model.goto_functions.function_map.find(ID_main);
  if(main == model.goto_functions.function_map.end())
    return false;

  bool after_join = false;
  const exprt *last_assumption = nullptr;
  std::size_t errors = 0;
  for(const auto &instruction : main->second.body.instructions)
  {
    if(&instruction == last_join)
      after_join = true;
    irep_idt callee;
    if(!direct_call(instruction, callee))
      continue;
    if(
      after_join &&
      (named_suffix(callee, "assume_abort_if_not") ||
       named_suffix(callee, "__VERIFIER_assume")) &&
      instruction.call_arguments().size() == 1)
      last_assumption = &instruction.call_arguments()[0];
    if(named_suffix(callee, "reach_error"))
    {
      ++errors;
      if(!after_join || last_assumption == nullptr)
        return false;
      if(!bad_linear_disequality(*last_assumption, bad_difference))
        return false;
    }
  }
  return errors == 1;
}

void inspect_workers(
  const goto_modelt &model,
  const namespacet &ns,
  audit_statst &stats)
{
  for(const auto &worker : stats.workers)
  {
    const auto found = model.goto_functions.function_map.find(worker);
    if(
      found == model.goto_functions.function_map.end() ||
      !found->second.body_available())
    {
      ++stats.unknown_calls;
      continue;
    }

    natural_loopst loops;
    loops(found->second.body);
    stats.loops += loops.loop_map.size();

    for(const auto &instruction : found->second.body.instructions)
    {
      if(instruction.is_assign())
      {
        irep_idt lhs;
        if(!symbol_identifier(instruction.assign_lhs(), lhs))
        {
          ++stats.indirect_assignments;
          continue;
        }
        if(!shared_integer(lhs, ns))
          continue;
        affine_formt rhs;
        if(affine_expression(instruction.assign_rhs(), rhs))
          ++stats.affine_assignments;
        else
          ++stats.nonlinear_assignments;
      }
      else if(instruction.is_function_call())
      {
        irep_idt callee;
        if(
          !direct_call(instruction, callee) ||
          (!named_suffix(callee, "assume_abort_if_not") &&
           !named_suffix(callee, "__VERIFIER_assume") &&
           !named_suffix(callee, "__VERIFIER_atomic_begin") &&
           !named_suffix(callee, "__VERIFIER_atomic_end")))
          ++stats.unknown_calls;
      }
    }
  }
}
} // namespace

void property_directed_affine_audit(
  const goto_modelt &goto_model,
  message_handlert &)
{
  namespacet ns(goto_model.symbol_table);
  audit_statst stats;
  const goto_programt::instructiont *first_create = nullptr;
  const goto_programt::instructiont *last_join = nullptr;
  if(!lifecycle(goto_model, stats, first_create, last_join))
  {
    std::cout << "NATIVE_PROPERTY_AFFINE_AUDIT candidate=0 reason=lifecycle\n";
    return;
  }

  affine_formt bad_difference;
  if(!property_after_join(goto_model, last_join, bad_difference))
  {
    std::cout << "NATIVE_PROPERTY_AFFINE_AUDIT candidate=0 reason=property\n";
    return;
  }

  inspect_workers(goto_model, ns, stats);
  const bool syntactic_candidate =
    stats.loops > 0 && stats.affine_assignments > 0 &&
    stats.nonlinear_assignments == 0 && stats.indirect_assignments == 0 &&
    stats.unknown_calls == 0;
  transition_systemt transition_system;
  std::map<irep_idt, rationalt> coefficients;
  const bool transitions =
    extract_transition_system(
      goto_model, ns, stats.workers, transition_system);
  const bool synthesized =
    transitions &&
    solve_property_conservation(
      bad_difference, transition_system, coefficients);
  std::vector<affine_formt> initial_facts;
  const bool base =
    synthesized &&
    initial_relation_established(
      goto_model,
      ns,
      first_create,
      coefficients,
      bad_difference.constant,
      &initial_facts);
  std::vector<counted_loopt> counted_loops;
  const bool counted =
    base &&
    extract_counted_loops(
      goto_model, ns, stats.workers, counted_loops);
  std::size_t equal_loop_pairs = 0;
  std::vector<mp_integer> lattice_multipliers;
  lattice_audit_statst lattice_stats;
  const bool lattice_discharged =
    base &&
    property_discharged_by_counted_loops(
      goto_model,
      ns,
      stats,
      first_create,
      bad_difference,
      transition_system,
      coefficients,
      initial_facts,
      counted_loops,
      equal_loop_pairs,
      lattice_multipliers,
      lattice_stats);
  const bool direct_certificate =
    base &&
    direct_conservation_certificate(
      goto_model,
      ns,
      stats,
      first_create,
      bad_difference,
      transition_system,
      coefficients,
      initial_facts);
  token_drain_audit_statst drain_stats;
  const bool token_drain_discharged =
    base &&
    token_drain_certificate(
      goto_model,
      ns,
      stats,
      first_create,
      bad_difference,
      transition_system,
      coefficients,
      initial_facts,
      drain_stats);
  std::cout << "NATIVE_PROPERTY_AFFINE_AUDIT candidate="
            << (syntactic_candidate ? 1 : 0)
            << " transitions=" << (transitions ? 1 : 0)
            << " synthesized=" << (synthesized ? 1 : 0)
            << " base=" << (base ? 1 : 0)
            << " strict_counted=" << (counted ? counted_loops.size() : 0)
            << " lattice_pairs=" << equal_loop_pairs
            << " lattice_discharged=" << (lattice_discharged ? 1 : 0)
            << " lattice_integer_invariant="
            << (lattice_stats.integer_invariant ? 1 : 0)
            << " lattice_integer_initial="
            << (lattice_stats.integer_initial ? 1 : 0)
            << " lattice_preserved=" << (lattice_stats.preserved ? 1 : 0)
            << " lattice_common_domain="
            << (lattice_stats.common_domain ? 1 : 0)
            << " lattice_complete_coverage="
            << (lattice_stats.complete_coverage ? 1 : 0)
            << " direct_certificate=" << (direct_certificate ? 1 : 0)
            << " drain_terminal_facts="
            << (drain_stats.terminal_facts ? 1 : 0)
            << " drain_unsigned_domain="
            << (drain_stats.unsigned_domain ? 1 : 0)
            << " drain_closed_paths="
            << (drain_stats.closed_paths ? 1 : 0)
            << " drain_guarded_updates="
            << (drain_stats.guarded_updates ? 1 : 0)
            << " drain_ordered_transfers="
            << (drain_stats.ordered_transfers ? 1 : 0)
            << " drain_global_snapshot="
            << (drain_stats.global_snapshot ? 1 : 0)
            << " drain_discharged="
            << (token_drain_discharged ? 1 : 0)
            << " drain_resources=" << drain_stats.resources.size()
            << " drain_token_paths=" << drain_stats.token_paths
            << " drain_snapshot_workers="
            << drain_stats.snapshot_workers
            << " drain_resource_updates="
            << drain_stats.resource_updates
            << " drain_atomic_updates="
            << drain_stats.atomic_updates
            << " drain_negative_updates="
            << drain_stats.negative_updates
            << " drain_guarded_negative_updates="
            << drain_stats.guarded_negative_updates
            << " initial_facts=" << initial_facts.size()
            << " property_symbols=" << bad_difference.coefficients.size()
            << " workers=" << stats.workers.size()
            << " loops=" << stats.loops
            << " affine_assignments=" << stats.affine_assignments
            << " nonlinear_assignments=" << stats.nonlinear_assignments
            << " indirect_assignments=" << stats.indirect_assignments
            << " unknown_calls=" << stats.unknown_calls
            << " explored_paths=" << transition_system.explored_paths
            << " rejected_paths=" << transition_system.rejected_paths;
  if(synthesized)
    std::cout << " coefficients=" << coefficient_string(coefficients);
  if(!counted_loops.empty())
    std::cout << " counted_loops=" << counted_loop_string(counted_loops);
  if(!lattice_multipliers.empty())
    std::cout << " lattice_multipliers="
              << integer_multipliers_string(lattice_multipliers);
  if(!drain_stats.property_multipliers.empty())
    std::cout << " drain_multipliers="
              << integer_multipliers_string(
                   drain_stats.property_multipliers);
  if(!initial_facts.empty())
    std::cout << " initial_equalities="
              << affine_facts_string(initial_facts);
  std::cout << '\n';
}

bool property_directed_affine_proof(
  const goto_modelt &goto_model,
  message_handlert &)
{
  namespacet ns(goto_model.symbol_table);
  audit_statst stats;
  const goto_programt::instructiont *first_create = nullptr;
  const goto_programt::instructiont *last_join = nullptr;
  if(!lifecycle(goto_model, stats, first_create, last_join))
    return false;

  affine_formt bad_difference;
  if(!property_after_join(goto_model, last_join, bad_difference))
    return false;

  inspect_workers(goto_model, ns, stats);
  if(
    stats.loops == 0 || stats.affine_assignments == 0 ||
    stats.nonlinear_assignments != 0 ||
    stats.indirect_assignments != 0 || stats.unknown_calls != 0)
    return false;

  transition_systemt transition_system;
  std::map<irep_idt, rationalt> coefficients;
  if(
    !extract_transition_system(
      goto_model, ns, stats.workers, transition_system) ||
    !solve_property_conservation(
      bad_difference, transition_system, coefficients))
    return false;

  std::vector<affine_formt> initial_facts;
  if(!initial_relation_established(
      goto_model,
      ns,
      first_create,
      coefficients,
      bad_difference.constant,
      &initial_facts))
    return false;

  const bool direct_certificate =
    direct_conservation_certificate(
      goto_model,
      ns,
      stats,
      first_create,
      bad_difference,
      transition_system,
      coefficients,
      initial_facts);
  std::vector<counted_loopt> counted_loops;
  std::size_t equal_loop_pairs = 0;
  std::vector<mp_integer> lattice_multipliers;
  lattice_audit_statst lattice_stats;
  const bool lattice_certificate =
    !direct_certificate &&
    extract_counted_loops(
      goto_model, ns, stats.workers, counted_loops) &&
    property_discharged_by_counted_loops(
      goto_model,
      ns,
      stats,
      first_create,
      bad_difference,
      transition_system,
      coefficients,
      initial_facts,
      counted_loops,
      equal_loop_pairs,
      lattice_multipliers,
      lattice_stats);
  token_drain_audit_statst drain_stats;
  const bool drain_certificate =
    !direct_certificate && !lattice_certificate &&
    token_drain_certificate(
      goto_model,
      ns,
      stats,
      first_create,
      bad_difference,
      transition_system,
      coefficients,
      initial_facts,
      drain_stats);
  if(
    !direct_certificate && !lattice_certificate &&
    !drain_certificate)
    return false;

  std::cout << "NATIVE_PROPERTY_AFFINE_CERTIFICATE applied=1"
            << " mode="
            << (direct_certificate
                  ? "direct"
                  : lattice_certificate ? "lattice" : "token-drain")
            << " workers=" << stats.workers.size()
            << " paths=" << transition_system.explored_paths
            << " relation=" << coefficient_string(coefficients);
  if(lattice_certificate)
    std::cout << " strict_counted=" << counted_loops.size()
              << " lattice_pairs=" << equal_loop_pairs
              << " lattice_multipliers="
              << integer_multipliers_string(lattice_multipliers);
  if(drain_certificate)
    std::cout << " drain_resources=" << drain_stats.resources.size()
              << " drain_token_paths=" << drain_stats.token_paths
              << " drain_snapshot_workers="
              << drain_stats.snapshot_workers
              << " drain_multipliers="
              << integer_multipliers_string(
                   drain_stats.property_multipliers);
  std::cout << '\n';
  return true;
}
