/*******************************************************************\

Module: Interference-Closed Predicate Cubes

\*******************************************************************/

#include "interference_predicate_cube.h"

#include <solvers/flattening/bv_pointers.h>
#include <solvers/sat/satcheck_minisat2.h>

#include <util/expr_util.h>
#include <util/arith_tools.h>
#include <util/bitvector_types.h>
#include <util/message.h>
#include <util/namespace.h>
#include <util/replace_symbol.h>
#include <util/std_expr.h>
#include <util/std_types.h>
#include <util/symbol.h>

#include <algorithm>
#include <map>

namespace
{
void collect_writer_local_replacements(
  const exprt &expr,
  const namespacet &ns,
  std::map<irep_idt, symbol_exprt> &replacements)
{
  if(expr.id() == ID_symbol)
  {
    const auto &symbol_expr = to_symbol_expr(expr);
    const symbolt *symbol = nullptr;
    if(
      !ns.lookup(symbol_expr.get_identifier(), symbol) &&
      !symbol->is_static_lifetime)
    {
      const irep_idt &identifier = symbol_expr.get_identifier();
      if(replacements.find(identifier) == replacements.end())
      {
        replacements.emplace(
          identifier,
          symbol_exprt(
            "__CPROVER_v49_writer$" + id2string(identifier),
            symbol_expr.type()));
      }
    }
  }
  for(const auto &operand : expr.operands())
    collect_writer_local_replacements(operand, ns, replacements);
}
} // namespace

bool interference_predicate_cubet::subsumes(
  const interference_predicate_cubet &other) const
{
  if(values.size() != other.values.size())
    return false;

  for(std::size_t index = 0; index < values.size(); ++index)
  {
    if(values[index].is_known() && values[index] != other.values[index])
      return false;
  }
  return true;
}

exprt interference_predicate_cube_kernelt::cube_expression(
  const interference_predicate_cubet &cube,
  const std::vector<exprt> &predicates) const
{
  PRECONDITION(cube.values.size() == predicates.size());
  exprt::operandst literals;
  for(std::size_t index = 0; index < predicates.size(); ++index)
  {
    if(cube.values[index].is_true())
      literals.push_back(predicates[index]);
    else if(cube.values[index].is_false())
      literals.push_back(boolean_negate(predicates[index]));
  }
  return conjunction(literals);
}

interference_predicate_cube_kernelt::query_resultt
interference_predicate_cube_kernelt::satisfiable(const exprt &formula) const
{
  satcheck_minisat_no_simplifiert sat(message_handler);
  bv_pointerst solver(ns, sat, message_handler);
  solver.set_to_true(formula);
  const auto result = solver();
  if(result == decision_proceduret::resultt::D_SATISFIABLE)
    return query_resultt::SAT;
  if(result == decision_proceduret::resultt::D_UNSATISFIABLE)
    return query_resultt::UNSAT;
  return query_resultt::ERROR;
}

interference_predicate_cube_kernelt::query_resultt
interference_predicate_cube_kernelt::counterexample(
  const exprt &premise,
  const exprt &claim) const
{
  satcheck_minisat_no_simplifiert sat(message_handler);
  bv_pointerst solver(ns, sat, message_handler);
  solver.set_to_true(premise);
  solver.set_to_false(claim);
  const auto result = solver();
  if(result == decision_proceduret::resultt::D_SATISFIABLE)
    return query_resultt::SAT;
  if(result == decision_proceduret::resultt::D_UNSATISFIABLE)
    return query_resultt::UNSAT;
  return query_resultt::ERROR;
}

interference_predicate_cube_kernelt::abstract_resultt
interference_predicate_cube_kernelt::abstract_formula(
  const exprt &formula,
  const std::vector<exprt> &predicates,
  interference_predicate_cubet &dest) const
{
  return abstract_preimages(formula, predicates, dest);
}

interference_predicate_cube_kernelt::abstract_resultt
interference_predicate_cube_kernelt::abstract_preimages(
  const exprt &premise,
  const std::vector<exprt> &preimages,
  interference_predicate_cubet &dest) const
{
  const auto feasible = satisfiable(premise);
  if(feasible == query_resultt::UNSAT)
    return abstract_resultt::BOTTOM;
  if(feasible == query_resultt::ERROR)
    return abstract_resultt::SOLVER_ERROR;

  dest.values.assign(preimages.size(), tvt::unknown());
  for(std::size_t index = 0; index < preimages.size(); ++index)
  {
    const auto positive = counterexample(premise, preimages[index]);
    if(positive == query_resultt::ERROR)
      return abstract_resultt::SOLVER_ERROR;
    if(positive == query_resultt::UNSAT)
    {
      dest.values[index] = tvt(true);
      continue;
    }

    const auto negative =
      counterexample(premise, boolean_negate(preimages[index]));
    if(negative == query_resultt::ERROR)
      return abstract_resultt::SOLVER_ERROR;
    if(negative == query_resultt::UNSAT)
      dest.values[index] = tvt(false);
  }
  return abstract_resultt::CUBE;
}

interference_predicate_cube_kernelt::abstract_resultt
interference_predicate_cube_kernelt::transfer_assignment(
  const interference_predicate_cubet &src,
  const std::vector<exprt> &predicates,
  const exprt &lhs,
  const exprt &rhs,
  interference_predicate_cubet &dest) const
{
  if(lhs.id() != ID_symbol)
    return abstract_resultt::SOLVER_ERROR;

  const exprt src_formula = cube_expression(src, predicates);
  std::vector<exprt> preimages;
  preimages.reserve(predicates.size());
  replace_symbolt replacement;
  replacement.set(to_symbol_expr(lhs), rhs);
  for(const auto &predicate : predicates)
  {
    exprt preimage = predicate;
    replacement.replace(preimage);
    preimages.push_back(std::move(preimage));
  }

  return abstract_preimages(src_formula, preimages, dest);
}

interference_predicate_cube_kernelt::abstract_resultt
interference_predicate_cube_kernelt::transfer_assume(
  const interference_predicate_cubet &src,
  const std::vector<exprt> &predicates,
  const exprt &condition,
  interference_predicate_cubet &dest) const
{
  return abstract_formula(
    make_and(cube_expression(src, predicates), condition), predicates, dest);
}

interference_predicate_cube_kernelt::abstract_resultt
interference_predicate_cube_kernelt::transfer_interference(
  const interference_predicate_cubet &writer,
  const std::vector<exprt> &writer_predicates,
  const interference_predicate_cubet &victim,
  const std::vector<exprt> &victim_predicates,
  const exprt &lhs,
  const exprt &rhs,
  interference_predicate_cubet &dest) const
{
  if(lhs.id() != ID_symbol)
    return abstract_resultt::SOLVER_ERROR;
  const exprt premise = make_and(
    cube_expression(writer, writer_predicates),
    cube_expression(victim, victim_predicates));
  std::vector<exprt> preimages;
  preimages.reserve(victim_predicates.size());
  replace_symbolt replacement;
  replacement.set(to_symbol_expr(lhs), rhs);
  for(const auto &predicate : victim_predicates)
  {
    exprt preimage = predicate;
    replacement.replace(preimage);
    preimages.push_back(std::move(preimage));
  }
  return abstract_preimages(premise, preimages, dest);
}

interference_predicate_cube_kernelt::abstract_resultt
interference_predicate_cube_kernelt::transfer_atomic_interference(
  const interference_predicate_cubet &writer,
  const std::vector<exprt> &writer_predicates,
  const interference_predicate_cubet &victim,
  const std::vector<exprt> &victim_predicates,
  const std::vector<interference_predicate_operationt> &operations,
  interference_predicate_cubet &dest) const
{
  std::map<irep_idt, symbol_exprt> writer_local_replacements;
  for(const auto &predicate : writer_predicates)
    collect_writer_local_replacements(
      predicate, ns, writer_local_replacements);
  for(const auto &operation : operations)
  {
    collect_writer_local_replacements(
      operation.lhs, ns, writer_local_replacements);
    collect_writer_local_replacements(
      operation.rhs, ns, writer_local_replacements);
  }
  replace_symbolt writer_renaming;
  for(const auto &replacement : writer_local_replacements)
    writer_renaming.set(
      symbol_exprt(replacement.first, replacement.second.type()),
      replacement.second);

  exprt writer_formula = cube_expression(writer, writer_predicates);
  writer_renaming.replace(writer_formula);
  std::vector<interference_predicate_operationt> renamed_operations = operations;
  for(auto &operation : renamed_operations)
  {
    writer_renaming.replace(operation.lhs);
    writer_renaming.replace(operation.rhs);
  }

  exprt path_condition = true_exprt();
  std::vector<exprt> preimages = victim_predicates;

  for(auto operation = renamed_operations.rbegin();
      operation != renamed_operations.rend();
      ++operation)
  {
    if(operation->kind == interference_predicate_operationt::kindt::ASSUME)
    {
      path_condition = make_and(operation->rhs, path_condition);
      continue;
    }

    if(operation->lhs.id() != ID_symbol)
      return abstract_resultt::SOLVER_ERROR;
    replace_symbolt replacement;
    replacement.set(to_symbol_expr(operation->lhs), operation->rhs);
    replacement.replace(path_condition);
    for(auto &preimage : preimages)
      replacement.replace(preimage);
  }

  const exprt premise = make_and(
    make_and(
      writer_formula,
      cube_expression(victim, victim_predicates)),
    path_condition);
  return abstract_preimages(premise, preimages, dest);
}

tvt interference_predicate_cube_kernelt::proves(
  const interference_predicate_cubet &cube,
  const std::vector<exprt> &predicates,
  const exprt &claim) const
{
  const auto result = counterexample(cube_expression(cube, predicates), claim);
  if(result == query_resultt::UNSAT)
    return tvt(true);
  if(result == query_resultt::SAT)
    return tvt(false);
  return tvt::unknown();
}

bool interference_predicate_cube_kernelt::insert_subsuming(
  std::vector<interference_predicate_cubet> &cubes,
  interference_predicate_cubet cube)
{
  for(const auto &existing : cubes)
  {
    if(existing.subsumes(cube))
      return false;
  }

  cubes.erase(
    std::remove_if(
      cubes.begin(),
      cubes.end(),
      [&cube](const interference_predicate_cubet &existing) {
        return cube.subsumes(existing);
      }),
    cubes.end());
  cubes.push_back(std::move(cube));
  return true;
}

bool interference_predicate_cube_self_test(
  const namespacet &ns,
  message_handlert &message_handler)
{
  const signedbv_typet type(32);
  const symbol_exprt x("interference_predicate_self_test::x", type);
  const exprt zero = from_integer(0, type);
  const exprt one = from_integer(1, type);
  const exprt two = from_integer(2, type);
  const std::vector<exprt> predicates{
    equal_exprt(x, zero), equal_exprt(x, one), binary_relation_exprt(x, ID_lt, two)};

  interference_predicate_cube_kernelt kernel(ns, message_handler);
  interference_predicate_cubet top;
  top.values.assign(predicates.size(), tvt::unknown());

  interference_predicate_cubet assigned;
  if(
    kernel.transfer_assignment(top, predicates, x, zero, assigned) !=
      interference_predicate_cube_kernelt::abstract_resultt::CUBE ||
    !assigned.values[0].is_true() || !assigned.values[1].is_false() ||
    !assigned.values[2].is_true())
    return false;

  interference_predicate_cubet assumed;
  if(
    kernel.transfer_assume(top, predicates, equal_exprt(x, one), assumed) !=
      interference_predicate_cube_kernelt::abstract_resultt::CUBE ||
    !assumed.values[0].is_false() || !assumed.values[1].is_true() ||
    !assumed.values[2].is_true())
    return false;

  std::vector<interference_predicate_cubet> cubes;
  if(!interference_predicate_cube_kernelt::insert_subsuming(cubes, assigned))
    return false;
  if(!interference_predicate_cube_kernelt::insert_subsuming(cubes, top))
    return false;
  if(cubes.size() != 1 || !cubes.front().subsumes(assigned))
    return false;
  if(interference_predicate_cube_kernelt::insert_subsuming(cubes, assumed))
    return false;

  return true;
}
