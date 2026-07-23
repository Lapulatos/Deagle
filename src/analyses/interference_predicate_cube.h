/*******************************************************************\

Module: Interference-Closed Predicate Cubes

\*******************************************************************/

#ifndef CPROVER_ANALYSES_INTERFERENCE_PREDICATE_CUBE_H
#define CPROVER_ANALYSES_INTERFERENCE_PREDICATE_CUBE_H

#include <util/expr.h>
#include <util/std_expr.h>
#include <util/threeval.h>

#include <utility>
#include <vector>

class message_handlert;
class namespacet;

bool interference_predicate_cube_self_test(
  const namespacet &ns,
  message_handlert &message_handler);

struct interference_predicate_cubet
{
  std::vector<tvt> values;

  bool subsumes(const interference_predicate_cubet &other) const;
};

struct interference_predicate_operationt
{
  enum class kindt
  {
    ASSIGN,
    ASSUME
  };

  kindt kind;
  exprt lhs;
  exprt rhs;

  static interference_predicate_operationt assignment(
    exprt lhs,
    exprt rhs)
  {
    return {kindt::ASSIGN, std::move(lhs), std::move(rhs)};
  }

  static interference_predicate_operationt assumption(exprt condition)
  {
    return {kindt::ASSUME, nil_exprt(), std::move(condition)};
  }
};

class interference_predicate_cube_kernelt
{
public:
  enum class abstract_resultt
  {
    CUBE,
    BOTTOM,
    SOLVER_ERROR
  };

  interference_predicate_cube_kernelt(
    const namespacet &ns,
    message_handlert &message_handler)
    : ns(ns), message_handler(message_handler)
  {
  }

  exprt cube_expression(
    const interference_predicate_cubet &cube,
    const std::vector<exprt> &predicates) const;

  abstract_resultt abstract_formula(
    const exprt &formula,
    const std::vector<exprt> &predicates,
    interference_predicate_cubet &dest) const;

  abstract_resultt transfer_assignment(
    const interference_predicate_cubet &src,
    const std::vector<exprt> &predicates,
    const exprt &lhs,
    const exprt &rhs,
    interference_predicate_cubet &dest) const;

  abstract_resultt transfer_assume(
    const interference_predicate_cubet &src,
    const std::vector<exprt> &predicates,
    const exprt &condition,
    interference_predicate_cubet &dest) const;

  abstract_resultt transfer_interference(
    const interference_predicate_cubet &writer,
    const std::vector<exprt> &writer_predicates,
    const interference_predicate_cubet &victim,
    const std::vector<exprt> &victim_predicates,
    const exprt &lhs,
    const exprt &rhs,
    interference_predicate_cubet &dest) const;

  /// Apply one indivisible writer path to a victim cube. Assignments to writer
  /// locals are retained because a later shared write may depend on them;
  /// reverse substitution existentially projects those locals from the final
  /// victim abstraction. ASSUME operations preserve path feasibility.
  abstract_resultt transfer_atomic_interference(
    const interference_predicate_cubet &writer,
    const std::vector<exprt> &writer_predicates,
    const interference_predicate_cubet &victim,
    const std::vector<exprt> &victim_predicates,
    const std::vector<interference_predicate_operationt> &operations,
    interference_predicate_cubet &dest) const;

  tvt proves(
    const interference_predicate_cubet &cube,
    const std::vector<exprt> &predicates,
    const exprt &claim) const;

  static bool insert_subsuming(
    std::vector<interference_predicate_cubet> &cubes,
    interference_predicate_cubet cube);

private:
  enum class query_resultt
  {
    SAT,
    UNSAT,
    ERROR
  };

  query_resultt satisfiable(const exprt &formula) const;
  query_resultt counterexample(const exprt &premise, const exprt &claim) const;
  abstract_resultt abstract_preimages(
    const exprt &premise,
    const std::vector<exprt> &preimages,
    interference_predicate_cubet &dest) const;

  const namespacet &ns;
  message_handlert &message_handler;
};

#endif // CPROVER_ANALYSES_INTERFERENCE_PREDICATE_CUBE_H
