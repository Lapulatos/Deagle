/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_SOLVERS_FLATTENING_EQUALITY_H
#define CPROVER_SOLVERS_FLATTENING_EQUALITY_H

#include <map>

#include <util/expr.h>

#include <solvers/prop/prop_conv_solver.h>

class equalityt:public prop_conv_solvert
{
public:
  equalityt(propt &_prop, message_handlert &message_handler)
    : prop_conv_solvert(_prop, message_handler)
  {
  }

  virtual literalt equality(const exprt &e1, const exprt &e2);

  using SUB = prop_conv_solvert;

  void finish_eager_conversion() override
  {
    add_equality_constraints();
    SUB::finish_eager_conversion();
    typemap.clear(); // if called incrementally, don't do it twice
  }

protected:
  typedef std::unordered_map<const exprt, unsigned, irep_hash> elementst;
  typedef std::map<std::pair<unsigned, unsigned>, literalt> equalitiest;
  typedef std::map<unsigned, exprt> elements_revt;

  struct typestructt
  {
    elementst elements;
    elements_revt elements_rev;
    equalitiest equalities;
  };

  // Equality constraints must be emitted in a stable type order. Iterating an
  // unordered map here made the SAT formula depend on process-local irep
  // intern numbers, which can change when an unrelated translation unit is
  // linked into the executable.
  typedef std::map<const typet, typestructt> typemapt;

  typemapt typemap;

  virtual literalt equality2(const exprt &e1, const exprt &e2);

  // an eager conversion of the transitivity constraints
  virtual void add_equality_constraints();
  virtual void add_equality_constraints(const typestructt &typestruct);
};

#endif // CPROVER_SOLVERS_FLATTENING_EQUALITY_H
