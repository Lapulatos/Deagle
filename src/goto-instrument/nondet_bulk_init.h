/*******************************************************************\

Module: Exact pre-thread nondeterministic bulk initialization

\*******************************************************************/

#ifndef CPROVER_GOTO_INSTRUMENT_NONDET_BULK_INIT_H
#define CPROVER_GOTO_INSTRUMENT_NONDET_BULK_INIT_H

#include <cstddef>

class goto_modelt;
class message_handlert;

struct nondet_bulk_init_statst
{
  std::size_t candidate_loops = 0;
  std::size_t transformed_loops = 0;
  std::size_t rejected_non_prethread = 0;
  std::size_t rejected_nonterminal = 0;
};

nondet_bulk_init_statst nondet_bulk_init(
  goto_modelt &goto_model,
  message_handlert &message_handler);

#endif
