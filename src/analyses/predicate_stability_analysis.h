/*******************************************************************\

Module: Predicate-Stable Linearization

\*******************************************************************/

#ifndef CPROVER_ANALYSES_PREDICATE_STABILITY_ANALYSIS_H
#define CPROVER_ANALYSES_PREDICATE_STABILITY_ANALYSIS_H

class goto_modelt;
class message_handlert;

bool predicate_stable_linearization_transform(
  goto_modelt &goto_model,
  message_handlert &message_handler,
  bool preserve_data_races = false);

#endif
