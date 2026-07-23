/*******************************************************************\

Module: Interference-Closed Predicate Analysis

\*******************************************************************/

#ifndef CPROVER_ANALYSES_INTERFERENCE_PREDICATE_ANALYSIS_H
#define CPROVER_ANALYSES_INTERFERENCE_PREDICATE_ANALYSIS_H

class goto_modelt;
class message_handlert;

enum class interference_predicate_resultt
{
  SAFE,
  UNKNOWN
};

/// Emit a structural profile used to validate the proof analysis front-end.
/// This function never proves a property and does not modify the input model.
bool interference_predicate_profile(
  const goto_modelt &goto_model,
  message_handlert &message_handler);

interference_predicate_resultt interference_predicate_fixedpoint(
  const goto_modelt &goto_model,
  message_handlert &message_handler,
  bool repeated_single_worker_only = false);

#endif // CPROVER_ANALYSES_INTERFERENCE_PREDICATE_ANALYSIS_H
