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
  bool repeated_single_worker_only = false,
  bool finite_protocol_product = false);

/// Try the finite protocol product only for a bounded lifecycle shape that is
/// admitted from the GOTO model itself. Unsupported shapes return UNKNOWN
/// without changing the input model.
interference_predicate_resultt interference_predicate_finite_product_auto(
  const goto_modelt &goto_model,
  message_handlert &message_handler,
  bool preserve_data_races = false);

#endif // CPROVER_ANALYSES_INTERFERENCE_PREDICATE_ANALYSIS_H
