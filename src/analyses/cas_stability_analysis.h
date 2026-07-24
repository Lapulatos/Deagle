/*******************************************************************\

Module: CAS Linearization Stability

\*******************************************************************/

#ifndef CPROVER_ANALYSES_CAS_STABILITY_ANALYSIS_H
#define CPROVER_ANALYSES_CAS_STABILITY_ANALYSIS_H

class goto_modelt;
class message_handlert;

/// Prove stable postconditions of unbounded homogeneous workers whose retry
/// loops linearize at a structurally validated atomic compare-and-swap.
bool cas_linearization_stability_transform(
  goto_modelt &goto_model,
  message_handlert &message_handler);

#endif // CPROVER_ANALYSES_CAS_STABILITY_ANALYSIS_H
