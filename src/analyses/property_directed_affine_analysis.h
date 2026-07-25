/*******************************************************************\

Module: Property-Directed Affine Relation Analysis

\*******************************************************************/

#ifndef CPROVER_ANALYSES_PROPERTY_DIRECTED_AFFINE_ANALYSIS_H
#define CPROVER_ANALYSES_PROPERTY_DIRECTED_AFFINE_ANALYSIS_H

class goto_modelt;
class message_handlert;

/// Audit the typed-GOTO prerequisites for property-directed affine synthesis.
/// This function is deliberately verdict-neutral.
void property_directed_affine_audit(
  const goto_modelt &goto_model,
  message_handlert &message_handler);

/// Prove an exact post-join equality using a directly established and
/// path-preserved affine conservation relation. Returns false on every
/// unsupported proof obligation.
bool property_directed_affine_proof(
  const goto_modelt &goto_model,
  message_handlert &message_handler);

#endif
