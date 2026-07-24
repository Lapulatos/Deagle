/*******************************************************************\

Module: Join-Scoped Compositional Effect Summary

\*******************************************************************/

#ifndef CPROVER_ANALYSES_JCES_ANALYSIS_H
#define CPROVER_ANALYSES_JCES_ANALYSIS_H

class goto_modelt;
class message_handlert;

/// Replace a fully joined finite worker region by the composition of exact
/// worker-loop translations over shared atomic scalars. Unsupported programs
/// are left byte-for-byte unchanged and return false.
bool jces_transform(
  goto_modelt &goto_model,
  message_handlert &message_handler);

/// Prove prefix-closed upper bounds for bounded monotone affine atomic workers
/// and remove their spawn calls when every property obligation is discharged.
bool prefix_affine_envelope_transform(
  goto_modelt &goto_model,
  message_handlert &message_handler);

/// Collapse worker body interleavings that are already excluded by an atomic
/// ticket-allocation / completion-gate protocol. Unsupported programs are
/// unchanged and return false.
bool ticket_rank_serializability_transform(
  goto_modelt &goto_model,
  message_handlert &message_handler);

#endif // CPROVER_ANALYSES_JCES_ANALYSIS_H
