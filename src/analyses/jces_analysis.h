/*******************************************************************\

Module: Join-Scoped Compositional Effect Summary

\*******************************************************************/

#ifndef CPROVER_ANALYSES_JCES_ANALYSIS_H
#define CPROVER_ANALYSES_JCES_ANALYSIS_H

class goto_modelt;
class message_handlert;

/// Audit whether fully joined atomic worker loops form inverse group actions
/// whose combined word restores one shared state to its identity.
void group_action_cancellation_audit(
  const goto_modelt &goto_model,
  message_handlert &message_handler);

/// Prove that fully joined atomic worker loops contribute inverse group
/// actions and therefore restore one shared state to its identity.
bool group_action_cancellation_proof(
  const goto_modelt &goto_model,
  message_handlert &message_handler);

/// Prove equality of two fully joined workers whose loop bodies spell the
/// same guarded transition word at different unrolling factors. Unsupported
/// programs are unchanged and return false.
bool transition_word_equivalence_transform(
  goto_modelt &goto_model,
  message_handlert &message_handler);

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

/// Aggregate fixed-count, same-mutex, commuting affine critical sections into
/// their exact post-join state. Unsupported programs are unchanged.
bool lock_scoped_commutative_aggregation_transform(
  goto_modelt &goto_model,
  message_handlert &message_handler);

/// Prove postconditions established at mutex-protected unit-update
/// linearization points and stable under every homogeneous worker transition.
/// This permits removing an otherwise unbounded homogeneous spawn loop.
bool lock_linearization_stability_transform(
  goto_modelt &goto_model,
  message_handlert &message_handler);

#endif // CPROVER_ANALYSES_JCES_ANALYSIS_H
