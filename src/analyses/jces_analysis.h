/*******************************************************************\

Module: Join-Scoped Compositional Effect Summary

\*******************************************************************/

#ifndef CPROVER_ANALYSES_JCES_ANALYSIS_H
#define CPROVER_ANALYSES_JCES_ANALYSIS_H

class goto_modelt;
class message_handlert;

/// Audit finite homogeneous spawn loops whose worker has one composable
/// affine scalar effect. This does not mutate the GOTO model.
bool homogeneous_spawn_witness_audit(
  const goto_modelt &goto_model,
  message_handlert &message_handler);

/// In a counterexample-only model, replace one finite homogeneous spawn loop
/// by the exact effect of the legal schedule that runs each worker to
/// completion immediately after creation. Unsupported models are unchanged.
bool homogeneous_spawn_witness_transform(
  goto_modelt &goto_model,
  message_handlert &message_handler);

/// Audit exact acceleration opportunities for event-free thread-local
/// counting loops. This does not mutate the GOTO model.
bool local_loop_acceleration_audit(
  const goto_modelt &goto_model,
  message_handlert &message_handler);

/// Replace event-free thread-local zero-based unit-counting loops with their
/// exact signed or unsigned bit-vector exit assignment.
bool local_loop_acceleration_transform(
  goto_modelt &goto_model,
  message_handlert &message_handler);

/// Audit whether a joined nested loop of unit additions is equivalent to a
/// joined loop that adds the runtime inner iteration count once.
void nested_iteration_homomorphism_audit(
  const goto_modelt &goto_model,
  message_handlert &message_handler);

/// Prove equality of joined accumulators using a runtime nested-iteration
/// homomorphism.
bool nested_iteration_homomorphism_proof(
  const goto_modelt &goto_model,
  message_handlert &message_handler);

/// Audit whether two fully joined workers compute the same monoid fold using
/// different segment boundaries and a conserved sum/bag projection.
void segmented_fold_conservation_audit(
  const goto_modelt &goto_model,
  message_handlert &message_handler);

/// Prove equality of two fully joined segmented folds by the invariant
/// projection sum (+) bag.
bool segmented_fold_conservation_proof(
  const goto_modelt &goto_model,
  message_handlert &message_handler);

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
