/*******************************************************************\

Module: Join-Scoped Compositional Effect Summary

\*******************************************************************/

#ifndef CPROVER_ANALYSES_JCES_ANALYSIS_H
#define CPROVER_ANALYSES_JCES_ANALYSIS_H

#include <cstddef>
#include <string>

class goto_modelt;
class message_handlert;

/// Audit a single canonical same-worker create loop whose omitted symmetric
/// workers may remain dormant before the first join.
bool dormant_spawn_cutoff_audit(
  const goto_modelt &goto_model,
  message_handlert &message_handler);

/// Materialize two symmetric workers in a counterexample-only model and
/// discard main from its first join onward. Unsupported programs are
/// unchanged.
bool dormant_spawn_cutoff_transform(
  goto_modelt &goto_model,
  message_handlert &message_handler);

/// Materialize one worker from a single canonical create loop and discard
/// main from its first join onward. This is a counterexample-only
/// under-approximation for properties reached before the join.
bool main_worker_prefix_transform(
  goto_modelt &goto_model,
  message_handlert &message_handler);

/// Return whether the GOTO model has one canonical create loop that can be
/// under-approximated by a main/worker counterexample prefix.
bool main_worker_prefix_applicable(const goto_modelt &goto_model);

/// Return the worker function selected by the canonical main/worker prefix.
/// An empty identifier denotes a non-applicable model.
std::string main_worker_prefix_worker_id(const goto_modelt &goto_model);

/// In a disposable counterexample model with two canonical worker classes,
/// retain one iteration of exactly two nested finite initialization loops
/// that precede both create loops.
bool pair_initialization_prefix_transform(
  goto_modelt &goto_model,
  message_handlert &message_handler);

/// Return whether the early pair-initialization under-approximation was
/// applied before pointer dereferencing.
bool pair_initialization_prefix_applied(const goto_modelt &goto_model);

/// In a disposable counterexample model with one homogeneous worker class,
/// retain two initialized object domains with two elements each, preserve a
/// cross-domain pointer splice, and materialize two symmetric workers.
bool cross_domain_list_prefix_transform(
  goto_modelt &goto_model,
  message_handlert &message_handler);

/// Return whether the early homogeneous cross-domain prefix was applied.
bool cross_domain_list_prefix_applied(const goto_modelt &goto_model);

/// In a disposable counterexample model, retain two initialized object and
/// mutex slots and materialize two instances of a worker whose object and
/// protecting-mutex choices are independently bounded.
bool independent_index_prefix_transform(
  goto_modelt &goto_model,
  message_handlert &message_handler);

/// Return whether the early independent-index prefix was applied.
bool independent_index_prefix_applied(const goto_modelt &goto_model);

/// In a disposable counterexample model with one homogeneous worker class,
/// retain two outer initialization domains, fully initialize each retained
/// inner domain, and materialize one representative worker fixed to a
/// retained domain. This is a fail-closed counterexample under-approximation.
bool single_worker_initialization_prefix_transform(
  goto_modelt &goto_model,
  message_handlert &message_handler);

/// Return whether the single-worker initialization prefix was applied.
bool single_worker_initialization_prefix_applied(
  const goto_modelt &goto_model);

/// Return the canonical inner-initialization loop that must be fully
/// unwound after applying the single-worker initialization prefix.
std::string single_worker_initialization_prefix_unwind_loop(
  const goto_modelt &goto_model);

std::string single_worker_initialization_prefix_outer_unwind_loop(
  const goto_modelt &goto_model);

// Soundly removes a dormant worker population when every worker performs an
// exact zero-sum scalar update while holding the same mutex that protects the
// zero assertion.
bool common_mutex_zero_sum_transform(
  goto_modelt &goto_model,
  message_handlert &message_handler);

bool common_mutex_zero_sum_applied(const goto_modelt &goto_model);

// Soundly removes a dormant worker population when the normalized worker
// resolves to a helper whose only shared effect is a balanced update under
// the same mutex that protects the zero assertion.
bool resolved_worker_zero_sum_transform(
  goto_modelt &goto_model,
  message_handlert &message_handler);

bool resolved_worker_zero_sum_applied(const goto_modelt &goto_model);

// Proves a two-base member-alias race instrumentation pattern: the worker
// protects one static aggregate member with its sibling mutex, while main
// derives both the data and mutex pointers from the same branch-selected
// aggregate base.
bool aggregate_member_lock_alias_transform(
  goto_modelt &goto_model,
  message_handlert &message_handler);

bool aggregate_member_lock_alias_applied(const goto_modelt &goto_model);

// Soundly removes a zero-sum worker population when one identical guard
// dominates main's direct lock, zero assertion, and matching unlock.
bool guarded_common_mutex_zero_sum_transform(
  goto_modelt &goto_model,
  message_handlert &message_handler);

bool guarded_common_mutex_zero_sum_applied(const goto_modelt &goto_model);

// Proves that a mutex-protected zero state is an inductive fixed point when
// every off-mutex update is reachable only after observing nonzero while
// holding that mutex.
bool mutex_zero_fixedpoint_transform(
  goto_modelt &goto_model,
  message_handlert &message_handler);

bool mutex_zero_fixedpoint_applied(const goto_modelt &goto_model);

// Audits constant store/assert pairs under a two-level pthread lifecycle.
// This audit does not transform the model.
bool nested_lifecycle_last_writer_audit(
  const goto_modelt &goto_model,
  message_handlert &message_handler);

// Discharges the property-wrapper calls only after the full two-level
// lifecycle and last-writer proof succeeds.
bool nested_lifecycle_last_writer_transform(
  goto_modelt &goto_model,
  message_handlert &message_handler);

// Proves property-error unreachability with a role-independent
// interprocedural abstract interpretation of one derived Boolean atomic lock.
bool boolean_atomic_lock_region_audit(
  const goto_modelt &goto_model,
  message_handlert &message_handler);

bool boolean_atomic_lock_region_transform(
  goto_modelt &goto_model,
  message_handlert &message_handler);

// Proves a monotone condition-wait predicate and removes an unbounded
// dispatcher whose possible error sites are all discharged by that proof.
bool monotone_condition_wait_transform(
  goto_modelt &goto_model,
  message_handlert &message_handler);

bool monotone_condition_wait_applied(const goto_modelt &goto_model);

/// Audit two or more canonical homogeneous create loops for a
/// counterexample-only self/cross worker-pair decomposition.
bool dormant_spawn_pair_audit(
  const goto_modelt &goto_model,
  message_handlert &message_handler);

/// Return the number of sound self/cross variants admitted by the dormant
/// spawn-pair analysis, or zero when fewer than two classes are applicable.
std::size_t dormant_spawn_pair_variant_count(
  const goto_modelt &goto_model);

/// Materialize one selected pair of worker roles and keep every omitted
/// worker class dormant. Unsupported variants leave the model unchanged.
bool dormant_spawn_pair_transform(
  goto_modelt &goto_model,
  std::size_t variant,
  message_handlert &message_handler);

/// Audit constant-bound, zero-based, straight-line lifecycle loops in main.
/// Such loops initialize an indexed thread descriptor and execute exactly one
/// pthread_create or pthread_join per iteration.
bool indexed_lifecycle_prefix_audit(
  const goto_modelt &goto_model,
  message_handlert &message_handler);

/// Exactly unroll admitted indexed lifecycle loops before bounded
/// counterexample search and, after a complete create/join prefix, stop the
/// disposable model at the final join. Unsupported loops are unchanged.
bool indexed_lifecycle_prefix_transform(
  goto_modelt &goto_model,
  message_handlert &message_handler);

/// Audit two finite, fully joined producer/consumer loops whose condition
/// variables enforce a one-token alternating execution. This does not mutate
/// the GOTO model.
bool alternating_phase_recurrence_audit(
  goto_modelt &goto_model,
  message_handlert &message_handler);

/// In a counterexample-only model, select the legal alternating execution of
/// an admitted producer/consumer pair and replace it by its exact triangular
/// state recurrence. Unsupported models are unchanged.
bool alternating_phase_recurrence_transform(
  goto_modelt &goto_model,
  message_handlert &message_handler);

/// Prove that two or more independently alternating atomic updates preserve
/// a nonnegative shared position. A joined monitor can therefore never clear
/// their atomic loop flag, so code after the joins is unreachable.
bool nonnegative_oscillator_monitor_transform(
  goto_modelt &goto_model,
  message_handlert &message_handler);

/// Replace fully joined bounded workers whose private phase alternates equal
/// opposite atomic updates for an even number of steps. The shared transition
/// word is exactly the identity; all unsupported shapes remain unchanged.
bool bounded_alternating_cancellation_transform(
  goto_modelt &goto_model,
  message_handlert &message_handler);

/// Replace fully joined workers whose private phase permits nondeterministic
/// termination only after an equal-opposite atomic update pair. Every finite
/// transition word is the identity; unsupported shapes remain unchanged.
bool phase_boundary_cancellation_transform(
  goto_modelt &goto_model,
  message_handlert &message_handler);

/// Replace fully joined workers whose only shared effect is an unsigned
/// nondeterministic loop followed by an unconditional constant overwrite.
/// Every terminating execution has the same post-join state, while a
/// nonterminating execution cannot reach code after the joins.
bool joined_terminal_overwrite_transform(
  goto_modelt &goto_model,
  message_handlert &message_handler);

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

/// After a native proof has made worker calls sequential, replace simple
/// unsigned zero-based accumulation loops by their exact modular closed form.
bool local_modular_accumulation_transform(
  goto_modelt &goto_model,
  message_handlert &message_handler);

/// Collapse exactly one marked pure spin loop to its first exiting
/// observation. Every omitted iteration must contain one atomic load,
/// local-only bookkeeping, and no shared effect.
bool pure_spin_wait_collapse_transform(
  goto_modelt &goto_model,
  message_handlert &message_handler,
  bool &empty_barrier_family,
  bool &within_proof_budget);

/// Apply the pure-spin transform only to models carrying the exact native
/// compiler-barrier marker. Unsupported marked models terminate inconclusive.
bool pure_spin_wait_dispatch(
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

/// Prove equality between a mutex-reduced partition count and a fully joined
/// sequential recount of the same array predicate.
bool partitioned_count_reduction_proof(
  const goto_modelt &goto_model,
  message_handlert &message_handler);

/// Prove a positive-epsilon two-sided floating-point disjunction after
/// establishing finiteness through a bounded joined mutex reduction.
bool finite_two_sided_disjunction_proof(
  const goto_modelt &goto_model,
  message_handlert &message_handler);

/// Prove a joined arithmetic-series result guarded by a single-writer
/// completion flag.
bool completion_flag_arithmetic_proof(
  const goto_modelt &goto_model,
  message_handlert &message_handler);

/// Prove that a state-published nonzero seed remains nonzero across
/// rejection-sampled successful CAS updates.
bool nonzero_cas_seed_proof(
  const goto_modelt &goto_model,
  message_handlert &message_handler);

/// Prove local and shared maximum assertions for aligned bounded chunks and
/// a mutex-protected monotone max reduction.
bool monotone_chunk_maximum_proof(
  const goto_modelt &goto_model,
  message_handlert &message_handler);

/// Prove equivalence of joined linear and row-major tiled copies from one
/// immutable source array.
bool linear_tiled_copy_equivalence_proof(
  const goto_modelt &goto_model,
  message_handlert &message_handler);

/// Prove that a joined atomic queue consumer can read only the value admitted
/// by the producer into the immutable backing array.
bool atomic_queue_occupancy_value_proof(
  const goto_modelt &goto_model,
  message_handlert &message_handler);

/// Prove equality of two consecutive immutable queue slots admitted by two
/// isomorphic unsigned modular folds and observed after full joins.
bool isomorphic_modular_fold_pair_proof(
  const goto_modelt &goto_model,
  message_handlert &message_handler);

/// Prove equality of two fully joined workers whose loop bodies spell the
/// same guarded transition word at different unrolling factors. Unsupported
/// programs are unchanged and return false.
bool transition_word_equivalence_transform(
  goto_modelt &goto_model,
  message_handlert &message_handler);

bool index_region_ownership_proof(
  goto_modelt &goto_model,
  message_handlert &message_handler);

bool post_store_stable_cell_proof(
  goto_modelt &goto_model,
  message_handlert &message_handler);

/// Prove absence of overflow and underflow in a two-worker bounded stack.
/// Every stack operation must be serialized by one mutex, the push loop may
/// execute no more than the array capacity, and pop must be guarded by a
/// positive stack height. Unsupported programs are unchanged.
bool stack_capacity_invariant_proof(
  goto_modelt &goto_model,
  message_handlert &message_handler);

/// Prove a serialized producer/consumer queue whose producer writes the same
/// bounded value sequence to queue storage and a reference array and whose
/// consumer reads both sequences at matching indices.
bool queue_sequence_correspondence_proof(
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
