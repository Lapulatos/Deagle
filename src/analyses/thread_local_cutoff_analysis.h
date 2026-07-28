/*******************************************************************\

Module: Homogeneous Thread-Local Cutoff

\*******************************************************************/

#ifndef CPROVER_ANALYSES_THREAD_LOCAL_CUTOFF_ANALYSIS_H
#define CPROVER_ANALYSES_THREAD_LOCAL_CUTOFF_ANALYSIS_H

class goto_modelt;
class message_handlert;

/// Prove the sole worker assertion for a homogeneous dynamic thread family
/// when a private TLS pointer receives a fresh calloc-zero array and the
/// assertion loop reads exactly that array before any write.
bool dynamic_tls_calloc_zero_proof(
  goto_modelt &goto_model,
  message_handlert &message_handler);

/// Materialize one legal pthread TLS-destructor execution after proving the
/// key, worker value, destructor guard, create, and join correspondence.
/// This is a counterexample-only under-approximation.
bool tls_destructor_counterexample_transform(
  goto_modelt &goto_model,
  message_handlert &message_handler);

/// Restrict a canonical homogeneous create/join family to one real worker
/// after proving that worker instances have no cross-thread visible state.
/// Unsupported programs are unchanged and return false.
bool homogeneous_thread_local_cutoff_transform(
  goto_modelt &goto_model,
  message_handlert &message_handler);

#endif // CPROVER_ANALYSES_THREAD_LOCAL_CUTOFF_ANALYSIS_H
