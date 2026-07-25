/*******************************************************************\

Module: Homogeneous Thread-Local Cutoff

\*******************************************************************/

#ifndef CPROVER_ANALYSES_THREAD_LOCAL_CUTOFF_ANALYSIS_H
#define CPROVER_ANALYSES_THREAD_LOCAL_CUTOFF_ANALYSIS_H

class goto_modelt;
class message_handlert;

/// Restrict a canonical homogeneous create/join family to one real worker
/// after proving that worker instances have no cross-thread visible state.
/// Unsupported programs are unchanged and return false.
bool homogeneous_thread_local_cutoff_transform(
  goto_modelt &goto_model,
  message_handlert &message_handler);

#endif // CPROVER_ANALYSES_THREAD_LOCAL_CUTOFF_ANALYSIS_H
