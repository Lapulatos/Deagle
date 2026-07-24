/*******************************************************************\

Module: Lock-Boundary Ego-Thread Abstraction

\*******************************************************************/

#ifndef CPROVER_ANALYSES_LOCK_EGO_ABSTRACTION_H
#define CPROVER_ANALYSES_LOCK_EGO_ABSTRACTION_H

class goto_modelt;
class message_handlert;

/// Replace an unbounded homogeneous pthread-create loop by one representative
/// worker and havoc the worker's shared write set after every lock acquisition.
/// The result is a safety over-approximation and must only be used as a
/// proof-only prepass.
bool lock_boundary_ego_thread_abstraction_transform(
  goto_modelt &goto_model,
  message_handlert &message_handler);

#endif // CPROVER_ANALYSES_LOCK_EGO_ABSTRACTION_H
