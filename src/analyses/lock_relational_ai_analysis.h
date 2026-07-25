/*******************************************************************\

Module: Lock-Indexed Relational Abstract Certificate

\*******************************************************************/

#ifndef CPROVER_ANALYSES_LOCK_RELATIONAL_AI_ANALYSIS_H
#define CPROVER_ANALYSES_LOCK_RELATIONAL_AI_ANALYSIS_H

class goto_modelt;
class message_handlert;

/// Prove all user reachability properties with a lock-indexed numeric
/// post-fixed point, then remove only the proved property/lifecycle slice.
/// Unsupported programs are unchanged and return false.
bool lock_relational_ai_transform(
  goto_modelt &goto_model,
  message_handlert &message_handler);

#endif // CPROVER_ANALYSES_LOCK_RELATIONAL_AI_ANALYSIS_H
