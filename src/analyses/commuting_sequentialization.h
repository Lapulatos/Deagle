/*******************************************************************\

Module: Join-Scoped Commuting Phase Sequentialization

\*******************************************************************/

#ifndef CPROVER_ANALYSES_COMMUTING_SEQUENTIALIZATION_H
#define CPROVER_ANALYSES_COMMUTING_SEQUENTIALIZATION_H

class goto_modelt;
class message_handlert;

/// Replace a flat create-then-join phase by direct worker calls when a
/// transitive effect certificate proves that every pair of workers commutes.
/// Unsupported programs are left unchanged and return false.
bool join_scoped_commuting_sequentialization_transform(
  goto_modelt &goto_model,
  message_handlert &message_handler);

#endif // CPROVER_ANALYSES_COMMUTING_SEQUENTIALIZATION_H
