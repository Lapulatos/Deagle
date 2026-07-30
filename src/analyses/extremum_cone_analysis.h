/*******************************************************************\

Module: Relational Extremum-Cone Invariant

\*******************************************************************/

#ifndef CPROVER_ANALYSES_EXTREMUM_CONE_ANALYSIS_H
#define CPROVER_ANALYSES_EXTREMUM_CONE_ANALYSIS_H

class goto_modelt;
class message_handlert;

bool relational_comparator_transitivity_proof(
  const goto_modelt &goto_model,
  message_handlert &message_handler);

bool relational_comparator_antisymmetry_proof(
  const goto_modelt &goto_model,
  message_handlert &message_handler);

bool extremum_cone_proof(
  const goto_modelt &goto_model,
  message_handlert &message_handler);

void role_split_affine_stream_audit(
  const goto_modelt &goto_model,
  message_handlert &message_handler);

void publication_frontier_sequence_audit(
  const goto_modelt &goto_model,
  message_handlert &message_handler);

void relational_bisimulation_audit(
  const goto_modelt &goto_model,
  message_handlert &message_handler);

#endif
