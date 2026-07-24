/*******************************************************************\

Module: Relational Extremum-Cone Invariant

\*******************************************************************/

#ifndef CPROVER_ANALYSES_EXTREMUM_CONE_ANALYSIS_H
#define CPROVER_ANALYSES_EXTREMUM_CONE_ANALYSIS_H

class goto_modelt;
class message_handlert;

bool extremum_cone_proof(
  const goto_modelt &goto_model,
  message_handlert &message_handler);

#endif
