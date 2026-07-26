/*******************************************************************\

Module: Protocol-Induced Capacity Cutoff

\*******************************************************************/

#ifndef CPROVER_ANALYSES_PROTOCOL_CAPACITY_ANALYSIS_H
#define CPROVER_ANALYSES_PROTOCOL_CAPACITY_ANALYSIS_H

class goto_modelt;
class message_handlert;

enum class protocol_capacity_resultt
{
  SAFE,
  UNKNOWN
};

protocol_capacity_resultt protocol_capacity_cutoff(
  const goto_modelt &goto_model,
  message_handlert &message_handler);

#endif // CPROVER_ANALYSES_PROTOCOL_CAPACITY_ANALYSIS_H
