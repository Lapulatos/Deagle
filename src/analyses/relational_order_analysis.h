/*******************************************************************\

Module: Relational Order-Law Certificates

\*******************************************************************/

#ifndef CPROVER_ANALYSES_RELATIONAL_ORDER_ANALYSIS_H
#define CPROVER_ANALYSES_RELATIONAL_ORDER_ANALYSIS_H

class goto_modelt;
class message_handlert;

bool relational_order_law_proof(
  const goto_modelt &goto_model,
  message_handlert &message_handler);

#endif
