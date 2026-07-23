/*******************************************************************\

Module: Join-Scoped Compositional Effect Summary

\*******************************************************************/

#ifndef CPROVER_ANALYSES_JCES_ANALYSIS_H
#define CPROVER_ANALYSES_JCES_ANALYSIS_H

class goto_modelt;
class message_handlert;

/// Replace a fully joined finite worker region by the composition of exact
/// worker-loop translations over shared atomic scalars. Unsupported programs
/// are left byte-for-byte unchanged and return false.
bool jces_transform(
  goto_modelt &goto_model,
  message_handlert &message_handler);

#endif // CPROVER_ANALYSES_JCES_ANALYSIS_H
