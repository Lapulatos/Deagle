/*******************************************************************\

Module: Lower finite pointer writes to explicit GOTO branches

\*******************************************************************/

#ifndef CPROVER_POINTER_ANALYSIS_LOWER_FINITE_POINTER_WRITES_H
#define CPROVER_POINTER_ANALYSIS_LOWER_FINITE_POINTER_WRITES_H

#include <cstddef>

class goto_modelt;

/// Replace assignments through a finite, precisely resolved pointer with
/// mutually exclusive direct assignments.  This prevents symbolic execution
/// from merging the inactive alternatives as writes to shared state.
///
/// The transformation is fail-closed: assignments with unknown or remaining
/// indirect alternatives are left unchanged. Explicit failed-object lvalues
/// are retained as guarded branches rather than discarded.
///
/// \return number of assignments lowered
std::size_t lower_finite_pointer_writes(
  goto_modelt &goto_model,
  std::size_t maximum_alternatives = 16);

#endif // CPROVER_POINTER_ANALYSIS_LOWER_FINITE_POINTER_WRITES_H
