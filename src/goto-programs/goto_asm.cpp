/*******************************************************************\

Module: Assembler -> Goto

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Assembler -> Goto

#include "goto_convert_class.h"

#include <util/string_constant.h>
#include <util/symbol.h>
#include <util/symbol_table.h>

#include <iostream>

void goto_convertt::convert_asm(
  const code_asmt &code,
  goto_programt &dest)
{
  if(code.get_flavor() == ID_gcc)
  {
    const code_asm_gcct &gcc_asm = to_code_asm_gcc(code);
    const bool empty_template =
      gcc_asm.asm_text().id() == ID_string_constant &&
      to_string_constant(gcc_asm.asm_text()).get_value().empty();
    const bool no_operands =
      gcc_asm.outputs().operands().empty() &&
      gcc_asm.inputs().operands().empty() &&
      gcc_asm.labels().operands().empty();
    const auto &clobbers = gcc_asm.clobbers().operands();
    const bool memory_clobber =
      clobbers.size() == 1 &&
      clobbers.front().id() == ID_gcc_asm_clobbered_register &&
      clobbers.front().operands().size() == 1 &&
      clobbers.front().op0().id() == ID_string_constant &&
      to_string_constant(clobbers.front().op0()).get_value() == "memory";
    if(empty_template && no_operands && memory_clobber)
    {
      static const irep_idt marker_name =
        "__CPROVER_deagle_empty_compiler_barrier";
      if(!symbol_table.has_symbol(marker_name))
      {
        auxiliary_symbolt marker;
        marker.name = marker_name;
        marker.base_name = marker_name;
        marker.mode = ID_C;
        marker.type = bool_typet();
        marker.value = true_exprt();
        marker.location = code.source_location();
        marker.is_static_lifetime = true;
        marker.is_file_local = true;
        symbol_table.add(marker);
      }
      return;
    }
  }

  std::cout << "Error: Deagle does not support asm code.\n";
  std::exit(1);
  (void)dest;
}
