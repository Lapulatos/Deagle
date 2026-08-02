/*******************************************************************\

Module: Interference-Closed Predicate Analysis

\*******************************************************************/

#include "interference_predicate_analysis.h"
#include "interference_predicate_cube.h"
#include "jces_analysis.h"

#include <goto-programs/goto_inline.h>
#include <goto-programs/goto_model.h>

#include <pointer-analysis/goto_program_dereference.h>
#include <pointer-analysis/value_set_analysis.h>

#include <langapi/language_util.h>

#include <util/expr_util.h>
#include <util/arith_tools.h>
#include <util/byte_operators.h>
#include <util/irep_hash.h>
#include <util/message.h>
#include <util/namespace.h>
#include <util/pointer_expr.h>
#include <util/pointer_offset_size.h>
#include <util/replace_expr.h>
#include <util/replace_symbol.h>
#include <util/simplify_expr.h>
#include <util/std_expr.h>
#include <util/std_code.h>

#include <algorithm>
#include <cstdlib>
#include <deque>
#include <functional>
#include <iostream>
#include <map>
#include <memory>
#include <set>
#include <sstream>
#include <unordered_map>
#include <unordered_set>
#include <vector>

namespace
{
bool reachable_product_call_graph_acyclic(
  const goto_functionst &functions,
  const std::vector<irep_idt> &roots,
  irep_idt &recursive_function)
{
  std::unordered_map<irep_idt, unsigned, irep_id_hash> visitation;
  std::function<bool(const irep_idt &)> visit =
    [&](const irep_idt &function_id) {
      const auto known = visitation.find(function_id);
      if(known != visitation.end())
      {
        if(known->second == 1)
        {
          recursive_function = function_id;
          return false;
        }
        return true;
      }
      const auto function = functions.function_map.find(function_id);
      if(
        function == functions.function_map.end() ||
        !function->second.body_available())
        return true;
      visitation.emplace(function_id, 1);
      for(const auto &instruction : function->second.body.instructions)
      {
        if(!instruction.is_function_call())
          continue;
        const exprt &callee = skip_typecast(instruction.call_function());
        if(callee.id() != ID_symbol)
          continue;
        if(!visit(to_symbol_expr(callee).get_identifier()))
          return false;
      }
      visitation[function_id] = 2;
      return true;
    };
  for(const auto &root : roots)
    if(!visit(root))
      return false;
  return true;
}

bool direct_product_lvalue(const exprt &input)
{
  const exprt &expression = skip_typecast(input);
  if(expression.id() == ID_symbol)
    return true;
  if(expression.id() == ID_member)
    return direct_product_lvalue(to_member_expr(expression).struct_op());
  if(expression.id() == ID_index)
    return direct_product_lvalue(to_index_expr(expression).array());
  return false;
}

bool exact_product_lvalue(const exprt &input)
{
  const exprt &expression = skip_typecast(input);
  if(expression.id() == ID_symbol)
    return true;
  if(expression.id() == ID_member)
    return exact_product_lvalue(to_member_expr(expression).struct_op());
  if(expression.id() == ID_index)
    return
      skip_typecast(to_index_expr(expression).index()).id() == ID_constant &&
      exact_product_lvalue(to_index_expr(expression).array());
  return false;
}

const exprt *direct_product_root_symbol(const exprt &input)
{
  const exprt &expression = skip_typecast(input);
  if(expression.id() == ID_symbol)
    return &expression;
  if(expression.id() == ID_member)
    return direct_product_root_symbol(to_member_expr(expression).struct_op());
  if(expression.id() == ID_index)
    return direct_product_root_symbol(to_index_expr(expression).array());
  return nullptr;
}

bool same_exact_product_object(const exprt &left_input, const exprt &right_input)
{
  const exprt &left = skip_typecast(left_input);
  const exprt &right = skip_typecast(right_input);
  if(left.id() != right.id())
    return false;
  if(left.id() == ID_symbol)
    return
      to_symbol_expr(left).get_identifier() ==
      to_symbol_expr(right).get_identifier();
  if(left.id() == ID_member)
    return
      to_member_expr(left).get_component_name() ==
        to_member_expr(right).get_component_name() &&
      same_exact_product_object(
        to_member_expr(left).struct_op(), to_member_expr(right).struct_op());
  if(left.id() == ID_index)
  {
    const auto left_index = numeric_cast<mp_integer>(
      skip_typecast(to_index_expr(left).index()));
    const auto right_index = numeric_cast<mp_integer>(
      skip_typecast(to_index_expr(right).index()));
    return
      left_index.has_value() && right_index.has_value() &&
      *left_index == *right_index &&
      same_exact_product_object(
        to_index_expr(left).array(), to_index_expr(right).array());
  }
  return false;
}

// A product state can resolve an address such as &p->field after p has been
// assigned one exact tracked-object address.  Keep this deliberately narrower
// than arbitrary pointer arithmetic: unresolved pointers still make the
// concrete product step fail closed.
bool state_resolvable_product_lvalue_shape(const exprt &input)
{
  const exprt &expression = skip_typecast(input);
  if(expression.id() == ID_symbol)
    return true;
  if(expression.id() == ID_member)
    return state_resolvable_product_lvalue_shape(
      to_member_expr(expression).struct_op());
  if(expression.id() == ID_index)
    return
      state_resolvable_product_lvalue_shape(
        to_index_expr(expression).array()) &&
      !has_subexpr(to_index_expr(expression).index(), ID_dereference) &&
      !has_subexpr(to_index_expr(expression).index(), ID_if);
  if(expression.id() == ID_dereference)
  {
    const exprt &pointer = to_dereference_expr(expression).pointer();
    return
      state_resolvable_product_lvalue_shape(pointer) &&
      !has_subexpr(pointer, ID_if);
  }
  return false;
}

bool finite_product_byte_extract_lvalue_shape(const exprt &input)
{
  const exprt &expression = skip_typecast(input);
  if(
    expression.id() != ID_byte_extract_little_endian &&
    expression.id() != ID_byte_extract_big_endian)
    return false;
  const auto &extract = to_byte_extract_expr(expression);
  const typet &target_type = extract.type();
  return
    target_type.id() != ID_array && target_type.id() != ID_struct &&
    target_type.id() != ID_union && direct_product_lvalue(extract.op()) &&
    !has_subexpr(extract.offset(), ID_dereference) &&
    !has_subexpr(extract.offset(), ID_if);
}

bool has_invalid_product_object(const exprt &input)
{
  if(input.get_bool(ID_C_invalid_object))
    return true;
  for(const auto &operand : input.operands())
    if(has_invalid_product_object(operand))
      return true;
  return false;
}

bool state_resolvable_scalar_dereferences(
  const exprt &input,
  const namespacet &ns)
{
  const exprt &expression = skip_typecast(input);
  if(expression.id() == ID_dereference)
  {
    const typet &type = ns.follow(expression.type());
    if(
      type.id() == ID_array || type.id() == ID_struct ||
      type.id() == ID_union ||
      !state_resolvable_product_lvalue_shape(
        to_dereference_expr(expression).pointer()))
      return false;
  }
  for(const auto &operand : expression.operands())
    if(!state_resolvable_scalar_dereferences(operand, ns))
      return false;
  return true;
}

bool is_string_literal_address(const exprt &input)
{
  const exprt &expression = skip_typecast(input);
  if(expression.id() != ID_address_of)
    return false;
  const exprt &object = to_address_of_expr(expression).object();
  return
    object.id() == ID_index &&
    to_index_expr(object).array().id() == ID_string_constant &&
    to_index_expr(object).index().is_zero();
}

void normalize_product_expression(exprt &expression)
{
  for(auto &operand : expression.operands())
    normalize_product_expression(operand);
  if(
    std::getenv("DEAGLE_FINITE_PRODUCT_AUDIT") != nullptr &&
    expression.id() == ID_typecast && expression.operands().size() == 1 &&
    (skip_typecast(expression.op0()).id() == ID_string_constant ||
     is_string_literal_address(expression.op0())))
    std::cout << "V225_FINITE_PRODUCT_STRING_CAST type_id="
              << expression.type().id() << " type={"
              << expression.type().pretty() << "}\n";
  if(
    expression.id() == ID_typecast &&
    (expression.type().id() == ID_bool ||
     expression.type().id() == ID_c_bool) &&
    expression.operands().size() == 1 &&
    (skip_typecast(expression.op0()).id() == ID_string_constant ||
     is_string_literal_address(expression.op0())))
    expression = true_exprt();
}

using product_predecessorst = std::map<
  const goto_programt::instructiont *,
  std::vector<goto_programt::const_targett>>;

bool resolve_unique_product_pointer(
  const goto_programt &program,
  const product_predecessorst &predecessors,
  goto_programt::const_targett use,
  const exprt &input,
  std::set<std::pair<irep_idt, unsigned>> &resolving,
  exprt &result)
{
  const exprt &expression = skip_typecast(input);
  if(expression.id() == ID_address_of)
  {
    if(!direct_product_lvalue(to_address_of_expr(expression).object()))
      return false;
    result = expression;
    return true;
  }
  if(expression.id() != ID_symbol || expression.type().id() != ID_pointer)
    return false;
  const irep_idt identifier =
    to_symbol_expr(expression).get_identifier();
  const auto recursion_key =
    std::make_pair(identifier, use->location_number);
  if(!resolving.insert(recursion_key).second)
    return false;

  std::deque<goto_programt::const_targett> pending;
  const auto initial = predecessors.find(&*use);
  if(initial == predecessors.end())
  {
    resolving.erase(recursion_key);
    return false;
  }
  pending.insert(pending.end(), initial->second.begin(), initial->second.end());
  std::set<const goto_programt::instructiont *> visited;
  bool found = false;
  exprt common;
  while(!pending.empty())
  {
    const auto current = pending.front();
    pending.pop_front();
    if(!visited.insert(&*current).second)
      continue;
    if(
      current->is_decl() &&
      current->decl_symbol().get_identifier() == identifier)
    {
      resolving.erase(recursion_key);
      return false;
    }
    if(
      current->is_assign() &&
      skip_typecast(current->assign_lhs()).id() == ID_symbol &&
      to_symbol_expr(skip_typecast(current->assign_lhs())).get_identifier() ==
        identifier)
    {
      exprt candidate;
      if(!resolve_unique_product_pointer(
           program,
           predecessors,
           current,
           current->assign_rhs(),
           resolving,
           candidate))
      {
        resolving.erase(recursion_key);
        return false;
      }
      if(!found)
      {
        common = std::move(candidate);
        found = true;
      }
      else if(common != candidate)
      {
        resolving.erase(recursion_key);
        return false;
      }
      continue;
    }
    const auto previous = predecessors.find(&*current);
    if(previous == predecessors.end())
    {
      resolving.erase(recursion_key);
      return false;
    }
    pending.insert(
      pending.end(), previous->second.begin(), previous->second.end());
  }
  resolving.erase(recursion_key);
  if(!found)
    return false;
  result = std::move(common);
  return true;
}

bool rewrite_unique_product_dereferences(
  const goto_programt &program,
  const product_predecessorst &predecessors,
  goto_programt::const_targett use,
  exprt &expression)
{
  for(auto &operand : expression.operands())
    if(!rewrite_unique_product_dereferences(
         program, predecessors, use, operand))
      return false;
  if(expression.id() != ID_dereference)
    return true;
  std::set<std::pair<irep_idt, unsigned>> resolving;
  exprt pointer;
  if(!resolve_unique_product_pointer(
       program,
       predecessors,
       use,
       to_dereference_expr(expression).pointer(),
       resolving,
       pointer) ||
     pointer.id() != ID_address_of)
    return false;
  expression = to_address_of_expr(pointer).object();
  return direct_product_lvalue(expression);
}

bool resolve_product_expression(
  const irep_idt &function_id,
  const goto_programt &program,
  const product_predecessorst &predecessors,
  goto_programt::targett location,
  exprt &expression,
  const namespacet &ns,
  value_setst &value_sets)
{
  if(!has_subexpr(expression, ID_dereference))
    return true;
  const exprt original = expression;
  const exprt &original_root = skip_typecast(original);
  if(
    std::getenv("DEAGLE_FINITE_PRODUCT_AUDIT") != nullptr &&
    original_root.id() == ID_address_of &&
    !state_resolvable_product_lvalue_shape(
      to_address_of_expr(original_root).object()))
    std::cout << "V225_FINITE_PRODUCT_ADDRESS_SHAPE_REJECT entry="
              << function_id << " location=" << location->location_number
              << " original={" << from_expr(ns, function_id, original)
              << "}" << std::endl;
  if(
    original_root.id() == ID_address_of &&
    state_resolvable_product_lvalue_shape(
      to_address_of_expr(original_root).object()))
    return true;
  if(rewrite_unique_product_dereferences(
       program, predecessors, location, expression))
    return true;
  expression = original;
  dereference(function_id, location, expression, ns, value_sets);
  const exprt &resolved_root = skip_typecast(expression);
  if(
    has_invalid_product_object(expression) &&
    has_subexpr(original, ID_dereference) &&
    state_resolvable_scalar_dereferences(original, ns))
  {
    expression = original;
    return true;
  }
  if(
    resolved_root.get_bool(ID_C_invalid_object) &&
    original_root.id() == ID_dereference &&
    ns.follow(original.type()).id() != ID_array &&
    ns.follow(original.type()).id() != ID_struct &&
    ns.follow(original.type()).id() != ID_union)
  {
    expression = original;
    return true;
  }
  if(
    original_root.id() == ID_dereference &&
    (has_subexpr(expression, ID_dereference) ||
     has_subexpr(expression, ID_if)) &&
    skip_typecast(to_dereference_expr(original_root).pointer()).id() ==
      ID_symbol &&
    ns.follow(original.type()).id() != ID_array &&
    ns.follow(original.type()).id() != ID_struct &&
    ns.follow(original.type()).id() != ID_union)
  {
    expression = original;
    return true;
  }
  const bool resolved =
    !has_subexpr(expression, ID_dereference) &&
    !has_subexpr(expression, ID_if);
  if(
    !resolved && original_root.id() == ID_address_of &&
    state_resolvable_product_lvalue_shape(
      to_address_of_expr(original_root).object()))
  {
    expression = original;
    return true;
  }
  if(
    !resolved &&
    std::getenv("DEAGLE_FINITE_PRODUCT_AUDIT") != nullptr)
    std::cout << "V225_FINITE_PRODUCT_DEREFERENCE entry=" << function_id
              << " location=" << location->location_number
              << " original={"
              << from_expr(ns, function_id, original) << "} resolved={"
              << from_expr(ns, function_id, expression) << "}\n";
  return resolved;
}

bool lower_unique_product_dereferences(
  goto_modelt &model,
  const std::vector<irep_idt> &thread_ids)
{
  const namespacet ns(model.symbol_table);
  value_set_analysist value_set_analysis(ns);
  value_set_analysis(model.goto_functions);
  for(auto &function_entry : model.goto_functions.function_map)
  {
    if(
      std::find(
        thread_ids.begin(), thread_ids.end(), function_entry.first) ==
      thread_ids.end())
      continue;
    auto &program = function_entry.second.body;
    product_predecessorst predecessors;
    for(auto location = program.instructions.begin();
        location != program.instructions.end(); ++location)
      for(const auto successor : program.get_successors(location))
        predecessors[&*successor].push_back(location);
    for(auto location = program.instructions.begin();
        location != program.instructions.end(); ++location)
    {
      if(location->is_assign())
      {
        exprt lhs = location->assign_lhs();
        exprt rhs = location->assign_rhs();
        normalize_product_expression(lhs);
        normalize_product_expression(rhs);
        const bool lhs_resolved = resolve_product_expression(
          function_entry.first,
          program,
          predecessors,
          location,
          lhs,
          ns,
          value_set_analysis);
        const bool rhs_resolved =
          lhs_resolved && resolve_product_expression(
            function_entry.first,
            program,
            predecessors,
            location,
            rhs,
            ns,
            value_set_analysis);
        const bool direct_lhs =
          rhs_resolved &&
          (direct_product_lvalue(lhs) ||
           skip_typecast(lhs).id() == ID_dereference ||
           finite_product_byte_extract_lvalue_shape(lhs));
        if(!lhs_resolved || !rhs_resolved || !direct_lhs)
        {
          if(std::getenv("DEAGLE_FINITE_PRODUCT_AUDIT") != nullptr)
            std::cout << "V225_FINITE_PRODUCT_PREP_REJECT entry="
                      << function_entry.first << " location="
                      << location->location_number << " lhs_resolved="
                      << lhs_resolved << " rhs_resolved=" << rhs_resolved
                      << " direct_lhs=" << direct_lhs << " lhs={"
                      << from_expr(ns, function_entry.first, lhs)
                      << "} rhs={"
                      << from_expr(ns, function_entry.first, rhs) << "}"
                      << std::endl;
          return false;
        }
        auto &assignment = to_code_assign(location->code_nonconst());
        assignment.lhs() = std::move(lhs);
        assignment.rhs() = std::move(rhs);
      }
      else if(
        location->is_goto() || location->is_assume() ||
        location->is_assert())
      {
        exprt condition = location->condition();
        normalize_product_expression(condition);
        if(!resolve_product_expression(
             function_entry.first,
             program,
             predecessors,
             location,
             condition,
             ns,
             value_set_analysis))
          return false;
        location->condition_nonconst() = std::move(condition);
      }
    }
  }
  model.goto_functions.update();
  return true;
}

void collect_product_symbol_ids(
  const exprt &expression,
  std::set<irep_idt> &identifiers)
{
  if(expression.id() == ID_symbol)
    identifiers.insert(to_symbol_expr(expression).get_identifier());
  for(const auto &operand : expression.operands())
    collect_product_symbol_ids(operand, identifiers);
}

bool isolate_product_thread_locals(
  goto_modelt &model,
  const std::vector<irep_idt> &thread_ids)
{
  for(std::size_t thread_index = 0; thread_index < thread_ids.size();
      ++thread_index)
  {
    auto function = model.goto_functions.function_map.find(
      thread_ids[thread_index]);
    if(
      function == model.goto_functions.function_map.end() ||
      !function->second.body_available())
      return false;
    std::set<irep_idt> identifiers;
    for(const auto &instruction : function->second.body.instructions)
    {
      collect_product_symbol_ids(instruction.code(), identifiers);
      if(instruction.has_condition())
        collect_product_symbol_ids(instruction.condition(), identifiers);
    }
    replace_symbolt replacement;
    std::vector<symbolt> cloned_symbols;
    for(const auto &identifier : identifiers)
    {
      const auto original = model.symbol_table.symbols.find(identifier);
      if(
        original == model.symbol_table.symbols.end() ||
        !original->second.is_thread_local || original->second.is_type)
        continue;
      const irep_idt cloned_identifier =
        id2string(thread_ids[thread_index]) + "$deagle_product_t" +
        std::to_string(thread_index) + "$" + id2string(identifier);
      if(model.symbol_table.symbols.count(cloned_identifier) != 0)
        return false;
      symbolt cloned = original->second;
      cloned.name = cloned_identifier;
      cloned.base_name = cloned_identifier;
      cloned.pretty_name = cloned_identifier;
      cloned_symbols.push_back(cloned);
      replacement.set(
        symbol_exprt(identifier, original->second.type),
        symbol_exprt(cloned_identifier, original->second.type));
    }
    for(const auto &symbol : cloned_symbols)
    {
      if(model.symbol_table.add(symbol))
        return false;
    }
    for(auto &instruction : function->second.body.instructions)
    {
      replacement.replace(instruction.code_nonconst());
      if(instruction.has_condition())
        replacement.replace(instruction.condition_nonconst());
    }
  }
  model.goto_functions.update();
  return true;
}

bool product_thread_local_symbol(
  const exprt &expression,
  const namespacet &ns,
  irep_idt &identifier)
{
  const exprt &value = skip_typecast(expression);
  if(value.id() != ID_symbol)
    return false;
  identifier = to_symbol_expr(value).get_identifier();
  const symbolt *symbol = nullptr;
  return
    !ns.lookup(identifier, symbol) && !symbol->is_type &&
    symbol->is_thread_local && !symbol->type.get_bool(ID_C_volatile);
}

void collect_product_thread_local_ids(
  const exprt &expression,
  const namespacet &ns,
  std::set<irep_idt> &identifiers)
{
  irep_idt identifier;
  if(product_thread_local_symbol(expression, ns, identifier))
    identifiers.insert(identifier);
  for(const auto &operand : expression.operands())
    collect_product_thread_local_ids(operand, ns, identifiers);
}

bool expression_reads_product_shared(
  const exprt &expression,
  const namespacet &ns)
{
  if(expression.id() == ID_symbol)
  {
    const symbolt *symbol = nullptr;
    if(
      !ns.lookup(to_symbol_expr(expression).get_identifier(), symbol) &&
      !symbol->is_type && symbol->is_static_lifetime &&
      !symbol->is_thread_local)
      return true;
  }
  for(const auto &operand : expression.operands())
  {
    if(expression_reads_product_shared(operand, ns))
      return true;
  }
  return false;
}

bool eliminate_dead_product_locals(
  goto_modelt &model,
  const std::vector<irep_idt> &thread_ids,
  std::size_t &removed)
{
  const namespacet ns(model.symbol_table);
  removed = 0;
  for(const auto &thread_id : thread_ids)
  {
    auto function = model.goto_functions.function_map.find(thread_id);
    if(
      function == model.goto_functions.function_map.end() ||
      !function->second.body_available())
      return false;
    auto &program = function->second.body;
    std::vector<goto_programt::targett> locations;
    std::map<const goto_programt::instructiont *, std::size_t> indices;
    for(auto location = program.instructions.begin();
        location != program.instructions.end(); ++location)
    {
      indices.emplace(&*location, locations.size());
      locations.push_back(location);
    }
    std::vector<std::set<irep_idt>> live_in(locations.size());
    std::vector<std::set<irep_idt>> live_out(locations.size());
    bool changed = true;
    while(changed)
    {
      changed = false;
      for(std::size_t reverse = locations.size(); reverse != 0; --reverse)
      {
        const std::size_t index = reverse - 1;
        const auto location = locations[index];
        std::set<irep_idt> out;
        for(const auto successor : program.get_successors(location))
        {
          const auto found = indices.find(&*successor);
          if(found == indices.end())
            return false;
          out.insert(
            live_in[found->second].begin(), live_in[found->second].end());
        }
        std::set<irep_idt> in = out;
        irep_idt defined;
        if(location->is_assign())
          collect_product_thread_local_ids(
            location->assign_lhs(), ns, in);
        if(
          location->is_assign() &&
          product_thread_local_symbol(
            location->assign_lhs(), ns, defined))
          in.erase(defined);
        if(location->is_assign())
          collect_product_thread_local_ids(
            location->assign_rhs(), ns, in);
        if(location->has_condition())
          collect_product_thread_local_ids(
            location->condition(), ns, in);
        if(in != live_in[index] || out != live_out[index])
        {
          live_in[index] = std::move(in);
          live_out[index] = std::move(out);
          changed = true;
        }
      }
    }
    for(std::size_t index = 0; index < locations.size(); ++index)
    {
      const auto location = locations[index];
      if(!location->is_assign())
        continue;
      irep_idt defined;
      if(
        !product_thread_local_symbol(
          location->assign_lhs(), ns, defined) ||
        live_out[index].count(defined) != 0 ||
        expression_reads_product_shared(location->assign_rhs(), ns) ||
        has_subexpr(location->assign_rhs(), ID_side_effect) ||
        has_subexpr(location->assign_rhs(), ID_dereference))
        continue;
      location->turn_into_skip();
      ++removed;
    }
  }
  model.goto_functions.update();
  if(std::getenv("DEAGLE_FINITE_PRODUCT_AUDIT") != nullptr)
    std::cout << "V225_FINITE_PRODUCT_DEAD_LOCALS removed=" << removed
              << '\n';
  return true;
}

bool eliminate_dead_product_locals_fixedpoint(
  goto_modelt &model,
  const std::vector<irep_idt> &thread_ids)
{
  std::size_t total = 0;
  for(std::size_t pass = 0; pass < 64; ++pass)
  {
    std::size_t removed = 0;
    if(!eliminate_dead_product_locals(model, thread_ids, removed))
      return false;
    total += removed;
    if(removed == 0)
    {
      if(std::getenv("DEAGLE_FINITE_PRODUCT_AUDIT") != nullptr)
        std::cout << "V225_FINITE_PRODUCT_DEAD_LOCALS_FIXEDPOINT removed="
                  << total << " passes=" << pass + 1 << '\n';
      return true;
    }
  }
  return false;
}


struct thread_profilet
{
  irep_idt entry;
  std::size_t instructions = 0;
  std::size_t predicates = 0;
  std::size_t shared_scalar_writes = 0;
  std::size_t pointer_writes = 0;
  std::size_t atomic_blocks = 0;
  std::size_t remaining_calls = 0;
  bool atomic_balanced = true;
};

void collect_boolean_atoms(
  const exprt &expr,
  std::unordered_set<exprt, irep_hash> &predicates)
{
  if(expr.id() == ID_not && expr.operands().size() == 1)
  {
    collect_boolean_atoms(expr.op0(), predicates);
    return;
  }

  if(expr.id() == ID_and || expr.id() == ID_or || expr.id() == ID_implies)
  {
    for(const auto &operand : expr.operands())
      collect_boolean_atoms(operand, predicates);
    return;
  }

  if(expr.type().id() == ID_bool)
    predicates.insert(expr);

  for(const auto &operand : expr.operands())
  {
    if(operand.type().id() == ID_bool)
      collect_boolean_atoms(operand, predicates);
  }
}

bool get_thread_entry(const exprt &argument, irep_idt &entry)
{
  const exprt &without_cast = skip_typecast(argument);
  if(without_cast.id() != ID_address_of)
    return false;
  const exprt &object =
    skip_typecast(to_address_of_expr(without_cast).object());
  if(object.id() != ID_symbol)
    return false;
  entry = to_symbol_expr(object).get_identifier();
  return true;
}

bool get_addressed_symbol(const exprt &argument, irep_idt &identifier)
{
  const exprt &without_cast = skip_typecast(argument);
  if(without_cast.id() != ID_address_of)
    return false;
  const exprt &object =
    skip_typecast(to_address_of_expr(without_cast).object());
  if(object.id() != ID_symbol)
    return false;
  identifier = to_symbol_expr(object).get_identifier();
  return true;
}

bool get_direct_symbol(const exprt &argument, irep_idt &identifier)
{
  const exprt &without_cast = skip_typecast(argument);
  if(without_cast.id() != ID_symbol)
    return false;
  identifier = to_symbol_expr(without_cast).get_identifier();
  return true;
}

bool exact_constant_expression(const exprt &expression)
{
  if(expression.id() == ID_constant)
    return true;
  return expression.id() == ID_typecast && expression.operands().size() == 1 &&
         exact_constant_expression(expression.op0());
}

bool materialize_bounded_thread_instances(
  goto_modelt &model,
  std::set<irep_idt> &materialized_entries,
  std::string &reason)
{
  auto main = model.goto_functions.function_map.find("main");
  if(
    main == model.goto_functions.function_map.end() ||
    !main->second.body_available())
  {
    reason = "materialize_missing_main";
    return false;
  }

  const namespacet ns(model.symbol_table);
  std::map<irep_idt, exprt> constants;
  std::map<std::string, irep_idt> handle_entries;
  std::size_t instance = 0;

  auto evaluate =
    [&](exprt value)
    {
      replace_symbolt replacement;
      for(const auto &constant : constants)
      {
        const symbolt *symbol = nullptr;
        if(ns.lookup(constant.first, symbol))
          continue;
        replacement.set(
          symbol_exprt(constant.first, symbol->type),
          constant.second);
      }
      replacement.replace(value);
      return simplify_expr(std::move(value), ns);
    };
  auto handle_key =
    [&](const exprt &argument, bool addressed)
    {
      exprt value = evaluate(argument);
      const exprt &stripped = skip_typecast(value);
      if(!addressed)
        value = address_of_exprt(stripped);
      value = simplify_expr(std::move(value), ns);
      return from_expr(ns, "", value);
    };

  for(auto instruction = main->second.body.instructions.begin();
      instruction != main->second.body.instructions.end(); ++instruction)
  {
    if(instruction->is_assign())
    {
      const exprt &lhs = skip_typecast(instruction->assign_lhs());
      if(lhs.id() == ID_symbol)
      {
        const irep_idt identifier =
          to_symbol_expr(lhs).get_identifier();
        exprt rhs = evaluate(instruction->assign_rhs());
        if(rhs.id() == ID_constant)
          constants[identifier] = std::move(rhs);
        else
          constants.erase(identifier);
      }
    }

    if(!instruction->is_function_call())
      continue;
    const exprt &called =
      skip_typecast(instruction->call_function());
    if(called.id() != ID_symbol)
      continue;
    const irep_idt callee =
      to_symbol_expr(called).get_identifier();
    if(callee == "pthread_create")
    {
      if(instruction->call_arguments().size() < 3)
      {
        reason = "materialize_create_arguments";
        return false;
      }
      irep_idt original_entry;
      if(!get_thread_entry(
           instruction->call_arguments()[2], original_entry))
      {
        reason = "materialize_create_entry";
        return false;
      }
      const auto original_function =
        model.goto_functions.function_map.find(original_entry);
      const auto original_symbol =
        model.symbol_table.symbols.find(original_entry);
      if(
        original_function == model.goto_functions.function_map.end() ||
        !original_function->second.body_available() ||
        original_symbol == model.symbol_table.symbols.end())
      {
        reason = "materialize_worker";
        return false;
      }

      const irep_idt cloned_entry =
        id2string(original_entry) + "$deagle_instance_" +
        std::to_string(instance++);
      if(
        model.goto_functions.function_map.count(cloned_entry) != 0 ||
        model.symbol_table.symbols.count(cloned_entry) != 0)
      {
        reason = "materialize_duplicate";
        return false;
      }

      auto &clone =
        model.goto_functions.function_map[cloned_entry];
      clone.copy_from(original_function->second);
      symbolt cloned_function_symbol = original_symbol->second;
      cloned_function_symbol.name = cloned_entry;
      cloned_function_symbol.base_name = cloned_entry;
      cloned_function_symbol.pretty_name = cloned_entry;
      if(model.symbol_table.add(cloned_function_symbol))
      {
        reason = "materialize_function_symbol";
        return false;
      }

      std::vector<std::pair<symbol_exprt, symbol_exprt>> renamings;
      const std::string local_prefix =
        id2string(original_entry) + "::";
      std::vector<symbolt> local_symbols;
      for(const auto &symbol_entry : model.symbol_table.symbols)
      {
        const std::string identifier =
          id2string(symbol_entry.first);
        if(identifier.rfind(local_prefix, 0) != 0)
          continue;
        symbolt cloned_local = symbol_entry.second;
        const irep_idt cloned_identifier =
          id2string(cloned_entry) +
          identifier.substr(id2string(original_entry).size());
        cloned_local.name = cloned_identifier;
        cloned_local.base_name = cloned_identifier;
        cloned_local.pretty_name = cloned_identifier;
        local_symbols.push_back(cloned_local);
        renamings.emplace_back(
          symbol_exprt(symbol_entry.first, symbol_entry.second.type),
          symbol_exprt(cloned_identifier, symbol_entry.second.type));
      }
      for(const auto &symbol : local_symbols)
      {
        if(model.symbol_table.add(symbol))
        {
          reason = "materialize_local_symbol";
          return false;
        }
      }
      if(
        instruction->call_arguments().size() < 4 ||
        cloned_function_symbol.type.id() != ID_code ||
        to_code_type(cloned_function_symbol.type).parameters().size() != 1)
      {
        reason = "materialize_worker_argument";
        return false;
      }
      const irep_idt original_parameter =
        to_code_type(cloned_function_symbol.type)
          .parameters()
          .front()
          .get_identifier();
      irep_idt cloned_parameter_identifier;
      typet cloned_parameter_type;
      bool cloned_parameter_found = false;
      for(const auto &renaming : renamings)
      {
        if(renaming.first.get_identifier() == original_parameter)
        {
          cloned_parameter_identifier = renaming.second.get_identifier();
          cloned_parameter_type = renaming.second.type();
          cloned_parameter_found = true;
          break;
        }
      }
      exprt concrete_argument =
        evaluate(instruction->call_arguments()[3]);
      if(
        !cloned_parameter_found ||
        !exact_constant_expression(concrete_argument) ||
        concrete_argument.type() != cloned_parameter_type)
      {
        reason = "materialize_worker_argument_not_constant";
        return false;
      }
      const symbol_exprt cloned_parameter(
        cloned_parameter_identifier, cloned_parameter_type);
      for(auto &clone_instruction : clone.body.instructions)
      {
        for(const auto &renaming : renamings)
        {
          replace_expr(
            renaming.first, renaming.second,
            clone_instruction.code_nonconst());
          if(clone_instruction.has_condition())
            replace_expr(
              renaming.first, renaming.second,
              clone_instruction.condition_nonconst());
        }
      }
      if(clone.body.instructions.empty())
      {
        reason = "materialize_empty_worker";
        return false;
      }
      clone.body.insert_before(
        clone.body.instructions.begin(),
        goto_programt::make_assignment(
          cloned_parameter,
          concrete_argument,
          clone.body.instructions.begin()->source_location()));
      if(std::getenv("DEAGLE_FINITE_PRODUCT_AUDIT") != nullptr)
        std::cout << "V302_THREAD_INSTANCE_ARGUMENT entry=" << cloned_entry
                  << " value={" << from_expr(ns, "", concrete_argument)
                  << "}\n";

      instruction->call_arguments()[2] =
        address_of_exprt(
          symbol_exprt(cloned_entry, cloned_function_symbol.type));
      const std::string key =
        handle_key(instruction->call_arguments()[0], true);
      if(std::getenv("DEAGLE_FINITE_PRODUCT_AUDIT") != nullptr)
        std::cout << "V302_THREAD_INSTANCE_CREATE key={" << key
                  << "} entry=" << cloned_entry << '\n';
      if(key.empty() || !handle_entries.emplace(key, cloned_entry).second)
      {
        reason = "materialize_create_handle";
        return false;
      }
      materialized_entries.insert(cloned_entry);
    }
    else if(callee == "pthread_join")
    {
      if(instruction->call_arguments().empty())
      {
        reason = "materialize_join_arguments";
        return false;
      }
      const std::string key =
        handle_key(instruction->call_arguments()[0], false);
      if(std::getenv("DEAGLE_FINITE_PRODUCT_AUDIT") != nullptr)
        std::cout << "V302_THREAD_INSTANCE_JOIN key={" << key << "}\n";
      const auto entry = handle_entries.find(key);
      if(entry == handle_entries.end())
      {
        reason = "materialize_join_handle";
        return false;
      }
      instruction->source_location_nonconst().set(
        "v49_join_entry", entry->second);
    }
  }
  if(materialized_entries.empty())
  {
    reason = "materialize_no_instances";
    return false;
  }
  model.goto_functions.update();
  if(std::getenv("DEAGLE_FINITE_PRODUCT_AUDIT") != nullptr)
    std::cout << "V302_BOUNDED_THREAD_INSTANCES applied=1 instances="
              << materialized_entries.size() << '\n';
  return true;
}


bool instruction_is_in_cycle(
  const goto_programt &program,
  goto_programt::const_targett target)
{
  std::deque<goto_programt::const_targett> pending;
  for(const auto successor : program.get_successors(target))
    pending.push_back(successor);
  std::set<const goto_programt::instructiont *> visited;
  while(!pending.empty())
  {
    const auto current = pending.front();
    pending.pop_front();
    if(current == target)
      return true;
    if(!visited.insert(&*current).second)
      continue;
    for(const auto successor : program.get_successors(current))
      pending.push_back(successor);
  }
  return false;
}

std::set<irep_idt> find_thread_entries(
  const goto_modelt &model,
  std::size_t *instance_count = nullptr,
  std::map<irep_idt, bool> *may_have_multiple_instances = nullptr)
{
  std::set<irep_idt> result;
  std::map<irep_idt, std::size_t> static_create_counts;
  const auto main_it = model.goto_functions.function_map.find("main");
  if(main_it == model.goto_functions.function_map.end())
    return result;

  const auto &program = main_it->second.body;
  for(auto instruction = program.instructions.begin();
      instruction != program.instructions.end(); ++instruction)
  {
    if(!instruction->is_function_call())
      continue;
    const exprt &function = skip_typecast(instruction->call_function());
    if(
      function.id() != ID_symbol ||
      to_symbol_expr(function).get_identifier() != "pthread_create")
      continue;
    const auto &arguments = instruction->call_arguments();
    if(arguments.size() < 3)
      continue;
    irep_idt entry;
    if(get_thread_entry(arguments[2], entry))
    {
      result.insert(entry);
      ++static_create_counts[entry];
      if(
        may_have_multiple_instances != nullptr &&
        instruction_is_in_cycle(program, instruction))
        (*may_have_multiple_instances)[entry] = true;
      if(instance_count != nullptr)
        ++*instance_count;
    }
  }
  if(may_have_multiple_instances != nullptr)
  {
    for(const auto &entry : result)
      (*may_have_multiple_instances)[entry] =
        (*may_have_multiple_instances)[entry] ||
        static_create_counts[entry] > 1;
  }
  return result;
}

bool is_ignored_synchronization_call(const irep_idt &identifier)
{
  return identifier == "pthread_mutex_lock" ||
         identifier == "pthread_mutex_unlock" ||
         identifier == "pthread_mutex_init" ||
         identifier == "pthread_mutex_destroy" ||
         identifier == "pthread_cond_wait" ||
         identifier == "pthread_cond_signal" ||
         identifier == "pthread_cond_broadcast" ||
         identifier == "pthread_cond_init" ||
         identifier == "pthread_cond_destroy" ||
         identifier == "pthread_create" || identifier == "pthread_join";
}

bool neutralize_synchronization_calls(
  goto_modelt &model,
  bool preserve_mutex_regions = false,
  std::string *failure_reason = nullptr)
{
  std::map<irep_idt, irep_idt> handle_entries;
  std::set<irep_idt> ambiguous_handles;
  const auto main_it = model.goto_functions.function_map.find("main");
  if(main_it != model.goto_functions.function_map.end())
  {
    for(auto &instruction : main_it->second.body.instructions)
    {
      if(!instruction.is_function_call())
        continue;
      const exprt &function = skip_typecast(instruction.call_function());
      if(
        function.id() != ID_symbol ||
        to_symbol_expr(function).get_identifier() != "pthread_create" ||
        instruction.call_arguments().size() < 3)
        continue;
      irep_idt handle;
      irep_idt entry;
      if(
        get_addressed_symbol(instruction.call_arguments()[0], handle) &&
        get_thread_entry(instruction.call_arguments()[2], entry))
      {
        if(handle_entries.find(handle) != handle_entries.end())
          ambiguous_handles.insert(handle);
        else
          handle_entries.emplace(handle, entry);
      }
    }
  }

  for(auto &function_entry : model.goto_functions.function_map)
  {
    std::vector<irep_idt> held_mutexes;
    for(auto &instruction : function_entry.second.body.instructions)
    {
      if(!instruction.is_function_call())
        continue;
      const exprt &function = skip_typecast(instruction.call_function());
      if(
        function.id() == ID_symbol &&
        is_ignored_synchronization_call(
          to_symbol_expr(function).get_identifier()))
      {
        const irep_idt &identifier =
          to_symbol_expr(function).get_identifier();
        if(
          preserve_mutex_regions &&
          (identifier == "pthread_mutex_lock" ||
           identifier == "pthread_mutex_unlock"))
        {
          irep_idt mutex;
          if(
            instruction.call_arguments().empty() ||
            !get_addressed_symbol(instruction.call_arguments()[0], mutex))
          {
            if(failure_reason != nullptr)
              *failure_reason = "affine_unresolved_mutex";
            return false;
          }
          if(identifier == "pthread_mutex_lock")
          {
            if(!held_mutexes.empty())
            {
              if(failure_reason != nullptr)
                *failure_reason = "affine_nested_mutex";
              return false;
            }
            held_mutexes.push_back(mutex);
            const source_locationt source_location =
              instruction.source_location();
            instruction =
              goto_programt::make_atomic_begin(source_location);
          }
          else
          {
            if(held_mutexes.empty() || held_mutexes.back() != mutex)
            {
              if(failure_reason != nullptr)
                *failure_reason = "affine_unbalanced_mutex";
              return false;
            }
            held_mutexes.pop_back();
            const source_locationt source_location =
              instruction.source_location();
            instruction = goto_programt::make_atomic_end(source_location);
          }
          instruction.source_location_nonconst().set(
            "v217_mutex", mutex);
          continue;
        }
        if(preserve_mutex_regions && identifier == "pthread_cond_wait")
        {
          if(failure_reason != nullptr)
            *failure_reason = "affine_cond_wait_requires_phase_summary";
          return false;
        }
        if(identifier == "pthread_create")
        {
          instruction.source_location_nonconst().set("v49_thread_spawn", true);
          if(instruction.call_arguments().size() >= 3)
          {
            irep_idt entry;
            if(get_thread_entry(instruction.call_arguments()[2], entry))
              instruction.source_location_nonconst().set(
                "v49_thread_entry", entry);
          }
        }
        else if(identifier == "pthread_join")
        {
          const irep_idt existing_entry =
            instruction.source_location().get("v49_join_entry");
          if(existing_entry != irep_idt())
          {
            instruction.turn_into_skip();
            continue;
          }
          irep_idt handle;
          if(
            !instruction.call_arguments().empty() &&
            get_direct_symbol(instruction.call_arguments()[0], handle) &&
            ambiguous_handles.find(handle) == ambiguous_handles.end() &&
            handle_entries.find(handle) != handle_entries.end())
            instruction.source_location_nonconst().set(
              "v49_join_entry", handle_entries[handle]);
          else
            instruction.source_location_nonconst().set(
              "v49_unresolved_join", true);
        }
        instruction.turn_into_skip();
      }
    }
    if(preserve_mutex_regions && !held_mutexes.empty())
    {
      if(failure_reason != nullptr)
        *failure_reason = "affine_unbalanced_mutex";
      return false;
    }
  }
  model.goto_functions.update();
  return true;
}

bool is_shared_scalar(const exprt &expr, const namespacet &ns)
{
  if(expr.id() != ID_symbol || expr.type().id() == ID_pointer)
    return false;
  const symbolt *symbol = nullptr;
  if(ns.lookup(to_symbol_expr(expr).get_identifier(), symbol))
    return false;
  return symbol->is_static_lifetime && !symbol->is_type;
}

void collect_shared_scalar_identifiers(
  const exprt &expr,
  const namespacet &ns,
  std::set<irep_idt> &result)
{
  const exprt &stripped = skip_typecast(expr);
  if(stripped.id() == ID_symbol && is_shared_scalar(stripped, ns))
    result.insert(to_symbol_expr(stripped).get_identifier());
  for(const auto &operand : expr.operands())
    collect_shared_scalar_identifiers(operand, ns, result);
}

std::set<irep_idt> instruction_shared_scalar_identifiers(
  const goto_programt::instructiont &instruction,
  const namespacet &ns)
{
  std::set<irep_idt> result;
  instruction.apply(
    [&ns, &result](const exprt &expr) {
      collect_shared_scalar_identifiers(expr, ns, result);
    });
  return result;
}

bool validate_mutex_ownership(
  const goto_modelt &model,
  const std::vector<irep_idt> &thread_ids,
  std::string &reason,
  std::size_t &region_count,
  std::size_t &protected_objects)
{
  const namespacet ns(model.symbol_table);
  std::map<irep_idt, irep_idt> object_mutex;
  std::set<const goto_programt::instructiont *> main_concurrent_locations;

  if(!thread_ids.empty())
  {
    const auto main_function =
      model.goto_functions.function_map.find(thread_ids.front());
    if(
      main_function != model.goto_functions.function_map.end() &&
      main_function->second.body_available())
    {
      const auto &program = main_function->second.body;
      for(auto spawn = program.instructions.begin();
          spawn != program.instructions.end(); ++spawn)
      {
        if(!spawn->source_location().get_bool("v49_thread_spawn"))
          continue;
        const irep_idt &entry =
          spawn->source_location().get("v49_thread_entry");
        if(entry == irep_idt())
          continue;
        std::vector<goto_programt::const_targett> work;
        const auto successors = program.get_successors(spawn);
        work.insert(work.end(), successors.begin(), successors.end());
        std::set<const goto_programt::instructiont *> visited;
        while(!work.empty())
        {
          const auto location = work.back();
          work.pop_back();
          if(!visited.insert(&*location).second)
            continue;
          if(location->source_location().get("v49_join_entry") == entry)
            continue;
          main_concurrent_locations.insert(&*location);
          const auto next = program.get_successors(location);
          work.insert(work.end(), next.begin(), next.end());
        }
      }
    }
  }

  struct accesst
  {
    irep_idt object;
    irep_idt mutex;
    bool concurrent;
  };
  std::vector<accesst> accesses;

  for(std::size_t thread_index = 0; thread_index < thread_ids.size();
      ++thread_index)
  {
    const auto function =
      model.goto_functions.function_map.find(thread_ids[thread_index]);
    if(
      function == model.goto_functions.function_map.end() ||
      !function->second.body_available())
      continue;
    const auto &program = function->second.body;
    irep_idt held_mutex;
    for(auto instruction = program.instructions.begin();
        instruction != program.instructions.end(); ++instruction)
    {
      irep_idt ownership_scope =
        instruction->source_location().get("deagle_lock_ownership_scope");
      if(ownership_scope == irep_idt())
        ownership_scope =
          instruction->source_location().get("v217_mutex");
      if(
        instruction->is_atomic_begin() &&
        ownership_scope != irep_idt())
      {
        if(held_mutex != irep_idt())
        {
          reason = "ownership_nested_mutex";
          return false;
        }
        held_mutex = ownership_scope;
        ++region_count;
        continue;
      }
      if(
        instruction->is_atomic_end() &&
        ownership_scope != irep_idt())
      {
        if(
          held_mutex == irep_idt() ||
          held_mutex != ownership_scope)
        {
          reason = "ownership_unbalanced_mutex";
          return false;
        }
        held_mutex = irep_idt();
        continue;
      }

      const bool concurrent =
        thread_index != 0 ||
        main_concurrent_locations.find(&*instruction) !=
          main_concurrent_locations.end();
      for(const auto &object :
          instruction_shared_scalar_identifiers(*instruction, ns))
      {
        accesses.push_back({object, held_mutex, concurrent});
        if(held_mutex != irep_idt() && object != held_mutex)
        {
          const auto inserted = object_mutex.emplace(object, held_mutex);
          if(!inserted.second && inserted.first->second != held_mutex)
          {
            reason = "ownership_multiple_mutexes";
            protected_objects = object_mutex.size();
            return false;
          }
        }
      }
    }
    if(held_mutex != irep_idt())
    {
      reason = "ownership_unbalanced_mutex";
      protected_objects = object_mutex.size();
      return false;
    }
  }

  for(const auto &access : accesses)
  {
    const auto protected_by = object_mutex.find(access.object);
    if(
      protected_by != object_mutex.end() && access.concurrent &&
      access.mutex != protected_by->second)
    {
      reason = "ownership_external_protected_access";
      protected_objects = object_mutex.size();
      return false;
    }
  }
  protected_objects = object_mutex.size();
  return true;
}

bool expression_contains_identifier(
  const exprt &expr,
  const irep_idt &identifier)
{
  if(
    expr.id() == ID_symbol &&
    to_symbol_expr(expr).get_identifier() == identifier)
    return true;
  for(const auto &operand : expr.operands())
  {
    if(expression_contains_identifier(operand, identifier))
      return true;
  }
  return false;
}

void collect_expression_identifiers(
  const exprt &expr,
  std::set<irep_idt> &identifiers)
{
  if(expr.id() == ID_symbol)
    identifiers.insert(to_symbol_expr(expr).get_identifier());
  for(const auto &operand : expr.operands())
    collect_expression_identifiers(operand, identifiers);
}

bool expression_contains_unsigned_max(
  const exprt &expr,
  const typet &type)
{
  if(expr.id() == ID_constant)
  {
    const auto value = numeric_cast<mp_integer>(expr);
    if(value.has_value() && type.id() == ID_unsignedbv)
    {
      const auto width = to_bitvector_type(type).get_width();
      if(*value == -1 || *value == power(2, width) - 1)
        return true;
    }
    const std::string bits =
      id2string(to_constant_expr(expr).get_value());
    if(
      !bits.empty() &&
      std::all_of(
        bits.begin(), bits.end(), [](char bit) { return bit == '1'; }))
      return true;
  }
  for(const auto &operand : expr.operands())
  {
    if(expression_contains_unsigned_max(operand, type))
      return true;
  }
  return false;
}

bool exact_unit_increment(
  const exprt &rhs,
  const irep_idt &identifier)
{
  const exprt &stripped = skip_typecast(rhs);
  if(stripped.id() != ID_plus || stripped.operands().size() != 2)
    return false;
  bool has_identifier = false;
  bool has_one = false;
  for(const auto &operand : stripped.operands())
  {
    const exprt &term = skip_typecast(operand);
    if(
      term.id() == ID_symbol &&
      to_symbol_expr(term).get_identifier() == identifier)
      has_identifier = true;
    const auto value = numeric_cast<mp_integer>(term);
    if(value.has_value() && *value == 1)
      has_one = true;
  }
  return has_identifier && has_one;
}

bool exact_ticket_admission_equality(const exprt &condition)
{
  const exprt &stripped = skip_typecast(condition);
  if(stripped.id() == ID_equal)
    return true;
  return stripped.id() == ID_not &&
         stripped.operands().size() == 1 &&
         skip_typecast(stripped.op0()).id() == ID_notequal;
}

struct ticket_allocator_summaryt
{
  irep_idt function;
  irep_idt counter;
  irep_idt pointer_parameter;
};

bool recognize_ticket_allocator(
  const irep_idt &function_id,
  const goto_functionst::goto_functiont &function,
  ticket_allocator_summaryt &summary)
{
  if(!function.body_available())
    return false;
  bool inside_atomic = false;
  bool saw_begin = false;
  bool saw_end = false;
  bool saw_no_wrap = false;
  bool saw_pointer_copy = false;
  bool saw_increment = false;
  irep_idt counter;
  irep_idt pointer_parameter;
  typet counter_type;
  std::vector<exprt> guard_conditions;

  for(const auto &instruction : function.body.instructions)
  {
    if(instruction.is_atomic_begin())
    {
      if(inside_atomic || saw_begin)
        return false;
      inside_atomic = true;
      saw_begin = true;
      continue;
    }
    if(instruction.is_atomic_end())
    {
      if(!inside_atomic || saw_end)
        return false;
      inside_atomic = false;
      saw_end = true;
      continue;
    }
    if(!inside_atomic)
      continue;
    if(instruction.is_function_call())
    {
      if(instruction.call_arguments().size() != 1)
        return false;
      const exprt &condition = instruction.call_arguments().front();
      guard_conditions.push_back(condition);
      saw_no_wrap = true;
      continue;
    }
    if(!instruction.is_assign())
      continue;
    if(instruction.assign_lhs().id() == ID_dereference)
    {
      const exprt &pointer =
        skip_typecast(to_dereference_expr(instruction.assign_lhs()).pointer());
      const exprt &rhs = skip_typecast(instruction.assign_rhs());
      if(pointer.id() != ID_symbol || rhs.id() != ID_symbol)
        return false;
      pointer_parameter = to_symbol_expr(pointer).get_identifier();
      counter = to_symbol_expr(rhs).get_identifier();
      counter_type = rhs.type();
      saw_pointer_copy = true;
      continue;
    }
    if(instruction.assign_lhs().id() == ID_symbol)
    {
      const irep_idt &lhs =
        to_symbol_expr(instruction.assign_lhs()).get_identifier();
      if(counter == irep_idt() || lhs != counter ||
         !exact_unit_increment(instruction.assign_rhs(), counter))
        return false;
      saw_increment = true;
    }
  }
  if(
    inside_atomic || !saw_begin || !saw_end || !saw_no_wrap ||
    !saw_pointer_copy || !saw_increment)
  {
    if(saw_begin)
      std::cout << "INTERFERENCE_TICKET_ALLOCATOR_AUDIT function="
                << function_id << " begin=" << saw_begin
                << " end=" << saw_end << " guard=" << saw_no_wrap
                << " copy=" << saw_pointer_copy
                << " increment=" << saw_increment << '\n';
    return false;
  }

  for(const auto &condition : guard_conditions)
  {
    if(
      expression_contains_identifier(condition, counter) &&
      expression_contains_unsigned_max(condition, counter_type))
    {
      summary = {function_id, counter, pointer_parameter};
      return true;
    }
  }
  std::cout << "INTERFERENCE_TICKET_ALLOCATOR_AUDIT function="
            << function_id << " structural=1 nowrap=0 counter="
            << counter << " counter_type=" << counter_type.id();
  for(const auto &condition : guard_conditions)
    std::cout << " guard_expr=" << condition.pretty();
  std::cout << '\n';
  return false;
}

bool rewrite_ticket_worker(
  goto_programt &program,
  const ticket_allocator_summaryt &allocator,
  const namespacet &ns,
  std::string &reason,
  std::size_t &region_count)
{
  for(auto call = program.instructions.begin();
      call != program.instructions.end(); ++call)
  {
    if(!call->is_function_call())
      continue;
    const exprt &function = skip_typecast(call->call_function());
    if(
      function.id() != ID_symbol ||
      to_symbol_expr(function).get_identifier() != allocator.function ||
      call->call_arguments().size() != 1)
      continue;
    irep_idt local_ticket;
    if(!get_addressed_symbol(call->call_arguments().front(), local_ticket))
    {
      reason = "ticket_allocator_argument";
      return false;
    }

    auto spin_begin = std::next(call);
    while(
      spin_begin != program.instructions.end() &&
      !spin_begin->is_atomic_begin())
      ++spin_begin;
    if(spin_begin == program.instructions.end())
    {
      reason = "ticket_spin_begin";
      return false;
    }
    auto spin_end = std::next(spin_begin);
    while(
      spin_end != program.instructions.end() &&
      !spin_end->is_atomic_end())
      ++spin_end;
    if(spin_end == program.instructions.end())
    {
      reason = "ticket_spin_end";
      return false;
    }

    goto_programt::targett admission = program.instructions.end();
    goto_programt::targett increment_slot = program.instructions.end();
    irep_idt serving;
    for(auto current = std::next(spin_begin); current != spin_end; ++current)
    {
      if(current->is_assign() || current->is_function_call())
      {
        reason = "ticket_spin_side_effect";
        return false;
      }
      if(!current->is_goto())
        continue;
      std::set<irep_idt> identifiers;
      collect_expression_identifiers(current->condition(), identifiers);
      if(
        identifiers.find(local_ticket) == identifiers.end() ||
        identifiers.size() != 2 ||
        !exact_ticket_admission_equality(current->condition()))
      {
        if(increment_slot != program.instructions.end())
        {
          reason = "ticket_spin_shape";
          return false;
        }
        increment_slot = current;
        continue;
      }
      for(const auto &identifier : identifiers)
      {
        if(identifier != local_ticket)
          serving = identifier;
      }
      admission = current;
    }
    if(
      admission == program.instructions.end() ||
      increment_slot == program.instructions.end() ||
      serving == irep_idt())
    {
      reason = "ticket_admission_equality";
      return false;
    }

    auto release_begin = std::next(spin_end);
    while(
      release_begin != program.instructions.end() &&
      !release_begin->is_atomic_begin())
      ++release_begin;
    if(release_begin == program.instructions.end())
    {
      reason = "ticket_release_begin";
      return false;
    }
    auto release_end = std::next(release_begin);
    while(
      release_end != program.instructions.end() &&
      !release_end->is_atomic_end())
      ++release_end;
    if(release_end == program.instructions.end())
    {
      reason = "ticket_release_end";
      return false;
    }
    std::size_t release_assignments = 0;
    for(auto current = std::next(release_begin);
        current != release_end; ++current)
    {
      if(!current->is_assign())
      {
        if(!current->is_skip())
        {
          reason = "ticket_release_instruction";
          return false;
        }
        continue;
      }
      if(
        current->assign_lhs().id() != ID_symbol ||
        to_symbol_expr(current->assign_lhs()).get_identifier() != serving ||
        !exact_unit_increment(current->assign_rhs(), serving))
      {
        reason = "ticket_release_increment";
        return false;
      }
      ++release_assignments;
    }
    if(release_assignments != 1)
    {
      reason = "ticket_release_count";
      return false;
    }

    const symbolt *local_symbol = nullptr;
    const symbolt *counter_symbol = nullptr;
    if(
      ns.lookup(local_ticket, local_symbol) ||
      ns.lookup(allocator.counter, counter_symbol) ||
      local_symbol->type.id() != ID_unsignedbv ||
      counter_symbol->type.id() != ID_unsignedbv ||
      local_symbol->type != counter_symbol->type)
    {
      reason = "ticket_counter_types";
      return false;
    }
    const symbol_exprt local_expr(local_ticket, local_symbol->type);
    const symbol_exprt counter_expr(
      allocator.counter, counter_symbol->type);

    const source_locationt admission_location = admission->source_location();
    exprt admission_condition = admission->condition();
    const auto width =
      to_bitvector_type(counter_symbol->type).get_width();
    const exprt no_wrap = notequal_exprt(
      local_expr,
      from_integer(power(2, width) - 1, counter_symbol->type));
    *admission = goto_programt::make_assumption(
      and_exprt(admission_condition, no_wrap), admission_location);
    source_locationt begin_location = call->source_location();
    begin_location.set("deagle_lock_ownership_scope", serving);
    *call = goto_programt::make_atomic_begin(begin_location);
    *spin_begin = goto_programt::make_assignment(
      local_expr, counter_expr, spin_begin->source_location());
    *increment_slot = goto_programt::make_assignment(
      counter_expr,
      plus_exprt(
        counter_expr,
        from_integer(1, counter_symbol->type)),
      increment_slot->source_location());
    spin_end->turn_into_skip();
    release_begin->turn_into_skip();
    source_locationt end_location = release_end->source_location();
    end_location.set("deagle_lock_ownership_scope", serving);
    *release_end = goto_programt::make_atomic_end(end_location);
    ++region_count;
    return true;
  }
  return false;
}

bool rewrite_ticket_lock_ownership(
  goto_modelt &model,
  std::string &reason,
  std::size_t &region_count)
{
  const namespacet ns(model.symbol_table);
  std::vector<ticket_allocator_summaryt> allocators;
  for(const auto &function : model.goto_functions.function_map)
  {
    ticket_allocator_summaryt summary;
    if(recognize_ticket_allocator(function.first, function.second, summary))
      allocators.push_back(std::move(summary));
  }
  for(const auto &allocator : allocators)
  {
    for(auto &function : model.goto_functions.function_map)
    {
      if(rewrite_ticket_worker(
           function.second.body, allocator, ns, reason, region_count))
      {
        model.goto_functions.update();
        std::cout << "INTERFERENCE_TICKET_OWNERSHIP regions="
                  << region_count << " allocator=" << allocator.function
                  << " counter=" << allocator.counter << '\n';
        return true;
      }
      if(!reason.empty())
        return false;
    }
  }
  reason = "ticket_protocol_not_found";
  return false;
}

bool uses_only_shared_symbols(const exprt &expr, const namespacet &ns)
{
  if(expr.id() == ID_symbol)
  {
    const symbolt *symbol = nullptr;
    const irep_idt &identifier = to_symbol_expr(expr).get_identifier();
    if(ns.lookup(identifier, symbol))
      return id2string(identifier).find("__CPROVER_v49_array$") == 0 ||
             id2string(identifier).find("__CPROVER_v49_done$") == 0;
    return symbol->is_static_lifetime && !symbol->is_type;
  }
  for(const auto &operand : expr.operands())
  {
    if(!uses_only_shared_symbols(operand, ns))
      return false;
  }
  return true;
}

bool contains_symbol_identifier(const exprt &expr, const irep_idt &identifier)
{
  if(
    expr.id() == ID_symbol &&
    to_symbol_expr(expr).get_identifier() == identifier)
    return true;
  for(const auto &operand : expr.operands())
  {
    if(contains_symbol_identifier(operand, identifier))
      return true;
  }
  return false;
}

bool is_abstract_noop_other(const goto_programt::instructiont &instruction)
{
  if(!instruction.is_other())
    return false;
  const irep_idt &statement = instruction.code().get_statement();
  if(statement == ID_output || statement == ID_fence)
    return true;
  if(statement == ID_expression)
  {
    const exprt &expression = to_code_expression(instruction.code()).expression();
    return !has_subexpr(expression, ID_side_effect);
  }
  return false;
}

struct immutable_arrayt
{
  symbol_exprt logical_array;
  typet element_type;
};

bool parse_direct_array_access(
  const exprt &expr,
  irep_idt &base_identifier,
  exprt &index)
{
  if(expr.id() != ID_dereference || expr.operands().size() != 1)
    return false;
  const exprt &pointer = skip_typecast(to_dereference_expr(expr).pointer());
  if(pointer.id() != ID_plus || pointer.operands().size() != 2)
    return false;

  const exprt *base = nullptr;
  const exprt *offset = nullptr;
  for(const auto &operand : pointer.operands())
  {
    const exprt &candidate = skip_typecast(operand);
    if(candidate.id() == ID_symbol && candidate.type().id() == ID_pointer)
      base = &candidate;
    else
      offset = &operand;
  }
  if(base == nullptr || offset == nullptr)
    return false;

  base_identifier = to_symbol_expr(*base).get_identifier();
  index = *offset;
  return true;
}

bool collect_immutable_arrays(
  const exprt &expr,
  const std::map<irep_idt, irep_idt> &aliases,
  std::map<irep_idt, immutable_arrayt> &arrays,
  std::string &reason)
{
  if(expr.id() == ID_dereference)
  {
    irep_idt base;
    exprt index;
    if(parse_direct_array_access(expr, base, index))
    {
      const auto alias = aliases.find(base);
      if(alias == aliases.end())
        return true;
      base = alias->second;
      const auto existing = arrays.find(base);
      if(existing == arrays.end())
      {
        const array_typet type(
          expr.type(), infinity_exprt(index.type()));
        arrays.emplace(
          base,
          immutable_arrayt{
            symbol_exprt(
              "__CPROVER_v49_array$" + id2string(base), type),
            expr.type()});
      }
      else if(existing->second.element_type != expr.type())
      {
        reason = "inconsistent_array_element_type";
        return false;
      }
    }
  }
  for(const auto &operand : expr.operands())
  {
    if(!collect_immutable_arrays(operand, aliases, arrays, reason))
      return false;
  }
  return true;
}

bool rewrite_immutable_array_reads(
  exprt &expr,
  const std::map<irep_idt, irep_idt> &aliases,
  const std::map<irep_idt, immutable_arrayt> &arrays,
  std::string &reason)
{
  for(auto &operand : expr.operands())
  {
    if(!rewrite_immutable_array_reads(operand, aliases, arrays, reason))
      return false;
  }
  if(expr.id() != ID_dereference)
    return true;
  irep_idt base;
  exprt index;
  if(!parse_direct_array_access(expr, base, index))
    return true;
  const auto alias = aliases.find(base);
  if(alias == aliases.end())
    return true;
  base = alias->second;
  const auto array = arrays.find(base);
  if(array == arrays.end())
  {
    reason = "missing_logical_array";
    return false;
  }
  expr = index_exprt(array->second.logical_array, index, expr.type());
  return true;
}

class pointer_aliasest
{
public:
  void add(const irep_idt &identifier)
  {
    parent.emplace(identifier, identifier);
  }

  irep_idt find(const irep_idt &identifier)
  {
    add(identifier);
    auto current = parent.find(identifier);
    if(current->second != identifier)
      current->second = find(current->second);
    return current->second;
  }

  void unite(const irep_idt &left, const irep_idt &right)
  {
    const irep_idt left_root = find(left);
    const irep_idt right_root = find(right);
    if(left_root != right_root)
      parent[right_root] = left_root;
  }

  const std::map<irep_idt, irep_idt> &all() const
  {
    return parent;
  }

private:
  std::map<irep_idt, irep_idt> parent;
};

void collect_direct_pointer_bases(
  const exprt &expr,
  pointer_aliasest &aliases,
  std::set<irep_idt> &dereferenced_bases)
{
  if(expr.id() == ID_dereference)
  {
    irep_idt base;
    exprt index;
    if(parse_direct_array_access(expr, base, index))
    {
      aliases.add(base);
      dereferenced_bases.insert(base);
    }
  }
  for(const auto &operand : expr.operands())
    collect_direct_pointer_bases(operand, aliases, dereferenced_bases);
}

bool canonicalize_immutable_arrays(
  goto_modelt &model,
  const std::vector<irep_idt> &thread_ids,
  std::string &reason)
{
  const namespacet ns(model.symbol_table);
  pointer_aliasest pointer_aliases;
  std::set<irep_idt> dereferenced_bases;
  std::map<irep_idt, std::size_t> pointer_definition_counts;
  std::vector<std::pair<irep_idt, irep_idt>> pointer_copy_edges;
  for(const auto &thread_id : thread_ids)
  {
    const auto function = model.goto_functions.function_map.find(thread_id);
    if(
      function == model.goto_functions.function_map.end() ||
      !function->second.body_available())
      continue;
    for(const auto &instruction : function->second.body.instructions)
    {
      if(instruction.has_condition())
        collect_direct_pointer_bases(
          instruction.condition(), pointer_aliases, dereferenced_bases);
      if(!instruction.is_assign())
        continue;
      collect_direct_pointer_bases(
        instruction.assign_lhs(), pointer_aliases, dereferenced_bases);
      collect_direct_pointer_bases(
        instruction.assign_rhs(), pointer_aliases, dereferenced_bases);
      if(
        instruction.assign_lhs().id() == ID_symbol &&
        instruction.assign_lhs().type().id() == ID_pointer)
      {
        const irep_idt &lhs =
          to_symbol_expr(instruction.assign_lhs()).get_identifier();
        ++pointer_definition_counts[lhs];
        pointer_aliases.add(lhs);
        const exprt &rhs = skip_typecast(instruction.assign_rhs());
        if(rhs.id() == ID_symbol && rhs.type().id() == ID_pointer)
        {
          const irep_idt &rhs_identifier =
            to_symbol_expr(rhs).get_identifier();
          pointer_aliases.add(rhs_identifier);
          pointer_copy_edges.emplace_back(lhs, rhs_identifier);
        }
      }
    }
  }

  for(const auto &edge : pointer_copy_edges)
  {
    if(
      pointer_definition_counts[edge.first] == 1 &&
      pointer_definition_counts[edge.second] == 1)
      pointer_aliases.unite(edge.first, edge.second);
  }

  std::map<irep_idt, irep_idt> component_canonical;
  for(const auto &base : dereferenced_bases)
  {
    const symbolt *symbol = nullptr;
    if(
      ns.lookup(base, symbol) || !symbol->is_static_lifetime ||
      symbol->type.id() != ID_pointer)
      continue;
    const irep_idt root = pointer_aliases.find(base);
    const auto existing = component_canonical.find(root);
    if(existing == component_canonical.end() || base < existing->second)
      component_canonical[root] = base;
  }

  std::map<irep_idt, irep_idt> aliases;
  for(const auto &entry : pointer_aliases.all())
  {
    const irep_idt root = pointer_aliases.find(entry.first);
    const auto canonical = component_canonical.find(root);
    if(canonical != component_canonical.end())
      aliases.emplace(entry.first, canonical->second);
  }

  std::map<irep_idt, immutable_arrayt> arrays;
  for(const auto &thread_id : thread_ids)
  {
    const auto function = model.goto_functions.function_map.find(thread_id);
    if(
      function == model.goto_functions.function_map.end() ||
      !function->second.body_available())
      continue;
    for(const auto &instruction : function->second.body.instructions)
    {
      if(
        instruction.has_condition() &&
        !collect_immutable_arrays(
          instruction.condition(), aliases, arrays, reason))
        return false;
      if(instruction.is_assign())
      {
        if(
          !collect_immutable_arrays(
            instruction.assign_lhs(), aliases, arrays, reason) ||
          !collect_immutable_arrays(
            instruction.assign_rhs(), aliases, arrays, reason))
          return false;
      }
    }
  }
  if(arrays.empty())
    return true;

  for(std::size_t thread_index = 0; thread_index < thread_ids.size();
      ++thread_index)
  {
    auto function =
      model.goto_functions.function_map.find(thread_ids[thread_index]);
    if(
      function == model.goto_functions.function_map.end() ||
      !function->second.body_available())
      continue;
    bool after_spawn = thread_index != 0;
    for(auto &instruction : function->second.body.instructions)
    {
      if(instruction.source_location().get_bool("v49_thread_spawn"))
        after_spawn = true;
      if(instruction.has_condition())
      {
        if(!rewrite_immutable_array_reads(
             instruction.condition_nonconst(), aliases, arrays, reason))
          return false;
      }
      if(!instruction.is_assign())
        continue;

      exprt &lhs = instruction.assign_lhs_nonconst();
      exprt &rhs = instruction.assign_rhs_nonconst();
      if(lhs.id() == ID_dereference)
      {
        irep_idt base;
        exprt index;
        if(!parse_direct_array_access(lhs, base, index))
        {
          if(!rewrite_immutable_array_reads(rhs, aliases, arrays, reason))
            return false;
          continue;
        }
        const auto alias = aliases.find(base);
        if(alias == aliases.end())
        {
          if(!rewrite_immutable_array_reads(rhs, aliases, arrays, reason))
            return false;
          continue;
        }
        base = alias->second;
        if(after_spawn)
        {
          reason = "array_write_after_spawn";
          return false;
        }
        const auto array = arrays.find(base);
        if(array == arrays.end())
        {
          reason = "missing_array_write_base";
          return false;
        }
        if(!rewrite_immutable_array_reads(rhs, aliases, arrays, reason))
          return false;
        rhs = with_exprt(array->second.logical_array, index, rhs);
        lhs = array->second.logical_array;
      }
      else
      {
        if(!rewrite_immutable_array_reads(rhs, aliases, arrays, reason))
          return false;
        if(lhs.id() == ID_symbol)
        {
          const auto alias =
            aliases.find(to_symbol_expr(lhs).get_identifier());
          if(alias != aliases.end() && after_spawn)
          {
            reason = "array_base_rebound_after_spawn";
            return false;
          }
        }
      }
    }
  }
  model.goto_functions.update();
  return true;
}

thread_profilet profile_thread(
  const irep_idt &entry,
  const goto_functionst::goto_functiont &function,
  const namespacet &ns)
{
  thread_profilet result;
  result.entry = entry;
  std::unordered_set<exprt, irep_hash> predicates;
  int atomic_depth = 0;

  for(const auto &instruction : function.body.instructions)
  {
    ++result.instructions;
    if(instruction.is_assert() || instruction.is_assume() || instruction.is_goto())
      collect_boolean_atoms(instruction.condition(), predicates);
    if(instruction.is_assign())
    {
      collect_boolean_atoms(instruction.assign_rhs(), predicates);
      if(is_shared_scalar(instruction.assign_lhs(), ns))
        ++result.shared_scalar_writes;
      else if(instruction.assign_lhs().id() == ID_dereference)
        ++result.pointer_writes;
    }
    if(instruction.is_atomic_begin())
    {
      if(atomic_depth == 0)
        ++result.atomic_blocks;
      ++atomic_depth;
    }
    else if(instruction.is_atomic_end())
    {
      --atomic_depth;
      if(atomic_depth < 0)
      {
        result.atomic_balanced = false;
        atomic_depth = 0;
      }
    }
    if(instruction.is_function_call())
      ++result.remaining_calls;
  }
  if(atomic_depth != 0)
    result.atomic_balanced = false;
  result.predicates = predicates.size();
  return result;
}

std::vector<exprt> predicate_basis(
  const irep_idt &entry,
  const goto_functionst::goto_functiont &function,
  const namespacet &ns,
  bool report_wp_audit)
{
  std::unordered_set<exprt, irep_hash> predicates;
  for(const auto &instruction : function.body.instructions)
  {
    if(instruction.is_assert() || instruction.is_assume() || instruction.is_goto())
      collect_boolean_atoms(instruction.condition(), predicates);
    if(instruction.is_assign())
      collect_boolean_atoms(instruction.assign_rhs(), predicates);
  }
  const std::vector<exprt> basis(predicates.begin(), predicates.end());

  if(report_wp_audit)
  {
    const std::size_t base_size = predicates.size();
    std::vector<std::pair<symbol_exprt, exprt>> assignments;
    for(const auto &instruction : function.body.instructions)
    {
      if(
        !instruction.is_assign() ||
        instruction.assign_lhs().id() != ID_symbol ||
        has_subexpr(instruction.assign_rhs(), ID_side_effect) ||
        has_subexpr(instruction.assign_rhs(), ID_dereference))
        continue;
      assignments.emplace_back(
        to_symbol_expr(instruction.assign_lhs()), instruction.assign_rhs());
    }

    std::vector<exprt> frontier(predicates.begin(), predicates.end());
    constexpr std::size_t max_wp_predicates = 256;
    constexpr unsigned max_wp_depth = 3;
    unsigned completed_depth = 0;
    bool reached_cap = false;
    for(unsigned depth = 1;
        depth <= max_wp_depth && !frontier.empty() && !reached_cap; ++depth)
    {
      std::vector<exprt> next_frontier;
      for(const auto &predicate : frontier)
      {
        for(const auto &assignment : assignments)
        {
          exprt preimage = predicate;
          replace_symbolt replacement;
          replacement.set(assignment.first, assignment.second);
          if(replacement.replace(preimage))
            continue;
          preimage = simplify_expr(std::move(preimage), ns);
          if(
            preimage.is_true() || preimage.is_false() ||
            preimage.type().id() != ID_bool ||
            has_subexpr(preimage, ID_side_effect) ||
            has_subexpr(preimage, ID_dereference))
            continue;
          if(predicates.insert(preimage).second)
          {
            next_frontier.push_back(std::move(preimage));
            if(predicates.size() >= max_wp_predicates)
            {
              reached_cap = true;
              break;
            }
          }
        }
        if(reached_cap)
          break;
      }
      completed_depth = depth;
      frontier = std::move(next_frontier);
    }
    std::cout << "INTERFERENCE_WP_AUDIT entry=" << entry
              << " base=" << base_size << " candidate=" << predicates.size()
              << " added=" << (predicates.size() - base_size)
              << " assignments=" << assignments.size()
              << " depth=" << completed_depth
              << " reached_cap=" << (reached_cap ? 1 : 0) << '\n';
  }
  return basis;
}

enum class wp_seed_modet
{
  BASE,
  ALL,
  CONTROL,
  ASSUME,
  GOTO,
  ERROR_CONTROL_GOTO,
  RHS
};

const char *wp_seed_mode_name(wp_seed_modet mode)
{
  switch(mode)
  {
  case wp_seed_modet::BASE:
    return "base";
  case wp_seed_modet::ALL:
    return "all";
  case wp_seed_modet::CONTROL:
    return "control";
  case wp_seed_modet::ASSUME:
    return "assume";
  case wp_seed_modet::GOTO:
    return "goto";
  case wp_seed_modet::ERROR_CONTROL_GOTO:
    return "error-control-goto";
  case wp_seed_modet::RHS:
    return "rhs";
  }
  UNREACHABLE;
  return "invalid";
}

bool parse_wp_seed_mode(wp_seed_modet &mode)
{
  const char *raw = std::getenv("DEAGLE_WP_SEED_MODE");
  if(raw == nullptr)
  {
    mode = wp_seed_modet::BASE;
    return true;
  }
  if(std::string(raw) == "all")
  {
    mode = wp_seed_modet::ALL;
    return true;
  }
  if(std::string(raw) == "control")
    mode = wp_seed_modet::CONTROL;
  else if(std::string(raw) == "assume")
    mode = wp_seed_modet::ASSUME;
  else if(std::string(raw) == "goto")
    mode = wp_seed_modet::GOTO;
  else if(std::string(raw) == "error-control-goto")
    mode = wp_seed_modet::ERROR_CONTROL_GOTO;
  else if(std::string(raw) == "rhs")
    mode = wp_seed_modet::RHS;
  else
    return false;
  return true;
}

bool parse_wp_max_depth(unsigned &depth)
{
  const char *raw = std::getenv("DEAGLE_WP_MAX_DEPTH");
  if(raw == nullptr || std::string(raw) == "3")
    depth = 3;
  else if(std::string(raw) == "2")
    depth = 2;
  else if(std::string(raw) == "1")
    depth = 1;
  else
    return false;
  return true;
}

struct wp_seed_collectiont
{
  std::vector<exprt> seeds;
  std::size_t assertions = 0;
  std::size_t assume_instructions = 0;
  std::size_t goto_instructions = 0;
  std::size_t selected_control_gotos = 0;
  std::size_t rhs_instructions = 0;
};

bool assertion_is_reachable(
  const goto_programt &program,
  goto_programt::const_targett start)
{
  std::deque<goto_programt::const_targett> pending;
  pending.push_back(start);
  std::set<const goto_programt::instructiont *> visited;
  while(!pending.empty())
  {
    const auto current = pending.front();
    pending.pop_front();
    if(!visited.insert(&*current).second)
      continue;
    if(current->is_assert())
      return true;
    for(const auto successor : program.get_successors(current))
      pending.push_back(successor);
  }
  return false;
}

bool goto_controls_assertion(
  const goto_programt &program,
  goto_programt::const_targett target)
{
  const auto successors = program.get_successors(target);
  if(successors.size() < 2)
    return false;
  std::size_t reaching_successors = 0;
  for(const auto successor : successors)
  {
    if(assertion_is_reachable(program, successor))
      ++reaching_successors;
  }
  return reaching_successors != 0 &&
         reaching_successors != successors.size();
}

wp_seed_collectiont collect_wp_seeds(
  const goto_functionst::goto_functiont &function,
  wp_seed_modet mode)
{
  std::unordered_set<exprt, irep_hash> seeds;
  wp_seed_collectiont result;
  for(auto instruction = function.body.instructions.begin();
      instruction != function.body.instructions.end(); ++instruction)
  {
    if(instruction->is_assert())
      ++result.assertions;
    if(instruction->is_assume())
    {
      ++result.assume_instructions;
      if(mode == wp_seed_modet::ALL || mode == wp_seed_modet::CONTROL ||
         mode == wp_seed_modet::ASSUME)
        collect_boolean_atoms(instruction->condition(), seeds);
    }
    if(instruction->is_goto())
    {
      ++result.goto_instructions;
      const bool controls_assertion =
        goto_controls_assertion(function.body, instruction);
      if(mode == wp_seed_modet::ALL || mode == wp_seed_modet::CONTROL ||
         mode == wp_seed_modet::GOTO ||
         (mode == wp_seed_modet::ERROR_CONTROL_GOTO && controls_assertion))
      {
        collect_boolean_atoms(instruction->condition(), seeds);
        if(controls_assertion)
          ++result.selected_control_gotos;
      }
    }
    if(instruction->is_assign())
    {
      ++result.rhs_instructions;
      if(mode == wp_seed_modet::ALL || mode == wp_seed_modet::RHS)
        collect_boolean_atoms(instruction->assign_rhs(), seeds);
    }
  }
  result.seeds.assign(seeds.begin(), seeds.end());
  return result;
}

std::vector<exprt> wp_predicate_closure(
  const irep_idt &entry,
  const goto_functionst::goto_functiont &function,
  const namespacet &ns,
  const std::vector<exprt> &basis,
  const std::vector<exprt> &seeds,
  wp_seed_modet mode,
  unsigned max_wp_depth,
  const wp_seed_collectiont &local_seed_collection)
{
  std::unordered_set<exprt, irep_hash> predicates(
    basis.begin(), basis.end());
  std::vector<std::pair<symbol_exprt, exprt>> assignments;
  for(const auto &instruction : function.body.instructions)
  {
    if(
      !instruction.is_assign() ||
      instruction.assign_lhs().id() != ID_symbol ||
      has_subexpr(instruction.assign_rhs(), ID_side_effect) ||
      has_subexpr(instruction.assign_rhs(), ID_dereference))
      continue;
    assignments.emplace_back(
      to_symbol_expr(instruction.assign_lhs()), instruction.assign_rhs());
  }

  std::vector<exprt> frontier(seeds.begin(), seeds.end());
  constexpr std::size_t max_wp_predicates = 64;
  unsigned completed_depth = 0;
  bool reached_cap = false;
  for(unsigned depth = 1;
      depth <= max_wp_depth && !frontier.empty() && !reached_cap; ++depth)
  {
    std::vector<exprt> next_frontier;
    for(const auto &predicate : frontier)
    {
      for(const auto &assignment : assignments)
      {
        exprt preimage = predicate;
        replace_symbolt replacement;
        replacement.set(assignment.first, assignment.second);
        if(replacement.replace(preimage))
          continue;
        preimage = simplify_expr(std::move(preimage), ns);
        if(
          preimage.is_true() || preimage.is_false() ||
          preimage.type().id() != ID_bool ||
          has_subexpr(preimage, ID_side_effect) ||
          has_subexpr(preimage, ID_dereference))
          continue;
        if(predicates.insert(preimage).second)
        {
          next_frontier.push_back(std::move(preimage));
          if(predicates.size() >= max_wp_predicates)
          {
            reached_cap = true;
            break;
          }
        }
      }
      if(reached_cap)
        break;
    }
    completed_depth = depth;
    frontier = std::move(next_frontier);
  }
  std::cout << "INTERFERENCE_WP_MODE entry=" << entry
            << " mode=" << wp_seed_mode_name(mode)
            << " base=" << basis.size() << " seeds=" << seeds.size()
            << " candidate=" << predicates.size()
            << " added=" << (predicates.size() - basis.size())
            << " assignments=" << assignments.size()
            << " assertions=" << local_seed_collection.assertions
            << " local_assume_instructions="
            << local_seed_collection.assume_instructions
            << " local_goto_instructions="
            << local_seed_collection.goto_instructions
            << " local_selected_control_gotos="
            << local_seed_collection.selected_control_gotos
            << " local_rhs_instructions="
            << local_seed_collection.rhs_instructions
            << " max_depth=" << max_wp_depth
            << " depth=" << completed_depth
            << " reached_cap=" << (reached_cap ? 1 : 0) << '\n';
  if(reached_cap)
    return basis;
  return std::vector<exprt>(predicates.begin(), predicates.end());
}

bool affine_integer_expression(const exprt &expr)
{
  const exprt &value = skip_typecast(expr);
  if(value.id() == ID_symbol || value.id() == ID_constant)
    return value.type().id() != ID_pointer;
  if(value.id() == ID_unary_minus && value.operands().size() == 1)
    return affine_integer_expression(value.op0());
  if(
    (value.id() == ID_plus || value.id() == ID_minus) &&
    !value.operands().empty())
  {
    for(const auto &operand : value.operands())
    {
      if(!affine_integer_expression(operand))
        return false;
    }
    return true;
  }
  if(value.id() == ID_mult && value.operands().size() == 2)
  {
    const exprt &left = skip_typecast(value.op0());
    const exprt &right = skip_typecast(value.op1());
    return (
      left.id() == ID_constant && affine_integer_expression(right)) ||
           (right.id() == ID_constant && affine_integer_expression(left));
  }
  return false;
}

bool relational_template(const exprt &expr)
{
  if(expr.id() == ID_not && expr.operands().size() == 1)
    return relational_template(expr.op0());
  return expr.id() == ID_equal || expr.id() == ID_notequal ||
         expr.id() == ID_lt || expr.id() == ID_le || expr.id() == ID_gt ||
         expr.id() == ID_ge;
}

bool contains_shared_symbol(const exprt &expr, const namespacet &ns)
{
  if(expr.id() == ID_symbol)
    return is_shared_scalar(expr, ns);
  for(const auto &operand : expr.operands())
  {
    if(contains_shared_symbol(operand, ns))
      return true;
  }
  return false;
}

exprt normalize_relational_template(exprt expr)
{
  if(expr.id() == ID_not && expr.operands().size() == 1)
  {
    const exprt &operand = expr.op0();
    if(operand.id() == ID_equal && operand.operands().size() == 2)
      return notequal_exprt(operand.op0(), operand.op1());
    if(operand.id() == ID_notequal && operand.operands().size() == 2)
      return equal_exprt(operand.op0(), operand.op1());
  }
  return expr;
}

void collect_signed_relational_templates(
  const exprt &expr,
  const namespacet &ns,
  std::unordered_set<exprt, irep_hash> &templates)
{
  if(
    relational_template(expr) && contains_shared_symbol(expr, ns) &&
    uses_only_shared_symbols(expr, ns))
  {
    templates.insert(normalize_relational_template(expr));
    return;
  }
  for(const auto &operand : expr.operands())
    collect_signed_relational_templates(operand, ns, templates);
}

struct affine_regiont
{
  irep_idt entry;
  irep_idt mutex;
  unsigned begin_location = 0;
  std::vector<std::pair<symbol_exprt, exprt>> assignments;
};

bool collect_affine_regions(
  const goto_modelt &model,
  const std::vector<irep_idt> &thread_ids,
  std::vector<affine_regiont> &regions,
  std::string &reason)
{
  for(const auto &thread_id : thread_ids)
  {
    const auto function =
      model.goto_functions.function_map.find(thread_id);
    if(
      function == model.goto_functions.function_map.end() ||
      !function->second.body_available())
      continue;
    const auto &program = function->second.body;
    for(auto instruction = program.instructions.begin();
        instruction != program.instructions.end(); ++instruction)
    {
      if(!instruction->is_atomic_begin() ||
         instruction->source_location().get("v217_mutex") == irep_idt())
        continue;
      affine_regiont region;
      region.entry = thread_id;
      region.mutex = instruction->source_location().get("v217_mutex");
      region.begin_location = instruction->location_number;
      bool complete = false;
      bool supported = true;
      for(auto current = std::next(instruction);
          current != program.instructions.end(); ++current)
      {
        if(current->is_atomic_end())
        {
          complete = true;
          break;
        }
        if(current->is_assign())
        {
          if(
            current->assign_lhs().id() != ID_symbol ||
            !affine_integer_expression(current->assign_rhs()) ||
            has_subexpr(current->assign_rhs(), ID_side_effect) ||
            has_subexpr(current->assign_rhs(), ID_dereference))
          {
            supported = false;
            continue;
          }
          region.assignments.emplace_back(
            to_symbol_expr(current->assign_lhs()),
            current->assign_rhs());
        }
        else if(
          current->is_goto() || current->is_assume() ||
          current->is_function_call() || current->is_start_thread() ||
          current->is_throw() || current->is_catch() ||
          (current->is_other() && !is_abstract_noop_other(*current)))
        {
          supported = false;
        }
      }
      if(!complete)
      {
        reason = "affine_region_unclosed";
        return false;
      }
      if(supported && !region.assignments.empty())
      {
        std::cout << "V217_AFFINE_REGION entry=" << region.entry
                  << " begin=" << region.begin_location
                  << " assignments=" << region.assignments.size();
        for(const auto &assignment : region.assignments)
          std::cout << " lhs=" << assignment.first.get_identifier();
        std::cout << '\n';
        regions.push_back(std::move(region));
      }
    }
  }
  return true;
}

void collect_symbol_identifiers(
  const exprt &expr,
  std::set<irep_idt> &identifiers)
{
  if(expr.id() == ID_symbol)
    identifiers.insert(to_symbol_expr(expr).get_identifier());
  for(const auto &operand : expr.operands())
    collect_symbol_identifiers(operand, identifiers);
}

bool uses_identifier_from(
  const exprt &expr,
  const std::set<irep_idt> &identifiers)
{
  if(
    expr.id() == ID_symbol &&
    identifiers.find(to_symbol_expr(expr).get_identifier()) !=
      identifiers.end())
    return true;
  for(const auto &operand : expr.operands())
  {
    if(uses_identifier_from(operand, identifiers))
      return true;
  }
  return false;
}

bool affine_access_discipline(
  const goto_modelt &model,
  const std::vector<irep_idt> &thread_ids,
  const std::vector<affine_regiont> &regions,
  const std::unordered_set<exprt, irep_hash> &templates,
  std::string &reason)
{
  if(regions.empty())
  {
    reason = "affine_no_supported_region";
    return false;
  }
  const irep_idt proof_mutex = regions.front().mutex;
  std::set<std::pair<irep_idt, unsigned>> supported_regions;
  for(const auto &region : regions)
  {
    if(region.mutex != proof_mutex)
    {
      reason = "affine_multiple_mutexes";
      return false;
    }
    supported_regions.emplace(region.entry, region.begin_location);
  }

  std::set<irep_idt> protected_identifiers;
  for(const auto &predicate : templates)
    collect_symbol_identifiers(predicate, protected_identifiers);

  for(std::size_t thread_index = 0; thread_index < thread_ids.size();
      ++thread_index)
  {
    const auto function =
      model.goto_functions.function_map.find(thread_ids[thread_index]);
    if(
      function == model.goto_functions.function_map.end() ||
      !function->second.body_available())
      continue;
    bool after_spawn = thread_index != 0;
    irep_idt current_mutex;
    unsigned current_begin = 0;
    for(const auto &instruction : function->second.body.instructions)
    {
      if(
        thread_index == 0 &&
        instruction.source_location().get_bool("v49_thread_spawn"))
        after_spawn = true;
      if(
        instruction.is_atomic_begin() &&
        instruction.source_location().get("v217_mutex") != irep_idt())
      {
        current_mutex = instruction.source_location().get("v217_mutex");
        current_begin = instruction.location_number;
        continue;
      }
      if(
        instruction.is_atomic_end() &&
        instruction.source_location().get("v217_mutex") != irep_idt())
      {
        current_mutex = irep_idt();
        current_begin = 0;
        continue;
      }

      bool relevant_access = false;
      if(
        instruction.has_condition() &&
        uses_identifier_from(
          instruction.condition(), protected_identifiers))
        relevant_access = true;
      if(instruction.is_assign())
      {
        relevant_access =
          relevant_access ||
          uses_identifier_from(
            instruction.assign_lhs(), protected_identifiers) ||
          uses_identifier_from(
            instruction.assign_rhs(), protected_identifiers);
      }
      if(!relevant_access || !after_spawn)
        continue;
      if(current_mutex != proof_mutex)
      {
        reason = "affine_unprotected_relevant_access";
        return false;
      }
      if(
        instruction.is_assign() &&
        supported_regions.find(
          {thread_ids[thread_index], current_begin}) ==
          supported_regions.end())
      {
        reason = "affine_access_in_unsupported_region";
        return false;
      }
    }
  }
  std::cout << "V217_AFFINE_ACCESS mutex=" << proof_mutex
            << " symbols=" << protected_identifiers.size()
            << " admitted=1\n";
  return true;
}

bool affine_template_closure(
  const goto_modelt &model,
  const std::vector<irep_idt> &thread_ids,
  const namespacet &ns,
  std::vector<exprt> &extra_predicates,
  std::string &reason)
{
  std::vector<affine_regiont> regions;
  if(!collect_affine_regions(model, thread_ids, regions, reason))
    return false;

  std::unordered_set<exprt, irep_hash> templates;
  for(const auto &thread_id : thread_ids)
  {
    const auto function =
      model.goto_functions.function_map.find(thread_id);
    if(
      function == model.goto_functions.function_map.end() ||
      !function->second.body_available())
      continue;
    for(const auto &instruction : function->second.body.instructions)
    {
      if(instruction.has_condition())
        collect_signed_relational_templates(
          instruction.condition(), ns, templates);
    }
  }

  const std::size_t original_size = templates.size();
  std::vector<exprt> frontier(templates.begin(), templates.end());
  constexpr std::size_t max_templates = 64;
  constexpr unsigned max_rounds = 16;
  for(unsigned round = 0;
      round < max_rounds && !frontier.empty(); ++round)
  {
    std::vector<exprt> next;
    for(const auto &predicate : frontier)
    {
      for(const auto &region : regions)
      {
        exprt preimage = predicate;
        for(auto assignment = region.assignments.rbegin();
            assignment != region.assignments.rend(); ++assignment)
        {
          replace_symbolt replacement;
          replacement.set(assignment->first, assignment->second);
          replacement.replace(preimage);
        }
        preimage = normalize_relational_template(
          simplify_expr(std::move(preimage), ns));
        std::cout << "V217_AFFINE_PREIMAGE entry=" << region.entry
                  << " begin=" << region.begin_location
                  << " expr=" << from_expr(ns, irep_idt(), preimage) << '\n';
        if(
          preimage.is_true() || preimage.is_false() ||
          !relational_template(preimage) ||
          !uses_only_shared_symbols(preimage, ns))
          continue;
        if(templates.insert(preimage).second)
        {
          next.push_back(preimage);
          if(templates.size() > max_templates)
          {
            reason = "affine_template_cap";
            return false;
          }
        }
      }
    }
    frontier = std::move(next);
  }
  if(!frontier.empty())
  {
    reason = "affine_template_nonfinite";
    return false;
  }
  if(!affine_access_discipline(
       model, thread_ids, regions, templates, reason))
    return false;

  extra_predicates.reserve(templates.size());
  for(const auto &predicate : templates)
    extra_predicates.push_back(predicate);
  std::cout << "V217_AFFINE_CLOSURE regions=" << regions.size()
            << " base_templates=" << original_size
            << " closed_templates=" << extra_predicates.size() << '\n';
  return true;
}

bool assertion_reachable_from(
  const goto_programt &program,
  goto_programt::const_targett start)
{
  std::deque<goto_programt::const_targett> pending;
  pending.push_back(start);
  std::set<const goto_programt::instructiont *> visited;
  while(!pending.empty())
  {
    const auto current = pending.front();
    pending.pop_front();
    if(!visited.insert(&*current).second)
      continue;
    if(current->is_assert())
      return true;
    for(const auto successor : program.get_successors(current))
      pending.push_back(successor);
  }
  return false;
}

bool error_control_safe_condition(
  const goto_programt &program,
  goto_programt::const_targett target,
  exprt &safe_condition)
{
  if(!target->is_goto())
    return false;
  const auto successors = program.get_successors(target);
  if(successors.size() != 2)
    return false;
  std::vector<goto_programt::const_targett> error_successors;
  for(const auto successor : successors)
  {
    if(assertion_reachable_from(program, successor))
      error_successors.push_back(successor);
  }
  if(error_successors.size() != 1)
    return false;
  const auto fallthrough = std::next(target);
  safe_condition =
    error_successors.front() == fallthrough
      ? target->condition()
      : boolean_negate(target->condition());
  return true;
}

bool end_reachable_without(
  const goto_programt &program,
  goto_programt::const_targett skipped)
{
  if(program.instructions.empty())
    return false;
  std::deque<goto_programt::const_targett> pending;
  pending.push_back(program.instructions.begin());
  std::set<const goto_programt::instructiont *> visited;
  while(!pending.empty())
  {
    const auto current = pending.front();
    pending.pop_front();
    if(current == skipped || !visited.insert(&*current).second)
      continue;
    if(current->is_end_function())
      return true;
    for(const auto successor : program.get_successors(current))
      pending.push_back(successor);
  }
  return false;
}

struct phase_worker_summaryt
{
  irep_idt entry;
  irep_idt mutex;
  std::vector<std::pair<symbol_exprt, exprt>> assignments;
};

bool build_phase_worker_summary(
  const goto_modelt &model,
  const irep_idt &entry,
  const std::set<irep_idt> &property_identifiers,
  phase_worker_summaryt &summary,
  std::string &reason)
{
  const auto function = model.goto_functions.function_map.find(entry);
  if(
    function == model.goto_functions.function_map.end() ||
    !function->second.body_available())
  {
    reason = "affine_phase_missing_worker";
    return false;
  }
  summary.entry = entry;
  irep_idt held_mutex;
  for(auto instruction = function->second.body.instructions.begin();
      instruction != function->second.body.instructions.end();
      ++instruction)
  {
    if(instruction->is_function_call())
    {
      const exprt &function_expr =
        skip_typecast(instruction->call_function());
      if(function_expr.id() != ID_symbol)
      {
        reason = "affine_phase_indirect_call";
        return false;
      }
      const irep_idt &identifier =
        to_symbol_expr(function_expr).get_identifier();
      if(
        identifier == "pthread_mutex_lock" ||
        identifier == "pthread_mutex_unlock")
      {
        irep_idt mutex;
        if(
          instruction->call_arguments().empty() ||
          !get_addressed_symbol(
            instruction->call_arguments()[0], mutex))
        {
          reason = "affine_phase_unresolved_mutex";
          return false;
        }
        if(identifier == "pthread_mutex_lock")
        {
          if(held_mutex != irep_idt())
          {
            reason = "affine_phase_nested_mutex";
            return false;
          }
          held_mutex = mutex;
        }
        else
        {
          if(held_mutex != mutex)
          {
            reason = "affine_phase_unbalanced_mutex";
            return false;
          }
          held_mutex = irep_idt();
        }
        continue;
      }
      if(identifier == "pthread_cond_wait")
      {
        irep_idt mutex;
        if(
          held_mutex == irep_idt() ||
          instruction->call_arguments().size() < 2 ||
          !get_addressed_symbol(
            instruction->call_arguments()[1], mutex) ||
          mutex != held_mutex)
        {
          reason = "affine_phase_cond_mutex_mismatch";
          return false;
        }
        continue;
      }
      if(
        identifier == "pthread_cond_signal" ||
        identifier == "pthread_cond_broadcast")
        continue;
      reason = "affine_phase_remaining_call";
      return false;
    }

    if(
      instruction->is_assign() &&
      instruction->assign_lhs().id() == ID_dereference)
    {
      reason = "affine_phase_pointer_write";
      return false;
    }
    if(
      !instruction->is_assign() ||
      instruction->assign_lhs().id() != ID_symbol)
      continue;
    const auto &lhs = to_symbol_expr(instruction->assign_lhs());
    if(
      property_identifiers.find(lhs.get_identifier()) ==
      property_identifiers.end())
      continue;
    if(held_mutex == irep_idt())
    {
      reason = "affine_phase_unprotected_assignment";
      return false;
    }
    if(
      instruction_is_in_cycle(function->second.body, instruction) ||
      end_reachable_without(function->second.body, instruction))
    {
      reason = "affine_phase_assignment_not_once";
      return false;
    }
    if(
      !affine_integer_expression(instruction->assign_rhs()) ||
      has_subexpr(instruction->assign_rhs(), ID_side_effect) ||
      has_subexpr(instruction->assign_rhs(), ID_dereference))
    {
      reason = "affine_phase_assignment_unsupported";
      return false;
    }
    if(summary.mutex == irep_idt())
      summary.mutex = held_mutex;
    else if(summary.mutex != held_mutex)
    {
      reason = "affine_phase_multiple_mutexes";
      return false;
    }
    summary.assignments.emplace_back(lhs, instruction->assign_rhs());
  }
  if(held_mutex != irep_idt())
  {
    reason = "affine_phase_unbalanced_mutex";
    return false;
  }
  if(summary.assignments.size() != 1)
  {
    reason = "affine_phase_assignment_count";
    return false;
  }
  return true;
}

bool collect_linear_initial_constants(
  const goto_programt &program,
  unsigned first_spawn_location,
  const namespacet &ns,
  std::map<irep_idt, exprt> &constants,
  std::string &reason)
{
  for(auto instruction = program.instructions.begin();
      instruction != program.instructions.end(); ++instruction)
  {
    if(instruction->location_number == first_spawn_location)
      return true;
    if(instruction->is_goto() || instruction->is_assume())
    {
      reason = "affine_phase_initial_control";
      return false;
    }
    if(
      !instruction->is_assign() ||
      instruction->assign_lhs().id() != ID_symbol)
      continue;
    exprt rhs = instruction->assign_rhs();
    replace_symbolt replacement;
    for(const auto &entry : constants)
    {
      const symbolt *symbol = nullptr;
      if(ns.lookup(entry.first, symbol))
        continue;
      replacement.set(
        symbol_exprt(entry.first, symbol->type), entry.second);
    }
    replacement.replace(rhs);
    rhs = simplify_expr(std::move(rhs), ns);
    const irep_idt &lhs =
      to_symbol_expr(instruction->assign_lhs()).get_identifier();
    if(rhs.id() == ID_constant)
      constants[lhs] = rhs;
    else
      constants.erase(lhs);
  }
  reason = "affine_phase_spawn_not_reached";
  return false;
}

interference_predicate_resultt affine_phase_certificate(
  const goto_modelt &goto_model,
  message_handlert &message_handler,
  std::string &reason)
{
  std::map<irep_idt, bool> multiple_instances;
  const auto entries =
    find_thread_entries(goto_model, nullptr, &multiple_instances);
  if(entries.empty() || entries.size() > 6)
  {
    reason = "affine_phase_worker_count";
    return interference_predicate_resultt::UNKNOWN;
  }
  for(const auto &entry : entries)
  {
    if(multiple_instances[entry])
    {
      reason = "affine_phase_repeated_worker";
      return interference_predicate_resultt::UNKNOWN;
    }
  }

  goto_modelt main_model;
  main_model.symbol_table = goto_model.symbol_table;
  main_model.goto_functions.copy_from(goto_model.goto_functions);
  neutralize_synchronization_calls(main_model);
  irep_idt main_entry = "main";
  for(const irep_idt &candidate :
      {irep_idt("__CPROVER__start"), irep_idt("__CPROVER_start")})
  {
    const auto start = main_model.goto_functions.function_map.find(candidate);
    if(
      start != main_model.goto_functions.function_map.end() &&
      start->second.body_available())
    {
      main_entry = candidate;
      break;
    }
  }
  goto_function_inline(
    main_model, main_entry, message_handler, false, false);
  main_model.goto_functions.update();
  const auto main_function =
    main_model.goto_functions.function_map.find(main_entry);
  if(
    main_function == main_model.goto_functions.function_map.end() ||
    !main_function->second.body_available())
  {
    reason = "affine_phase_missing_main";
    return interference_predicate_resultt::UNKNOWN;
  }

  exprt safe_condition;
  unsigned safe_location = 0;
  for(auto instruction = main_function->second.body.instructions.begin();
      instruction != main_function->second.body.instructions.end();
      ++instruction)
  {
    exprt candidate;
    if(
      error_control_safe_condition(
        main_function->second.body, instruction, candidate))
    {
      if(safe_location != 0)
      {
        reason = "affine_phase_multiple_properties";
        return interference_predicate_resultt::UNKNOWN;
      }
      safe_condition = std::move(candidate);
      safe_location = instruction->location_number;
    }
  }
  if(safe_location == 0)
  {
    reason = "affine_phase_property_not_found";
    return interference_predicate_resultt::UNKNOWN;
  }

  const namespacet ns(main_model.symbol_table);
  std::set<irep_idt> property_identifiers;
  collect_symbol_identifiers(safe_condition, property_identifiers);
  for(auto identifier = property_identifiers.begin();
      identifier != property_identifiers.end();)
  {
    const symbolt *symbol = nullptr;
    if(
      ns.lookup(*identifier, symbol) || !symbol->is_static_lifetime ||
      symbol->type.id() == ID_pointer)
      identifier = property_identifiers.erase(identifier);
    else
      ++identifier;
  }
  if(property_identifiers.empty())
  {
    reason = "affine_phase_no_property_scalar";
    return interference_predicate_resultt::UNKNOWN;
  }

  unsigned first_spawn = 0;
  std::set<irep_idt> joined_entries;
  bool after_spawn = false;
  for(const auto &instruction : main_function->second.body.instructions)
  {
    if(instruction.source_location().get_bool("v49_thread_spawn"))
    {
      if(first_spawn == 0)
        first_spawn = instruction.location_number;
      after_spawn = true;
    }
    const irep_idt &joined =
      instruction.source_location().get("v49_join_entry");
    if(joined != irep_idt())
      joined_entries.insert(joined);
    if(
      after_spawn && instruction.is_assign() &&
      instruction.assign_lhs().id() == ID_symbol &&
      property_identifiers.find(
        to_symbol_expr(instruction.assign_lhs()).get_identifier()) !=
        property_identifiers.end())
    {
      reason = "affine_phase_main_write_after_spawn";
      return interference_predicate_resultt::UNKNOWN;
    }
    if(instruction.location_number == safe_location)
      break;
  }
  if(first_spawn == 0 || joined_entries != entries)
  {
    reason = "affine_phase_incomplete_join";
    return interference_predicate_resultt::UNKNOWN;
  }

  std::map<irep_idt, exprt> initial_constants;
  if(!collect_linear_initial_constants(
       main_function->second.body,
       first_spawn,
       ns,
       initial_constants,
       reason))
    return interference_predicate_resultt::UNKNOWN;
  for(const auto &identifier : property_identifiers)
  {
    if(initial_constants.find(identifier) == initial_constants.end())
    {
      reason = "affine_phase_initial_value_unknown";
      return interference_predicate_resultt::UNKNOWN;
    }
  }

  std::vector<phase_worker_summaryt> workers;
  for(const auto &entry : entries)
  {
    phase_worker_summaryt worker;
    if(!build_phase_worker_summary(
         goto_model,
         entry,
         property_identifiers,
         worker,
         reason))
      return interference_predicate_resultt::UNKNOWN;
    if(!workers.empty() && worker.mutex != workers.front().mutex)
    {
      reason = "affine_phase_cross_mutex";
      return interference_predicate_resultt::UNKNOWN;
    }
    workers.push_back(std::move(worker));
  }

  std::vector<std::size_t> order(workers.size());
  for(std::size_t index = 0; index < order.size(); ++index)
    order[index] = index;
  std::size_t orders = 0;
  do
  {
    std::map<irep_idt, exprt> environment = initial_constants;
    for(const auto worker_index : order)
    {
      const auto &assignment = workers[worker_index].assignments.front();
      exprt rhs = assignment.second;
      replace_symbolt replacement;
      for(const auto &entry : environment)
      {
        const symbolt *symbol = nullptr;
        if(ns.lookup(entry.first, symbol))
          continue;
        replacement.set(
          symbol_exprt(entry.first, symbol->type), entry.second);
      }
      replacement.replace(rhs);
      environment[assignment.first.get_identifier()] =
        simplify_expr(std::move(rhs), ns);
    }
    exprt claim = safe_condition;
    replace_symbolt replacement;
    for(const auto &entry : environment)
    {
      const symbolt *symbol = nullptr;
      if(ns.lookup(entry.first, symbol))
        continue;
      replacement.set(
        symbol_exprt(entry.first, symbol->type), entry.second);
    }
    replacement.replace(claim);
    claim = simplify_expr(std::move(claim), ns);
    if(!claim.is_true())
    {
      reason = "affine_phase_order_not_safe";
      return interference_predicate_resultt::UNKNOWN;
    }
    ++orders;
  } while(std::next_permutation(order.begin(), order.end()));

  std::cout << "V217_AFFINE_PHASE result=SAFE workers=" << workers.size()
            << " mutex=" << workers.front().mutex << " orders=" << orders
            << " property={"
            << from_expr(ns, irep_idt(), safe_condition) << "}\n";
  return interference_predicate_resultt::SAFE;
}

struct fixedpoint_threadt
{
  irep_idt entry;
  const goto_programt *program = nullptr;
  std::vector<exprt> predicates;
  std::map<unsigned, goto_programt::const_targett> locations;
  std::map<unsigned, unsigned> atomic_depth;
  std::map<unsigned, unsigned> atomic_regions;
  std::map<unsigned, bool> concurrent_location;
  std::map<unsigned, std::size_t> join_workers;
  unsigned first_spawn_location = 0;
  bool may_have_multiple_instances = false;
  std::map<unsigned, std::vector<interference_predicate_cubet>> states;
};

struct interference_effectt
{
  std::size_t writer_thread;
  unsigned location_number;
  unsigned path_number;
  interference_predicate_cubet writer_cube;
  std::vector<interference_predicate_operationt> operations;
};

struct finite_product_threadt
{
  irep_idt entry;
  const goto_programt *program = nullptr;
  std::vector<goto_programt::const_targett> locations;
  std::map<const goto_programt::instructiont *, std::size_t> indices;
  std::map<std::size_t, std::size_t> spawn_workers;
  std::map<std::size_t, std::size_t> join_workers;
};

struct finite_product_statet
{
  std::vector<std::size_t> pcs;
  std::vector<bool> active;
  std::vector<bool> completed;
  std::shared_ptr<std::vector<std::size_t>> values =
    std::make_shared<std::vector<std::size_t>>();
  int atomic_owner = -1;
};

struct finite_product_symmetry_groupt
{
  std::vector<std::size_t> threads;
  std::vector<std::vector<std::size_t>> local_slots;
};

class finite_product_runnert
{
public:
  finite_product_runnert(
    goto_modelt &model,
    const std::vector<irep_idt> &thread_ids,
    const std::vector<bool> &may_have_multiple_instances)
    : model(model), ns(model.symbol_table)
  {
    if(thread_ids.size() < 2 || thread_ids.size() > max_workers)
    {
      fail("worker_count");
      return;
    }
    if(thread_ids.size() != may_have_multiple_instances.size())
    {
      fail("worker_metadata");
      return;
    }
    for(std::size_t index = 1; index < may_have_multiple_instances.size(); ++index)
    {
      if(may_have_multiple_instances[index])
      {
        fail("multiple_worker_instances");
        return;
      }
    }

    for(const auto &thread_id : thread_ids)
    {
      const auto function = model.goto_functions.function_map.find(thread_id);
      if(
        function == model.goto_functions.function_map.end() ||
        !function->second.body_available())
      {
        fail("missing_thread_body");
        return;
      }
      if(function->second.body.instructions.size() > max_locations_per_worker)
      {
        std::cout << "V225_FINITE_PRODUCT_LOCATION_CAP entry=" << thread_id
                  << " locations="
                  << function->second.body.instructions.size()
                  << " cap=" << max_locations_per_worker << '\n';
        fail("location_cap");
        return;
      }
      finite_product_threadt thread;
      thread.entry = thread_id;
      thread.program = &function->second.body;
      for(auto location = thread.program->instructions.begin();
          location != thread.program->instructions.end(); ++location)
      {
        thread.indices.emplace(&*location, thread.locations.size());
        thread.locations.push_back(location);
      }
      threads.push_back(std::move(thread));
    }

    collect_shared_symbols();
    if(failed)
      return;
    if(std::getenv("DEAGLE_FINITE_PRODUCT_AUDIT") != nullptr)
    {
      std::cout << "V225_FINITE_PRODUCT_SYMBOLS count=" << symbols.size();
      for(const auto &object : symbols)
        std::cout << " object={"
                  << from_expr(ns, irep_idt(), object) << '}';
      std::cout << '\n';
    }
    if(symbols.empty() || symbols.size() > max_symbols)
    {
      fail("symbol_count");
      return;
    }
    build_symmetry_groups();
    symmetric_thread_mask.assign(threads.size(), false);
    symmetric_slot_mask.assign(symbols.size(), false);
    for(const auto &group : symmetry_groups)
    {
      for(const auto thread_index : group.threads)
        symmetric_thread_mask[thread_index] = true;
      for(const auto &slots : group.local_slots)
      {
        for(const auto slot : slots)
          symmetric_slot_mask[slot] = true;
      }
    }
    if(!build_live_local_slots())
    {
      fail("local_liveness");
      return;
    }
    audit_lifecycle(thread_ids);
    if(failed)
      return;
    audit_instructions();
  }

  interference_predicate_resultt run()
  {
    if(failed)
      return report_unknown();

    finite_product_statet initial;
    initial.pcs.assign(threads.size(), 0);
    initial.active.assign(threads.size(), false);
    initial.completed.assign(threads.size(), false);
    initial.active.front() = true;
    for(const auto &object : symbols)
    {
      exprt value;
      if(object.id() == ID_symbol)
      {
        const symbolt *symbol = nullptr;
        if(ns.lookup(to_symbol_expr(object).get_identifier(), symbol))
          return fail_run("missing_symbol");
        if(symbol->is_static_lifetime)
        {
          value = symbol->value;
          if(value.is_nil() || value.id().empty())
            value = from_integer(0, symbol->type);
        }
        else
          value.make_nil();
      }
      else
      {
        const exprt *root = &object;
        while(root->id() == ID_member || root->id() == ID_index)
        {
          if(root->id() == ID_member)
            root = &to_member_expr(*root).struct_op();
          else
            root = &to_index_expr(*root).array();
        }
        if(root->id() != ID_symbol)
          return fail_run("unsupported_initializer_root");
        const symbolt *symbol = nullptr;
        if(ns.lookup(to_symbol_expr(*root).get_identifier(), symbol))
          return fail_run("missing_member_symbol");
        if(!symbol->is_static_lifetime)
        {
          value.make_nil();
        }
        else if(symbol->value.is_nil() || symbol->value.id().empty())
        {
          value = from_integer(0, object.type());
        }
        else
        {
          value = object;
          replace_expr(*root, symbol->value, value);
        }
      }
      if(value.is_not_nil())
        value = simplify_expr(std::move(value), ns);
      if(value.is_not_nil() && !is_exact_constant(value))
      {
        if(std::getenv("DEAGLE_FINITE_PRODUCT_AUDIT") != nullptr)
          std::cout << "V225_FINITE_PRODUCT_INITIALIZER object={"
                    << from_expr(ns, irep_idt(), object) << "} value={"
                    << from_expr(ns, irep_idt(), value) << "} object_irep={"
                    << object.pretty() << "} value_irep={" << value.pretty()
                    << "}\n";
        return fail_run("nonconstant_initializer");
      }
      initial.values->push_back(intern_state_value(value));
    }

    std::deque<finite_product_statet> pending;
    std::unordered_set<std::string> visited;
    auto normalize_state =
      [&](finite_product_statet &state, bool &reachable)
      {
        reachable = true;
        while(true)
        {
          std::size_t selected = threads.size();
          if(state.atomic_owner >= 0)
            selected = static_cast<std::size_t>(state.atomic_owner);
          else
          {
            for(std::size_t thread_index = 0;
                thread_index < threads.size(); ++thread_index)
            {
              if(!state.active[thread_index])
                continue;
              const std::size_t pc = state.pcs[thread_index];
              if(pc >= threads[thread_index].locations.size())
                continue;
              const auto join = threads[thread_index].join_workers.find(pc);
              if(
                threads[thread_index].spawn_workers.count(pc) != 0 ||
                (join != threads[thread_index].join_workers.end() &&
                 state.completed[join->second]) ||
                threads[thread_index].locations[pc]->is_end_function())
              {
                selected = thread_index;
                break;
              }
            }
          }
          if(selected == threads.size())
          {
            for(std::size_t thread_index = 0;
                thread_index < threads.size(); ++thread_index)
            {
              if(
                state.active[thread_index] &&
                invisible_local_step(
                  threads[thread_index], state.pcs[thread_index]))
              {
                selected = thread_index;
                break;
              }
            }
          }
          if(selected == threads.size())
            return true;
          const auto &selected_thread = threads[selected];
          const std::size_t selected_pc = state.pcs[selected];
          if(selected_pc >= selected_thread.locations.size())
          {
            fail("normalized_pc");
            return false;
          }
          const auto selected_location =
            selected_thread.locations[selected_pc];
          if(
            selected_thread.spawn_workers.count(selected_pc) == 0 &&
            selected_thread.join_workers.count(selected_pc) == 0 &&
            (selected_location->is_skip() ||
             selected_location->is_location() ||
             selected_location->is_decl() ||
             selected_location->is_dead() ||
             selected_location->is_set_return_value()))
          {
            if(selected_location->is_decl() || selected_location->is_dead())
            {
              const exprt &object = selected_location->is_decl()
                ? static_cast<const exprt &>(selected_location->decl_symbol())
                : static_cast<const exprt &>(selected_location->dead_symbol());
              const auto tracked = symbol_indices.find(object);
              if(tracked != symbol_indices.end())
                mutable_state_values(state)[tracked->second] = nil_value_id;
            }
            state.pcs[selected] = selected_pc + 1;
            continue;
          }
          bool step_reachable = true;
          if(!deterministic_step_in_place(
               selected, state, step_reachable))
            return false;
          if(++transition_count > max_transitions)
          {
            fail("transition_cap");
            return false;
          }
          if(
            std::getenv("DEAGLE_FINITE_PRODUCT_AUDIT") != nullptr &&
            transition_count % 1000000 == 0)
          {
            std::cout << "V225_FINITE_PRODUCT_PROGRESS transitions="
                      << transition_count << " states=" << visited.size()
                      << " pending=" << pending.size() << std::endl;
          }
          if(!step_reachable)
          {
            reachable = false;
            return true;
          }
        }
      };
    bool initial_reachable = true;
    if(!normalize_state(initial, initial_reachable))
      return report_unknown();
    if(!initial_reachable)
      return fail_run("unreachable_initial_state");
    visited.insert(key(initial));
    pending.push_back(std::move(initial));
    auto compute_successors =
      [&](const std::size_t thread_index,
          const finite_product_statet &state,
          std::vector<finite_product_statet> &result)
      {
        std::vector<finite_product_statet> successors;
        if(!step(thread_index, state, successors))
          return false;
        for(auto &successor : successors)
        {
          ++transition_count;
          if(transition_count > max_transitions)
          {
            fail("transition_cap");
            return false;
          }
          if(
            std::getenv("DEAGLE_FINITE_PRODUCT_AUDIT") != nullptr &&
            transition_count % 1000000 == 0)
          {
            std::cout << "V225_FINITE_PRODUCT_PROGRESS transitions="
                      << transition_count << " states=" << visited.size()
                      << " pending=" << pending.size() << std::endl;
          }
          bool reachable = true;
          if(!normalize_state(successor, reachable))
            return false;
          if(reachable)
            result.push_back(std::move(successor));
        }
        return true;
      };

    while(!pending.empty())
    {
      finite_product_statet state = std::move(pending.front());
      pending.pop_front();
      std::vector<std::size_t> enabled;
      for(std::size_t thread_index = 0; thread_index < threads.size();
          ++thread_index)
      {
        if(!state.active[thread_index])
          continue;
        const std::size_t pc = state.pcs[thread_index];
        if(pc >= threads[thread_index].locations.size())
          continue;
        const auto join = threads[thread_index].join_workers.find(pc);
        if(
          join != threads[thread_index].join_workers.end() &&
          !state.completed[join->second])
          continue;
        enabled.push_back(thread_index);
      }
      for(const auto thread_index : enabled)
      {
        std::vector<finite_product_statet> successors;
        if(!compute_successors(thread_index, state, successors))
          return report_unknown();
        for(auto &successor : successors)
        {
          const std::string state_key = key(successor);
          if(visited.insert(state_key).second)
          {
            if(visited.size() > max_states)
              return fail_run("state_cap");
            pending.push_back(std::move(successor));
          }
        }
      }
    }

    std::cout << "V225_FINITE_PRODUCT result=SAFE workers="
              << threads.size() - 1 << " symbols=" << symbols.size()
              << " states=" << visited.size()
              << " transitions=" << transition_count << '\n';
    return interference_predicate_resultt::SAFE;
  }

private:
  static constexpr std::size_t max_workers = 5;
  // Diagnostic headroom only: the release gate still needs a structural
  // resource predictor that excludes the expensive recursive-MCS product.
  static constexpr std::size_t max_symbols = 340;
  static constexpr std::size_t max_locations_per_worker = 2048;
  static constexpr std::size_t max_states = 5000000;
  static constexpr std::size_t max_transitions = 20000000;
  static constexpr std::size_t max_assignment_normalization_cache_entries =
    4096;

  goto_modelt &model;
  namespacet ns;
  std::vector<finite_product_threadt> threads;
  std::vector<exprt> symbols;
  std::unordered_map<exprt, std::size_t, irep_hash> symbol_indices;
  std::vector<finite_product_symmetry_groupt> symmetry_groups;
  std::vector<bool> symmetric_thread_mask;
  std::vector<bool> symmetric_slot_mask;
  std::unordered_map<exprt, std::size_t, irep_hash> state_value_ids;
  std::vector<exprt> state_values;
  std::unordered_map<exprt, exprt, irep_hash> assignment_normalization_cache;
  std::vector<int> slot_owners;
  std::vector<std::vector<std::set<std::size_t>>> live_local_slots;
  std::vector<std::vector<std::vector<bool>>> live_local_slot_masks;
  bool failed = false;
  std::string failure_reason;
  std::size_t transition_count = 0;
  std::size_t diagnostic_thread = static_cast<std::size_t>(-1);
  unsigned diagnostic_location = 0;


  static constexpr std::size_t nil_value_id =
    std::numeric_limits<std::size_t>::max();

  std::size_t intern_state_value(const exprt &value)
  {
    if(value.is_nil())
      return nil_value_id;
    INVARIANT(
      is_exact_constant(value),
      "finite product states contain exact constants");
    const auto inserted =
      state_value_ids.emplace(value, state_values.size());
    if(inserted.second)
      state_values.push_back(value);
    return inserted.first->second;
  }

  const exprt &state_value(const std::size_t id) const
  {
    PRECONDITION(id != nil_value_id && id < state_values.size());
    return state_values[id];
  }

  static std::vector<std::size_t> &mutable_state_values(
    finite_product_statet &state)
  {
    if(!state.values.unique())
      state.values =
        std::make_shared<std::vector<std::size_t>>(*state.values);
    return *state.values;
  }

  void fail(const std::string &reason)
  {
    failed = true;
    failure_reason = reason;
  }

  interference_predicate_resultt fail_run(const std::string &reason)
  {
    fail(reason);
    return report_unknown();
  }

  interference_predicate_resultt report_unknown() const
  {
    std::cout << "V225_FINITE_PRODUCT result=UNKNOWN reason="
              << failure_reason << " states_or_transitions="
              << transition_count << '\n';
    return interference_predicate_resultt::UNKNOWN;
  }

  static bool is_exact_constant(const exprt &expr)
  {
    if(
      expr.is_true() || expr.is_false() || expr.id() == ID_constant ||
      (expr.id() == ID_address_of &&
       exact_product_lvalue(to_address_of_expr(expr).object())) ||
      (expr.id() == ID_typecast && expr.operands().size() == 1 &&
       is_exact_constant(to_typecast_expr(expr).op())))
      return true;
    if(expr.id() != ID_plus || expr.type().id() != ID_pointer)
      return false;
    std::size_t pointer_operands = 0;
    for(const auto &operand : expr.operands())
    {
      if(!is_exact_constant(operand))
        return false;
      if(operand.type().id() == ID_pointer)
        ++pointer_operands;
    }
    return pointer_operands == 1;
  }

  bool product_scalar_object(const exprt &input) const
  {
    const exprt &expr = skip_typecast(input);
    const typet &type = ns.follow(expr.type());
    if(
      type.id() == ID_array ||
      type.id() == ID_struct || type.id() == ID_union ||
      type.id() == ID_code)
      return false;
    const exprt *root = &expr;
    while(root->id() == ID_member)
      root = &to_member_expr(*root).struct_op();
    if(root->id() != ID_symbol)
      return false;
    const symbolt *symbol = nullptr;
    return
      !ns.lookup(to_symbol_expr(*root).get_identifier(), symbol) &&
      !symbol->is_type;
  }

  bool finite_index_elements(
    const exprt &input,
    std::vector<exprt> &elements) const
  {
    const exprt &expr = skip_typecast(input);
    if(expr.id() == ID_member)
    {
      const typet &element_type = ns.follow(expr.type());
      if(
        element_type.id() == ID_array || element_type.id() == ID_struct ||
        element_type.id() == ID_union || element_type.id() == ID_code)
        return false;
      std::vector<std::pair<irep_idt, typet>> member_path;
      const exprt *base_cursor = &expr;
      while(skip_typecast(*base_cursor).id() == ID_member)
      {
        const auto &member =
          to_member_expr(skip_typecast(*base_cursor));
        member_path.emplace_back(
          member.get_component_name(), member.type());
        base_cursor = &member.struct_op();
      }
      const exprt &base = skip_typecast(*base_cursor);
      if(base.id() != ID_index)
        return false;
      const auto &index = to_index_expr(base);
      const exprt &array = skip_typecast(index.array());
      const typet &array_type = ns.follow(array.type());
      if(
        array_type.id() != ID_array || array.id() != ID_symbol ||
        !direct_product_lvalue(array))
        return false;
      const auto size =
        numeric_cast<std::size_t>(to_array_type(array_type).size());
      constexpr std::size_t max_finite_member_elements = 8;
      if(
        !size.has_value() || *size == 0 ||
        *size > max_finite_member_elements)
        return false;
      elements.clear();
      elements.reserve(*size);
      for(std::size_t element = 0; element < *size; ++element)
      {
        exprt candidate = index_exprt(
          array, from_integer(element, index.index().type()), base.type());
        for(auto member = member_path.rbegin();
            member != member_path.rend(); ++member)
          candidate = member_exprt(
            std::move(candidate), member->first, member->second);
        candidate = simplify_expr(std::move(candidate), ns);
        if(!direct_product_lvalue(candidate))
          return false;
        elements.push_back(std::move(candidate));
      }
      return true;
    }
    if(expr.id() != ID_index)
      return false;
    const auto &index = to_index_expr(expr);
    const exprt &array = skip_typecast(index.array());
    const typet &array_type = ns.follow(array.type());
    if(
      array_type.id() != ID_array ||
      (!direct_product_lvalue(array) &&
       !state_resolvable_address_object(array)))
      return false;
    const auto size =
      numeric_cast<std::size_t>(to_array_type(array_type).size());
    constexpr std::size_t max_finite_index_elements = 8;
    if(
      !size.has_value() || *size == 0 ||
      *size > max_finite_index_elements)
      return false;
    const typet &element_type = ns.follow(expr.type());
    if(
      element_type.id() == ID_array || element_type.id() == ID_struct ||
      element_type.id() == ID_union || element_type.id() == ID_code)
      return false;
    elements.clear();
    elements.reserve(*size);
    for(std::size_t element = 0; element < *size; ++element)
    {
      exprt constant_index = from_integer(element, index.index().type());
      exprt candidate = index_exprt(array, constant_index, expr.type());
      candidate = simplify_expr(std::move(candidate), ns);
      if(!direct_product_lvalue(candidate))
        return false;
      elements.push_back(std::move(candidate));
    }
    return true;
  }

  bool finite_index_lvalue(const exprt &lhs) const
  {
    std::vector<exprt> elements;
    if(!finite_index_elements(lhs, elements))
      return false;
    return std::all_of(
      elements.begin(),
      elements.end(),
      [&](const exprt &element) {
        return symbol_indices.find(element) != symbol_indices.end();
      });
  }

  bool finite_address_index_supported(const exprt &input) const
  {
    const exprt &object = skip_typecast(input);
    if(object.id() == ID_member)
      return finite_address_index_supported(
        to_member_expr(object).struct_op());
    if(object.id() != ID_index)
      return false;
    const auto &index = to_index_expr(object);
    const exprt &array = skip_typecast(index.array());
    const typet &array_type = ns.follow(array.type());
    if(
      array_type.id() != ID_array ||
      (!direct_product_lvalue(array) &&
       !state_resolvable_address_object(array)))
      return false;
    const auto size =
      numeric_cast<std::size_t>(to_array_type(array_type).size());
    constexpr std::size_t max_finite_address_elements = 8;
    return
      size.has_value() && *size != 0 &&
      *size <= max_finite_address_elements &&
      expression_supported(index.index());
  }

  bool finite_dereference_lvalue(const exprt &input) const
  {
    const exprt &lhs = skip_typecast(input);
    if(lhs.id() != ID_dereference)
      return false;
    const typet &type = ns.follow(lhs.type());
    return
      type.id() != ID_array && type.id() != ID_struct &&
      type.id() != ID_union &&
      expression_supported(to_dereference_expr(lhs).pointer());
  }

  bool finite_byte_extract_lvalue(const exprt &input) const
  {
    const exprt &lhs = skip_typecast(input);
    if(!finite_product_byte_extract_lvalue_shape(lhs))
      return false;
    return expression_supported(to_byte_extract_expr(lhs).offset());
  }

  bool exact_pointer_object(const exprt &input, exprt &object) const
  {
    const exprt &pointer = skip_typecast(input);
    if(pointer.id() == ID_address_of)
    {
      const exprt &candidate = to_address_of_expr(pointer).object();
      if(!exact_in_bounds_product_lvalue(candidate))
        return false;
      object = candidate;
      return true;
    }
    if(pointer.id() == ID_symbol && input.type().id() == ID_pointer)
    {
      const typet &array_type = ns.follow(pointer.type());
      if(array_type.id() == ID_array)
      {
        const auto size = numeric_cast<std::size_t>(
          to_array_type(array_type).size());
        if(!size.has_value() || *size == 0)
          return false;
        object = index_exprt(
          pointer,
          from_integer(0, to_array_type(array_type).index_type()),
          to_array_type(array_type).element_type());
        object = simplify_expr(std::move(object), ns);
        return exact_in_bounds_product_lvalue(object);
      }
    }
    if(pointer.id() != ID_plus || pointer.operands().size() != 2)
      return false;
    const exprt *base_pointer = nullptr;
    const exprt *offset = nullptr;
    for(const auto &operand : pointer.operands())
    {
      if(skip_typecast(operand).type().id() == ID_pointer)
        base_pointer = &operand;
      else
        offset = &operand;
    }
    if(base_pointer == nullptr || offset == nullptr)
      return false;
    exprt base_object;
    if(!exact_pointer_object(*base_pointer, base_object))
      return false;
    const exprt &base = skip_typecast(base_object);
    if(base.id() != ID_index)
      return false;
    const auto base_index = numeric_cast<std::size_t>(
      skip_typecast(to_index_expr(base).index()));
    const auto exact_offset =
      numeric_cast<std::size_t>(skip_typecast(*offset));
    if(!base_index.has_value() || !exact_offset.has_value())
      return false;
    const exprt &array = skip_typecast(to_index_expr(base).array());
    const typet &array_type = ns.follow(array.type());
    if(array_type.id() != ID_array)
      return false;
    const auto size =
      numeric_cast<std::size_t>(to_array_type(array_type).size());
    if(
      !size.has_value() || *base_index >= *size ||
      *exact_offset >= *size - *base_index)
      return false;
    object = index_exprt(
      array,
      from_integer(
        *base_index + *exact_offset,
        to_index_expr(base).index().type()),
      base.type());
    object = simplify_expr(std::move(object), ns);
    return exact_product_lvalue(object);
  }

  bool exact_in_bounds_product_lvalue(const exprt &input) const
  {
    const exprt &object = skip_typecast(input);
    if(object.id() == ID_symbol)
      return true;
    if(object.id() == ID_member)
      return exact_in_bounds_product_lvalue(
        to_member_expr(object).struct_op());
    if(object.id() != ID_index)
      return false;
    const auto &index = to_index_expr(object);
    const auto exact_index =
      numeric_cast<std::size_t>(skip_typecast(index.index()));
    const typet &array_type = ns.follow(index.array().type());
    if(array_type.id() != ID_array || !exact_index.has_value())
      return false;
    const auto size =
      numeric_cast<std::size_t>(to_array_type(array_type).size());
    return
      size.has_value() && *exact_index < *size &&
      exact_in_bounds_product_lvalue(index.array());
  }

  void canonicalize_exact_pointer(exprt &value) const
  {
    if(value.type().id() != ID_pointer)
      return;
    exprt object;
    if(!exact_pointer_object(value, object))
      return;
    exprt address = address_of_exprt(std::move(object));
    value = typecast_exprt::conditional_cast(address, value.type());
  }

  void canonicalize_exact_pointers(exprt &value) const
  {
    for(auto &operand : value.operands())
      canonicalize_exact_pointers(operand);
    if(value.type().id() == ID_pointer)
    {
      canonicalize_exact_pointer(value);
      return;
    }
    value = simplify_expr(std::move(value), ns);
  }

  static bool distinct_exact_array_elements(
    const exprt &left_input,
    const exprt &right_input)
  {
    const exprt &left = skip_typecast(left_input);
    const exprt &right = skip_typecast(right_input);
    if(left.id() != ID_index || right.id() != ID_index)
      return false;
    const auto &left_index = to_index_expr(left);
    const auto &right_index = to_index_expr(right);
    if(left_index.array() != right_index.array())
      return false;
    const auto left_value = numeric_cast<mp_integer>(
      skip_typecast(left_index.index()));
    const auto right_value = numeric_cast<mp_integer>(
      skip_typecast(right_index.index()));
    return
      left_value.has_value() && right_value.has_value() &&
      *left_value != *right_value;
  }

  bool distinct_static_root_objects(
    const exprt &left,
    const exprt &right) const
  {
    const exprt *left_root = direct_product_root_symbol(left);
    const exprt *right_root = direct_product_root_symbol(right);
    if(left_root == nullptr || right_root == nullptr)
      return false;
    const irep_idt &left_id =
      to_symbol_expr(*left_root).get_identifier();
    const irep_idt &right_id =
      to_symbol_expr(*right_root).get_identifier();
    if(left_id == right_id)
      return false;
    const symbolt *left_symbol = nullptr;
    const symbolt *right_symbol = nullptr;
    return
      !ns.lookup(left_id, left_symbol) &&
      !ns.lookup(right_id, right_symbol) &&
      left_symbol->is_static_lifetime && right_symbol->is_static_lifetime;
  }

  void evaluate_exact_pointer_comparisons(exprt &value) const
  {
    for(auto &operand : value.operands())
      evaluate_exact_pointer_comparisons(operand);
    if(
      (value.id() != ID_equal && value.id() != ID_notequal) ||
      value.operands().size() != 2)
      return;
    exprt objects[2];
    bool exact_objects[2] = {false, false};
    bool null_operands[2] = {false, false};
    for(std::size_t index = 0; index < 2; ++index)
    {
      const exprt &candidate = skip_typecast(value.operands()[index]);
      null_operands[index] =
        candidate.id() == ID_constant &&
        candidate.type().id() == ID_pointer &&
        is_null_pointer(to_constant_expr(candidate));
      if(!null_operands[index])
        exact_objects[index] =
          exact_pointer_object(value.operands()[index], objects[index]);
    }
    bool equality;
    if(
      (null_operands[0] && exact_objects[1]) ||
      (null_operands[1] && exact_objects[0]))
      equality = false;
    else if(exact_objects[0] && exact_objects[1])
    {
      if(objects[0] == objects[1])
        equality = true;
      else if(distinct_exact_array_elements(objects[0], objects[1]))
        equality = false;
      else if(distinct_static_root_objects(objects[0], objects[1]))
        equality = false;
      else
        return;
    }
    else
      return;
    if(value.id() == ID_equal)
    {
      if(equality)
        value = true_exprt();
      else
        value = false_exprt();
    }
    else
    {
      if(equality)
        value = false_exprt();
      else
        value = true_exprt();
    }
  }

  bool overwrites_tracked_member(const exprt &input) const
  {
    const exprt &lhs = skip_typecast(input);
    if(lhs.id() != ID_symbol)
      return false;
    for(const auto &object : symbols)
    {
      const exprt *root = &object;
      bool has_member = false;
      while(root->id() == ID_member)
      {
        has_member = true;
        root = &to_member_expr(*root).struct_op();
      }
      if(has_member && *root == lhs)
        return true;
    }
    return false;
  }

  bool aggregate_member_updates(
    const exprt &input_lhs,
    const exprt &input_rhs,
    std::vector<std::pair<std::size_t, exprt>> &updates) const
  {
    const exprt &lhs = skip_typecast(input_lhs);
    if(lhs.id() != ID_symbol)
      return false;
    for(std::size_t index = 0; index < symbols.size(); ++index)
    {
      const exprt &object = symbols[index];
      const exprt *root = &object;
      bool has_member = false;
      while(root->id() == ID_member)
      {
        has_member = true;
        root = &to_member_expr(*root).struct_op();
      }
      if(!has_member || *root != lhs)
        continue;
      exprt projected = object;
      if(replace_expr(lhs, input_rhs, projected))
        return false;
      updates.emplace_back(index, std::move(projected));
    }
    return !updates.empty();
  }

  bool apply_assignment(
    const exprt &lhs,
    const exprt &rhs,
    finite_product_statet &state)
  {
    const auto tracked = symbol_indices.find(lhs);
    std::vector<std::pair<std::size_t, exprt>> updates;
    if(tracked != symbol_indices.end())
      updates.emplace_back(tracked->second, rhs);
    else if(skip_typecast(lhs).id() == ID_dereference)
    {
      exprt pointer =
        to_dereference_expr(skip_typecast(lhs)).pointer();
      substitute_state_values(pointer, state);
      pointer = simplify_expr(std::move(pointer), ns);
      canonicalize_exact_pointer(pointer);
      exprt object;
      if(!exact_pointer_object(pointer, object))
        return fail_step("finite_dereference_target");
      const auto exact = symbol_indices.find(object);
      if(exact == symbol_indices.end())
        return fail_step("finite_dereference_slot");
      updates.emplace_back(exact->second, rhs);
    }
    else if(
      skip_typecast(lhs).id() == ID_byte_extract_little_endian ||
      skip_typecast(lhs).id() == ID_byte_extract_big_endian)
    {
      const auto &extract = to_byte_extract_expr(skip_typecast(lhs));
      exprt exact_offset;
      if(!evaluate(extract.offset(), state, exact_offset))
        return false;
      exact_offset = simplify_expr(std::move(exact_offset), ns);
      const auto offset = numeric_cast<mp_integer>(exact_offset);
      if(!offset.has_value() || *offset < 0)
        return fail_step("finite_byte_extract_offset");
      const auto object = get_subexpression_at_offset(
        extract.op(), *offset, extract.type(), ns);
      if(
        !object.has_value() ||
        !exact_in_bounds_product_lvalue(*object) ||
        object->id() == ID_byte_extract_little_endian ||
        object->id() == ID_byte_extract_big_endian)
        return fail_step("finite_byte_extract_target");
      const auto exact = symbol_indices.find(*object);
      auto exact_slot = exact;
      if(exact_slot == symbol_indices.end())
      {
        std::size_t path_matches = 0;
        for(auto candidate = symbol_indices.begin();
            candidate != symbol_indices.end(); ++candidate)
        {
          if(
            candidate->first.type() == extract.type() &&
            same_exact_product_object(candidate->first, *object))
          {
            exact_slot = candidate;
            ++path_matches;
          }
        }
        if(path_matches != 1)
        {
          const auto base_offset = compute_pointer_offset(extract.op(), ns);
          const exprt *base_root = direct_product_root_symbol(extract.op());
          std::size_t matches = 0;
          if(base_offset.has_value() && base_root != nullptr)
          {
            const mp_integer absolute_offset = *base_offset + *offset;
            for(auto candidate = symbol_indices.begin();
                candidate != symbol_indices.end(); ++candidate)
            {
              if(candidate->first.type() != extract.type())
                continue;
              const exprt *candidate_root =
                direct_product_root_symbol(candidate->first);
              if(
                candidate_root == nullptr ||
                to_symbol_expr(*candidate_root).get_identifier() !=
                  to_symbol_expr(*base_root).get_identifier())
                continue;
              const auto candidate_offset =
                compute_pointer_offset(candidate->first, ns);
              if(
                !candidate_offset.has_value() ||
                *candidate_offset != absolute_offset)
                continue;
              exact_slot = candidate;
              ++matches;
            }
          }
          if(matches != 1)
          {
            if(std::getenv("DEAGLE_FINITE_PRODUCT_AUDIT") != nullptr)
            {
              std::cout << "V225_FINITE_PRODUCT_BYTE_EXTRACT_SLOT lhs={"
                        << from_expr(ns, irep_idt(), lhs) << "} offset={"
                        << from_expr(ns, irep_idt(), exact_offset)
                        << "} object={" << from_expr(ns, irep_idt(), *object)
                        << "} path_matches=" << path_matches
                        << " matches=" << matches << std::endl;
              const exprt *wanted_root = direct_product_root_symbol(*object);
              for(const auto &candidate : symbol_indices)
              {
                const exprt *candidate_root =
                  direct_product_root_symbol(candidate.first);
                if(
                  wanted_root == nullptr || candidate_root == nullptr ||
                  to_symbol_expr(*candidate_root).get_identifier() !=
                    to_symbol_expr(*wanted_root).get_identifier())
                  continue;
                std::cout
                  << "V225_FINITE_PRODUCT_BYTE_EXTRACT_CANDIDATE object={"
                  << from_expr(ns, irep_idt(), candidate.first)
                  << "} same_path="
                  << same_exact_product_object(candidate.first, *object)
                  << " same_type="
                  << (candidate.first.type() == extract.type())
                  << " candidate_type={" << candidate.first.type().pretty()
                  << "} target_type={" << extract.type().pretty() << "}"
                  << std::endl;
              }
            }
            return fail_step("finite_byte_extract_slot");
          }
        }
      }
      updates.emplace_back(exact_slot->second, rhs);
    }
    else if(finite_index_lvalue(lhs))
    {
      exprt exact_lhs = lhs;
      substitute_lvalue_indices(exact_lhs, state);
      exact_lhs = simplify_expr(std::move(exact_lhs), ns);
      auto exact = symbol_indices.find(exact_lhs);
      if(exact == symbol_indices.end())
      {
        std::size_t matches = 0;
        for(auto candidate = symbol_indices.begin();
            candidate != symbol_indices.end(); ++candidate)
        {
          if(
            candidate->first.type() == exact_lhs.type() &&
            same_exact_product_object(candidate->first, exact_lhs))
          {
            exact = candidate;
            ++matches;
          }
        }
        if(matches != 1)
          return fail_step("finite_index_target");
      }
      if(exact == symbol_indices.end())
        return fail_step("finite_index_target");
      updates.emplace_back(exact->second, rhs);
    }
    else if(overwrites_tracked_member(lhs))
    {
      if(!aggregate_member_updates(lhs, rhs, updates))
        return fail_step("aggregate_assignment_projection");
    }
    for(auto &update : updates)
    {
      exprt value;
      if(!evaluate(update.second, state, value))
        return false;
      const typet &target_type = symbols[update.first].type();
      if(value.type() != target_type)
        value = typecast_exprt::conditional_cast(value, target_type);
      const auto cached = assignment_normalization_cache.find(value);
      if(cached != assignment_normalization_cache.end())
        value = cached->second;
      else
      {
        const exprt unnormalized = value;
        value = simplify_expr(std::move(value), ns);
        canonicalize_exact_pointer(value);
        if(
          assignment_normalization_cache.size() <
          max_assignment_normalization_cache_entries)
          assignment_normalization_cache.emplace(unnormalized, value);
      }
      if(!is_exact_constant(value))
        return fail_step("assignment_cast");
      update.second = std::move(value);
    }
    for(auto &update : updates)
      mutable_state_values(state)[update.first] =
        intern_state_value(update.second);
    return true;
  }

  bool expression_mentions_shared_object(const exprt &input) const
  {
    const exprt &expr = skip_typecast(input);
    if(expr.id() == ID_symbol)
    {
      const symbolt *symbol = nullptr;
      return
        !ns.lookup(to_symbol_expr(expr).get_identifier(), symbol) &&
        !symbol->is_type && symbol->is_static_lifetime &&
        !symbol->is_thread_local;
    }
    for(const auto &operand : expr.operands())
    {
      if(expression_mentions_shared_object(operand))
        return true;
    }
    return false;
  }

  bool address_computation_reads_shared_value(const exprt &input) const
  {
    const exprt &object = skip_typecast(input);
    if(object.id() == ID_symbol)
      return false;
    if(object.id() == ID_member)
      return address_computation_reads_shared_value(
        to_member_expr(object).struct_op());
    if(object.id() == ID_index)
      return
        address_computation_reads_shared_value(
          to_index_expr(object).array()) ||
        expression_reads_shared_value(to_index_expr(object).index());
    if(object.id() == ID_dereference)
      return expression_reads_shared_value(
        to_dereference_expr(object).pointer());
    for(const auto &operand : object.operands())
    {
      if(expression_reads_shared_value(operand))
        return true;
    }
    return false;
  }

  bool expression_reads_shared_value(const exprt &input) const
  {
    const exprt &expr = skip_typecast(input);
    if(expr.id() == ID_address_of)
      return address_computation_reads_shared_value(
        to_address_of_expr(expr).object());
    if(expr.id() == ID_symbol)
    {
      const symbolt *symbol = nullptr;
      return
        !ns.lookup(to_symbol_expr(expr).get_identifier(), symbol) &&
        !symbol->is_type && symbol->is_static_lifetime &&
        !symbol->is_thread_local;
    }
    for(const auto &operand : expr.operands())
    {
      if(expression_reads_shared_value(operand))
        return true;
    }
    return false;
  }

  bool invisible_local_step(
    const finite_product_threadt &thread,
    const std::size_t pc) const
  {
    if(pc >= thread.locations.size())
      return false;
    const auto location = thread.locations[pc];
    if(
      thread.spawn_workers.count(pc) != 0 ||
      thread.join_workers.count(pc) != 0 || location->is_atomic_begin() ||
      location->is_atomic_end() || location->is_end_function() ||
      location->is_assert())
      return false;
    if(location->is_assign())
    {
      irep_idt local_identifier;
      return
        product_thread_local_symbol(
          location->assign_lhs(), ns, local_identifier) &&
        !finite_boolean_nondet_assignment(
          location->assign_lhs(), location->assign_rhs()) &&
        !expression_reads_shared_value(location->assign_rhs());
    }
    if(location->is_assume() || location->is_goto())
      return !expression_mentions_shared_object(location->condition());
    return
      location->is_skip() || location->is_location() ||
      location->is_decl() || location->is_dead() ||
      location->is_set_return_value();
  }

  bool finite_boolean_nondet_assignment(
    const exprt &lhs,
    const exprt &rhs) const
  {
    const exprt &value = skip_typecast(rhs);
    if(
      value.id() != ID_side_effect ||
      value.get(ID_statement) != ID_nondet ||
      !value.operands().empty())
      return false;
    if(symbol_indices.find(lhs) == symbol_indices.end())
      return false;
    const typet &type = ns.follow(lhs.type());
    return type.id() == ID_bool || type.id() == ID_c_bool;
  }

  static std::string replace_all_text(
    std::string text,
    const std::string &from,
    const std::string &to)
  {
    if(from.empty())
      return text;
    std::size_t position = 0;
    while((position = text.find(from, position)) != std::string::npos)
    {
      text.replace(position, from.size(), to);
      position += to.size();
    }
    return text;
  }

  static std::string symmetry_base(const irep_idt &entry)
  {
    const std::string text = id2string(entry);
    const std::size_t marker = text.find("$deagle_instance_");
    return marker == std::string::npos ? text : text.substr(0, marker);
  }

  bool canonical_local_key(
    const irep_idt &identifier,
    const std::size_t thread_index,
    std::string &key) const
  {
    const std::string entry = id2string(threads[thread_index].entry);
    const std::string marker =
      entry + "$deagle_product_t" + std::to_string(thread_index) + "$";
    const std::string text = id2string(identifier);
    if(text.rfind(marker, 0) != 0)
      return false;
    key = replace_all_text(
      text.substr(marker.size()), entry,
      symmetry_base(threads[thread_index].entry));
    return true;
  }

  bool canonicalize_symmetry_expression(
    exprt &expression,
    const std::size_t thread_index) const
  {
    if(expression.id() == ID_symbol)
    {
      const irep_idt identifier =
        to_symbol_expr(expression).get_identifier();
      const symbolt *symbol = nullptr;
      if(
        !ns.lookup(identifier, symbol) && symbol->is_thread_local &&
        !symbol->is_type)
      {
        std::string key;
        if(!canonical_local_key(identifier, thread_index, key))
          return false;
        expression = symbol_exprt("__product_local$" + key, expression.type());
        return true;
      }
    }
    for(auto &operand : expression.operands())
    {
      if(!canonicalize_symmetry_expression(operand, thread_index))
        return false;
    }
    return true;
  }

  bool thread_signature(
    const std::size_t thread_index,
    std::string &signature) const
  {
    const auto &thread = threads[thread_index];
    std::ostringstream out;
    for(std::size_t pc = 0; pc < thread.locations.size(); ++pc)
    {
      const auto location = thread.locations[pc];
      exprt code = location->code();
      if(!canonicalize_symmetry_expression(code, thread_index))
        return false;
      out << static_cast<unsigned>(location->type()) << ':' << code.pretty();
      if(location->has_condition())
      {
        exprt condition = location->condition();
        if(!canonicalize_symmetry_expression(condition, thread_index))
          return false;
        out << '?' << condition.pretty();
      }
      out << "->";
      for(const auto target : location->targets)
      {
        const auto found = thread.indices.find(&*target);
        if(found == thread.indices.end())
          return false;
        out << found->second << ',';
      }
      out << ';';
    }
    signature = out.str();
    return true;
  }

  void build_symmetry_groups()
  {
    std::map<std::string, std::vector<std::size_t>> candidates;
    for(std::size_t thread_index = 1; thread_index < threads.size();
        ++thread_index)
      candidates[symmetry_base(threads[thread_index].entry)].push_back(
        thread_index);
    for(const auto &candidate : candidates)
    {
      if(candidate.second.size() < 2)
        continue;
      std::string reference_signature;
      if(!thread_signature(candidate.second.front(), reference_signature))
        continue;
      bool equivalent = true;
      for(std::size_t index = 1; index < candidate.second.size(); ++index)
      {
        std::string signature;
        if(
          !thread_signature(candidate.second[index], signature) ||
          signature != reference_signature)
        {
          if(
            std::getenv("DEAGLE_FINITE_PRODUCT_AUDIT") != nullptr &&
            !signature.empty())
          {
            std::size_t difference = 0;
            while(
              difference < reference_signature.size() &&
              difference < signature.size() &&
              reference_signature[difference] == signature[difference])
              ++difference;
            std::cout << "V225_FINITE_PRODUCT_SYMMETRY_REJECT base="
                      << candidate.first << " difference=" << difference
                      << " left={"
                      << reference_signature.substr(difference, 160)
                      << "} right={" << signature.substr(difference, 160)
                      << "}\n";
          }
          equivalent = false;
          break;
        }
      }
      if(!equivalent)
        continue;
      std::vector<std::map<std::string, std::size_t>> slots(
        candidate.second.size());
      for(std::size_t member = 0; member < candidate.second.size(); ++member)
      {
        const std::size_t thread_index = candidate.second[member];
        for(std::size_t symbol_index = 0; symbol_index < symbols.size();
            ++symbol_index)
        {
          exprt canonical = symbols[symbol_index];
          const exprt *root = &canonical;
          while(root->id() == ID_member)
            root = &to_member_expr(*root).struct_op();
          if(root->id() != ID_symbol)
            continue;
          std::string local_key;
          if(!canonical_local_key(
               to_symbol_expr(*root).get_identifier(),
               thread_index,
               local_key))
            continue;
          if(!canonicalize_symmetry_expression(canonical, thread_index))
          {
            equivalent = false;
            break;
          }
          slots[member].emplace(canonical.pretty(), symbol_index);
        }
        if(!equivalent)
          break;
      }
      if(!equivalent)
        continue;
      const auto &keys = slots.front();
      for(std::size_t member = 1; member < slots.size(); ++member)
      {
        if(slots[member].size() != keys.size())
        {
          equivalent = false;
          break;
        }
        auto left = keys.begin();
        auto right = slots[member].begin();
        for(; left != keys.end(); ++left, ++right)
        {
          if(left->first != right->first)
          {
            equivalent = false;
            break;
          }
        }
      }
      if(!equivalent)
        continue;
      finite_product_symmetry_groupt group;
      group.threads = candidate.second;
      group.local_slots.resize(candidate.second.size());
      for(const auto &entry : keys)
      {
        for(std::size_t member = 0; member < slots.size(); ++member)
          group.local_slots[member].push_back(
            slots[member].find(entry.first)->second);
      }
      symmetry_groups.push_back(std::move(group));
      if(std::getenv("DEAGLE_FINITE_PRODUCT_AUDIT") != nullptr)
        std::cout << "V225_FINITE_PRODUCT_SYMMETRY base="
                  << candidate.first << " threads="
                  << candidate.second.size() << " local_slots="
                  << keys.size() << '\n';
    }
  }

  void collect_expr_symbols(const exprt &expr, std::set<exprt> &result)
  {
    std::vector<exprt> finite_elements;
    if(finite_index_elements(expr, finite_elements))
    {
      result.insert(finite_elements.begin(), finite_elements.end());
      const exprt *indexed = &expr;
      while(skip_typecast(*indexed).id() == ID_member)
        indexed = &to_member_expr(skip_typecast(*indexed)).struct_op();
      const exprt &base_index = skip_typecast(*indexed);
      if(base_index.id() != ID_index)
        return;
      collect_expr_symbols(to_index_expr(base_index).index(), result);
      return;
    }
    if(
      (expr.id() == ID_symbol || expr.id() == ID_member) &&
      product_scalar_object(expr))
    {
      result.insert(expr);
      return;
    }
    for(const auto &operand : expr.operands())
      collect_expr_symbols(operand, result);
  }

  bool collect_exact_subobjects_of_type(
    const exprt &input,
    const typet &target_type,
    std::set<exprt> &result,
    std::size_t &added) const
  {
    constexpr std::size_t max_byte_extract_targets = 32;
    if(added > max_byte_extract_targets)
      return false;
    const exprt &object = skip_typecast(input);
    const typet &object_type = ns.follow(object.type());
    if(object.type() == target_type)
    {
      if(!exact_product_lvalue(object))
        return false;
      if(result.insert(object).second)
        ++added;
      return added <= max_byte_extract_targets;
    }
    if(object_type.id() == ID_struct)
    {
      for(const auto &component : to_struct_type(object_type).components())
      {
        const member_exprt member(
          object, component.get_name(), component.type());
        if(!collect_exact_subobjects_of_type(
             member, target_type, result, added))
          return false;
      }
      return true;
    }
    if(object_type.id() == ID_array)
    {
      const auto size = numeric_cast<std::size_t>(
        to_array_type(object_type).size());
      constexpr std::size_t max_finite_byte_extract_elements = 8;
      if(
        !size.has_value() || *size == 0 ||
        *size > max_finite_byte_extract_elements)
        return false;
      for(std::size_t index = 0; index < *size; ++index)
      {
        const index_exprt element(
          object,
          from_integer(index, to_array_type(object_type).index_type()),
          to_array_type(object_type).element_type());
        if(!collect_exact_subobjects_of_type(
             element, target_type, result, added))
          return false;
      }
      return true;
    }
    return true;
  }

  void collect_shared_symbols()
  {
    std::set<exprt> found;
    for(const auto &thread : threads)
    {
      for(const auto location : thread.locations)
      {
        if(location->is_assign())
        {
          const exprt &lhs = skip_typecast(location->assign_lhs());
          if(
            lhs.id() == ID_byte_extract_little_endian ||
            lhs.id() == ID_byte_extract_big_endian)
          {
            const auto &extract = to_byte_extract_expr(lhs);
            std::size_t added = 0;
            if(!collect_exact_subobjects_of_type(
                 extract.op(), extract.type(), found, added))
            {
              fail("finite_byte_extract_targets");
              return;
            }
          }
          collect_expr_symbols(location->assign_lhs(), found);
          collect_expr_symbols(location->assign_rhs(), found);
        }
        else if(
          location->is_assume() || location->is_assert() ||
          location->is_goto())
          collect_expr_symbols(location->condition(), found);
      }
    }
    symbols.assign(found.begin(), found.end());
    for(std::size_t index = 0; index < symbols.size(); ++index)
      symbol_indices.emplace(symbols[index], index);
  }

  void collect_thread_local_slots(
    const exprt &expression,
    const std::size_t thread_index,
    std::set<std::size_t> &result) const
  {
    const auto found = symbol_indices.find(expression);
    if(
      found != symbol_indices.end() &&
      slot_owners[found->second] == static_cast<int>(thread_index))
    {
      result.insert(found->second);
      return;
    }
    for(const auto &operand : expression.operands())
      collect_thread_local_slots(operand, thread_index, result);
  }

  bool build_live_local_slots()
  {
    slot_owners.assign(symbols.size(), -1);
    for(std::size_t symbol_index = 0; symbol_index < symbols.size();
        ++symbol_index)
    {
      const exprt *root = &symbols[symbol_index];
      while(root->id() == ID_member)
        root = &to_member_expr(*root).struct_op();
      if(root->id() != ID_symbol)
        continue;
      for(std::size_t thread_index = 0; thread_index < threads.size();
          ++thread_index)
      {
        std::string key;
        if(canonical_local_key(
             to_symbol_expr(*root).get_identifier(), thread_index, key))
        {
          if(slot_owners[symbol_index] != -1)
            return false;
          slot_owners[symbol_index] = static_cast<int>(thread_index);
        }
      }
    }
    live_local_slots.resize(threads.size());
    for(std::size_t thread_index = 0; thread_index < threads.size();
        ++thread_index)
    {
      const auto &thread = threads[thread_index];
      auto &live = live_local_slots[thread_index];
      live.resize(thread.locations.size());
      std::vector<std::set<std::size_t>> live_out(thread.locations.size());
      bool changed = true;
      while(changed)
      {
        changed = false;
        for(std::size_t reverse = thread.locations.size(); reverse != 0;
            --reverse)
        {
          const std::size_t pc = reverse - 1;
          const auto location = thread.locations[pc];
          std::set<std::size_t> out;
          for(const auto successor : thread.program->get_successors(location))
          {
            const auto found = thread.indices.find(&*successor);
            if(found == thread.indices.end())
              return false;
            out.insert(
              live[found->second].begin(), live[found->second].end());
          }
          std::set<std::size_t> in = out;
          if(location->is_assign())
          {
            collect_thread_local_slots(
              location->assign_lhs(), thread_index, in);
            const auto defined = symbol_indices.find(location->assign_lhs());
            if(
              defined != symbol_indices.end() &&
              slot_owners[defined->second] ==
                static_cast<int>(thread_index))
              in.erase(defined->second);
            collect_thread_local_slots(
              location->assign_rhs(), thread_index, in);
          }
          if(location->has_condition())
            collect_thread_local_slots(
              location->condition(), thread_index, in);
          if(in != live[pc] || out != live_out[pc])
          {
            live[pc] = std::move(in);
            live_out[pc] = std::move(out);
            changed = true;
          }
        }
      }
    }
    live_local_slot_masks.resize(threads.size());
    for(std::size_t thread_index = 0; thread_index < threads.size();
        ++thread_index)
    {
      const auto &live = live_local_slots[thread_index];
      auto &masks = live_local_slot_masks[thread_index];
      masks.assign(live.size(), std::vector<bool>(symbols.size(), false));
      for(std::size_t pc = 0; pc < live.size(); ++pc)
      {
        for(const auto slot : live[pc])
          masks[pc][slot] = true;
      }
    }
    live_local_slots.clear();
    live_local_slots.shrink_to_fit();
    return true;
  }

  bool local_slot_live(
    const std::size_t slot,
    const finite_product_statet &state) const
  {
    const int owner = slot_owners[slot];
    if(owner < 0)
      return true;
    const std::size_t thread_index = static_cast<std::size_t>(owner);
    const std::size_t pc = state.pcs[thread_index];
    return
      pc < live_local_slot_masks[thread_index].size() &&
      live_local_slot_masks[thread_index][pc][slot];
  }

  void audit_lifecycle(const std::vector<irep_idt> &thread_ids)
  {
    for(std::size_t thread_index = 0; thread_index < threads.size();
        ++thread_index)
    {
      auto &thread = threads[thread_index];
      for(std::size_t pc = 0; pc < thread.locations.size(); ++pc)
      {
        const auto location = thread.locations[pc];
        const irep_idt &spawn_entry =
          location->source_location().get("v49_thread_entry");
        if(spawn_entry != irep_idt())
        {
          if(thread_index != 0)
            return fail("nested_thread_creation");
          const auto worker =
            std::find(thread_ids.begin() + 1, thread_ids.end(), spawn_entry);
          if(worker == thread_ids.end())
            return fail("spawn_target_not_found");
          thread.spawn_workers.emplace(
            pc, static_cast<std::size_t>(worker - thread_ids.begin()));
          if(std::getenv("DEAGLE_FINITE_PRODUCT_AUDIT") != nullptr)
            std::cout << "V225_FINITE_PRODUCT_SPAWN thread=" << thread_index
                      << " pc=" << pc << " location="
                      << location->location_number << " worker="
                      << static_cast<std::size_t>(worker - thread_ids.begin())
                      << " line=" << location->source_location().get_line()
                      << '\n';
        }
        const irep_idt &join_entry =
          location->source_location().get("v49_join_entry");
        if(join_entry != irep_idt())
        {
          if(thread_index != 0)
            return fail("worker_join");
          const auto worker =
            std::find(thread_ids.begin() + 1, thread_ids.end(), join_entry);
          if(worker == thread_ids.end())
            return fail("join_target_not_found");
          thread.join_workers.emplace(
            pc, static_cast<std::size_t>(worker - thread_ids.begin()));
        }
        if(location->source_location().get_bool("v49_unresolved_join"))
          return fail("unresolved_join");
      }
    }
    for(std::size_t worker = 1; worker < threads.size(); ++worker)
    {
      std::size_t spawns = 0;
      for(const auto &spawn : threads.front().spawn_workers)
        spawns += spawn.second == worker ? 1 : 0;
      if(spawns != 1)
        return fail("worker_spawn_count");
    }
  }

  bool expression_supported(const exprt &expr) const
  {
    if(symbol_indices.find(expr) != symbol_indices.end())
      return true;
    if(expr.id() == ID_dereference)
      return expression_supported(to_dereference_expr(expr).pointer());
    if(expr.id() == ID_address_of)
    {
      const exprt &object = to_address_of_expr(expr).object();
      if(exact_product_lvalue(object))
        return true;
      if(state_resolvable_address_object(object))
        return true;
      if(finite_address_index_supported(object))
        return true;
      std::vector<exprt> elements;
      return
        finite_index_elements(object, elements) &&
        expression_supported(to_index_expr(object).index());
    }
    if(expr.id() == ID_index)
    {
      std::vector<exprt> elements;
      if(!finite_index_elements(expr, elements))
        return false;
      if(
        !std::all_of(
          elements.begin(),
          elements.end(),
          [&](const exprt &element) {
            return symbol_indices.find(element) != symbol_indices.end();
          }))
        return false;
      return expression_supported(to_index_expr(expr).index());
    }
    if(expr.id() == ID_member)
    {
      std::vector<exprt> elements;
      if(finite_index_elements(expr, elements))
      {
        if(
          !std::all_of(
            elements.begin(),
            elements.end(),
            [&](const exprt &element) {
              return symbol_indices.find(element) != symbol_indices.end();
            }))
          return false;
        const exprt *indexed = &expr;
        while(skip_typecast(*indexed).id() == ID_member)
          indexed = &to_member_expr(skip_typecast(*indexed)).struct_op();
        const exprt &base_index = skip_typecast(*indexed);
        if(base_index.id() != ID_index)
          return false;
        return expression_supported(to_index_expr(base_index).index());
      }
    }
    if(
      expr.id() == ID_side_effect)
    {
      if(std::getenv("DEAGLE_FINITE_PRODUCT_AUDIT") != nullptr)
        std::cout << "V225_FINITE_PRODUCT_UNSUPPORTED_EXPR id=" << expr.id()
                  << " expr={" << expr.pretty() << "}\n";
      return false;
    }
    for(const auto &operand : expr.operands())
    {
      if(!expression_supported(operand))
        return false;
    }
    return true;
  }

  bool state_resolvable_address_object(const exprt &input) const
  {
    const exprt &object = skip_typecast(input);
    if(object.id() == ID_symbol)
      return true;
    if(object.id() == ID_member)
      return state_resolvable_address_object(
        to_member_expr(object).struct_op());
    if(object.id() == ID_dereference)
      return expression_supported(to_dereference_expr(object).pointer());
    if(object.id() == ID_index)
      return finite_address_index_supported(object);
    return false;
  }

  void audit_instructions()
  {
    for(const auto &thread : threads)
    {
      unsigned atomic_depth = 0;
      for(const auto location : thread.locations)
      {
        if(location->is_atomic_begin())
        {
          if(atomic_depth != 0)
            return fail("nested_atomic");
          ++atomic_depth;
        }
        else if(location->is_atomic_end())
        {
          if(atomic_depth != 1)
            return fail("unbalanced_atomic_end");
          --atomic_depth;
        }
        else if(location->is_assign())
        {
          const exprt &lhs = location->assign_lhs();
          const auto tracked = symbol_indices.find(lhs);
          const bool finite_index = finite_index_lvalue(lhs);
          const bool finite_dereference =
            finite_dereference_lvalue(lhs);
          const bool finite_byte_extract =
            finite_byte_extract_lvalue(lhs);
          const bool finite_boolean_nondet =
            finite_boolean_nondet_assignment(
              lhs, location->assign_rhs());
          if(finite_boolean_nondet && atomic_depth != 0)
            return fail("atomic_nondet_assignment");
          if(
            (tracked != symbol_indices.end() || finite_index ||
             finite_dereference || finite_byte_extract) &&
            !finite_boolean_nondet &&
            !expression_supported(location->assign_rhs()))
          {
            if(std::getenv("DEAGLE_FINITE_PRODUCT_AUDIT") != nullptr)
              std::cout << "V225_FINITE_PRODUCT_RHS_REJECT entry="
                        << thread.entry << " location="
                        << location->location_number << " lhs={"
                        << from_expr(ns, thread.entry, lhs) << "} rhs={"
                        << from_expr(
                             ns, thread.entry, location->assign_rhs())
                        << "}" << std::endl;
            return fail("unsupported_shared_rhs");
          }
          if(
            tracked == symbol_indices.end() && !finite_index &&
            !finite_dereference && !finite_byte_extract &&
            (!direct_product_lvalue(lhs) || product_scalar_object(lhs)))
          {
            if(std::getenv("DEAGLE_FINITE_PRODUCT_AUDIT") != nullptr)
              std::cout << "V225_FINITE_PRODUCT_LHS_REJECT entry="
                        << thread.entry << " location="
                        << location->location_number << " id=" << lhs.id()
                        << " expr={" << from_expr(ns, thread.entry, lhs)
                        << "}" << std::endl;
            return fail("unsupported_shared_lhs");
          }
          if(tracked == symbol_indices.end() && overwrites_tracked_member(lhs))
          {
            std::vector<std::pair<std::size_t, exprt>> updates;
            if(!aggregate_member_updates(
                 lhs, location->assign_rhs(), updates))
              return fail("aggregate_assignment_projection");
            for(const auto &update : updates)
            {
              if(!expression_supported(update.second))
              {
                if(std::getenv("DEAGLE_FINITE_PRODUCT_AUDIT") != nullptr)
                  std::cout << "V225_FINITE_PRODUCT_AGGREGATE_RHS_REJECT "
                            << "entry=" << thread.entry << " location="
                            << location->location_number << " lhs={"
                            << from_expr(ns, thread.entry, lhs) << "} rhs={"
                            << from_expr(
                                 ns, thread.entry, location->assign_rhs())
                            << "} slot=" << update.first << " projected={"
                            << from_expr(ns, thread.entry, update.second)
                            << "}" << std::endl;
                return fail("unsupported_aggregate_rhs");
              }
            }
          }
        }
        else if(
          (location->is_assume() || location->is_assert() ||
           location->is_goto()) &&
          !expression_supported(location->condition()))
        {
          if(std::getenv("DEAGLE_FINITE_PRODUCT_AUDIT") != nullptr)
            std::cout << "V225_FINITE_PRODUCT_REJECT location="
                      << location->location_number << " condition={"
                      << from_expr(ns, thread.entry, location->condition())
                      << "}\n";
          return fail("unsupported_condition");
        }
        else if(
          location->is_function_call() || location->is_start_thread() ||
          location->is_throw() || location->is_catch() ||
          (location->is_other() && !is_abstract_noop_other(*location)))
          return fail("unsupported_instruction");
      }
      if(atomic_depth != 0)
        return fail("unbalanced_atomic_begin");
    }
  }

  void substitute_state_values(
    exprt &expression,
    const finite_product_statet &state) const
  {
    if(expression.id() == ID_address_of)
    {
      substitute_lvalue_indices(
        to_address_of_expr(expression).object(), state);
      expression = simplify_expr(std::move(expression), ns);
      return;
    }
    if(expression.id() == ID_dereference)
    {
      auto &pointer = to_dereference_expr(expression).pointer();
      substitute_state_values(pointer, state);
      exprt object;
      if(exact_pointer_object(pointer, object))
      {
        const auto target = symbol_indices.find(object);
        if(
          target != symbol_indices.end() &&
          (*state.values)[target->second] != nil_value_id)
        {
          expression = state_value((*state.values)[target->second]);
          return;
        }
        const typet &object_type = ns.follow(object.type());
        if(
          object_type.id() == ID_array || object_type.id() == ID_struct ||
          object_type.id() == ID_union)
        {
          expression = std::move(object);
          return;
        }
      }
      return;
    }
    const auto found = symbol_indices.find(expression);
    if(
      found != symbol_indices.end() &&
      (*state.values)[found->second] != nil_value_id)
    {
      expression = state_value((*state.values)[found->second]);
      return;
    }
    for(auto &operand : expression.operands())
      substitute_state_values(operand, state);
    evaluate_exact_pointer_comparisons(expression);
    expression = simplify_expr(std::move(expression), ns);
    const auto simplified = symbol_indices.find(expression);
    if(
      simplified != symbol_indices.end() &&
      (*state.values)[simplified->second] != nil_value_id)
      expression = state_value((*state.values)[simplified->second]);
  }

  void substitute_lvalue_indices(
    exprt &lvalue,
    const finite_product_statet &state) const
  {
    if(lvalue.id() == ID_index)
    {
      auto &index = to_index_expr(lvalue);
      substitute_lvalue_indices(index.array(), state);
      substitute_state_values(index.index(), state);
      lvalue = simplify_expr(std::move(lvalue), ns);
    }
    else if(lvalue.id() == ID_member)
      substitute_lvalue_indices(to_member_expr(lvalue).struct_op(), state);
    else if(lvalue.id() == ID_dereference)
    {
      auto &pointer = to_dereference_expr(lvalue).pointer();
      substitute_state_values(pointer, state);
      pointer = simplify_expr(std::move(pointer), ns);
      canonicalize_exact_pointer(pointer);
      exprt object;
      if(exact_pointer_object(pointer, object))
        lvalue = std::move(object);
    }
    else if(lvalue.id() == ID_typecast)
      substitute_lvalue_indices(to_typecast_expr(lvalue).op(), state);
  }

  bool evaluate_simple_exact_expression(
    const exprt &input,
    const finite_product_statet &state,
    exprt &result) const
  {
    if(is_exact_constant(input))
    {
      result = input;
      return true;
    }
    const auto tracked = symbol_indices.find(input);
    if(
      tracked != symbol_indices.end() &&
      (*state.values)[tracked->second] != nil_value_id)
    {
      result = state_value((*state.values)[tracked->second]);
      return true;
    }
    if(input.id() == ID_symbol)
      return false;
    if(input.id() == ID_address_of)
    {
      result = input;
      substitute_lvalue_indices(
        to_address_of_expr(result).object(), state);
      result = simplify_expr(std::move(result), ns);
      canonicalize_exact_pointers(result);
      return is_exact_constant(result);
    }
    if(
      input.id() == ID_dereference ||
      input.id() == ID_index || input.id() == ID_member ||
      input.id() == ID_byte_extract_little_endian ||
      input.id() == ID_byte_extract_big_endian ||
      input.id() == ID_pointer_offset || input.id() == ID_side_effect)
      return false;
    result = input;
    for(std::size_t index = 0; index < input.operands().size(); ++index)
    {
      exprt operand;
      if(!evaluate_simple_exact_expression(
           input.operands()[index], state, operand))
        return false;
      result.operands()[index] = std::move(operand);
    }
    result = simplify_expr(std::move(result), ns);
    canonicalize_exact_pointers(result);
    evaluate_exact_pointer_comparisons(result);
    result = simplify_expr(std::move(result), ns);
    return is_exact_constant(result);
  }

  bool evaluate(
    const exprt &input,
    const finite_product_statet &state,
    exprt &result)
  {
    if(evaluate_simple_exact_expression(input, state, result))
      return true;
    result = input;
    substitute_state_values(result, state);
    result = simplify_expr(std::move(result), ns);
    canonicalize_exact_pointers(result);
    evaluate_exact_pointer_comparisons(result);
    result = simplify_expr(std::move(result), ns);
    if(!is_exact_constant(result))
    {
      if(std::getenv("DEAGLE_FINITE_PRODUCT_AUDIT") != nullptr)
      {
        std::cout << "V225_FINITE_PRODUCT_NONCONSTANT thread="
                  << diagnostic_thread << " location="
                  << diagnostic_location << " input={"
                  << from_expr(ns, irep_idt(), input) << "} result={"
                  << from_expr(ns, irep_idt(), result) << "} input_irep={"
                  << input.pretty() << "} result_irep={" << result.pretty()
                  << "}" << std::endl;
        if(diagnostic_thread < threads.size())
        {
          std::set<irep_idt> referenced_ids;
          collect_product_symbol_ids(input, referenced_ids);
          bool definitions_changed = true;
          while(definitions_changed)
          {
            definitions_changed = false;
            for(const auto &definition : threads[diagnostic_thread].locations)
            {
              if(!definition->is_assign())
                continue;
              const exprt &definition_lhs =
                skip_typecast(definition->assign_lhs());
              if(definition_lhs.id() != ID_symbol)
                continue;
              const irep_idt &defined =
                to_symbol_expr(definition_lhs).get_identifier();
              if(referenced_ids.count(defined) == 0)
                continue;
              std::set<irep_idt> rhs_ids;
              collect_product_symbol_ids(
                definition->assign_rhs(), rhs_ids);
              for(const auto &rhs_id : rhs_ids)
                if(referenced_ids.insert(rhs_id).second)
                  definitions_changed = true;
              std::cout << "V225_FINITE_PRODUCT_NONCONSTANT_DEFINITION location="
                        << definition->location_number << " lhs={"
                        << from_expr(ns, threads[diagnostic_thread].entry,
                                     definition->assign_lhs())
                        << "} rhs={"
                        << from_expr(ns, threads[diagnostic_thread].entry,
                                     definition->assign_rhs())
                        << "}" << std::endl;
            }
          }
          for(const auto &slot : symbol_indices)
          {
            const exprt *root = direct_product_root_symbol(slot.first);
            if(
              root == nullptr ||
              referenced_ids.count(
                to_symbol_expr(*root).get_identifier()) == 0)
              continue;
            std::cout << "V225_FINITE_PRODUCT_NONCONSTANT_SLOT object={"
                      << from_expr(ns, irep_idt(), slot.first) << "} value={"
                      << ((*state.values)[slot.second] == nil_value_id
                            ? std::string("<nil>")
                            : from_expr(
                                ns,
                                irep_idt(),
                                state_value((*state.values)[slot.second])))
                      << "}" << std::endl;
          }
          const std::size_t current_pc =
            state.pcs[diagnostic_thread];
          const std::size_t first_pc = current_pc > 12 ? current_pc - 12 : 0;
          for(std::size_t pc = first_pc;
              pc <= current_pc &&
              pc < threads[diagnostic_thread].locations.size(); ++pc)
          {
            const auto prior = threads[diagnostic_thread].locations[pc];
            std::cout << "V225_FINITE_PRODUCT_NONCONSTANT_WINDOW pc=" << pc
                      << " location=" << prior->location_number << " code={"
                      << prior->code().pretty() << "}" << std::endl;
          }
          for(const auto location : threads[diagnostic_thread].locations)
          {
            if(location->location_number != diagnostic_location)
              continue;
            std::cout << "V225_FINITE_PRODUCT_NONCONSTANT_CONTEXT entry="
                      << threads[diagnostic_thread].entry << " source={"
                      << location->source_location().as_string()
                      << "} code={" << location->code().pretty() << "}"
                      << std::endl;
            break;
          }
        }
      }
      fail("nonconstant_evaluation");
      return false;
    }
    return true;
  }

  std::size_t index_of(
    const finite_product_threadt &thread,
    goto_programt::const_targett location)
  {
    const auto found = thread.indices.find(&*location);
    if(found == thread.indices.end())
    {
      fail("successor_not_found");
      return thread.locations.size();
    }
    return found->second;
  }

  bool advance(
    std::size_t thread_index,
    const finite_product_statet &state,
    std::vector<finite_product_statet> &successors,
    goto_programt::const_targett successor)
  {
    finite_product_statet next = state;
    next.pcs[thread_index] = index_of(threads[thread_index], successor);
    if(failed)
      return false;
    successors.push_back(std::move(next));
    return true;
  }

  bool deterministic_step_in_place(
    const std::size_t thread_index,
    finite_product_statet &state,
    bool &reachable)
  {
    reachable = true;
    const auto &thread = threads[thread_index];
    const std::size_t pc = state.pcs[thread_index];
    if(pc >= thread.locations.size())
      return fail_step("deterministic_pc");
    const auto location = thread.locations[pc];
    diagnostic_thread = thread_index;
    diagnostic_location = location->location_number;
    const auto spawn = thread.spawn_workers.find(pc);
    const auto join = thread.join_workers.find(pc);
    if(
      join != thread.join_workers.end() &&
      !state.completed[join->second])
      return fail_step("deterministic_blocked_join");
    if(location->is_end_function())
    {
      state.active[thread_index] = false;
      state.completed[thread_index] = true;
      state.pcs[thread_index] = thread.locations.size();
      if(state.atomic_owner == static_cast<int>(thread_index))
        return fail_step("atomic_end_function");
      return true;
    }
    const auto next_location = std::next(location);
    if(next_location == thread.program->instructions.end())
      return fail_step("deterministic_fallthrough");

    if(location->is_atomic_begin())
    {
      if(state.atomic_owner != -1)
        return fail_step("nested_atomic_runtime");
      state.atomic_owner = static_cast<int>(thread_index);
    }
    else if(location->is_atomic_end())
    {
      if(state.atomic_owner != static_cast<int>(thread_index))
        return fail_step("atomic_owner");
      state.atomic_owner = -1;
    }
    else if(location->is_assign())
    {
      if(finite_boolean_nondet_assignment(
           location->assign_lhs(), location->assign_rhs()))
        return fail_step("deterministic_nondet_assignment");
      if(!apply_assignment(
           location->assign_lhs(), location->assign_rhs(), state))
        return false;
    }

    if(spawn != thread.spawn_workers.end())
    {
      if(state.active[spawn->second] || state.completed[spawn->second])
        return fail_step("worker_reactivation");
      state.active[spawn->second] = true;
    }
    else if(location->is_assert())
    {
      exprt condition;
      if(!evaluate(location->condition(), state, condition))
        return false;
      if(condition.is_false())
        return fail_step("reachable_assertion");
      if(!condition.is_true())
        return fail_step("nonboolean_assertion");
    }
    else if(location->is_assume())
    {
      exprt condition;
      if(!evaluate(location->condition(), state, condition))
        return false;
      if(condition.is_false())
      {
        reachable = false;
        return true;
      }
      if(!condition.is_true())
        return fail_step("nonboolean_assumption");
    }
    else if(location->is_goto())
    {
      exprt condition;
      if(!evaluate(location->condition(), state, condition))
        return false;
      goto_programt::const_targett successor;
      if(condition.is_true())
        successor = location->get_target();
      else if(condition.is_false())
        successor = next_location;
      else
        return fail_step("nonboolean_guard");
      state.pcs[thread_index] = index_of(thread, successor);
      return !failed;
    }

    state.pcs[thread_index] = pc + 1;
    return true;
  }

  bool step(
    std::size_t thread_index,
    const finite_product_statet &state,
    std::vector<finite_product_statet> &successors)
  {
    const auto &thread = threads[thread_index];
    const std::size_t pc = state.pcs[thread_index];
    if(pc >= thread.locations.size())
      return true;
    const auto location = thread.locations[pc];
    diagnostic_thread = thread_index;
    diagnostic_location = location->location_number;

    const auto join = thread.join_workers.find(pc);
    if(join != thread.join_workers.end() && !state.completed[join->second])
      return true;

    const auto spawn = thread.spawn_workers.find(pc);
    if(spawn != thread.spawn_workers.end())
    {
      if(state.active[spawn->second] || state.completed[spawn->second])
      {
        if(std::getenv("DEAGLE_FINITE_PRODUCT_AUDIT") != nullptr)
          std::cout << "V225_FINITE_PRODUCT_REACTIVATION thread="
                    << thread_index << " pc=" << pc << " location="
                    << location->location_number << " worker="
                    << spawn->second << " active="
                    << state.active[spawn->second] << " completed="
                    << state.completed[spawn->second] << " state={"
                    << key(state) << "}\n";
        return fail_step("worker_reactivation");
      }
    }

    if(location->is_end_function())
    {
      finite_product_statet next = state;
      next.active[thread_index] = false;
      next.completed[thread_index] = true;
      next.pcs[thread_index] = thread.locations.size();
      if(next.atomic_owner == static_cast<int>(thread_index))
        return fail_step("atomic_end_function");
      successors.push_back(std::move(next));
      return true;
    }

    auto next_location = std::next(location);
    if(next_location == thread.program->instructions.end())
      return fail_step("missing_fallthrough");

    finite_product_statet base = state;
    if(spawn != thread.spawn_workers.end())
      base.active[spawn->second] = true;

    if(location->is_atomic_begin())
    {
      if(base.atomic_owner != -1)
        return fail_step("nested_atomic_runtime");
      base.atomic_owner = static_cast<int>(thread_index);
    }
    else if(location->is_atomic_end())
    {
      if(base.atomic_owner != static_cast<int>(thread_index))
        return fail_step("atomic_owner");
      base.atomic_owner = -1;
    }
    else if(location->is_assign())
    {
      if(finite_boolean_nondet_assignment(
           location->assign_lhs(), location->assign_rhs()))
      {
        const auto target = symbol_indices.find(location->assign_lhs());
        if(target == symbol_indices.end())
          return fail_step("finite_nondet_slot");
        for(unsigned value = 0; value != 2; ++value)
        {
          finite_product_statet next = base;
          mutable_state_values(next)[target->second] = intern_state_value(
            from_integer(value, symbols[target->second].type()));
          next.pcs[thread_index] = pc + 1;
          successors.push_back(std::move(next));
        }
        return true;
      }
      if(!apply_assignment(
           location->assign_lhs(), location->assign_rhs(), base))
        return false;
    }
    else if(location->is_assert())
    {
      exprt condition;
      if(!evaluate(location->condition(), base, condition))
        return false;
      if(condition.is_false())
        return fail_step("reachable_assertion");
      if(!condition.is_true())
        return fail_step("nonboolean_assertion");
    }
    else if(location->is_assume())
    {
      exprt condition;
      if(!evaluate(location->condition(), base, condition))
        return false;
      if(condition.is_false())
        return true;
      if(!condition.is_true())
        return fail_step("nonboolean_assumption");
    }
    else if(location->is_goto())
    {
      exprt condition;
      if(!evaluate(location->condition(), base, condition))
        return false;
      goto_programt::const_targett successor;
      if(condition.is_true())
        successor = location->get_target();
      else if(condition.is_false())
        successor = next_location;
      else
        return fail_step("nonboolean_guard");
      finite_product_statet next = std::move(base);
      next.pcs[thread_index] = index_of(thread, successor);
      if(failed)
        return false;
      successors.push_back(std::move(next));
      return true;
    }

    base.pcs[thread_index] = pc + 1;
    successors.push_back(std::move(base));
    return true;
  }

  bool fail_step(const std::string &reason)
  {
    fail(reason);
    return false;
  }

  template <typename T>
  static void append_binary(std::string &out, const T &value)
  {
    out.append(
      reinterpret_cast<const char *>(&value), sizeof(value));
  }

  static void append_state_value(
    std::string &out,
    const std::size_t value_id)
  {
    if(value_id == nil_value_id)
      out.push_back('U');
    else
    {
      out.push_back('V');
      append_binary(out, value_id);
    }
  }

  std::string key(const finite_product_statet &state)
  {
    std::string out;
    out.reserve(
      sizeof(state.atomic_owner) +
      state.pcs.size() * (sizeof(std::size_t) + 2) +
      state.values->size() * 4);
    append_binary(out, state.atomic_owner);
    for(std::size_t index = 0; index < state.pcs.size(); ++index)
    {
      if(!symmetric_thread_mask[index])
      {
        append_binary(out, state.pcs[index]);
        out.push_back(state.active[index] ? 1 : 0);
        out.push_back(state.completed[index] ? 1 : 0);
      }
    }
    for(const auto &group : symmetry_groups)
    {
      std::vector<std::string> configurations;
      configurations.reserve(group.threads.size());
      for(std::size_t member = 0; member < group.threads.size(); ++member)
      {
        const std::size_t thread_index = group.threads[member];
        std::string configuration;
        append_binary(configuration, state.pcs[thread_index]);
        configuration.push_back(state.active[thread_index] ? 1 : 0);
        configuration.push_back(state.completed[thread_index] ? 1 : 0);
        for(const auto slot : group.local_slots[member])
        {
          if(local_slot_live(slot, state))
            append_state_value(configuration, (*state.values)[slot]);
        }
        configurations.push_back(std::move(configuration));
      }
      std::sort(configurations.begin(), configurations.end());
      for(const auto &configuration : configurations)
      {
        const std::size_t size = configuration.size();
        append_binary(out, size);
        out.append(configuration);
      }
    }
    for(std::size_t index = 0; index < state.values->size(); ++index)
    {
      if(!symmetric_slot_mask[index] && local_slot_live(index, state))
        append_state_value(out, (*state.values)[index]);
    }
    return out;
  }
};

class fixedpoint_runnert
{
public:
  fixedpoint_runnert(
    goto_modelt &model,
    std::vector<irep_idt> thread_ids,
    const std::vector<bool> &may_have_multiple_instances,
    const std::vector<exprt> &extra_predicates,
    message_handlert &message_handler)
    : model(model),
      ns(model.symbol_table),
      kernel(ns, message_handler),
      message_handler(message_handler),
      affine_diagnostics(!extra_predicates.empty()),
      affine_templates(extra_predicates)
  {
    PRECONDITION(
      thread_ids.size() == may_have_multiple_instances.size());
    wp_seed_modet seed_mode;
    if(!parse_wp_seed_mode(seed_mode))
    {
      failed = true;
      failure_reason = "invalid_wp_seed_mode";
      return;
    }
    unsigned wp_max_depth;
    if(!parse_wp_max_depth(wp_max_depth))
    {
      failed = true;
      failure_reason = "invalid_wp_max_depth";
      return;
    }
    for(std::size_t worker = 0; worker < thread_ids.size(); ++worker)
    {
      std::ostringstream identifier;
      identifier << "__CPROVER_v49_done$" << worker;
      completion_symbols.emplace_back(identifier.str(), bool_typet());
    }
    std::unordered_set<exprt, irep_hash> shared_predicates;
    std::unordered_set<exprt, irep_hash> shared_seeds;
    for(std::size_t worker = 1; worker < completion_symbols.size(); ++worker)
      shared_predicates.insert(completion_symbols[worker]);
    for(const auto &predicate : extra_predicates)
      shared_predicates.insert(predicate);
    for(const auto &thread_id : thread_ids)
    {
      const auto function_it = model.goto_functions.function_map.find(thread_id);
      if(
        function_it == model.goto_functions.function_map.end() ||
        !function_it->second.body_available())
        continue;
      for(const auto &predicate :
          predicate_basis(thread_id, function_it->second, ns, false))
      {
        if(uses_only_shared_symbols(predicate, ns))
          shared_predicates.insert(predicate);
      }
      for(const auto &predicate :
          collect_wp_seeds(function_it->second, seed_mode).seeds)
      {
        if(uses_only_shared_symbols(predicate, ns))
          shared_seeds.insert(predicate);
      }
    }

    for(std::size_t thread_index = 0; thread_index < thread_ids.size();
        ++thread_index)
    {
      const auto &thread_id = thread_ids[thread_index];
      const bool main_thread = thread_id == thread_ids.front();
      const auto function_it = model.goto_functions.function_map.find(thread_id);
      if(
        function_it == model.goto_functions.function_map.end() ||
        !function_it->second.body_available())
      {
        failed = true;
        failure_reason = "missing_thread_body";
        return;
      }
      fixedpoint_threadt thread;
      thread.entry = thread_id;
      thread.may_have_multiple_instances =
        may_have_multiple_instances[thread_index];
      thread.program = &function_it->second.body;
      thread.predicates =
        predicate_basis(thread_id, function_it->second, ns, false);
      for(const auto &predicate : thread.predicates)
      {
        if(has_subexpr(predicate, ID_dereference))
        {
          failed = true;
          failure_reason = "unsupported_predicate_dereference";
          return;
        }
      }
      std::unordered_set<exprt, irep_hash> own_predicates(
        thread.predicates.begin(), thread.predicates.end());
      for(const auto &predicate : shared_predicates)
      {
        if(own_predicates.insert(predicate).second)
          thread.predicates.push_back(predicate);
      }
      const wp_seed_collectiont local_seed_collection =
        collect_wp_seeds(function_it->second, seed_mode);
      std::vector<exprt> origin_seeds;
      if(seed_mode == wp_seed_modet::ALL)
        origin_seeds = thread.predicates;
      else
      {
        origin_seeds = local_seed_collection.seeds;
        std::unordered_set<exprt, irep_hash> own_seeds(
          origin_seeds.begin(), origin_seeds.end());
        for(const auto &predicate : shared_seeds)
        {
          if(own_seeds.insert(predicate).second)
            origin_seeds.push_back(predicate);
        }
      }
      thread.predicates = wp_predicate_closure(
        thread_id,
        function_it->second,
        ns,
        thread.predicates,
        origin_seeds,
        seed_mode,
        wp_max_depth,
        local_seed_collection);
      if(thread.predicates.size() > max_predicates)
      {
        failed = true;
        failure_reason = "predicate_cap";
        return;
      }
      for(auto location = thread.program->instructions.begin();
          location != thread.program->instructions.end(); ++location)
        thread.locations.emplace(location->location_number, location);
      std::vector<unsigned> atomic_stack;
      unsigned atomic_depth = 0;
      bool concurrent = !main_thread;
      for(auto location = thread.program->instructions.begin();
          location != thread.program->instructions.end(); ++location)
      {
        thread.concurrent_location.emplace(
          location->location_number, concurrent);
        if(
          main_thread &&
          location->source_location().get_bool("v49_thread_spawn"))
        {
          if(thread.first_spawn_location == 0)
            thread.first_spawn_location = location->location_number;
          concurrent = true;
        }
        else if(
          !main_thread &&
          location->source_location().get_bool("v49_thread_spawn"))
        {
          failed = true;
          failure_reason = "nested_thread_creation";
          return;
        }
        const irep_idt &join_entry =
          location->source_location().get("v49_join_entry");
        if(join_entry != irep_idt())
        {
          if(!main_thread)
          {
            failed = true;
            failure_reason = "worker_join_unsupported";
            return;
          }
          const auto worker =
            std::find(thread_ids.begin() + 1, thread_ids.end(), join_entry);
          if(worker == thread_ids.end())
          {
            failed = true;
            failure_reason = "join_target_not_found";
            return;
          }
          const std::size_t worker_index =
            static_cast<std::size_t>(worker - thread_ids.begin());
          if(may_have_multiple_instances[worker_index])
          {
            failed = true;
            failure_reason = "multi_instance_join_unsupported";
            return;
          }
          thread.join_workers.emplace(
            location->location_number, worker_index);
        }
        if(location->source_location().get_bool("v49_unresolved_join"))
        {
          failed = true;
          failure_reason = "unresolved_join";
          return;
        }
        if(location->is_atomic_begin())
        {
          thread.atomic_depth.emplace(location->location_number, atomic_depth);
          atomic_stack.push_back(location->location_number);
          ++atomic_depth;
        }
        else if(location->is_atomic_end())
        {
          thread.atomic_depth.emplace(location->location_number, atomic_depth);
          if(atomic_stack.empty())
          {
            failed = true;
            failure_reason = "unbalanced_atomic_end";
            return;
          }
          thread.atomic_regions.emplace(
            atomic_stack.back(), location->location_number);
          atomic_stack.pop_back();
          --atomic_depth;
        }
        else
          thread.atomic_depth.emplace(location->location_number, atomic_depth);
      }
      if(!atomic_stack.empty() || atomic_depth != 0)
      {
        failed = true;
        failure_reason = "unbalanced_atomic_begin";
        return;
      }
      threads.push_back(std::move(thread));
    }
    if(threads.empty() || threads.front().first_spawn_location == 0)
    {
      failed = true;
      failure_reason = "missing_main_spawn_marker";
    }
  }

  interference_predicate_resultt run()
  {
    if(failed)
      return report_unknown();

    auto &main_thread = threads.front();
    if(main_thread.program->instructions.empty())
    {
      failure_reason = "empty_main";
      return report_unknown();
    }
    interference_predicate_cubet top;
    top.values.assign(main_thread.predicates.size(), tvt::unknown());
    for(std::size_t predicate = 0;
        predicate < main_thread.predicates.size(); ++predicate)
    {
      for(std::size_t worker = 1; worker < completion_symbols.size(); ++worker)
      {
        if(main_thread.predicates[predicate] == completion_symbols[worker])
          top.values[predicate] = tvt(false);
      }
    }
    add_cube(
      0,
      main_thread.program->instructions.begin()->location_number,
      std::move(top));

    while(!worklist.empty() && !failed)
    {
      const auto item = worklist.front();
      worklist.pop_front();
      process_location(item.first, item.second);
    }
    if(failed)
      return report_unknown();

    std::size_t assertions = 0;
    for(std::size_t thread_index = 0; thread_index < threads.size(); ++thread_index)
    {
      const auto &thread = threads[thread_index];
      for(const auto &location_entry : thread.locations)
      {
        const auto location = location_entry.second;
        if(!location->is_assert())
          continue;
        ++assertions;
        const auto state_it = thread.states.find(location_entry.first);
        if(state_it == thread.states.end())
          continue;
        for(const auto &cube : state_it->second)
        {
          const tvt proved =
            kernel.proves(cube, thread.predicates, location->condition());
          if(!proved.is_true())
          {
            std::cout << "V217_ASSERTION_CUBE entry=" << thread.entry
                      << " location=" << location_entry.first
                      << " condition="
                      << from_expr(ns, irep_idt(), location->condition());
            for(std::size_t index = 0; index < cube.values.size(); ++index)
            {
              if(cube.values[index].is_true())
                std::cout << " true={"
                          << from_expr(
                               ns, irep_idt(), thread.predicates[index])
                          << '}';
              else if(cube.values[index].is_false())
                std::cout << " false={"
                          << from_expr(
                               ns, irep_idt(), thread.predicates[index])
                          << '}';
            }
            std::cout << '\n';
            if(proved.is_unknown())
            {
              failed = true;
              failure_reason = "assertion_solver_error";
            }
            else
              failure_reason = "assertion_not_proved";
            return report_unknown();
          }
        }
      }
    }
    if(assertions == 0)
    {
      failure_reason = "no_assertions";
      return report_unknown();
    }

    std::cout << "INTERFERENCE_PREDICATE_FIXEDPOINT result=SAFE threads="
              << threads.size() << " effects=" << effects.size()
              << " locations=" << reached_locations
              << " cubes=" << inserted_cubes << " assertions=" << assertions
              << '\n';
    return interference_predicate_resultt::SAFE;
  }

private:
  static const std::size_t max_predicates = 256;
  static const std::size_t max_cubes_per_location = 64;
  static const std::size_t max_effects = 4096;
  static const std::size_t max_atomic_paths = 64;

  goto_modelt &model;
  namespacet ns;
  interference_predicate_cube_kernelt kernel;
  message_handlert &message_handler;
  std::vector<fixedpoint_threadt> threads;
  std::vector<symbol_exprt> completion_symbols;
  std::vector<interference_effectt> effects;
  std::set<std::string> effect_keys;
  std::deque<std::pair<std::size_t, unsigned>> worklist;
  bool failed = false;
  std::string failure_reason;
  std::size_t inserted_cubes = 0;
  std::size_t reached_locations = 0;
  bool affine_diagnostics = false;
  std::vector<exprt> affine_templates;
  bool affine_invariant_active = false;

  interference_predicate_resultt report_unknown() const
  {
    std::cout << "INTERFERENCE_PREDICATE_FIXEDPOINT result=UNKNOWN reason="
              << failure_reason << " threads=" << threads.size()
              << " effects=" << effects.size() << " locations="
              << reached_locations << " cubes=" << inserted_cubes << '\n';
    return interference_predicate_resultt::UNKNOWN;
  }

  std::string effect_key(
    std::size_t thread_index,
    unsigned location_number,
    unsigned path_number,
    const interference_predicate_cubet &cube) const
  {
    std::ostringstream out;
    out << thread_index << ':' << location_number << ':' << path_number << ':';
    for(const auto value : cube.values)
      out << (value.is_true() ? '1' : value.is_false() ? '0' : 'x');
    return out.str();
  }

  bool inside_atomic(std::size_t thread_index, unsigned location_number) const
  {
    const auto depth = threads[thread_index].atomic_depth.find(location_number);
    return depth != threads[thread_index].atomic_depth.end() &&
           depth->second != 0;
  }

  bool can_receive_interference(
    std::size_t thread_index,
    unsigned location_number) const
  {
    const auto concurrent =
      threads[thread_index].concurrent_location.find(location_number);
    return concurrent == threads[thread_index].concurrent_location.end() ||
           concurrent->second;
  }

  bool assignment_is_relevant(
    const fixedpoint_threadt &thread,
    const exprt &lhs) const
  {
    PRECONDITION(lhs.id() == ID_symbol);
    const irep_idt &identifier = to_symbol_expr(lhs).get_identifier();
    for(const auto &predicate : thread.predicates)
    {
      if(contains_symbol_identifier(predicate, identifier))
        return true;
    }
    return false;
  }

  bool affine_initial_templates_hold()
  {
    if(affine_templates.empty())
      return true;
    const auto &main_thread = threads.front();
    std::map<irep_idt, exprt> constants;
    for(auto instruction = main_thread.program->instructions.begin();
        instruction != main_thread.program->instructions.end();
        ++instruction)
    {
      if(instruction->location_number == main_thread.first_spawn_location)
        break;
      if(instruction->is_goto() || instruction->is_assume())
      {
        failure_reason = "affine_initial_control_unsupported";
        return false;
      }
      if(
        !instruction->is_assign() ||
        instruction->assign_lhs().id() != ID_symbol)
        continue;
      exprt rhs = instruction->assign_rhs();
      replace_symbolt replacement;
      for(const auto &entry : constants)
      {
        const symbolt *symbol = nullptr;
        if(ns.lookup(entry.first, symbol))
          continue;
        replacement.set(
          symbol_exprt(entry.first, symbol->type), entry.second);
      }
      replacement.replace(rhs);
      rhs = simplify_expr(std::move(rhs), ns);
      const irep_idt &lhs =
        to_symbol_expr(instruction->assign_lhs()).get_identifier();
      if(rhs.id() == ID_constant)
        constants[lhs] = rhs;
      else
        constants.erase(lhs);
    }

    replace_symbolt replacement;
    for(const auto &entry : constants)
    {
      const symbolt *symbol = nullptr;
      if(ns.lookup(entry.first, symbol))
        continue;
      replacement.set(
        symbol_exprt(entry.first, symbol->type), entry.second);
    }
    for(const auto &invariant : affine_templates)
    {
      exprt initialized = invariant;
      replacement.replace(initialized);
      initialized = simplify_expr(std::move(initialized), ns);
      if(!initialized.is_true())
      {
        std::cout << "V217_AFFINE_INITIALIZATION proved=0 invariant={"
                  << from_expr(ns, irep_idt(), invariant)
                  << "} reduced={"
                  << from_expr(ns, irep_idt(), initialized) << "}\n";
        failure_reason = "affine_initial_template_not_proved";
        return false;
      }
    }
    std::cout << "V217_AFFINE_INITIALIZATION proved=1 constants="
              << constants.size() << " templates=" << affine_templates.size()
              << '\n';
    return true;
  }

  bool add_cube(
    std::size_t thread_index,
    unsigned location_number,
    interference_predicate_cubet cube)
  {
    auto &thread = threads[thread_index];
    if(affine_invariant_active)
    {
      for(const auto &invariant : affine_templates)
      {
        const auto predicate =
          std::find(
            thread.predicates.begin(), thread.predicates.end(), invariant);
        if(predicate == thread.predicates.end())
        {
          failed = true;
          failure_reason = "affine_invariant_predicate_missing";
          return false;
        }
        cube.values[static_cast<std::size_t>(
          predicate - thread.predicates.begin())] = tvt(true);
      }
    }
    auto &cubes = thread.states[location_number];
    const bool first_at_location = cubes.empty();
    if(!interference_predicate_cube_kernelt::insert_subsuming(cubes, cube))
      return false;
    if(cubes.size() > max_cubes_per_location)
    {
      failed = true;
      failure_reason = "cube_cap";
      return false;
    }
    ++inserted_cubes;
    if(first_at_location)
      ++reached_locations;
    worklist.emplace_back(thread_index, location_number);

    if(
      inside_atomic(thread_index, location_number) ||
      !can_receive_interference(thread_index, location_number))
      return true;

    const auto effects_snapshot = effects;
    for(const auto &effect : effects_snapshot)
    {
      if(
        effect.writer_thread == thread_index &&
        !thread.may_have_multiple_instances)
        continue;
      interference_predicate_cubet interfered;
      const auto result = kernel.transfer_atomic_interference(
        effect.writer_cube,
        threads[effect.writer_thread].predicates,
        cube,
        thread.predicates,
        effect.operations,
        interfered);
      if(result == interference_predicate_cube_kernelt::abstract_resultt::CUBE)
        add_cube(thread_index, location_number, std::move(interfered));
      else if(result ==
              interference_predicate_cube_kernelt::abstract_resultt::SOLVER_ERROR)
      {
        failed = true;
        failure_reason = "interference_solver_error";
        return false;
      }
    }
    return true;
  }

  void add_effect(
    std::size_t writer_thread,
    unsigned location_number,
    unsigned path_number,
    const interference_predicate_cubet &writer_cube,
    const std::vector<interference_predicate_operationt> &operations)
  {
    const std::string key =
      effect_key(writer_thread, location_number, path_number, writer_cube);
    if(!effect_keys.insert(key).second)
      return;
    if(effects.size() >= max_effects)
    {
      failed = true;
      failure_reason = "effect_cap";
      return;
    }
    effects.push_back(interference_effectt{
      writer_thread, location_number, path_number, writer_cube, operations});
    const auto effect = effects.back();
    if(affine_diagnostics)
    {
      std::cout << "V217_AFFINE_EFFECT writer=" << writer_thread
                << " location=" << location_number
                << " operations=" << operations.size();
      for(std::size_t index = 0; index < writer_cube.values.size(); ++index)
      {
        if(writer_cube.values[index].is_true())
          std::cout << " writer_true={"
                    << from_expr(
                         ns,
                         irep_idt(),
                         threads[writer_thread].predicates[index])
                    << '}';
        else if(writer_cube.values[index].is_false())
          std::cout << " writer_false={"
                    << from_expr(
                         ns,
                         irep_idt(),
                         threads[writer_thread].predicates[index])
                    << '}';
      }
      for(const auto &operation : operations)
      {
        if(operation.kind == interference_predicate_operationt::kindt::ASSIGN)
          std::cout << " assign={"
                    << from_expr(ns, irep_idt(), operation.lhs) << ":="
                    << from_expr(ns, irep_idt(), operation.rhs) << '}';
        else
          std::cout << " assume={"
                    << from_expr(ns, irep_idt(), operation.rhs) << '}';
      }
      std::cout << '\n';
    }

    for(std::size_t victim = 0; victim < threads.size() && !failed; ++victim)
    {
      if(
        victim == writer_thread &&
        !threads[victim].may_have_multiple_instances)
        continue;
      std::vector<std::pair<unsigned, interference_predicate_cubet>> snapshot;
      for(const auto &state_entry : threads[victim].states)
      {
        if(
          inside_atomic(victim, state_entry.first) ||
          !can_receive_interference(victim, state_entry.first))
          continue;
        for(const auto &cube : state_entry.second)
          snapshot.emplace_back(state_entry.first, cube);
      }
      for(const auto &state : snapshot)
      {
        interference_predicate_cubet interfered;
        const auto result = kernel.transfer_atomic_interference(
          effect.writer_cube,
          threads[writer_thread].predicates,
          state.second,
          threads[victim].predicates,
          effect.operations,
          interfered);
        if(result == interference_predicate_cube_kernelt::abstract_resultt::CUBE)
          add_cube(victim, state.first, std::move(interfered));
        else if(result ==
                interference_predicate_cube_kernelt::abstract_resultt::SOLVER_ERROR)
        {
          failed = true;
          failure_reason = "interference_solver_error";
          return;
        }
      }
    }
  }

  exprt normalized_rhs(
    const exprt &rhs,
    std::size_t thread_index,
    unsigned location_number)
  {
    if(!has_subexpr(rhs, ID_side_effect))
      return rhs;
    if(
      rhs.id() == ID_side_effect &&
      rhs.get(ID_statement) == ID_nondet)
    {
      std::ostringstream identifier;
      identifier << "__CPROVER_v49_nondet$" << thread_index << '$'
                 << location_number;
      return symbol_exprt(identifier.str(), rhs.type());
    }
    failed = true;
    failure_reason = "unsupported_side_effect_rhs";
    return rhs;
  }

  void start_workers(const interference_predicate_cubet &main_cube)
  {
    if(!affine_templates.empty())
    {
      if(!affine_initial_templates_hold())
      {
        failed = true;
        return;
      }
      affine_invariant_active = true;
      std::cout << "V217_AFFINE_INVARIANT activated=1 templates="
                << affine_templates.size() << '\n';
    }
    const exprt initial_formula =
      kernel.cube_expression(main_cube, threads.front().predicates);
    for(std::size_t worker = 1; worker < threads.size(); ++worker)
    {
      if(threads[worker].program->instructions.empty())
        continue;
      interference_predicate_cubet initial_cube;
      const auto result = kernel.abstract_formula(
        initial_formula, threads[worker].predicates, initial_cube);
      if(result == interference_predicate_cube_kernelt::abstract_resultt::CUBE)
        add_cube(
          worker,
          threads[worker].program->instructions.begin()->location_number,
          std::move(initial_cube));
      else if(result ==
              interference_predicate_cube_kernelt::abstract_resultt::SOLVER_ERROR)
      {
        failed = true;
        failure_reason = "initialization_solver_error";
        return;
      }
    }
  }

  struct atomic_path_statet
  {
    goto_programt::const_targett location;
    std::vector<interference_predicate_operationt> operations;
    std::set<unsigned> visited;
    bool writes_shared = false;
  };

  void emit_atomic_effects(
    std::size_t thread_index,
    goto_programt::const_targett begin,
    const interference_predicate_cubet &entry_cube)
  {
    auto &thread = threads[thread_index];
    const auto region = thread.atomic_regions.find(begin->location_number);
    if(region == thread.atomic_regions.end())
    {
      failed = true;
      failure_reason = "missing_atomic_end";
      return;
    }

    std::deque<atomic_path_statet> paths;
    for(const auto successor : thread.program->get_successors(begin))
    {
      atomic_path_statet initial;
      initial.location = successor;
      paths.push_back(std::move(initial));
    }

    unsigned completed_paths = 0;
    while(!paths.empty() && !failed)
    {
      atomic_path_statet path = std::move(paths.front());
      paths.pop_front();
      if(path.location->location_number == region->second)
      {
        if(completed_paths >= max_atomic_paths)
        {
          failed = true;
          failure_reason = "atomic_path_cap";
          return;
        }
        if(path.writes_shared)
          add_effect(
            thread_index,
            begin->location_number,
            completed_paths,
            entry_cube,
            path.operations);
        ++completed_paths;
        continue;
      }

      const unsigned current_number = path.location->location_number;
      if(!path.visited.insert(current_number).second)
      {
        failed = true;
        failure_reason = "atomic_loop_unsupported";
        return;
      }

      if(path.location->is_assign())
      {
        exprt lhs =
          simplify_expr(path.location->assign_lhs(), ns);
        if(lhs.id() == ID_dereference)
        {
          exprt pointer =
            simplify_expr(to_dereference_expr(lhs).pointer(), ns);
          if(pointer.id() == ID_address_of)
          {
            const exprt &object =
              skip_typecast(to_address_of_expr(pointer).object());
            if(object.id() == ID_symbol)
              lhs = object;
          }
        }
        if(lhs.id() != ID_symbol)
        {
          std::cout << "INTERFERENCE_ATOMIC_LHS_AUDIT id=" << lhs.id()
                    << " expr=" << from_expr(ns, irep_idt(), lhs);
          if(lhs.id() == ID_dereference)
            std::cout << " pointer_id="
                      << to_dereference_expr(lhs).pointer().id()
                      << " pointer="
                      << to_dereference_expr(lhs).pointer().pretty();
          std::cout << '\n';
          failed = true;
          failure_reason = "unsupported_atomic_assignment_lhs";
          return;
        }
        const exprt rhs = normalized_rhs(
          path.location->assign_rhs(), thread_index, current_number);
        if(failed)
          return;
        if(has_subexpr(rhs, ID_dereference))
        {
          failed = true;
          failure_reason = "unsupported_atomic_rhs_dereference";
          return;
        }
        path.writes_shared =
          path.writes_shared || is_shared_scalar(lhs, ns);
        path.operations.push_back(
          interference_predicate_operationt::assignment(
            lhs, rhs));
      }
      else if(path.location->is_assume())
        path.operations.push_back(
          interference_predicate_operationt::assumption(
            path.location->condition()));
      else if(
        path.location->is_function_call() || path.location->is_start_thread() ||
        path.location->is_throw() || path.location->is_catch() ||
        (path.location->is_other() && !path.location->is_atomic_begin() &&
         !path.location->is_atomic_end() &&
         !is_abstract_noop_other(*path.location)))
      {
        failed = true;
        failure_reason = "unsupported_atomic_instruction";
        return;
      }

      const auto successors = thread.program->get_successors(path.location);
      if(successors.empty())
      {
        failed = true;
        failure_reason = "atomic_path_escapes";
        return;
      }
      for(const auto successor : successors)
      {
        atomic_path_statet next = path;
        next.location = successor;
        if(path.location->is_goto())
        {
          exprt guard = path.location->condition();
          if(
            std::next(path.location) != thread.program->instructions.end() &&
            successor == std::next(path.location))
            guard = boolean_negate(guard);
          next.operations.push_back(
            interference_predicate_operationt::assumption(std::move(guard)));
        }
        paths.push_back(std::move(next));
        if(paths.size() > max_atomic_paths * 4)
        {
          failed = true;
          failure_reason = "atomic_path_work_cap";
          return;
        }
      }
    }
    if(completed_paths == 0 && !failed)
    {
      failed = true;
      failure_reason = "atomic_no_complete_path";
    }
  }

  void process_location(std::size_t thread_index, unsigned location_number)
  {
    auto &thread = threads[thread_index];
    const auto location_it = thread.locations.find(location_number);
    if(location_it == thread.locations.end())
    {
      failed = true;
      failure_reason = "missing_location";
      return;
    }
    const auto location = location_it->second;
    const auto cubes = thread.states[location_number];
    for(const auto &cube : cubes)
    {
      if(failed)
        return;
      if(
        thread_index != 0 && location->is_end_function() &&
        !thread.may_have_multiple_instances)
      {
        const std::vector<interference_predicate_operationt> operations{
          interference_predicate_operationt::assignment(
            completion_symbols[thread_index], true_exprt())};
        add_effect(
          thread_index,
          location_number,
          0,
          cube,
          operations);
        if(failed)
          return;
      }
      if(
        thread_index == 0 &&
        location_number == thread.first_spawn_location)
      {
        start_workers(cube);
        if(failed)
          return;
      }
      if(location->is_atomic_begin() && !inside_atomic(thread_index, location_number))
      {
        emit_atomic_effects(thread_index, location, cube);
        if(failed)
          return;
      }
      for(const auto successor : thread.program->get_successors(location))
      {
        interference_predicate_cubet next_cube;
        auto result = interference_predicate_cube_kernelt::abstract_resultt::CUBE;
        const auto join = thread.join_workers.find(location_number);
        if(join != thread.join_workers.end())
          result = kernel.transfer_assume(
            cube,
            thread.predicates,
            completion_symbols[join->second],
            next_cube);
        else if(location->is_assign())
        {
          if(location->assign_lhs().id() != ID_symbol)
          {
            failed = true;
            std::ostringstream reason;
            reason << "unsupported_assignment_lhs_"
                   << location->assign_lhs().id() << "_at_"
                   << location_number;
            failure_reason = reason.str();
            return;
          }
          if(!assignment_is_relevant(thread, location->assign_lhs()))
            next_cube = cube;
          else
          {
            const exprt rhs = normalized_rhs(
              location->assign_rhs(), thread_index, location_number);
            if(failed)
              return;
            if(has_subexpr(rhs, ID_dereference))
            {
              failed = true;
              failure_reason = "unsupported_rhs_dereference";
              return;
            }
            if(
              is_shared_scalar(location->assign_lhs(), ns) &&
              !inside_atomic(thread_index, location_number) &&
              can_receive_interference(thread_index, location_number))
            {
              const std::vector<interference_predicate_operationt> operations{
                interference_predicate_operationt::assignment(
                  location->assign_lhs(), rhs)};
              add_effect(
                thread_index,
                location_number,
                0,
                cube,
                operations);
            }
            result = kernel.transfer_assignment(
              cube,
              thread.predicates,
              location->assign_lhs(),
              rhs,
              next_cube);
          }
        }
        else if(location->is_assume())
          result = kernel.transfer_assume(
            cube, thread.predicates, location->condition(), next_cube);
        else if(location->is_goto())
        {
          exprt guard = location->condition();
          if(
            std::next(location) != thread.program->instructions.end() &&
            successor == std::next(location))
            guard = boolean_negate(guard);
          result = kernel.transfer_assume(
            cube, thread.predicates, guard, next_cube);
        }
        else if(
          location->is_function_call() ||
          (location->is_other() && !is_abstract_noop_other(*location)) ||
          location->is_start_thread() || location->is_throw() ||
          location->is_catch())
        {
          failed = true;
          std::ostringstream reason;
          reason << "unsupported_instruction_type_"
                 << static_cast<unsigned>(location->type());
          if(location->is_other())
            reason << "_statement_" << location->code().get_statement();
          failure_reason = reason.str();
          return;
        }
        else
          next_cube = cube;

        if(result == interference_predicate_cube_kernelt::abstract_resultt::CUBE)
          add_cube(
            thread_index, successor->location_number, std::move(next_cube));
        else if(result ==
                interference_predicate_cube_kernelt::abstract_resultt::SOLVER_ERROR)
        {
          failed = true;
          failure_reason = "sequential_solver_error";
          return;
        }
      }
    }
  }
};
} // namespace

bool interference_predicate_profile(
  const goto_modelt &goto_model,
  message_handlert &message_handler)
{
  const auto entries = find_thread_entries(goto_model);
  if(entries.empty())
  {
    std::cout << "INTERFERENCE_PREDICATE_PROFILE admitted=0 reason=no_thread_entries\n";
    return false;
  }

  goto_modelt inlined_model;
  inlined_model.symbol_table = goto_model.symbol_table;
  inlined_model.goto_functions.copy_from(goto_model.goto_functions);
  neutralize_synchronization_calls(inlined_model);
  for(const auto &entry : entries)
    goto_function_inline(inlined_model, entry, message_handler, false, false);

  const namespacet ns(inlined_model.symbol_table);
  bool admitted = true;
  std::size_t total_predicates = 0;
  std::size_t total_shared_writes = 0;
  std::size_t total_atomic_blocks = 0;
  for(const auto &entry : entries)
  {
    const auto function_it = inlined_model.goto_functions.function_map.find(entry);
    if(
      function_it == inlined_model.goto_functions.function_map.end() ||
      !function_it->second.body_available())
    {
      admitted = false;
      std::cout << "INTERFERENCE_PREDICATE_THREAD entry=" << entry
                << " admitted=0 reason=missing_body\n";
      continue;
    }

    const auto profile = profile_thread(entry, function_it->second, ns);
    total_predicates += profile.predicates;
    total_shared_writes += profile.shared_scalar_writes;
    total_atomic_blocks += profile.atomic_blocks;
    if(!profile.atomic_balanced || profile.predicates > 256)
      admitted = false;
    std::cout << "INTERFERENCE_PREDICATE_THREAD entry=" << profile.entry
              << " instructions=" << profile.instructions
              << " predicates=" << profile.predicates
              << " shared_scalar_writes=" << profile.shared_scalar_writes
              << " pointer_writes=" << profile.pointer_writes
              << " atomic_blocks=" << profile.atomic_blocks
              << " atomic_balanced=" << (profile.atomic_balanced ? 1 : 0)
              << " remaining_calls=" << profile.remaining_calls << '\n';
  }

  std::cout << "INTERFERENCE_PREDICATE_PROFILE admitted=" << (admitted ? 1 : 0)
            << " threads=" << entries.size()
            << " predicates=" << total_predicates
            << " shared_scalar_writes=" << total_shared_writes
            << " atomic_blocks=" << total_atomic_blocks << '\n';
  return admitted;
}

interference_predicate_resultt interference_predicate_fixedpoint(
  const goto_modelt &goto_model,
  message_handlert &message_handler,
  bool repeated_single_worker_only,
  bool finite_protocol_product)
{
  const bool finite_product_mode =
    !repeated_single_worker_only &&
    (finite_protocol_product ||
     std::getenv("DEAGLE_FINITE_PROTOCOL_PRODUCT") != nullptr);
  goto_modelt analysis_model;
  analysis_model.symbol_table = goto_model.symbol_table;
  analysis_model.goto_functions.copy_from(goto_model.goto_functions);
  std::set<irep_idt> materialized_entries;
  if(finite_product_mode)
  {
    goto_modelt materialized_model;
    materialized_model.symbol_table = analysis_model.symbol_table;
    materialized_model.goto_functions.copy_from(
      analysis_model.goto_functions);
    std::string materialize_reason;
    if(
      indexed_lifecycle_full_transform(
        materialized_model, message_handler) &&
      materialize_bounded_thread_instances(
        materialized_model,
        materialized_entries,
        materialize_reason))
      analysis_model = std::move(materialized_model);
    else if(std::getenv("DEAGLE_FINITE_PRODUCT_AUDIT") != nullptr)
      std::cout << "V302_BOUNDED_THREAD_INSTANCES applied=0 reason="
                << materialize_reason << '\n';
  }

  std::map<irep_idt, bool> multiple_instances;
  const auto entries =
    find_thread_entries(analysis_model, nullptr, &multiple_instances);
  for(const auto &entry : materialized_entries)
    multiple_instances[entry] = false;
  if(entries.empty())
  {
    std::cout << "INTERFERENCE_PREDICATE_FIXEDPOINT result=UNKNOWN "
                 "reason=no_thread_entries\n";
    return interference_predicate_resultt::UNKNOWN;
  }
  const bool affine_mode = std::getenv("DEAGLE_AFFINE_MODE") != nullptr;
  const bool ownership_mode =
    std::getenv("DEAGLE_LOCK_OWNERSHIP_MODE") != nullptr;
  std::string affine_failure_reason;
  if(affine_mode && !repeated_single_worker_only)
  {
    const auto phase_result =
      affine_phase_certificate(
        goto_model, message_handler, affine_failure_reason);
    if(phase_result == interference_predicate_resultt::SAFE)
      return phase_result;
    std::cout << "V217_AFFINE_PHASE result=UNKNOWN reason="
              << affine_failure_reason << '\n';
  }

  if(
    repeated_single_worker_only &&
    (entries.size() != 1 || !multiple_instances[*entries.begin()]))
  {
    std::cout << "INTERFERENCE_PREDICATE_FIXEDPOINT result=UNKNOWN "
                 "reason=recursive_worker_gate entries="
              << entries.size() << " repeated="
              << (entries.size() == 1 && multiple_instances[*entries.begin()]
                    ? 1
                    : 0)
              << '\n';
    return interference_predicate_resultt::UNKNOWN;
  }

  if(ownership_mode)
  {
    std::string ticket_reason;
    std::size_t ticket_regions = 0;
    if(!rewrite_ticket_lock_ownership(
         analysis_model, ticket_reason, ticket_regions))
      std::cout << "INTERFERENCE_TICKET_OWNERSHIP regions=0 reason="
                << ticket_reason << '\n';
  }
  if(!neutralize_synchronization_calls(
       analysis_model,
       affine_mode || ownership_mode,
       &affine_failure_reason))
  {
    std::cout << "INTERFERENCE_PREDICATE_FIXEDPOINT result=UNKNOWN reason="
              << affine_failure_reason << '\n';
    return interference_predicate_resultt::UNKNOWN;
  }

  std::vector<irep_idt> thread_ids;
  irep_idt main_entry = "main";
  for(const irep_idt candidate :
      {irep_idt("__CPROVER__start"), irep_idt("__CPROVER_start")})
  {
    const auto start = analysis_model.goto_functions.function_map.find(candidate);
    if(
      start != analysis_model.goto_functions.function_map.end() &&
      start->second.body_available())
    {
      main_entry = candidate;
      break;
    }
  }
  thread_ids.push_back(main_entry);
  std::vector<bool> thread_multiple_instances{false};
  thread_ids.insert(thread_ids.end(), entries.begin(), entries.end());
  for(const auto &entry : entries)
    thread_multiple_instances.push_back(multiple_instances[entry]);
  if(finite_product_mode)
  {
    irep_idt recursive_function;
    if(!reachable_product_call_graph_acyclic(
         analysis_model.goto_functions,
         thread_ids,
         recursive_function))
    {
      std::cout << "V225_FINITE_PRODUCT result=UNKNOWN "
                   "reason=recursive_call_graph function="
                << recursive_function
                << " states_or_transitions=0\n";
      return interference_predicate_resultt::UNKNOWN;
    }
  }
  for(const auto &thread_id : thread_ids)
  {
    if(
      finite_product_mode &&
      std::getenv("DEAGLE_FINITE_PRODUCT_AUDIT") != nullptr)
    {
      const auto function =
        analysis_model.goto_functions.function_map.find(thread_id);
      std::cout << "V225_FINITE_PRODUCT_INLINE phase=before entry="
                << thread_id << " instructions="
                << (function == analysis_model.goto_functions.function_map.end()
                      ? 0
                      : function->second.body.instructions.size())
                << std::endl;
    }
    goto_function_inline(analysis_model, thread_id, message_handler, false, false);
    if(
      finite_product_mode &&
      std::getenv("DEAGLE_FINITE_PRODUCT_AUDIT") != nullptr)
    {
      const auto function =
        analysis_model.goto_functions.function_map.find(thread_id);
      std::cout << "V225_FINITE_PRODUCT_INLINE phase=after entry="
                << thread_id << " instructions="
                << (function == analysis_model.goto_functions.function_map.end()
                      ? 0
                      : function->second.body.instructions.size())
                << std::endl;
    }
  }
  analysis_model.goto_functions.update();
  analysis_model.goto_functions.compute_location_numbers();

  std::string ownership_reason;
  std::size_t ownership_regions = 0;
  std::size_t ownership_objects = 0;
  if(!validate_mutex_ownership(
       analysis_model,
       thread_ids,
       ownership_reason,
       ownership_regions,
       ownership_objects))
  {
    std::cout << "INTERFERENCE_PREDICATE_FIXEDPOINT result=UNKNOWN reason="
              << ownership_reason << " ownership_regions="
              << ownership_regions << " protected_objects="
              << ownership_objects << '\n';
    return interference_predicate_resultt::UNKNOWN;
  }
  if(ownership_regions != 0)
    std::cout << "INTERFERENCE_OWNERSHIP regions=" << ownership_regions
              << " protected_objects=" << ownership_objects << '\n';

  if(finite_product_mode)
  {
    goto_modelt product_model;
    product_model.symbol_table = analysis_model.symbol_table;
    product_model.goto_functions.copy_from(analysis_model.goto_functions);
    std::size_t removed_functions = 0;
    for(auto function = product_model.goto_functions.function_map.begin();
        function != product_model.goto_functions.function_map.end();)
    {
      if(
        std::find(thread_ids.begin(), thread_ids.end(), function->first) ==
        thread_ids.end())
      {
        function = product_model.goto_functions.function_map.erase(function);
        ++removed_functions;
      }
      else
        ++function;
    }
    if(std::getenv("DEAGLE_FINITE_PRODUCT_AUDIT") != nullptr)
      std::cout << "V225_FINITE_PRODUCT_PREP phase=thread_projection"
                << " retained=" << thread_ids.size()
                << " removed=" << removed_functions << std::endl;
    if(std::getenv("DEAGLE_FINITE_PRODUCT_AUDIT") != nullptr)
      std::cout << "V225_FINITE_PRODUCT_PREP phase=dereference_before"
                << std::endl;
    const bool dereferences_lowered =
      lower_unique_product_dereferences(product_model, thread_ids);
    if(std::getenv("DEAGLE_FINITE_PRODUCT_AUDIT") != nullptr)
      std::cout << "V225_FINITE_PRODUCT_PREP phase=dereference_after result="
                << dereferences_lowered << std::endl;
    const bool locals_isolated =
      dereferences_lowered &&
      isolate_product_thread_locals(product_model, thread_ids);
    if(std::getenv("DEAGLE_FINITE_PRODUCT_AUDIT") != nullptr)
      std::cout << "V225_FINITE_PRODUCT_PREP phase=isolate_after result="
                << locals_isolated << std::endl;
    const bool dead_locals_eliminated =
      locals_isolated &&
      eliminate_dead_product_locals_fixedpoint(product_model, thread_ids);
    if(std::getenv("DEAGLE_FINITE_PRODUCT_AUDIT") != nullptr)
      std::cout << "V225_FINITE_PRODUCT_PREP phase=dead_locals_after result="
                << dead_locals_eliminated << std::endl;
    if(dead_locals_eliminated)
    {
      finite_product_runnert finite_product(
        product_model, thread_ids, thread_multiple_instances);
      const auto result = finite_product.run();
      if(result == interference_predicate_resultt::SAFE)
        return result;
    }
    else
      std::cout << "V225_FINITE_PRODUCT result=UNKNOWN "
                   "reason=nonunique_dereference states_or_transitions=0\n";
    std::cout << "V225_FINITE_PRODUCT_FALLBACK fixedpoint=1\n";
  }

  if(repeated_single_worker_only)
  {
    const namespacet ns(analysis_model.symbol_table);
    const auto worker =
      analysis_model.goto_functions.function_map.find(*entries.begin());
    if(
      worker == analysis_model.goto_functions.function_map.end() ||
      !worker->second.body_available())
    {
      std::cout << "INTERFERENCE_PREDICATE_FIXEDPOINT result=UNKNOWN "
                   "reason=recursive_worker_missing_body\n";
      return interference_predicate_resultt::UNKNOWN;
    }
    const auto profile = profile_thread(worker->first, worker->second, ns);
    constexpr std::size_t max_recursive_worker_instructions = 100;
    constexpr std::size_t max_recursive_worker_predicates = 16;
    if(
      profile.instructions > max_recursive_worker_instructions ||
      profile.predicates > max_recursive_worker_predicates)
    {
      std::cout << "INTERFERENCE_PREDICATE_FIXEDPOINT result=UNKNOWN "
                   "reason=recursive_worker_complexity_gate instructions="
                << profile.instructions << " predicates=" << profile.predicates
                << '\n';
      return interference_predicate_resultt::UNKNOWN;
    }
  }

  std::string array_failure_reason;
  if(!canonicalize_immutable_arrays(
       analysis_model, thread_ids, array_failure_reason))
  {
    std::cout << "INTERFERENCE_PREDICATE_FIXEDPOINT result=UNKNOWN reason="
              << array_failure_reason << '\n';
    return interference_predicate_resultt::UNKNOWN;
  }

  std::vector<exprt> extra_predicates;
  if(affine_mode)
  {
    const namespacet ns(analysis_model.symbol_table);
    if(!affine_template_closure(
         analysis_model,
         thread_ids,
         ns,
         extra_predicates,
         affine_failure_reason))
    {
      std::cout << "INTERFERENCE_PREDICATE_FIXEDPOINT result=UNKNOWN reason="
                << affine_failure_reason << '\n';
      return interference_predicate_resultt::UNKNOWN;
    }
  }

  fixedpoint_runnert runner(
    analysis_model,
    thread_ids,
    thread_multiple_instances,
    extra_predicates,
    message_handler);
  return runner.run();
}

interference_predicate_resultt interference_predicate_finite_product_auto(
  const goto_modelt &goto_model,
  message_handlert &message_handler)
{
  const auto main = goto_model.goto_functions.function_map.find("main");
  if(
    main == goto_model.goto_functions.function_map.end() ||
    !main->second.body_available())
    return interference_predicate_resultt::UNKNOWN;

  std::size_t creates = 0;
  std::size_t joins = 0;
  bool repeated_create = false;
  bool repeated_join = false;
  for(auto instruction = main->second.body.instructions.begin();
      instruction != main->second.body.instructions.end(); ++instruction)
  {
    if(!instruction->is_function_call())
      continue;
    const exprt &function = skip_typecast(instruction->call_function());
    if(function.id() != ID_symbol)
      continue;
    const irep_idt identifier =
      to_symbol_expr(function).get_identifier();
    if(identifier == "pthread_create")
    {
      ++creates;
      repeated_create =
        repeated_create ||
        instruction_is_in_cycle(main->second.body, instruction);
    }
    else if(identifier == "pthread_join")
    {
      ++joins;
      repeated_join =
        repeated_join ||
        instruction_is_in_cycle(main->second.body, instruction);
    }
  }
  const bool admitted_explicit_pair =
    creates == 2 && joins == 1 && repeated_create;
  const bool admitted_bounded_pair =
    creates == 1 && joins == 1 && repeated_create && repeated_join;
  if(!admitted_explicit_pair && !admitted_bounded_pair)
    return interference_predicate_resultt::UNKNOWN;

  if(admitted_bounded_pair)
  {
    goto_modelt materialized_model;
    materialized_model.symbol_table = goto_model.symbol_table;
    materialized_model.goto_functions.copy_from(goto_model.goto_functions);
    std::set<irep_idt> materialized_entries;
    std::string materialize_reason;
    if(
      !indexed_lifecycle_full_transform(
        materialized_model, message_handler) ||
      !materialize_bounded_thread_instances(
        materialized_model,
        materialized_entries,
        materialize_reason))
    {
      if(std::getenv("DEAGLE_FINITE_PRODUCT_AUDIT") != nullptr)
        std::cout << "V225_FINITE_PRODUCT_AUTO admitted=0 reason="
                  << (materialize_reason.empty()
                        ? "bounded_lifecycle_transform"
                        : materialize_reason)
                  << '\n';
      return interference_predicate_resultt::UNKNOWN;
    }
  }

  const auto entries = find_thread_entries(goto_model);
  bool loop_worker = false;
  std::deque<irep_idt> pending_functions(entries.begin(), entries.end());
  std::set<irep_idt> visited_functions;
  while(!pending_functions.empty() && !loop_worker)
  {
    const irep_idt function_id = pending_functions.front();
    pending_functions.pop_front();
    if(!visited_functions.insert(function_id).second)
      continue;
    const auto worker =
      goto_model.goto_functions.function_map.find(function_id);
    if(
      worker == goto_model.goto_functions.function_map.end() ||
      !worker->second.body_available())
      continue;
    for(auto instruction = worker->second.body.instructions.begin();
        instruction != worker->second.body.instructions.end(); ++instruction)
    {
      if(instruction_is_in_cycle(worker->second.body, instruction))
      {
        loop_worker = true;
        break;
      }
      if(!instruction->is_function_call())
        continue;
      const exprt &callee = skip_typecast(instruction->call_function());
      if(callee.id() == ID_symbol)
        pending_functions.push_back(
          to_symbol_expr(callee).get_identifier());
    }
  }
  if(!loop_worker)
    return interference_predicate_resultt::UNKNOWN;

  std::cout << "V225_FINITE_PRODUCT_AUTO admitted=1 creates=" << creates
            << " joins=" << joins << " entries=" << entries.size()
            << " bounded_lifecycle=" << admitted_bounded_pair << '\n';
  return interference_predicate_fixedpoint(
    goto_model, message_handler, false, true);
}
