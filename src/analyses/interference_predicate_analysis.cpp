/*******************************************************************\

Module: Interference-Closed Predicate Analysis

\*******************************************************************/

#include "interference_predicate_analysis.h"
#include "interference_predicate_cube.h"

#include <goto-programs/goto_inline.h>
#include <goto-programs/goto_model.h>

#include <langapi/language_util.h>

#include <util/expr_util.h>
#include <util/irep_hash.h>
#include <util/message.h>
#include <util/namespace.h>
#include <util/pointer_expr.h>
#include <util/replace_symbol.h>
#include <util/simplify_expr.h>
#include <util/std_expr.h>
#include <util/std_code.h>

#include <algorithm>
#include <cstdlib>
#include <deque>
#include <iostream>
#include <map>
#include <set>
#include <sstream>
#include <unordered_set>
#include <vector>

namespace
{
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
  const goto_functionst::goto_functiont &function)
{
  std::unordered_set<exprt, irep_hash> predicates;
  for(const auto &instruction : function.body.instructions)
  {
    if(instruction.is_assert() || instruction.is_assume() || instruction.is_goto())
      collect_boolean_atoms(instruction.condition(), predicates);
    if(instruction.is_assign())
      collect_boolean_atoms(instruction.assign_rhs(), predicates);
  }
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
    for(std::size_t worker = 0; worker < thread_ids.size(); ++worker)
    {
      std::ostringstream identifier;
      identifier << "__CPROVER_v49_done$" << worker;
      completion_symbols.emplace_back(identifier.str(), bool_typet());
    }
    std::unordered_set<exprt, irep_hash> shared_predicates;
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
      for(const auto &predicate : predicate_basis(function_it->second))
      {
        if(uses_only_shared_symbols(predicate, ns))
          shared_predicates.insert(predicate);
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
      thread.predicates = predicate_basis(function_it->second);
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
        if(path.location->assign_lhs().id() != ID_symbol)
        {
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
        path.writes_shared = path.writes_shared ||
                             is_shared_scalar(path.location->assign_lhs(), ns);
        path.operations.push_back(
          interference_predicate_operationt::assignment(
            path.location->assign_lhs(), rhs));
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
            failure_reason = "unsupported_assignment_lhs";
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
  bool repeated_single_worker_only)
{
  std::map<irep_idt, bool> multiple_instances;
  const auto entries =
    find_thread_entries(goto_model, nullptr, &multiple_instances);
  if(entries.empty())
  {
    std::cout << "INTERFERENCE_PREDICATE_FIXEDPOINT result=UNKNOWN "
                 "reason=no_thread_entries\n";
    return interference_predicate_resultt::UNKNOWN;
  }
  const bool affine_mode = std::getenv("DEAGLE_AFFINE_MODE") != nullptr;
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

  goto_modelt analysis_model;
  analysis_model.symbol_table = goto_model.symbol_table;
  analysis_model.goto_functions.copy_from(goto_model.goto_functions);
  if(!neutralize_synchronization_calls(
       analysis_model, affine_mode, &affine_failure_reason))
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
  for(const auto &thread_id : thread_ids)
    goto_function_inline(analysis_model, thread_id, message_handler, false, false);
  analysis_model.goto_functions.update();

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
