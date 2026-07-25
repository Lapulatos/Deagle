/*******************************************************************\

Module: Lock-Indexed Relational Abstract Certificate

\*******************************************************************/

#include "lock_relational_ai_analysis.h"

#include <goto-programs/goto_model.h>
#include <linking/static_lifetime_init.h>

#include <util/arith_tools.h>
#include <util/expr_util.h>
#include <util/message.h>
#include <util/namespace.h>
#include <util/pointer_expr.h>
#include <util/std_code.h>
#include <util/std_expr.h>

#include <algorithm>
#include <deque>
#include <iostream>
#include <limits>
#include <map>
#include <set>
#include <sstream>
#include <string>
#include <vector>

namespace
{
const exprt &strip(const exprt &expr)
{
  return skip_typecast(expr);
}

bool symbol_id(const exprt &src, irep_idt &identifier)
{
  const exprt &expr = strip(src);
  if(expr.id() != ID_symbol)
    return false;
  identifier = to_symbol_expr(expr).get_identifier();
  return true;
}

bool call_id(
  const goto_programt::instructiont &instruction,
  irep_idt &identifier)
{
  return
    instruction.is_function_call() &&
    symbol_id(instruction.call_function(), identifier);
}

bool integer_constant(const exprt &src, long long &value)
{
  mp_integer integer;
  const exprt &expr = strip(src);
  if(
    expr.id() != ID_constant ||
    to_integer(to_constant_expr(expr), integer))
    return false;
  const mp_integer low = std::numeric_limits<long long>::min();
  const mp_integer high = std::numeric_limits<long long>::max();
  if(integer < low || integer > high)
    return false;
  value = integer.to_long();
  return true;
}

bool named(const irep_idt &identifier, const std::string &suffix)
{
  const std::string name = id2string(identifier);
  return
    name == suffix ||
    (name.size() > suffix.size() &&
     name.compare(name.size() - suffix.size(), suffix.size(), suffix) == 0);
}

bool is_lock(const irep_idt &identifier)
{
  return named(identifier, "pthread_mutex_lock");
}

bool is_unlock(const irep_idt &identifier)
{
  return named(identifier, "pthread_mutex_unlock");
}

bool is_mutex_init(const irep_idt &identifier)
{
  return named(identifier, "pthread_mutex_init");
}

bool is_create(const irep_idt &identifier)
{
  return named(identifier, "pthread_create");
}

bool is_join(const irep_idt &identifier)
{
  return named(identifier, "pthread_join");
}

bool is_property(const irep_idt &identifier)
{
  return named(identifier, "__VERIFIER_assert");
}

bool is_error(const irep_idt &identifier)
{
  return
    named(identifier, "reach_error") ||
    named(identifier, "__VERIFIER_error");
}

bool ignored_external(const irep_idt &identifier)
{
  return
    is_lock(identifier) || is_unlock(identifier) ||
    is_mutex_init(identifier) || is_create(identifier) ||
    is_join(identifier) || is_property(identifier) ||
    is_error(identifier) || named(identifier, "sleep") ||
    named(identifier, "abort") ||
    named(identifier, "__CPROVER_assume");
}

struct intervalt
{
  bool lower_set;
  bool upper_set;
  long long lower;
  long long upper;

  intervalt()
    : lower_set(false), upper_set(false), lower(0), upper(0)
  {
  }

  static intervalt singleton(long long value)
  {
    intervalt result;
    result.lower_set = result.upper_set = true;
    result.lower = result.upper = value;
    return result;
  }

  bool operator==(const intervalt &other) const
  {
    return
      lower_set == other.lower_set && upper_set == other.upper_set &&
      (!lower_set || lower == other.lower) &&
      (!upper_set || upper == other.upper);
  }

  bool operator!=(const intervalt &other) const
  {
    return !(*this == other);
  }
};

struct statet
{
  bool bottom;
  std::map<std::string, intervalt> values;

  statet() : bottom(false)
  {
  }

  intervalt get(const std::string &key) const
  {
    const auto found = values.find(key);
    return found == values.end() ? intervalt() : found->second;
  }

  void set(const std::string &key, const intervalt &value)
  {
    if(!value.lower_set && !value.upper_set)
      values.erase(key);
    else
      values[key] = value;
  }
};

bool join_interval(intervalt &dest, const intervalt &src)
{
  const intervalt old = dest;
  if(dest.lower_set && (!src.lower_set || src.lower < dest.lower))
  {
    if(src.lower_set)
      dest.lower = src.lower;
    else
      dest.lower_set = false;
  }
  if(dest.upper_set && (!src.upper_set || src.upper > dest.upper))
  {
    if(src.upper_set)
      dest.upper = src.upper;
    else
      dest.upper_set = false;
  }
  return dest != old;
}

bool join_state(statet &dest, const statet &src)
{
  if(src.bottom)
    return false;
  if(dest.bottom)
  {
    dest = src;
    return true;
  }
  bool changed = false;
  for(auto iterator = dest.values.begin(); iterator != dest.values.end();)
  {
    const auto other = src.values.find(iterator->first);
    if(other == src.values.end())
    {
      iterator = dest.values.erase(iterator);
      changed = true;
    }
    else
    {
      changed |= join_interval(iterator->second, other->second);
      ++iterator;
    }
  }
  return changed;
}

void widen_state(statet &dest, const statet &old)
{
  for(auto &entry : dest.values)
  {
    const auto previous = old.values.find(entry.first);
    if(previous == old.values.end())
      continue;
    if(
      previous->second.lower_set && entry.second.lower_set &&
      entry.second.lower < previous->second.lower)
      entry.second.lower_set = false;
    if(
      previous->second.upper_set && entry.second.upper_set &&
      entry.second.upper > previous->second.upper)
      entry.second.upper_set = false;
  }
}

bool meet_interval(intervalt &dest, const intervalt &src)
{
  if(src.lower_set && (!dest.lower_set || src.lower > dest.lower))
  {
    dest.lower_set = true;
    dest.lower = src.lower;
  }
  if(src.upper_set && (!dest.upper_set || src.upper < dest.upper))
  {
    dest.upper_set = true;
    dest.upper = src.upper;
  }
  return
    !(dest.lower_set && dest.upper_set && dest.lower > dest.upper);
}

struct analysist
{
  goto_modelt &model;
  namespacet ns;
  std::set<std::string> shared_roots;
  std::map<irep_idt, std::string> aliases;
  std::map<std::string, intervalt> initial;
  std::set<std::string> locks;
  std::set<std::pair<std::string, std::string>> lock_edges;
  std::map<std::string, std::string> protection;
  std::set<irep_idt> pre_spawn_functions;
  std::map<std::string, statet> lock_invariants;
  std::map<std::string, unsigned> lock_changes;
  std::size_t properties;
  std::string reason;

  explicit analysist(goto_modelt &goto_model)
    : model(goto_model),
      ns(goto_model.symbol_table),
      properties(0)
  {
    for(const auto &entry : model.symbol_table.symbols)
    {
      const symbolt &symbol = entry.second;
      if(
        symbol.is_static_lifetime && !symbol.is_type &&
        symbol.type.id() != ID_code)
        shared_roots.insert(id2string(entry.first));
    }
  }

  bool shared(const std::string &key) const
  {
    const std::size_t split = key.find('#');
    return shared_roots.count(key.substr(0, split)) != 0;
  }

  bool atom(const exprt &src, std::string &key) const
  {
    const exprt &expr = strip(src);
    if(expr.id() == ID_symbol)
    {
      key = id2string(to_symbol_expr(expr).get_identifier());
      return true;
    }
    if(expr.id() == ID_member)
    {
      const member_exprt &member = to_member_expr(expr);
      std::string base;
      if(!atom(member.compound(), base))
        return false;
      key = base + "#" + id2string(member.get_component_name());
      return true;
    }
    if(expr.id() == ID_dereference)
    {
      const exprt &pointer =
        strip(to_dereference_expr(expr).pointer());
      if(pointer.id() == ID_address_of)
        return atom(to_address_of_expr(pointer).object(), key);
      if(pointer.id() == ID_symbol)
      {
        const irep_idt identifier =
          to_symbol_expr(pointer).get_identifier();
        const auto alias = aliases.find(identifier);
        if(alias != aliases.end())
        {
          key = alias->second;
          return true;
        }
      }
      return false;
    }
    return false;
  }

  bool lock_argument(
    const goto_programt::instructiont &instruction,
    std::string &lock) const
  {
    if(instruction.call_arguments().empty())
      return false;
    const exprt &argument = strip(instruction.call_arguments().front());
    if(argument.id() != ID_address_of)
      return false;
    return atom(to_address_of_expr(argument).object(), lock) &&
           shared(lock);
  }

  void collect_aliases()
  {
    std::map<irep_idt, std::set<std::string>> candidates;
    for(const auto &function_entry : model.goto_functions.function_map)
    {
      for(const auto &instruction :
          function_entry.second.body.instructions)
      {
        if(instruction.is_assign())
        {
          irep_idt pointer;
          const exprt &rhs = strip(instruction.assign_rhs());
          if(
            symbol_id(instruction.assign_lhs(), pointer) &&
            rhs.id() == ID_address_of)
          {
            std::string target;
            if(
              atom(to_address_of_expr(rhs).object(), target) &&
              shared(target))
              candidates[pointer].insert(target);
          }
          continue;
        }
        irep_idt callee;
        if(!call_id(instruction, callee))
          continue;
        const auto symbol = model.symbol_table.symbols.find(callee);
        if(
          symbol == model.symbol_table.symbols.end() ||
          symbol->second.type.id() != ID_code)
          continue;
        const auto &parameters =
          to_code_type(symbol->second.type).parameters();
        const auto &arguments = instruction.call_arguments();
        if(parameters.size() != arguments.size())
          continue;
        for(std::size_t index = 0; index < parameters.size(); ++index)
        {
          const irep_idt parameter = parameters[index].get_identifier();
          const exprt &argument = strip(arguments[index]);
          if(parameter.empty() || argument.id() != ID_address_of)
            continue;
          std::string target;
          if(atom(to_address_of_expr(argument).object(), target) &&
             shared(target))
            candidates[parameter].insert(target);
        }
      }
    }
    for(const auto &entry : candidates)
    {
      if(entry.second.size() == 1)
        aliases[entry.first] = *entry.second.begin();
    }
  }

  void collect_initial_expr(
    const std::string &base,
    const typet &type,
    const exprt &value)
  {
    long long integer;
    if(integer_constant(value, integer))
    {
      initial[base] = intervalt::singleton(integer);
      return;
    }
    const typet &resolved_type = ns.follow(type);
    if(
      resolved_type.id() != ID_struct ||
      value.operands().empty())
      return;
    const auto &components = to_struct_type(resolved_type).components();
    if(components.size() != value.operands().size())
      return;
    for(std::size_t index = 0; index < components.size(); ++index)
      collect_initial_expr(
        base + "#" + id2string(components[index].get_name()),
        components[index].type(),
        value.operands()[index]);
  }

  void collect_initial()
  {
    for(const auto &entry : model.symbol_table.symbols)
    {
      const symbolt &symbol = entry.second;
      if(
        !symbol.is_static_lifetime || symbol.is_type ||
        symbol.type.id() == ID_code || symbol.value.is_nil())
        continue;
      collect_initial_expr(
        id2string(entry.first), symbol.type, symbol.value);
    }
    const auto initialize =
      model.goto_functions.function_map.find(INITIALIZE_FUNCTION);
    if(initialize == model.goto_functions.function_map.end())
      return;
    for(const auto &instruction : initialize->second.body.instructions)
    {
      if(!instruction.is_assign())
        continue;
      std::string lhs;
      long long value;
      if(
        atom(instruction.assign_lhs(), lhs) &&
        integer_constant(instruction.assign_rhs(), value) &&
        shared(lhs))
        initial[lhs] = intervalt::singleton(value);
      else if(atom(instruction.assign_lhs(), lhs) && shared(lhs))
        collect_initial_expr(
          lhs,
          instruction.assign_lhs().type(),
          instruction.assign_rhs());
    }
  }

  void collect_pre_spawn()
  {
    const auto main_function =
      model.goto_functions.function_map.find(ID_main);
    if(main_function == model.goto_functions.function_map.end())
      return;
    std::set<irep_idt> candidates;
    for(const auto &instruction :
        main_function->second.body.instructions)
    {
      irep_idt callee;
      if(!call_id(instruction, callee))
        continue;
      if(is_create(callee))
      {
        pre_spawn_functions = candidates;
        return;
      }
      if(
        model.goto_functions.function_map.count(callee) != 0 &&
        !ignored_external(callee))
        candidates.insert(callee);
    }
  }

  bool user_function(const irep_idt &identifier) const
  {
    if(
      identifier == INITIALIZE_FUNCTION ||
      identifier == goto_functionst::entry_point() ||
      identifier == "__spawned_thread" ||
      ignored_external(identifier) ||
      named(identifier, "pthread_"))
      return false;
    const auto found = model.goto_functions.function_map.find(identifier);
    return
      found != model.goto_functions.function_map.end() &&
      found->second.body_available();
  }
};

struct lock_nodet
{
  std::size_t index;
  std::vector<std::string> stack;
};

bool same_stack(
  const std::vector<std::string> &left,
  const std::vector<std::string> &right)
{
  return left == right;
}

void collect_expr_atoms(
  const analysist &analysis,
  const exprt &expr,
  std::set<std::string> &atoms)
{
  // Taking an address does not read the addressed object.  Potential escape
  // remains fail-closed at the assignment/call transfer sites.
  if(strip(expr).id() == ID_address_of)
    return;
  std::string key;
  if(analysis.atom(expr, key))
  {
    if(analysis.shared(key))
      atoms.insert(key);
    return;
  }
  for(const auto &operand : expr.operands())
    collect_expr_atoms(analysis, operand, atoms);
}

bool validate_expression(
  analysist &analysis,
  const exprt &src)
{
  const exprt &expr = strip(src);
  if(expr.id() == ID_address_of)
    return true;
  if(expr.id() == ID_dereference)
  {
    std::string resolved;
    if(!analysis.atom(expr, resolved))
    {
      analysis.reason = "unresolved_dereference";
      return false;
    }
  }
  std::string key;
  if(analysis.atom(expr, key) && analysis.shared(key))
  {
    const typet &type = analysis.ns.follow(expr.type());
    if(
      type.id() != ID_signedbv ||
      type.get_bool(ID_C_volatile))
    {
      analysis.reason = "shared_scalar_type";
      return false;
    }
    return true;
  }
  for(const auto &operand : expr.operands())
  {
    if(!validate_expression(analysis, operand))
      return false;
  }
  return true;
}

bool call_graph_acyclic(
  const irep_idt &node,
  const std::map<irep_idt, std::set<irep_idt>> &edges,
  std::set<irep_idt> &active,
  std::set<irep_idt> &done)
{
  if(active.count(node) != 0)
    return false;
  if(done.count(node) != 0)
    return true;
  active.insert(node);
  const auto found = edges.find(node);
  if(found != edges.end())
  {
    for(const auto &target : found->second)
    {
      if(!call_graph_acyclic(target, edges, active, done))
        return false;
    }
  }
  active.erase(node);
  done.insert(node);
  return true;
}

bool validate_model(analysist &analysis)
{
  std::map<irep_idt, std::set<irep_idt>> call_edges;
  for(const auto &function_entry :
      analysis.model.goto_functions.function_map)
  {
    if(!analysis.user_function(function_entry.first))
      continue;
    for(const auto &instruction :
        function_entry.second.body.instructions)
    {
      if(
        instruction.is_atomic_begin() ||
        instruction.is_atomic_end())
      {
        analysis.reason = "unsupported_atomic_region";
        return false;
      }
      if(instruction.is_assign())
      {
        const exprt &rhs = strip(instruction.assign_rhs());
        if(rhs.id() == ID_address_of)
        {
          const exprt &object =
            to_address_of_expr(rhs).object();
          std::string addressed;
          if(
            analysis.atom(object, addressed) &&
            analysis.shared(addressed) &&
            analysis.ns.follow(object.type()).id() ==
              ID_signedbv)
          {
            analysis.reason = "scalar_address_taken";
            return false;
          }
        }
        if(
          !validate_expression(analysis, instruction.assign_lhs()) ||
          !validate_expression(analysis, instruction.assign_rhs()))
          return false;
      }
      else if(
        instruction.is_goto() || instruction.is_assume() ||
        instruction.is_assert())
      {
        if(!validate_expression(analysis, instruction.condition()))
          return false;
      }
      if(!instruction.is_function_call())
        continue;
      irep_idt callee;
      if(!call_id(instruction, callee))
      {
        analysis.reason = "indirect_call";
        return false;
      }
      if(is_error(callee) || named(callee, "abort"))
      {
        analysis.reason = "unproved_error_call";
        return false;
      }
      for(const auto &argument : instruction.call_arguments())
      {
        if(!validate_expression(analysis, argument))
          return false;
      }
      if(
        is_lock(callee) || is_unlock(callee) ||
        is_mutex_init(callee) || is_create(callee) ||
        is_join(callee) || is_property(callee) ||
        named(callee, "sleep") ||
        named(callee, "__CPROVER_assume"))
        continue;
      const auto target =
        analysis.model.goto_functions.function_map.find(callee);
      if(
        target == analysis.model.goto_functions.function_map.end() ||
        !target->second.body_available() ||
        !analysis.user_function(callee))
      {
        analysis.reason = "unsupported_call";
        return false;
      }
      call_edges[function_entry.first].insert(callee);
    }
  }
  std::set<irep_idt> active;
  std::set<irep_idt> done;
  for(const auto &entry : call_edges)
  {
    if(!call_graph_acyclic(entry.first, call_edges, active, done))
    {
      analysis.reason = "recursive_call_graph";
      return false;
    }
  }
  return true;
}

bool compute_locksets(
  analysist &analysis,
  const irep_idt &function_id,
  std::vector<std::vector<std::string>> &at,
  std::vector<goto_programt::targett> &order)
{
  auto &program =
    analysis.model.goto_functions.function_map.at(function_id).body;
  std::map<const goto_programt::instructiont *, std::size_t> positions;
  for(auto iterator = program.instructions.begin();
      iterator != program.instructions.end(); ++iterator)
  {
    positions[&*iterator] = order.size();
    order.push_back(iterator);
  }
  if(order.empty())
    return true;
  std::vector<bool> reached(order.size(), false);
  at.resize(order.size());
  std::deque<std::size_t> work;
  reached[0] = true;
  work.push_back(0);
  while(!work.empty())
  {
    const std::size_t index = work.front();
    work.pop_front();
    std::vector<std::string> after = at[index];
    irep_idt callee;
    if(call_id(*order[index], callee))
    {
      std::string lock;
      if(is_lock(callee))
      {
        if(!analysis.lock_argument(*order[index], lock))
        {
          analysis.reason = "lock_argument";
          return false;
        }
        if(std::find(after.begin(), after.end(), lock) != after.end())
        {
          analysis.reason = "recursive_lock";
          return false;
        }
        if(!after.empty())
          analysis.lock_edges.insert({after.back(), lock});
        after.push_back(lock);
        analysis.locks.insert(lock);
      }
      else if(is_unlock(callee))
      {
        if(
          !analysis.lock_argument(*order[index], lock) ||
          after.empty() || after.back() != lock)
        {
          analysis.reason = "lock_balance";
          return false;
        }
        after.pop_back();
      }
    }
    std::vector<std::size_t> successors;
    if(order[index]->is_goto())
    {
      for(const auto &target : order[index]->targets)
        successors.push_back(positions.at(&*target));
      if(
        !order[index]->condition().is_true() &&
        index + 1 < order.size())
        successors.push_back(index + 1);
    }
    else if(
      !order[index]->is_end_function() &&
      index + 1 < order.size())
      successors.push_back(index + 1);
    else if(
      order[index]->is_end_function() &&
      !after.empty())
    {
      analysis.reason = "lock_balance";
      return false;
    }
    for(const std::size_t successor : successors)
    {
      if(!reached[successor])
      {
        reached[successor] = true;
        at[successor] = after;
        work.push_back(successor);
      }
      else if(!same_stack(at[successor], after))
      {
        analysis.reason = "lockset_join";
        return false;
      }
    }
  }
  return true;
}

bool lock_order_acyclic(
  const std::string &node,
  const std::set<std::pair<std::string, std::string>> &edges,
  std::set<std::string> &active,
  std::set<std::string> &done)
{
  if(active.count(node) != 0)
    return false;
  if(done.count(node) != 0)
    return true;
  active.insert(node);
  for(const auto &edge : edges)
  {
    if(
      edge.first == node &&
      !lock_order_acyclic(edge.second, edges, active, done))
      return false;
  }
  active.erase(node);
  done.insert(node);
  return true;
}

bool collect_protection(analysist &analysis)
{
  std::map<std::string, std::set<std::string>> candidates;
  for(const auto &entry : analysis.model.goto_functions.function_map)
  {
    if(!analysis.user_function(entry.first))
      continue;
    std::vector<std::vector<std::string>> locksets;
    std::vector<goto_programt::targett> order;
    if(!compute_locksets(analysis, entry.first, locksets, order))
      return false;
    const bool initializer =
      analysis.pre_spawn_functions.count(entry.first) != 0;
    for(std::size_t index = 0; index < order.size(); ++index)
    {
      const auto &instruction = *order[index];
      irep_idt callee;
      if(
        call_id(instruction, callee) &&
        (is_lock(callee) || is_unlock(callee) ||
         is_mutex_init(callee) || is_create(callee) ||
         is_join(callee)))
        continue;
      if(
        initializer && locksets[index].empty() &&
        instruction.is_assign())
      {
        std::string lhs;
        long long assigned;
        if(
          analysis.atom(instruction.assign_lhs(), lhs) &&
          analysis.shared(lhs) &&
          integer_constant(instruction.assign_rhs(), assigned))
        {
          const auto initial = analysis.initial.find(lhs);
          if(
            initial != analysis.initial.end() &&
            initial->second.lower_set &&
            initial->second.upper_set &&
            initial->second.lower == assigned &&
            initial->second.upper == assigned)
            continue;
        }
      }
      std::set<std::string> atoms;
      if(instruction.is_assign())
      {
        collect_expr_atoms(analysis, instruction.assign_lhs(), atoms);
        collect_expr_atoms(analysis, instruction.assign_rhs(), atoms);
      }
      else if(instruction.is_goto() || instruction.is_assume())
        collect_expr_atoms(analysis, instruction.condition(), atoms);
      else if(instruction.is_function_call())
      {
        const auto direct =
          call_id(instruction, callee)
            ? analysis.model.goto_functions.function_map.find(callee)
            : analysis.model.goto_functions.function_map.end();
        // A direct call to a body-available user function transfers no shared
        // value merely by passing an address.  The callee body is analysed
        // separately after formal-to-actual alias resolution.  Counting
        // `helper(&shared)` as an unlocked read here would reject sound
        // encapsulated mutex APIs such as queue_get(&queue).
        if(
          direct != analysis.model.goto_functions.function_map.end() &&
          direct->second.body_available() &&
          !ignored_external(callee))
          continue;
        for(const auto &argument : instruction.call_arguments())
          collect_expr_atoms(analysis, argument, atoms);
      }
      for(const auto &atom : atoms)
      {
        if(locksets[index].empty())
        {
          analysis.reason = "unprotected_shared";
          return false;
        }
        std::set<std::string> held(
          locksets[index].begin(), locksets[index].end());
        auto found = candidates.find(atom);
        if(found == candidates.end())
          candidates[atom] = held;
        else
        {
          std::set<std::string> intersection;
          std::set_intersection(
            found->second.begin(), found->second.end(),
            held.begin(), held.end(),
            std::inserter(intersection, intersection.begin()));
          found->second = intersection;
        }
      }
    }
  }
  for(const auto &entry : candidates)
  {
    if(entry.second.size() != 1)
    {
      analysis.reason = "protection_set";
      return false;
    }
    analysis.protection[entry.first] = *entry.second.begin();
  }
  std::set<std::string> active;
  std::set<std::string> done;
  for(const auto &lock : analysis.locks)
  {
    if(!lock_order_acyclic(
         lock, analysis.lock_edges, active, done))
    {
      analysis.reason = "cyclic_lock_order";
      return false;
    }
  }
  return !analysis.protection.empty();
}

bool add_checked(long long left, long long right, long long &result)
{
  if(
    (right > 0 && left > std::numeric_limits<long long>::max() - right) ||
    (right < 0 && left < std::numeric_limits<long long>::min() - right))
    return false;
  result = left + right;
  return true;
}

bool signed_bounds(
  const typet &type,
  long long &minimum,
  long long &maximum)
{
  if(type.id() != ID_signedbv)
    return false;
  const std::size_t width = to_bitvector_type(type).get_width();
  if(width == 0 || width > 64)
    return false;
  if(width == 64)
  {
    minimum = std::numeric_limits<long long>::min();
    maximum = std::numeric_limits<long long>::max();
  }
  else
  {
    maximum = (static_cast<long long>(1) << (width - 1)) - 1;
    minimum = -maximum - 1;
  }
  return true;
}

bool eval_interval(
  const analysist &analysis,
  const statet &state,
  const exprt &src,
  intervalt &result)
{
  const exprt &expr = strip(src);
  long long constant;
  if(integer_constant(expr, constant))
  {
    result = intervalt::singleton(constant);
    return true;
  }
  std::string key;
  if(analysis.atom(expr, key))
  {
    result = state.get(key);
    return true;
  }
  if(
    (expr.id() == ID_plus || expr.id() == ID_minus) &&
    expr.operands().size() == 2)
  {
    long long type_minimum;
    long long type_maximum;
    if(!signed_bounds(expr.type(), type_minimum, type_maximum))
      return false;
    intervalt left;
    intervalt right;
    if(
      !eval_interval(analysis, state, expr.op0(), left) ||
      !eval_interval(analysis, state, expr.op1(), right))
      return false;
    if(
      expr.id() == ID_minus && right.lower_set &&
      right.upper_set && right.lower == right.upper)
    {
      if(right.lower == std::numeric_limits<long long>::min())
        return false;
      right.lower = right.upper = -right.lower;
    }
    else if(expr.id() == ID_minus)
      return false;
    result = intervalt();
    if(left.lower_set && right.lower_set)
    {
      if(!add_checked(left.lower, right.lower, result.lower))
        return false;
      if(result.lower < type_minimum || result.lower > type_maximum)
        return false;
      result.lower_set = true;
    }
    if(left.upper_set && right.upper_set)
    {
      if(!add_checked(left.upper, right.upper, result.upper))
        return false;
      if(result.upper < type_minimum || result.upper > type_maximum)
        return false;
      result.upper_set = true;
    }
    return true;
  }
  return false;
}

enum class truth_valuet
{
  FALSE_VALUE,
  TRUE_VALUE,
  UNKNOWN
};

truth_valuet evaluate_condition(
  const analysist &analysis,
  const statet &state,
  const exprt &src)
{
  const exprt &expr = strip(src);
  if(expr.is_true())
    return truth_valuet::TRUE_VALUE;
  if(expr.is_false())
    return truth_valuet::FALSE_VALUE;
  if(expr.id() == ID_not && expr.operands().size() == 1)
  {
    const truth_valuet value =
      evaluate_condition(analysis, state, expr.op0());
    if(value == truth_valuet::TRUE_VALUE)
      return truth_valuet::FALSE_VALUE;
    if(value == truth_valuet::FALSE_VALUE)
      return truth_valuet::TRUE_VALUE;
    return truth_valuet::UNKNOWN;
  }
  if(expr.operands().size() != 2)
    return truth_valuet::UNKNOWN;
  intervalt left;
  intervalt right;
  if(
    !eval_interval(analysis, state, expr.op0(), left) ||
    !eval_interval(analysis, state, expr.op1(), right))
    return truth_valuet::UNKNOWN;
  if(expr.id() == ID_equal || expr.id() == ID_notequal)
  {
    bool definitely_equal =
      left.lower_set && left.upper_set && right.lower_set &&
      right.upper_set && left.lower == left.upper &&
      right.lower == right.upper && left.lower == right.lower;
    bool disjoint =
      (left.upper_set && right.lower_set && left.upper < right.lower) ||
      (right.upper_set && left.lower_set && right.upper < left.lower);
    if(expr.id() == ID_equal)
      return definitely_equal
               ? truth_valuet::TRUE_VALUE
               : (disjoint ? truth_valuet::FALSE_VALUE
                           : truth_valuet::UNKNOWN);
    return disjoint
             ? truth_valuet::TRUE_VALUE
             : (definitely_equal ? truth_valuet::FALSE_VALUE
                                 : truth_valuet::UNKNOWN);
  }
  if(expr.id() == ID_lt)
  {
    if(left.upper_set && right.lower_set && left.upper < right.lower)
      return truth_valuet::TRUE_VALUE;
    if(left.lower_set && right.upper_set && left.lower >= right.upper)
      return truth_valuet::FALSE_VALUE;
  }
  if(expr.id() == ID_le)
  {
    if(left.upper_set && right.lower_set && left.upper <= right.lower)
      return truth_valuet::TRUE_VALUE;
    if(left.lower_set && right.upper_set && left.lower > right.upper)
      return truth_valuet::FALSE_VALUE;
  }
  if(expr.id() == ID_gt)
    return evaluate_condition(analysis, state, binary_relation_exprt(
      expr.op1(), ID_lt, expr.op0()));
  if(expr.id() == ID_ge)
    return evaluate_condition(analysis, state, binary_relation_exprt(
      expr.op1(), ID_le, expr.op0()));
  return truth_valuet::UNKNOWN;
}

void refine_bound(
  intervalt &value,
  const irep_idt &relation,
  long long constant)
{
  if(relation == ID_equal)
    value = intervalt::singleton(constant);
  else if(relation == ID_lt && constant > std::numeric_limits<long long>::min())
  {
    const long long upper = constant - 1;
    if(!value.upper_set || upper < value.upper)
    {
      value.upper_set = true;
      value.upper = upper;
    }
  }
  else if(relation == ID_le)
  {
    if(!value.upper_set || constant < value.upper)
    {
      value.upper_set = true;
      value.upper = constant;
    }
  }
  else if(relation == ID_gt && constant < std::numeric_limits<long long>::max())
  {
    const long long lower = constant + 1;
    if(!value.lower_set || lower > value.lower)
    {
      value.lower_set = true;
      value.lower = lower;
    }
  }
  else if(relation == ID_ge)
  {
    if(!value.lower_set || constant > value.lower)
    {
      value.lower_set = true;
      value.lower = constant;
    }
  }
}

void assume_condition(
  const analysist &analysis,
  statet &state,
  const exprt &src,
  bool positive)
{
  if(state.bottom)
    return;
  const truth_valuet truth = evaluate_condition(analysis, state, src);
  if(
    (positive && truth == truth_valuet::FALSE_VALUE) ||
    (!positive && truth == truth_valuet::TRUE_VALUE))
  {
    state.bottom = true;
    state.values.clear();
    return;
  }
  const exprt &expr = strip(src);
  if(expr.id() == ID_not && expr.operands().size() == 1)
  {
    assume_condition(
      analysis, state, expr.op0(), !positive);
    return;
  }
  if(expr.operands().size() != 2)
    return;
  std::string key;
  long long constant;
  if(
    !analysis.atom(expr.op0(), key) ||
    !integer_constant(expr.op1(), constant))
    return;
  irep_idt relation = expr.id();
  if(!positive)
  {
    if(relation == ID_lt)
      relation = ID_ge;
    else if(relation == ID_le)
      relation = ID_gt;
    else if(relation == ID_gt)
      relation = ID_le;
    else if(relation == ID_ge)
      relation = ID_lt;
    else if(relation == ID_equal)
      relation = ID_notequal;
    else if(relation == ID_notequal)
      relation = ID_equal;
  }
  intervalt value = state.get(key);
  refine_bound(value, relation, constant);
  if(
    value.lower_set && value.upper_set &&
    value.lower > value.upper)
  {
    state.bottom = true;
    state.values.clear();
  }
  else
    state.set(key, value);
}

struct node_keyt
{
  std::size_t index;
  std::vector<std::string> stack;

  bool operator<(const node_keyt &other) const
  {
    if(index != other.index)
      return index < other.index;
    return stack < other.stack;
  }
};

bool analyze_function(
  analysist &analysis,
  const irep_idt &function_id,
  bool &invariant_changed,
  bool &all_properties)
{
  auto &program =
    analysis.model.goto_functions.function_map.at(function_id).body;
  std::vector<goto_programt::targett> order;
  std::map<const goto_programt::instructiont *, std::size_t> positions;
  for(auto iterator = program.instructions.begin();
      iterator != program.instructions.end(); ++iterator)
  {
    positions[&*iterator] = order.size();
    order.push_back(iterator);
  }
  if(order.empty())
    return true;
  statet entry;
  if(function_id == ID_main)
  {
    for(const auto &initial : analysis.initial)
      entry.set(initial.first, initial.second);
  }
  std::map<node_keyt, statet> states;
  std::map<node_keyt, unsigned> merges;
  std::deque<node_keyt> work;
  const node_keyt start{0, {}};
  states[start] = entry;
  work.push_back(start);
  std::size_t visits = 0;
  while(!work.empty())
  {
    if(++visits > 200000)
    {
      analysis.reason = "local_fixedpoint";
      return false;
    }
    const node_keyt key = work.front();
    work.pop_front();
    statet state = states[key];
    if(state.bottom)
      continue;
    const auto &instruction = *order[key.index];
    std::vector<std::string> after_stack = key.stack;
    irep_idt callee;
    if(instruction.is_assign())
    {
      std::string lhs;
      intervalt value;
      if(!analysis.atom(instruction.assign_lhs(), lhs))
      {
        std::set<std::string> atoms;
        collect_expr_atoms(
          analysis, instruction.assign_lhs(), atoms);
        if(!atoms.empty())
        {
          analysis.reason = "assignment_lhs";
          return false;
        }
      }
      else if(
        !eval_interval(
          analysis, state, instruction.assign_rhs(), value))
      {
        if(analysis.shared(lhs))
        {
          analysis.reason = "assignment_rhs";
          return false;
        }
        state.set(lhs, intervalt());
      }
      else
        state.set(lhs, value);
    }
    else if(call_id(instruction, callee))
    {
      std::string lock;
      if(is_lock(callee))
      {
        if(!analysis.lock_argument(instruction, lock))
          return false;
        after_stack.push_back(lock);
        const statet &invariant = analysis.lock_invariants[lock];
        for(const auto &protected_entry : analysis.protection)
        {
          if(protected_entry.second != lock)
            continue;
          intervalt current = state.get(protected_entry.first);
          const intervalt imported =
            invariant.get(protected_entry.first);
          if(!meet_interval(current, imported))
          {
            state.bottom = true;
            break;
          }
          state.set(protected_entry.first, current);
        }
      }
      else if(is_unlock(callee))
      {
        if(
          !analysis.lock_argument(instruction, lock) ||
          after_stack.empty() || after_stack.back() != lock)
          return false;
        statet exported;
        for(const auto &protected_entry : analysis.protection)
        {
          if(protected_entry.second == lock)
            exported.set(
              protected_entry.first,
              state.get(protected_entry.first));
        }
        statet old = analysis.lock_invariants[lock];
        if(join_state(analysis.lock_invariants[lock], exported))
        {
          ++analysis.lock_changes[lock];
          if(analysis.lock_changes[lock] > 3)
            widen_state(analysis.lock_invariants[lock], old);
          invariant_changed = true;
        }
        after_stack.pop_back();
        for(const auto &protected_entry : analysis.protection)
        {
          const bool retained =
            std::find(
              after_stack.begin(), after_stack.end(),
              protected_entry.second) != after_stack.end();
          if(!retained)
            state.set(protected_entry.first, intervalt());
        }
      }
      else if(is_property(callee))
      {
        ++analysis.properties;
        if(
          instruction.call_arguments().size() != 1 ||
          evaluate_condition(
            analysis, state,
            instruction.call_arguments().front()) !=
            truth_valuet::TRUE_VALUE)
          all_properties = false;
      }
      else if(is_create(callee))
      {
        // After the first spawn, a main-thread path may observe any state
        // exported by a concurrent critical section.  Starting every
        // function from the static initializer would under-approximate that
        // interference.
        for(const auto &protected_entry : analysis.protection)
          state.set(protected_entry.first, intervalt());
      }
      else if(is_error(callee) || named(callee, "abort"))
      {
        analysis.reason = "unproved_error_call";
        return false;
      }
      else if(!ignored_external(callee))
      {
        const auto function =
          analysis.model.goto_functions.function_map.find(callee);
        if(
          function == analysis.model.goto_functions.function_map.end() ||
          !function->second.body_available())
        {
          analysis.reason = "unknown_call";
          return false;
        }
      }
    }
    else if(instruction.is_assert())
    {
      ++analysis.properties;
      if(
        evaluate_condition(
          analysis, state, instruction.condition()) !=
        truth_valuet::TRUE_VALUE)
        all_properties = false;
    }
    else if(
      instruction.is_other() &&
      !instruction.code().get_statement().empty())
    {
      std::set<std::string> atoms;
      instruction.apply(
        [&analysis, &atoms](const exprt &expr) {
          collect_expr_atoms(analysis, expr, atoms);
        });
      if(!atoms.empty())
      {
        analysis.reason = "other_shared";
        return false;
      }
    }

    std::vector<std::pair<std::size_t, statet>> successors;
    if(instruction.is_goto())
    {
      for(const auto &target : instruction.targets)
      {
        statet branch = state;
        assume_condition(
          analysis, branch, instruction.condition(), true);
        successors.push_back({positions.at(&*target), branch});
      }
      if(
        !instruction.condition().is_true() &&
        key.index + 1 < order.size())
      {
        statet branch = state;
        assume_condition(
          analysis, branch, instruction.condition(), false);
        successors.push_back({key.index + 1, branch});
      }
    }
    else if(
      !instruction.is_end_function() &&
      key.index + 1 < order.size())
      successors.push_back({key.index + 1, state});

    for(auto &successor : successors)
    {
      if(successor.second.bottom)
        continue;
      const node_keyt next{successor.first, after_stack};
      const auto existing = states.find(next);
      if(existing == states.end())
      {
        states[next] = successor.second;
        work.push_back(next);
      }
      else
      {
        statet old = existing->second;
        if(join_state(existing->second, successor.second))
        {
          if(++merges[next] > 3)
            widen_state(existing->second, old);
          work.push_back(next);
        }
      }
    }
  }
  return true;
}

bool initialize_lock_invariants(analysist &analysis)
{
  for(const auto &lock : analysis.locks)
  {
    statet state;
    for(const auto &entry : analysis.protection)
    {
      if(entry.second != lock)
        continue;
      const auto initial = analysis.initial.find(entry.first);
      if(initial == analysis.initial.end())
      {
        analysis.reason = "initial_value";
        return false;
      }
      state.set(entry.first, initial->second);
    }
    analysis.lock_invariants[lock] = state;
  }
  return true;
}

bool run_fixedpoint(analysist &analysis)
{
  if(!initialize_lock_invariants(analysis))
    return false;
  bool stable_properties = false;
  for(unsigned round = 0; round < 20; ++round)
  {
    bool changed = false;
    bool all_properties = true;
    analysis.properties = 0;
    for(const auto &entry : analysis.model.goto_functions.function_map)
    {
      if(
        analysis.user_function(entry.first) &&
        !analyze_function(
          analysis, entry.first, changed, all_properties))
        return false;
    }
    stable_properties = all_properties;
    if(!changed)
      return stable_properties && analysis.properties != 0;
  }
  analysis.reason = "global_fixedpoint";
  return false;
}

void transform_model(analysist &analysis)
{
  for(auto &function_entry :
      analysis.model.goto_functions.function_map)
  {
    for(auto &instruction :
        function_entry.second.body.instructions)
    {
      irep_idt callee;
      if(
        call_id(instruction, callee) &&
        (is_property(callee) || is_create(callee) ||
         is_join(callee)))
        instruction.turn_into_skip();
      if(
        function_entry.first == ID_main &&
        instruction.is_backwards_goto())
        instruction.turn_into_skip();
    }
  }
  analysis.model.goto_functions.update();
}
} // namespace

bool lock_relational_ai_transform(
  goto_modelt &goto_model,
  message_handlert &message_handler)
{
  (void)message_handler;
  analysist analysis(goto_model);
  analysis.collect_aliases();
  analysis.collect_initial();
  analysis.collect_pre_spawn();
  if(
    !validate_model(analysis) ||
    !collect_protection(analysis))
  {
    std::cout << "NATIVE_LOCK_RELATIONAL_AI applied=0 reason="
              << analysis.reason << '\n';
    return false;
  }
  if(!run_fixedpoint(analysis))
  {
    if(analysis.reason.empty())
      analysis.reason = "property_not_proved";
    std::cout << "NATIVE_LOCK_RELATIONAL_AI applied=0 reason="
              << analysis.reason
              << " properties=" << analysis.properties << '\n';
    return false;
  }
  transform_model(analysis);
  std::cout << "NATIVE_LOCK_RELATIONAL_AI applied=1"
            << " locks=" << analysis.locks.size()
            << " objects=" << analysis.protection.size()
            << " properties=" << analysis.properties << '\n';
  return true;
}
