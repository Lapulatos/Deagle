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

bool is_trylock(const irep_idt &identifier)
{
  return named(identifier, "pthread_mutex_trylock");
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

bool is_allocator(const irep_idt &identifier)
{
  return
    named(identifier, "malloc") ||
    named(identifier, "calloc");
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
    is_trylock(identifier) ||
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

struct region_selectort
{
  std::string container;
  std::string selector;
  irep_idt selector_symbol;

  bool operator==(const region_selectort &other) const
  {
    return
      container == other.container &&
      selector == other.selector &&
      selector_symbol == other.selector_symbol;
  }
};

struct analysist
{
  using alias_contextt = std::map<irep_idt, std::string>;

  goto_modelt &model;
  namespacet ns;
  std::set<std::string> shared_roots;
  std::map<irep_idt, std::string> aliases;
  std::set<irep_idt> congruence_aliases;
  std::set<irep_idt> static_initialized_aliases;
  std::set<irep_idt> region_summary_functions;
  std::set<irep_idt> region_initializers;
  std::set<irep_idt> region_inserters;
  std::map<irep_idt, std::size_t> region_return_parameters;
  std::map<irep_idt, std::size_t> region_insert_node_parameters;
  std::set<irep_idt> region_zero_fields;
  std::map<irep_idt, region_selectort> region_selectors;
  std::set<std::string> region_roots;
  std::map<irep_idt, std::vector<alias_contextt>> function_contexts;
  const alias_contextt *active_aliases;
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
      active_aliases(nullptr),
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

  bool data_pointer(const irep_idt &identifier) const
  {
    const auto symbol = model.symbol_table.symbols.find(identifier);
    if(symbol == model.symbol_table.symbols.end())
      return false;
    const typet &type = ns.follow(symbol->second.type);
    return
      type.id() == ID_pointer &&
      ns.follow(to_pointer_type(type).base_type()).id() != ID_code;
  }

  std::vector<irep_idt> data_pointer_parameters(
    const irep_idt &function) const
  {
    std::vector<irep_idt> result;
    const auto symbol = model.symbol_table.symbols.find(function);
    if(
      symbol == model.symbol_table.symbols.end() ||
      symbol->second.type.id() != ID_code)
      return result;
    for(const auto &parameter :
        to_code_type(symbol->second.type).parameters())
    {
      const irep_idt identifier = parameter.get_identifier();
      if(!identifier.empty() && data_pointer(identifier))
        result.push_back(identifier);
    }
    return result;
  }

  bool pointer_member_of(
    const exprt &src,
    irep_idt &pointer,
    irep_idt &field) const
  {
    const exprt &expr = strip(src);
    if(expr.id() != ID_member)
      return false;
    const member_exprt &member = to_member_expr(expr);
    const exprt &compound = strip(member.compound());
    if(compound.id() != ID_dereference)
      return false;
    if(
      !symbol_id(
        to_dereference_expr(compound).pointer(), pointer))
      return false;
    field = member.get_component_name();
    return true;
  }

  bool discover_region_initializer(
    const irep_idt &function,
    const goto_programt &program)
  {
    const auto parameters = data_pointer_parameters(function);
    if(parameters.size() != 1)
      return false;
    bool scalar_zero = false;
    irep_idt scalar_field;
    for(const auto &instruction : program.instructions)
    {
      if(
        instruction.is_skip() || instruction.is_location() ||
        instruction.is_decl() || instruction.is_dead() ||
        instruction.is_end_function())
        continue;
      if(!instruction.is_assign())
        return false;
      irep_idt pointer;
      irep_idt field;
      if(
        !pointer_member_of(
          instruction.assign_lhs(), pointer, field) ||
        pointer != parameters.front())
        return false;
      const typet &type =
        ns.follow(instruction.assign_lhs().type());
      if(type.id() == ID_signedbv)
      {
        long long value;
        if(
          !integer_constant(
            instruction.assign_rhs(), value) ||
          value != 0 ||
          (scalar_zero && scalar_field != field))
          return false;
        scalar_zero = true;
        scalar_field = field;
      }
      else if(
        type.id() != ID_pointer ||
        !strip(instruction.assign_rhs()).is_zero())
        return false;
    }
    if(!scalar_zero)
      return false;
    region_zero_fields.insert(scalar_field);
    return true;
  }

  bool discover_region_traversal(
    const irep_idt &function,
    const goto_programt &program,
    std::size_t &parameter_index)
  {
    const auto symbol = model.symbol_table.symbols.find(function);
    if(
      symbol == model.symbol_table.symbols.end() ||
      symbol->second.type.id() != ID_code)
      return false;
    const auto &parameters =
      to_code_type(symbol->second.type).parameters();
    std::vector<std::pair<std::size_t, irep_idt>> pointers;
    for(std::size_t index = 0; index < parameters.size(); ++index)
    {
      const irep_idt identifier =
        parameters[index].get_identifier();
      if(!identifier.empty() && data_pointer(identifier))
        pointers.push_back({index, identifier});
    }
    if(pointers.size() != 1)
      return false;

    std::set<irep_idt> derived{pointers.front().second};
    bool changed = true;
    while(changed)
    {
      changed = false;
      for(const auto &instruction : program.instructions)
      {
        if(!instruction.is_assign())
          continue;
        irep_idt lhs;
        if(
          !symbol_id(instruction.assign_lhs(), lhs) ||
          !data_pointer(lhs))
          continue;
        const exprt &rhs = strip(instruction.assign_rhs());
        irep_idt source;
        if(symbol_id(rhs, source) && derived.count(source) != 0)
          changed |= derived.insert(lhs).second;
        else
        {
          irep_idt base;
          irep_idt field;
          if(
            pointer_member_of(rhs, base, field) &&
            derived.count(base) != 0 &&
            ns.follow(rhs.type()).id() == ID_pointer)
            changed |= derived.insert(lhs).second;
        }
      }
    }

    bool returned = false;
    bool traversed = false;
    for(const auto &instruction : program.instructions)
    {
      irep_idt callee;
      if(instruction.is_function_call())
      {
        if(
          !call_id(instruction, callee) ||
          (!is_lock(callee) && !is_unlock(callee)))
          return false;
        continue;
      }
      if(instruction.is_set_return_value())
      {
        irep_idt result;
        if(
          !symbol_id(instruction.return_value(), result) ||
          derived.count(result) == 0)
          return false;
        returned = true;
        continue;
      }
      if(!instruction.is_assign())
        continue;
      irep_idt pointer;
      irep_idt field;
      if(pointer_member_of(instruction.assign_lhs(), pointer, field))
        return false;
      if(pointer_member_of(instruction.assign_rhs(), pointer, field))
      {
        if(derived.count(pointer) == 0)
          return false;
        traversed = true;
      }
    }
    if(!returned || !traversed)
      return false;
    parameter_index = pointers.front().first;
    return true;
  }

  bool discover_region_inserter(
    const irep_idt &function,
    const goto_programt &program,
    std::size_t &node_parameter_index)
  {
    const auto symbol = model.symbol_table.symbols.find(function);
    if(
      symbol == model.symbol_table.symbols.end() ||
      symbol->second.type.id() != ID_code)
      return false;
    const auto &parameters =
      to_code_type(symbol->second.type).parameters();
    std::vector<std::pair<std::size_t, irep_idt>> pointers;
    for(std::size_t index = 0; index < parameters.size(); ++index)
    {
      const irep_idt identifier =
        parameters[index].get_identifier();
      if(!identifier.empty() && data_pointer(identifier))
        pointers.push_back({index, identifier});
    }
    if(pointers.size() != 2)
      return false;
    std::set<irep_idt> derived{
      pointers[0].second, pointers[1].second};
    bool link_write = false;
    for(const auto &instruction : program.instructions)
    {
      irep_idt callee;
      if(instruction.is_function_call())
      {
        if(
          !call_id(instruction, callee) ||
          (!is_lock(callee) && !is_unlock(callee)))
          return false;
        continue;
      }
      if(instruction.is_set_return_value())
        return false;
      if(!instruction.is_assign())
        continue;
      irep_idt lhs;
      if(symbol_id(instruction.assign_lhs(), lhs))
      {
        if(data_pointer(lhs))
          derived.insert(lhs);
        continue;
      }
      irep_idt pointer;
      irep_idt field;
      if(
        !pointer_member_of(
          instruction.assign_lhs(), pointer, field) ||
        derived.count(pointer) == 0 ||
        ns.follow(instruction.assign_lhs().type()).id() !=
          ID_pointer)
        return false;
      link_write = true;
    }
    if(!link_write)
      return false;
    node_parameter_index = pointers.front().first;
    return true;
  }

  void discover_region_summaries()
  {
    for(const auto &entry : model.goto_functions.function_map)
    {
      if(!user_function(entry.first))
        continue;
      if(discover_region_initializer(entry.first, entry.second.body))
      {
        region_initializers.insert(entry.first);
        region_summary_functions.insert(entry.first);
      }
    }
    if(region_initializers.empty())
      return;
    for(const auto &entry : model.goto_functions.function_map)
    {
      if(!user_function(entry.first))
        continue;
      std::size_t parameter = 0;
      if(
        discover_region_traversal(
          entry.first, entry.second.body, parameter))
      {
        region_return_parameters[entry.first] = parameter;
        region_summary_functions.insert(entry.first);
      }
      else if(
        discover_region_inserter(
          entry.first, entry.second.body, parameter))
      {
        region_inserters.insert(entry.first);
        region_insert_node_parameters[entry.first] = parameter;
        region_summary_functions.insert(entry.first);
      }
    }
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
    if(expr.id() == ID_index && expr.operands().size() == 2)
    {
      std::string base;
      if(!atom(expr.op0(), base) || !shared(base))
        return false;
      const exprt &index = strip(expr.op1());
      if(index.id() != ID_symbol && index.id() != ID_constant)
        return false;
      // The selector is retained and checked separately by the indexed-lock
      // correlation audit.  The value domain uses one parametric family
      // representing an arbitrary but fixed element.
      key = base + "#[]";
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
        if(active_aliases != nullptr)
        {
          const auto contextual = active_aliases->find(identifier);
          if(contextual != active_aliases->end())
          {
            key = contextual->second;
            return true;
          }
        }
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
    if(argument.id() == ID_address_of)
      return atom(to_address_of_expr(argument).object(), lock) &&
             shared(lock);
    irep_idt identifier;
    if(!symbol_id(argument, identifier))
      return false;
    if(active_aliases != nullptr)
    {
      const auto contextual = active_aliases->find(identifier);
      if(contextual != active_aliases->end())
      {
        lock = contextual->second;
        return shared(lock);
      }
    }
    const auto alias = aliases.find(identifier);
    if(alias == aliases.end())
      return false;
    lock = alias->second;
    return shared(lock);
  }

  bool region_argument(
    const exprt &src,
    std::string &target,
    region_selectort &selector) const
  {
    const exprt &argument = strip(src);
    if(!atom(argument, target) || !shared(target))
      return false;
    selector = region_selectort{};
    if(
      argument.id() == ID_index &&
      argument.operands().size() == 2)
    {
      std::string container;
      if(!atom(argument.op0(), container) || !shared(container))
        return false;
      const exprt &index = strip(argument.op1());
      selector.container = container;
      if(index.id() == ID_symbol)
      {
        selector.selector_symbol =
          to_symbol_expr(index).get_identifier();
        selector.selector =
          "s:" + id2string(selector.selector_symbol);
      }
      else if(index.id() == ID_constant)
        selector.selector =
          "c:" + id2string(index.get(ID_value));
      else
        return false;
    }
    target += "#<region>";
    return true;
  }

  void collect_aliases()
  {
    std::map<irep_idt, std::set<std::string>> candidates;
    std::set<irep_idt> incompatible;
    std::set<irep_idt> noncopy_pointer_assignments;
    std::vector<std::pair<irep_idt, irep_idt>> copies;
    std::vector<std::pair<irep_idt, irep_idt>> selector_copies;
    for(const auto &entry : model.symbol_table.symbols)
    {
      const symbolt &symbol = entry.second;
      if(
        !data_pointer(entry.first) || symbol.value.is_nil())
        continue;
      const exprt &value = strip(symbol.value);
      if(value.id() != ID_address_of)
      {
        incompatible.insert(entry.first);
        continue;
      }
      std::string target;
      if(
        atom(to_address_of_expr(value).object(), target) &&
        shared(target))
      {
        candidates[entry.first].insert(target);
        congruence_aliases.insert(entry.first);
        static_initialized_aliases.insert(entry.first);
      }
      else
        incompatible.insert(entry.first);
    }
    for(const auto &function_entry : model.goto_functions.function_map)
    {
      for(const auto &instruction :
          function_entry.second.body.instructions)
      {
        if(instruction.is_assign())
        {
          irep_idt pointer;
          const exprt &rhs = strip(instruction.assign_rhs());
          if(symbol_id(instruction.assign_lhs(), pointer))
          {
            if(data_pointer(pointer))
            {
              if(rhs.id() == ID_address_of)
              {
                noncopy_pointer_assignments.insert(pointer);
                std::string target;
                if(
                  atom(to_address_of_expr(rhs).object(), target) &&
                  shared(target))
                {
                  candidates[pointer].insert(target);
                  if(
                    function_entry.first ==
                    INITIALIZE_FUNCTION)
                  {
                    congruence_aliases.insert(pointer);
                    static_initialized_aliases.insert(pointer);
                  }
                }
                else
                {
                  noncopy_pointer_assignments.insert(pointer);
                  incompatible.insert(pointer);
                }
              }
              else if(
                function_entry.first == INITIALIZE_FUNCTION &&
                rhs.is_zero())
              {
                // Static null initialization establishes no pointee. A later
                // dominating assignment may establish the unique target.
              }
              else
              {
                irep_idt source;
                if(
                  symbol_id(rhs, source) &&
                  data_pointer(source))
                {
                  copies.push_back({pointer, source});
                  selector_copies.push_back({pointer, source});
                  congruence_aliases.insert(pointer);
                }
                else
                {
                  noncopy_pointer_assignments.insert(pointer);
                  incompatible.insert(pointer);
                }
              }
            }
          }
          continue;
        }
        irep_idt callee;
        if(!call_id(instruction, callee))
          continue;
        const auto region_return =
          region_return_parameters.find(callee);
        if(region_return != region_return_parameters.end())
        {
          irep_idt lhs;
          const auto &arguments = instruction.call_arguments();
          if(
            instruction.call_lhs().is_nil() ||
            !symbol_id(instruction.call_lhs(), lhs) ||
            region_return->second >= arguments.size())
            continue;
          std::string target;
          region_selectort selector;
          if(
            region_argument(
              arguments[region_return->second],
              target, selector))
          {
            candidates[lhs].insert(target);
            region_roots.insert(
              target.substr(
                0, target.size() -
                     std::string("#<region>").size()));
            if(!selector.selector.empty())
              region_selectors[lhs] = std::move(selector);
          }
          else
            incompatible.insert(lhs);
          continue;
        }
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
    bool changed = true;
    while(changed)
    {
      changed = false;
      for(const auto &copy : copies)
      {
        if(incompatible.count(copy.second) != 0)
          changed |= incompatible.insert(copy.first).second;
        auto &destination = candidates[copy.first];
        const std::size_t old_size = destination.size();
        const auto source = candidates.find(copy.second);
        if(source != candidates.end())
          destination.insert(
            source->second.begin(), source->second.end());
        changed |= destination.size() != old_size;
      }
    }
    for(const auto &copy : copies)
    {
      const auto source = candidates.find(copy.second);
      if(
        source == candidates.end() || source->second.empty())
        incompatible.insert(copy.first);
    }
    changed = true;
    while(changed)
    {
      changed = false;
      for(const auto &copy : selector_copies)
      {
        const auto source = region_selectors.find(copy.second);
        if(source == region_selectors.end())
          continue;
        const auto destination = region_selectors.find(copy.first);
        if(destination == region_selectors.end())
        {
          region_selectors[copy.first] = source->second;
          changed = true;
        }
        else if(!(destination->second == source->second))
        {
          incompatible.insert(copy.first);
          region_selectors.erase(copy.first);
        }
      }
    }
    for(const auto &entry : candidates)
    {
      if(
        entry.second.size() == 1 &&
        (incompatible.count(entry.first) == 0 ||
         (
           noncopy_pointer_assignments.count(entry.first) == 0 &&
           entry.second.begin()->size() >=
             std::string("#<region>").size() &&
           entry.second.begin()->compare(
             entry.second.begin()->size() -
               std::string("#<region>").size(),
             std::string("#<region>").size(),
             "#<region>") == 0)))
        aliases[entry.first] = *entry.second.begin();
    }
    for(const auto &entry : aliases)
    {
      if(
        entry.second.size() >=
          std::string("#<region>").size() &&
        entry.second.compare(
          entry.second.size() -
            std::string("#<region>").size(),
          std::string("#<region>").size(),
          "#<region>") == 0)
      {
        congruence_aliases.erase(entry.first);
        for(const auto &field : region_zero_fields)
          initial[
            entry.second + "#" + id2string(field)] =
              intervalt::singleton(0);
      }
    }
    for(auto iterator = congruence_aliases.begin();
        iterator != congruence_aliases.end();)
    {
      if(aliases.count(*iterator) == 0)
        iterator = congruence_aliases.erase(iterator);
      else
        ++iterator;
    }
  }

  bool resolve_context_argument(
    const exprt &src,
    std::string &target) const
  {
    const exprt &argument = strip(src);
    if(argument.id() == ID_address_of)
      return
        atom(to_address_of_expr(argument).object(), target) &&
        shared(target);
    irep_idt identifier;
    if(!symbol_id(argument, identifier))
      return false;
    if(active_aliases != nullptr)
    {
      const auto contextual = active_aliases->find(identifier);
      if(contextual != active_aliases->end())
      {
        target = contextual->second;
        return shared(target);
      }
    }
    const auto alias = aliases.find(identifier);
    if(alias == aliases.end())
      return false;
    target = alias->second;
    return shared(target);
  }

  bool collect_function_contexts()
  {
    for(const auto &caller_entry : model.goto_functions.function_map)
    {
      if(!user_function(caller_entry.first))
        continue;
      for(const auto &instruction :
          caller_entry.second.body.instructions)
      {
        irep_idt callee;
        if(!call_id(instruction, callee) || !user_function(callee))
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
        {
          reason = "context_arity";
          return false;
        }
        alias_contextt context;
        for(std::size_t index = 0; index < parameters.size(); ++index)
        {
          const typet &parameter_type =
            ns.follow(parameters[index].type());
          if(parameter_type.id() != ID_pointer)
            continue;
          if(
            ns.follow(
              to_pointer_type(parameter_type).base_type()).id() ==
            ID_code)
            continue;
          const irep_idt parameter =
            parameters[index].get_identifier();
          std::string target;
          if(
            parameter.empty() ||
            !resolve_context_argument(arguments[index], target))
          {
            reason = "context_argument";
            return false;
          }
          context[parameter] = target;
        }
        if(context.empty())
          continue;
        auto &contexts = function_contexts[callee];
        if(
          std::find(contexts.begin(), contexts.end(), context) ==
          contexts.end())
          contexts.push_back(std::move(context));
      }
    }
    return true;
  }

  std::vector<alias_contextt> contexts_for(
    const irep_idt &function) const
  {
    const auto found = function_contexts.find(function);
    if(found != function_contexts.end() && !found->second.empty())
      return found->second;
    return {alias_contextt{}};
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
    if(resolved_type.id() == ID_array)
    {
      if(value.operands().empty())
        return;
      const exprt &representative = value.operands().front();
      if(value.id() == ID_array)
      {
        for(const auto &element : value.operands())
        {
          if(element != representative)
            return;
        }
      }
      else if(value.id() != ID_array_of)
        return;
      collect_initial_expr(
        base + "#[]",
        to_array_type(resolved_type).element_type(),
        representative);
      return;
    }
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
      region_summary_functions.count(identifier) != 0 ||
      (!region_return_parameters.empty() &&
       is_allocator(identifier)) ||
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

bool validate_region_publication(analysist &analysis)
{
  if(analysis.region_return_parameters.empty())
    return true;

  for(auto &function_entry :
      analysis.model.goto_functions.function_map)
  {
    if(
      analysis.region_summary_functions.count(
        function_entry.first) != 0)
      continue;
    auto &program = function_entry.second.body;
    std::vector<goto_programt::targett> order;
    std::map<const goto_programt::instructiont *, std::size_t>
      positions;
    for(auto iterator = program.instructions.begin();
        iterator != program.instructions.end(); ++iterator)
    {
      positions[&*iterator] = order.size();
      order.push_back(iterator);
    }
    if(order.empty())
      continue;
    std::vector<bool> reached(order.size(), false);
    std::vector<std::set<irep_idt>> states(order.size());
    std::deque<std::size_t> work;
    reached[0] = true;
    work.push_back(0);
    while(!work.empty())
    {
      const std::size_t index = work.front();
      work.pop_front();
      std::set<irep_idt> after = states[index];
      const auto &instruction = *order[index];
      if(instruction.is_assign())
      {
        irep_idt member_pointer;
        irep_idt member_field;
        if(
          analysis.pointer_member_of(
            instruction.assign_lhs(),
            member_pointer, member_field) &&
          analysis.region_zero_fields.count(member_field) != 0)
          after.erase(member_pointer);
        irep_idt lhs;
        if(
          symbol_id(instruction.assign_lhs(), lhs) &&
          analysis.data_pointer(lhs))
        {
          irep_idt rhs;
          if(
            symbol_id(instruction.assign_rhs(), rhs) &&
            after.count(rhs) != 0)
            after.insert(lhs);
          else
            after.erase(lhs);
        }
      }
      irep_idt callee;
      if(call_id(instruction, callee))
      {
        if(named(callee, "free") || named(callee, "realloc"))
        {
          analysis.reason = "region_deallocation";
          return false;
        }
        if(
          analysis.region_initializers.count(callee) != 0)
        {
          if(instruction.call_arguments().size() != 1)
          {
            analysis.reason = "region_initializer_arity";
            return false;
          }
          irep_idt initialized;
          if(
            symbol_id(
              instruction.call_arguments().front(),
              initialized))
            after.insert(initialized);
          else
          {
            analysis.reason = "region_initializer_argument";
            return false;
          }
        }
        const auto inserter =
          analysis.region_insert_node_parameters.find(callee);
        if(inserter !=
           analysis.region_insert_node_parameters.end())
        {
          if(
            inserter->second >=
              instruction.call_arguments().size())
          {
            analysis.reason = "region_inserter_arity";
            return false;
          }
          irep_idt node;
          if(
            !symbol_id(
              instruction.call_arguments()[inserter->second],
              node) ||
            after.count(node) == 0)
          {
            analysis.reason =
              "region_publish_before_initialization";
            return false;
          }
        }
      }

      std::vector<std::size_t> successors;
      if(instruction.is_goto())
      {
        for(const auto &target : instruction.targets)
          successors.push_back(positions.at(&*target));
        if(
          !instruction.condition().is_true() &&
          index + 1 < order.size())
          successors.push_back(index + 1);
      }
      else if(
        !instruction.is_end_function() &&
        index + 1 < order.size())
        successors.push_back(index + 1);
      for(const auto successor : successors)
      {
        if(!reached[successor])
        {
          reached[successor] = true;
          states[successor] = after;
          work.push_back(successor);
        }
        else
        {
          std::set<irep_idt> intersection;
          std::set_intersection(
            states[successor].begin(),
            states[successor].end(),
            after.begin(), after.end(),
            std::inserter(
              intersection, intersection.begin()));
          if(intersection != states[successor])
          {
            states[successor] = std::move(intersection);
            work.push_back(successor);
          }
        }
      }
    }
  }

  const auto main_function =
    analysis.model.goto_functions.function_map.find(ID_main);
  if(main_function ==
     analysis.model.goto_functions.function_map.end())
  {
    analysis.reason = "region_main_missing";
    return false;
  }
  std::set<irep_idt> initialized_pointers;
  std::set<std::string> initialized_roots;
  for(const auto &instruction :
      main_function->second.body.instructions)
  {
    if(instruction.is_assign())
    {
      irep_idt member_pointer;
      irep_idt member_field;
      if(
        analysis.pointer_member_of(
          instruction.assign_lhs(),
          member_pointer, member_field) &&
        analysis.region_zero_fields.count(member_field) != 0)
      {
        initialized_pointers.erase(member_pointer);
        initialized_roots.erase(
          id2string(member_pointer));
      }
      irep_idt lhs;
      if(
        symbol_id(instruction.assign_lhs(), lhs) &&
        analysis.data_pointer(lhs))
      {
        irep_idt rhs;
        if(
          symbol_id(instruction.assign_rhs(), rhs) &&
          initialized_pointers.count(rhs) != 0)
          initialized_pointers.insert(lhs);
        else
          initialized_pointers.erase(lhs);
      }
      std::string root;
      if(
        analysis.atom(instruction.assign_lhs(), root) &&
        analysis.region_roots.count(root) != 0)
      {
        irep_idt source;
        if(
          symbol_id(instruction.assign_rhs(), source) &&
          initialized_pointers.count(source) != 0)
          initialized_roots.insert(root);
        else
          initialized_roots.erase(root);
      }
    }
    irep_idt callee;
    if(!call_id(instruction, callee))
      continue;
    if(analysis.region_initializers.count(callee) != 0)
    {
      if(instruction.call_arguments().size() != 1)
      {
        analysis.reason = "region_initializer_arity";
        return false;
      }
      const exprt &argument =
        instruction.call_arguments().front();
      irep_idt initialized;
      if(symbol_id(argument, initialized))
        initialized_pointers.insert(initialized);
      std::string root;
      if(
        analysis.atom(argument, root) &&
        analysis.region_roots.count(root) != 0)
        initialized_roots.insert(root);
    }
    if(is_create(callee))
    {
      for(const auto &root : analysis.region_roots)
      {
        if(initialized_roots.count(root) == 0)
        {
          analysis.reason =
            "region_root_not_initialized";
          return false;
        }
      }
      break;
    }
  }
  return true;
}

bool zero_test_when_true(
  const exprt &src,
  const irep_idt &symbol,
  bool &zero_when_true)
{
  const exprt &expr = strip(src);
  if(expr.id() == ID_not && expr.operands().size() == 1)
  {
    if(!zero_test_when_true(expr.op0(), symbol, zero_when_true))
      return false;
    zero_when_true = !zero_when_true;
    return true;
  }
  if(
    (expr.id() != ID_equal && expr.id() != ID_notequal) ||
    expr.operands().size() != 2)
    return false;
  irep_idt compared;
  long long constant;
  if(
    !(
      symbol_id(expr.op0(), compared) &&
      integer_constant(expr.op1(), constant)) &&
    !(
      symbol_id(expr.op1(), compared) &&
      integer_constant(expr.op0(), constant)))
    return false;
  if(compared != symbol || constant != 0)
    return false;
  zero_when_true = expr.id() == ID_equal;
  return true;
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
  irep_idt pointer;
  if(
    symbol_id(strip(expr), pointer) &&
    analysis.aliases.count(pointer) != 0)
  {
    // Reading an immutable pointer value does not read its pointee.  Uses
    // which dereference it are resolved by atom().
    return;
  }
  std::string key;
  if(analysis.atom(expr, key))
  {
    if(
      analysis.region_roots.count(key) != 0 &&
      analysis.ns.follow(expr.type()).id() == ID_pointer)
      return;
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
  irep_idt pointer;
  if(
    symbol_id(expr, pointer) &&
    (analysis.aliases.count(pointer) != 0 ||
     (analysis.active_aliases != nullptr &&
      analysis.active_aliases->count(pointer) != 0)))
    return true;
  if(expr.id() == ID_dereference)
  {
    std::string resolved;
    if(!analysis.atom(expr, resolved))
    {
      irep_idt unresolved_pointer;
      analysis.reason =
        symbol_id(
          to_dereference_expr(expr).pointer(),
          unresolved_pointer)
          ? "unresolved_dereference_" +
              id2string(unresolved_pointer)
          : "unresolved_dereference_expression";
      return false;
    }
  }
  std::string key;
  if(analysis.atom(expr, key) && analysis.shared(key))
  {
    const typet &type = analysis.ns.follow(expr.type());
    if(
      type.id() == ID_pointer &&
      analysis.region_roots.count(key) != 0)
      return true;
    if(
      !analysis.region_return_parameters.empty() &&
      key == "__CPROVER_max_malloc_size")
      return true;
    if(
      type.id() != ID_signedbv ||
      type.get_bool(ID_C_volatile))
    {
      analysis.reason =
        "shared_scalar_type_" + key + "_" +
        id2string(type.id());
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

void collect_escaped_congruence_aliases(
  const analysist &analysis,
  const exprt &src,
  std::set<irep_idt> &escaped)
{
  const exprt &expr = strip(src);
  if(expr.id() == ID_address_of)
  {
    irep_idt identifier;
    if(
      symbol_id(to_address_of_expr(expr).object(), identifier) &&
      analysis.congruence_aliases.count(identifier) != 0)
      escaped.insert(identifier);
  }
  for(const auto &operand : expr.operands())
    collect_escaped_congruence_aliases(
      analysis, operand, escaped);
}

bool validate_congruence_alias_escapes(analysist &analysis)
{
  std::set<irep_idt> escaped;
  for(const auto &function_entry :
      analysis.model.goto_functions.function_map)
  {
    if(!analysis.user_function(function_entry.first))
      continue;
    for(const auto &instruction :
        function_entry.second.body.instructions)
    {
      instruction.apply(
        [&analysis, &escaped](const exprt &expr) {
          collect_escaped_congruence_aliases(
            analysis, expr, escaped);
        });
    }
  }
  if(escaped.empty())
    return true;
  analysis.reason = "pointer_alias_escape";
  return false;
}

bool initialized_alias_uses(
  analysist &analysis,
  const exprt &src,
  const std::set<irep_idt> &initialized)
{
  const exprt &expr = strip(src);
  if(expr.id() == ID_dereference)
  {
    irep_idt pointer;
    if(
      symbol_id(to_dereference_expr(expr).pointer(), pointer) &&
      analysis.congruence_aliases.count(pointer) != 0 &&
      initialized.count(pointer) == 0)
    {
      analysis.reason = "pointer_not_initialized";
      return false;
    }
  }
  for(const auto &operand : expr.operands())
  {
    if(!initialized_alias_uses(
         analysis, operand, initialized))
      return false;
  }
  return true;
}

bool audit_alias_initialization_in_function(
  analysist &analysis,
  const irep_idt &function_id,
  const std::set<irep_idt> &entry,
  bool collect_publication,
  std::set<irep_idt> &published,
  bool &publication_seen)
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
  std::vector<bool> reached(order.size(), false);
  std::vector<std::set<irep_idt>> states(order.size());
  std::deque<std::size_t> work;
  reached[0] = true;
  states[0] = entry;
  work.push_back(0);
  while(!work.empty())
  {
    const std::size_t index = work.front();
    work.pop_front();
    std::set<irep_idt> after = states[index];
    const auto &instruction = *order[index];
    bool valid_uses = true;
    instruction.apply(
      [&analysis, &after, &valid_uses](const exprt &expr) {
        if(
          valid_uses &&
          !initialized_alias_uses(
            analysis, expr, after))
          valid_uses = false;
      });
    if(!valid_uses)
      return false;

    if(instruction.is_assign())
    {
      irep_idt lhs;
      if(
        symbol_id(instruction.assign_lhs(), lhs) &&
        analysis.aliases.count(lhs) != 0)
      {
        bool established = false;
        const exprt &rhs = strip(instruction.assign_rhs());
        if(rhs.id() == ID_address_of)
        {
          std::string target;
          established =
            analysis.atom(
              to_address_of_expr(rhs).object(), target) &&
            target == analysis.aliases.at(lhs);
        }
        else
        {
          irep_idt source;
          established =
            symbol_id(rhs, source) &&
            analysis.aliases.count(source) != 0 &&
            analysis.aliases.at(source) ==
              analysis.aliases.at(lhs) &&
            after.count(source) != 0;
        }
        if(established)
          after.insert(lhs);
        else
          after.erase(lhs);
      }
    }

    irep_idt callee;
    if(
      collect_publication &&
      call_id(instruction, callee) &&
      is_create(callee))
    {
      if(!publication_seen)
      {
        published = after;
        publication_seen = true;
      }
      else
      {
        std::set<irep_idt> intersection;
        std::set_intersection(
          published.begin(), published.end(),
          after.begin(), after.end(),
          std::inserter(
            intersection, intersection.begin()));
        published = std::move(intersection);
      }
    }

    std::vector<std::size_t> successors;
    if(instruction.is_goto())
    {
      for(const auto &target : instruction.targets)
        successors.push_back(positions.at(&*target));
      if(
        !instruction.condition().is_true() &&
        index + 1 < order.size())
        successors.push_back(index + 1);
    }
    else if(
      !instruction.is_end_function() &&
      index + 1 < order.size())
      successors.push_back(index + 1);
    for(const std::size_t successor : successors)
    {
      if(!reached[successor])
      {
        reached[successor] = true;
        states[successor] = after;
        work.push_back(successor);
      }
      else
      {
        std::set<irep_idt> intersection;
        std::set_intersection(
          states[successor].begin(),
          states[successor].end(),
          after.begin(), after.end(),
          std::inserter(
            intersection, intersection.begin()));
        if(intersection != states[successor])
        {
          states[successor] = std::move(intersection);
          work.push_back(successor);
        }
      }
    }
  }
  return true;
}

bool validate_congruence_alias_initialization(
  analysist &analysis)
{
  std::set<irep_idt> published;
  bool publication_seen = false;
  const auto main_function =
    analysis.model.goto_functions.function_map.find(ID_main);
  if(
    main_function !=
      analysis.model.goto_functions.function_map.end() &&
    !audit_alias_initialization_in_function(
      analysis, ID_main,
      analysis.static_initialized_aliases, true,
      published, publication_seen))
    return false;
  if(!publication_seen)
    published = analysis.static_initialized_aliases;

  for(const auto &entry :
      analysis.model.goto_functions.function_map)
  {
    if(
      entry.first == ID_main ||
      !analysis.user_function(entry.first))
      continue;
    std::set<irep_idt> initial =
      analysis.static_initialized_aliases;
    if(
      analysis.pre_spawn_functions.count(entry.first) == 0)
      initial.insert(published.begin(), published.end());
    std::set<irep_idt> ignored_publication;
    bool ignored_seen = false;
    if(!audit_alias_initialization_in_function(
         analysis, entry.first, initial, false,
         ignored_publication, ignored_seen))
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

struct indexed_origint
{
  std::string base;
  std::string selector;
  irep_idt selector_symbol;
};

bool indexed_origin(
  const analysist &analysis,
  const exprt &src,
  indexed_origint &origin)
{
  const exprt &expr = strip(src);
  if(expr.id() == ID_member)
    return indexed_origin(
      analysis, to_member_expr(expr).compound(), origin);
  if(expr.id() != ID_index || expr.operands().size() != 2)
    return false;
  if(!analysis.atom(expr.op0(), origin.base) ||
     !analysis.shared(origin.base))
    return false;
  const exprt &selector = strip(expr.op1());
  if(selector.id() == ID_symbol)
  {
    origin.selector_symbol =
      to_symbol_expr(selector).get_identifier();
    origin.selector =
      "s:" + id2string(origin.selector_symbol);
    return true;
  }
  if(selector.id() == ID_constant)
  {
    origin.selector =
      "c:" + id2string(selector.get(ID_value));
    origin.selector_symbol.clear();
    return true;
  }
  return false;
}

void collect_indexed_origins(
  const analysist &analysis,
  const exprt &expr,
  std::vector<indexed_origint> &origins)
{
  indexed_origint origin;
  if(indexed_origin(analysis, expr, origin))
  {
    origins.push_back(std::move(origin));
    return;
  }
  if(strip(expr).id() == ID_address_of)
    return;
  for(const auto &operand : expr.operands())
    collect_indexed_origins(analysis, operand, origins);
}

void collect_region_pointer_uses(
  const analysist &analysis,
  const exprt &src,
  std::set<irep_idt> &pointers)
{
  const exprt &expr = strip(src);
  if(expr.id() == ID_dereference)
  {
    irep_idt pointer;
    if(
      symbol_id(
        to_dereference_expr(expr).pointer(), pointer) &&
      analysis.region_selectors.count(pointer) != 0)
      pointers.insert(pointer);
  }
  for(const auto &operand : expr.operands())
    collect_region_pointer_uses(analysis, operand, pointers);
}

bool validate_index_relations(
  analysist &analysis,
  const goto_programt &program)
{
  std::vector<indexed_origint> held_indexed_locks;
  std::map<irep_idt, indexed_origint> captured;
  std::set<std::pair<std::string, irep_idt>> drifted;
  std::set<irep_idt> drifted_region_pointers;
  std::set<irep_idt> active_region_pointers;

  for(const auto &instruction : program.instructions)
  {
    irep_idt callee;
    if(call_id(instruction, callee) && is_trylock(callee))
    {
      indexed_origint origin;
      if(
        !instruction.call_arguments().empty() &&
        strip(instruction.call_arguments().front()).id() ==
          ID_address_of &&
        indexed_origin(
          analysis,
          to_address_of_expr(
            strip(instruction.call_arguments().front())).object(),
          origin) &&
        !origin.selector.empty())
      {
        analysis.reason = "conditional_indexed_lock";
        return false;
      }
      continue;
    }
    if(call_id(instruction, callee) &&
       (is_lock(callee) || is_unlock(callee)))
    {
      if(is_lock(callee))
      {
        indexed_origint origin;
        if(
          !instruction.call_arguments().empty() &&
          strip(instruction.call_arguments().front()).id() ==
            ID_address_of &&
          indexed_origin(
            analysis,
            to_address_of_expr(
              strip(instruction.call_arguments().front())).object(),
            origin))
          held_indexed_locks.push_back(std::move(origin));
        else
          held_indexed_locks.push_back(indexed_origint{});
      }
      else if(!held_indexed_locks.empty())
        held_indexed_locks.pop_back();
      continue;
    }

    if(instruction.is_assign())
    {
      irep_idt lhs;
      if(symbol_id(instruction.assign_lhs(), lhs))
      {
        for(const auto &entry : analysis.region_selectors)
        {
          if(
            active_region_pointers.count(entry.first) != 0 &&
            !entry.second.selector_symbol.empty() &&
            lhs == entry.second.selector_symbol)
            drifted_region_pointers.insert(entry.first);
        }
        for(const auto &entry : captured)
        {
          if(
            !entry.second.selector_symbol.empty() &&
            lhs == entry.second.selector_symbol)
            drifted.insert(
              {entry.second.base,
               entry.second.selector_symbol});
        }
        const exprt &rhs = strip(instruction.assign_rhs());
        if(rhs.id() == ID_address_of)
        {
          indexed_origint origin;
          if(
            indexed_origin(
              analysis,
              to_address_of_expr(rhs).object(),
              origin))
            captured[lhs] = std::move(origin);
        }
        if(analysis.region_selectors.count(lhs) != 0)
          active_region_pointers.insert(lhs);
      }
    }
    if(
      instruction.is_function_call() &&
      !instruction.call_lhs().is_nil())
    {
      irep_idt lhs;
      if(
        symbol_id(instruction.call_lhs(), lhs) &&
        analysis.region_selectors.count(lhs) != 0)
        active_region_pointers.insert(lhs);
    }

    std::vector<indexed_origint> accesses;
    if(instruction.is_assign())
    {
      collect_indexed_origins(
        analysis, instruction.assign_lhs(), accesses);
      collect_indexed_origins(
        analysis, instruction.assign_rhs(), accesses);
    }
    else if(
      instruction.is_goto() || instruction.is_assume() ||
      instruction.is_assert())
      collect_indexed_origins(
        analysis, instruction.condition(), accesses);
    else if(
      call_id(instruction, callee) && is_property(callee))
    {
      for(const auto &argument : instruction.call_arguments())
        collect_indexed_origins(analysis, argument, accesses);
    }

    for(const auto &access : accesses)
    {
      if(
        !access.selector_symbol.empty() &&
        drifted.count(
          {access.base, access.selector_symbol}) != 0)
      {
        analysis.reason = "indexed_pointer_drift";
        return false;
      }
      for(const auto &lock : held_indexed_locks)
      {
        if(
          !lock.base.empty() && lock.base == access.base &&
          lock.selector != access.selector)
        {
          analysis.reason = "indexed_lock_mismatch";
          return false;
        }
      }
    }

    std::set<irep_idt> region_uses;
    if(instruction.is_assign())
    {
      collect_region_pointer_uses(
        analysis, instruction.assign_lhs(), region_uses);
      collect_region_pointer_uses(
        analysis, instruction.assign_rhs(), region_uses);
    }
    else if(
      instruction.is_goto() || instruction.is_assume() ||
      instruction.is_assert())
      collect_region_pointer_uses(
        analysis, instruction.condition(), region_uses);
    else if(
      call_id(instruction, callee) && is_property(callee))
    {
      for(const auto &argument : instruction.call_arguments())
        collect_region_pointer_uses(
          analysis, argument, region_uses);
    }
    for(const auto &pointer : region_uses)
    {
      const auto region = analysis.region_selectors.find(pointer);
      if(
        region == analysis.region_selectors.end() ||
        drifted_region_pointers.count(pointer) != 0)
      {
        analysis.reason = "region_selector_drift";
        return false;
      }
      bool matched = false;
      for(const auto &lock : held_indexed_locks)
      {
        if(
          !lock.selector.empty() &&
          lock.selector == region->second.selector)
        {
          matched = true;
          break;
        }
      }
      if(!matched)
      {
        analysis.reason = "region_lock_selector_mismatch";
        return false;
      }
    }
  }
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
    if(
      !validate_index_relations(
        analysis, function_entry.second.body))
      return false;
    const auto contexts =
      analysis.contexts_for(function_entry.first);
    for(const auto &context : contexts)
    {
      analysis.active_aliases = &context;
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
              irep_idt pointer;
              if(
                !symbol_id(
                  instruction.assign_lhs(), pointer) ||
                analysis.aliases.count(pointer) == 0 ||
                analysis.aliases.at(pointer) != addressed)
              {
                analysis.reason = "scalar_address_taken";
                return false;
              }
            }
          }
          if(
            !validate_expression(
              analysis, instruction.assign_lhs()) ||
            !validate_expression(
              analysis, instruction.assign_rhs()))
            return false;
        }
        else if(
          instruction.is_goto() || instruction.is_assume() ||
          instruction.is_assert())
        {
          if(
            !validate_expression(
              analysis, instruction.condition()))
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
        if(is_error(callee))
        {
          analysis.reason = "unproved_error_call";
          return false;
        }
        if(
          analysis.region_summary_functions.count(callee) != 0)
          continue;
        if(
          !analysis.region_return_parameters.empty() &&
          is_allocator(callee))
          continue;
        for(const auto &argument :
            instruction.call_arguments())
        {
          if(!validate_expression(analysis, argument))
            return false;
        }
        if(
          is_lock(callee) || is_unlock(callee) ||
          is_trylock(callee) ||
          is_mutex_init(callee) || is_create(callee) ||
          is_join(callee) || is_property(callee) ||
          named(callee, "sleep") || named(callee, "abort") ||
          named(callee, "__CPROVER_assume"))
          continue;
        const auto target =
          analysis.model.goto_functions.function_map.find(callee);
        if(
          target ==
            analysis.model.goto_functions.function_map.end() ||
          !target->second.body_available() ||
          !analysis.user_function(callee))
        {
          analysis.reason =
            "unsupported_call_" + id2string(callee);
          return false;
        }
        call_edges[function_entry.first].insert(callee);
      }
    }
  }
  analysis.active_aliases = nullptr;
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
  struct flow_statet
  {
    std::vector<std::string> stack;
    std::map<irep_idt, std::string> pending;

    bool operator==(const flow_statet &other) const
    {
      return stack == other.stack && pending == other.pending;
    }
  };
  std::vector<bool> reached(order.size(), false);
  std::vector<flow_statet> states(order.size());
  at.resize(order.size());
  std::deque<std::size_t> work;
  reached[0] = true;
  work.push_back(0);
  while(!work.empty())
  {
    const std::size_t index = work.front();
    work.pop_front();
    const flow_statet before = states[index];
    at[index] = before.stack;
    flow_statet after = before;
    irep_idt callee;
    if(call_id(*order[index], callee))
    {
      std::string lock;
      if(is_lock(callee))
      {
        if(!after.pending.empty())
        {
          analysis.reason = "conditional_lock_unconsumed";
          return false;
        }
        if(!analysis.lock_argument(*order[index], lock))
        {
          analysis.reason = "lock_argument";
          return false;
        }
        if(
          std::find(
            after.stack.begin(), after.stack.end(), lock) !=
          after.stack.end())
        {
          analysis.reason = "recursive_lock";
          return false;
        }
        if(!after.stack.empty())
          analysis.lock_edges.insert({after.stack.back(), lock});
        after.stack.push_back(lock);
        analysis.locks.insert(lock);
      }
      else if(is_trylock(callee))
      {
        irep_idt result;
        if(
          !after.pending.empty() ||
          order[index]->call_lhs().is_nil() ||
          !symbol_id(order[index]->call_lhs(), result) ||
          !analysis.lock_argument(*order[index], lock) ||
          std::find(
            after.stack.begin(), after.stack.end(), lock) !=
            after.stack.end())
        {
          analysis.reason = "conditional_lock_call";
          return false;
        }
        after.pending[result] = lock;
        analysis.locks.insert(lock);
      }
      else if(is_unlock(callee))
      {
        if(
          !analysis.lock_argument(*order[index], lock) ||
          !after.pending.empty() || after.stack.empty() ||
          after.stack.back() != lock)
        {
          analysis.reason = "lock_balance";
          return false;
        }
        after.stack.pop_back();
      }
    }
    else if(
      !after.pending.empty() && !order[index]->is_goto())
    {
      analysis.reason = "conditional_lock_unconsumed";
      return false;
    }
    std::vector<std::pair<std::size_t, flow_statet>> successors;
    if(order[index]->is_goto())
    {
      bool conditional_lock = !after.pending.empty();
      bool zero_on_target = false;
      std::string conditional_mutex;
      if(conditional_lock)
      {
        if(
          after.pending.size() != 1 ||
          !zero_test_when_true(
            order[index]->condition(),
            after.pending.begin()->first,
            zero_on_target))
        {
          analysis.reason = "conditional_lock_branch";
          return false;
        }
        conditional_mutex = after.pending.begin()->second;
      }
      for(const auto &target : order[index]->targets)
      {
        flow_statet branch = after;
        branch.pending.clear();
        if(conditional_lock && zero_on_target)
        {
          if(!branch.stack.empty())
            analysis.lock_edges.insert(
              {branch.stack.back(), conditional_mutex});
          branch.stack.push_back(conditional_mutex);
        }
        successors.push_back(
          {positions.at(&*target), std::move(branch)});
      }
      if(
        !order[index]->condition().is_true() &&
        index + 1 < order.size())
      {
        flow_statet branch = after;
        branch.pending.clear();
        if(conditional_lock && !zero_on_target)
        {
          if(!branch.stack.empty())
            analysis.lock_edges.insert(
              {branch.stack.back(), conditional_mutex});
          branch.stack.push_back(conditional_mutex);
        }
        successors.push_back({index + 1, std::move(branch)});
      }
    }
    else if(
      !order[index]->is_end_function() &&
      index + 1 < order.size())
      successors.push_back({index + 1, after});
    else if(
      order[index]->is_end_function() &&
      (!after.stack.empty() || !after.pending.empty()))
    {
      analysis.reason = "lock_balance";
      return false;
    }
    for(auto &successor : successors)
    {
      if(!reached[successor.first])
      {
        reached[successor.first] = true;
        states[successor.first] = std::move(successor.second);
        work.push_back(successor.first);
      }
      else if(!(states[successor.first] == successor.second))
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
    const auto contexts = analysis.contexts_for(entry.first);
    for(const auto &context : contexts)
    {
      analysis.active_aliases = &context;
      std::vector<std::vector<std::string>> locksets;
      std::vector<goto_programt::targett> order;
      if(
        !compute_locksets(
          analysis, entry.first, locksets, order))
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
           is_trylock(callee) ||
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
            integer_constant(
              instruction.assign_rhs(), assigned))
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
          collect_expr_atoms(
            analysis, instruction.assign_lhs(), atoms);
          collect_expr_atoms(
            analysis, instruction.assign_rhs(), atoms);
        }
        else if(
          instruction.is_goto() || instruction.is_assume())
          collect_expr_atoms(
            analysis, instruction.condition(), atoms);
        else if(instruction.is_function_call())
        {
          const auto direct =
            call_id(instruction, callee)
              ? analysis.model.goto_functions.function_map.find(
                  callee)
              : analysis.model.goto_functions.function_map.end();
          // Direct user calls are analyzed in each instantiated callee
          // context; passing an address is not itself a shared read.
          if(
            direct !=
              analysis.model.goto_functions.function_map.end() &&
            direct->second.body_available() &&
            !ignored_external(callee))
            continue;
          for(const auto &argument :
              instruction.call_arguments())
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
              std::inserter(
                intersection, intersection.begin()));
            found->second = intersection;
          }
        }
      }
    }
  }
  analysis.active_aliases = nullptr;
  for(const auto &entry : candidates)
  {
    if(entry.second.empty())
    {
      analysis.reason = "protection_set";
      return false;
    }
    // Every member of the intersection is a must-held protecting lock.
    // Prefer an outermost candidate so that a relational invariant spans the
    // complete nested-lock transaction.  Publishing at an inner lock can
    // forget relations that are temporarily broken and restored before the
    // outer unlock.  Requiring the intersection to be a singleton needlessly
    // rejects consistently nested locking.
    auto selected = entry.second.begin();
    for(auto candidate = entry.second.begin();
        candidate != entry.second.end(); ++candidate)
    {
      bool enclosed_by_other_candidate = false;
      for(const auto &edge : analysis.lock_edges)
      {
        if(
          edge.second == *candidate &&
          entry.second.count(edge.first) != 0)
        {
          enclosed_by_other_candidate = true;
          break;
        }
      }
      if(!enclosed_by_other_candidate)
      {
        selected = candidate;
        break;
      }
    }
    analysis.protection[entry.first] = *selected;
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

bool validate_region_lock_congruence(analysist &analysis)
{
  if(analysis.region_return_parameters.empty())
    return true;

  std::set<std::string> indexed_roots;
  for(const auto &entry : analysis.region_selectors)
  {
    if(!entry.second.container.empty())
      indexed_roots.insert(
        entry.second.container + "#[]");
  }

  std::set<std::string> scalar_roots;
  std::set<std::string> scalar_locks;
  for(const auto &root : analysis.region_roots)
  {
    if(indexed_roots.count(root) != 0)
      continue;
    scalar_roots.insert(root);
    std::set<std::string> root_locks;
    for(const auto &field : analysis.region_zero_fields)
    {
      const auto protected_field =
        analysis.protection.find(
          root + "#<region>#" + id2string(field));
      if(protected_field != analysis.protection.end())
        root_locks.insert(protected_field->second);
    }
    if(root_locks.size() != 1)
    {
      analysis.reason =
        "scalar_region_lock_not_functional";
      return false;
    }
    scalar_locks.insert(*root_locks.begin());
  }

  if(scalar_roots.empty())
    return true;
  if(scalar_roots.size() < 2)
  {
    analysis.reason = "scalar_region_lock_unidentifiable";
    return false;
  }
  if(scalar_locks.size() != scalar_roots.size())
  {
    analysis.reason = "scalar_region_lock_not_injective";
    return false;
  }
  return true;
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
  std::map<irep_idt, std::string> pending;

  bool operator<(const node_keyt &other) const
  {
    if(index != other.index)
      return index < other.index;
    if(stack != other.stack)
      return stack < other.stack;
    return pending < other.pending;
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
  const node_keyt start{0, {}, {}};
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
    std::map<irep_idt, std::string> after_pending = key.pending;
    auto acquire = [&analysis](
      statet &target_state,
      std::vector<std::string> &target_stack,
      const std::string &lock) {
      target_stack.push_back(lock);
      const statet &invariant = analysis.lock_invariants[lock];
      for(const auto &protected_entry : analysis.protection)
      {
        if(protected_entry.second != lock)
          continue;
        intervalt current =
          target_state.get(protected_entry.first);
        const intervalt imported =
          invariant.get(protected_entry.first);
        if(!meet_interval(current, imported))
        {
          target_state.bottom = true;
          return;
        }
        target_state.set(protected_entry.first, current);
      }
    };
    irep_idt callee;
    if(instruction.is_assign())
    {
      std::string lhs;
      intervalt value;
      irep_idt pointer;
      const exprt &rhs = strip(instruction.assign_rhs());
      bool immutable_pointer_assignment = false;
      if(
        symbol_id(instruction.assign_lhs(), pointer) &&
        analysis.aliases.count(pointer) != 0 &&
        rhs.id() == ID_address_of)
      {
        std::string target;
        immutable_pointer_assignment =
          analysis.atom(
            to_address_of_expr(rhs).object(), target) &&
          target == analysis.aliases.at(pointer);
      }
      if(immutable_pointer_assignment)
      {
        // The pointer binding was checked by pointer congruence. It carries
        // no numeric state in this abstract domain.
      }
      else if(!analysis.atom(instruction.assign_lhs(), lhs))
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
        if(
          !after_pending.empty() ||
          !analysis.lock_argument(instruction, lock))
          return false;
        acquire(state, after_stack, lock);
      }
      else if(is_trylock(callee))
      {
        irep_idt result;
        if(
          !after_pending.empty() ||
          instruction.call_lhs().is_nil() ||
          !symbol_id(instruction.call_lhs(), result) ||
          !analysis.lock_argument(instruction, lock) ||
          std::find(
            after_stack.begin(), after_stack.end(), lock) !=
            after_stack.end())
        {
          analysis.reason = "conditional_lock_call";
          return false;
        }
        after_pending[result] = lock;
      }
      else if(is_unlock(callee))
      {
        if(
          !analysis.lock_argument(instruction, lock) ||
          !after_pending.empty() ||
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
      else if(is_error(callee))
      {
        analysis.reason = "unproved_error_call";
        return false;
      }
      else if(named(callee, "abort"))
      {
        // abort() terminates this path and therefore has the same abstract
        // effect as assume(false).  Treating it as a verification failure
        // rejects ordinary SV-COMP assume helpers, including unreachable
        // helpers shipped in benchmark headers.
        state.bottom = true;
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
    else if(
      !after_pending.empty() && !instruction.is_goto())
    {
      analysis.reason = "conditional_lock_unconsumed";
      return false;
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

    struct successort
    {
      std::size_t index;
      statet state;
      std::vector<std::string> stack;
      std::map<irep_idt, std::string> pending;
    };
    std::vector<successort> successors;
    if(instruction.is_goto())
    {
      bool conditional_lock = !after_pending.empty();
      bool zero_on_target = false;
      std::string conditional_mutex;
      if(conditional_lock)
      {
        if(
          after_pending.size() != 1 ||
          !zero_test_when_true(
            instruction.condition(),
            after_pending.begin()->first,
            zero_on_target))
        {
          analysis.reason = "conditional_lock_branch";
          return false;
        }
        conditional_mutex = after_pending.begin()->second;
      }
      for(const auto &target : instruction.targets)
      {
        statet branch = state;
        std::vector<std::string> branch_stack = after_stack;
        assume_condition(
          analysis, branch, instruction.condition(), true);
        if(
          conditional_lock && zero_on_target &&
          !branch.bottom)
          acquire(branch, branch_stack, conditional_mutex);
        successors.push_back(
          {positions.at(&*target), std::move(branch),
           std::move(branch_stack), {}});
      }
      if(
        !instruction.condition().is_true() &&
        key.index + 1 < order.size())
      {
        statet branch = state;
        std::vector<std::string> branch_stack = after_stack;
        assume_condition(
          analysis, branch, instruction.condition(), false);
        if(
          conditional_lock && !zero_on_target &&
          !branch.bottom)
          acquire(branch, branch_stack, conditional_mutex);
        successors.push_back(
          {key.index + 1, std::move(branch),
           std::move(branch_stack), {}});
      }
    }
    else if(
      !instruction.is_end_function() &&
      key.index + 1 < order.size())
      successors.push_back(
        {key.index + 1, state, after_stack, after_pending});
    else if(
      instruction.is_end_function() &&
      !after_pending.empty())
    {
      analysis.reason = "conditional_lock_unconsumed";
      return false;
    }

    for(auto &successor : successors)
    {
      if(successor.state.bottom)
        continue;
      const node_keyt next{
        successor.index,
        std::move(successor.stack),
        std::move(successor.pending)};
      const auto existing = states.find(next);
      if(existing == states.end())
      {
        states[next] = successor.state;
        work.push_back(next);
      }
      else
      {
        statet old = existing->second;
        if(join_state(existing->second, successor.state))
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
      if(!analysis.user_function(entry.first))
        continue;
      const auto contexts = analysis.contexts_for(entry.first);
      for(const auto &context : contexts)
      {
        analysis.active_aliases = &context;
        if(
          !analyze_function(
            analysis, entry.first, changed, all_properties))
          return false;
      }
    }
    analysis.active_aliases = nullptr;
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
  analysis.discover_region_summaries();
  analysis.collect_aliases();
  if(!analysis.collect_function_contexts())
  {
    std::cout << "NATIVE_LOCK_RELATIONAL_AI applied=0 reason="
              << analysis.reason
              << " region_initializers="
              << analysis.region_initializers.size()
              << " region_inserters="
              << analysis.region_inserters.size()
              << " region_traversals="
              << analysis.region_return_parameters.size()
              << " region_aliases="
              << analysis.region_selectors.size()
              << " aliases=" << analysis.aliases.size()
              << " roots=" << analysis.region_roots.size()
              << '\n';
    return false;
  }
  if(!validate_region_publication(analysis))
  {
    std::cout << "NATIVE_LOCK_RELATIONAL_AI applied=0 reason="
              << analysis.reason
              << " region_initializers="
              << analysis.region_initializers.size()
              << " region_inserters="
              << analysis.region_inserters.size()
              << " region_traversals="
              << analysis.region_return_parameters.size()
              << '\n';
    return false;
  }
  analysis.collect_initial();
  analysis.collect_pre_spawn();
  if(
    !validate_congruence_alias_escapes(analysis) ||
    !validate_congruence_alias_initialization(analysis) ||
    !validate_model(analysis) ||
    !collect_protection(analysis) ||
    !validate_region_lock_congruence(analysis))
  {
    std::cout << "NATIVE_LOCK_RELATIONAL_AI applied=0 reason="
              << analysis.reason
              << " region_initializers="
              << analysis.region_initializers.size()
              << " region_inserters="
              << analysis.region_inserters.size()
              << " region_traversals="
              << analysis.region_return_parameters.size()
              << " region_aliases="
              << analysis.region_selectors.size()
              << " aliases=" << analysis.aliases.size()
              << " roots=" << analysis.region_roots.size()
              << '\n';
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
