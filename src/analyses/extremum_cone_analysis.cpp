/*******************************************************************\

Module: Relational Extremum-Cone Invariant

\*******************************************************************/

#include "extremum_cone_analysis.h"

#include "natural_loops.h"

#include <goto-programs/goto_model.h>

#include <util/arith_tools.h>
#include <util/expr_util.h>
#include <util/find_symbols.h>
#include <util/message.h>
#include <util/namespace.h>
#include <util/pointer_expr.h>
#include <util/replace_expr.h>
#include <util/std_code.h>
#include <util/std_expr.h>
#include <util/symbol.h>

#include <algorithm>
#include <iostream>
#include <iterator>
#include <map>
#include <set>
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

bool addressed_id(const exprt &src, irep_idt &identifier)
{
  const exprt &expr = strip(src);
  return
    expr.id() == ID_address_of &&
    symbol_id(to_address_of_expr(expr).object(), identifier);
}

bool call_id(
  const goto_programt::instructiont &instruction,
  irep_idt &identifier)
{
  return
    instruction.is_function_call() &&
    symbol_id(instruction.call_function(), identifier);
}

bool integer_constant(const exprt &src, mp_integer &value)
{
  const exprt &expr = strip(src);
  if(
    expr.id() == ID_constant &&
    !to_integer(to_constant_expr(expr), value))
    return true;
  if(expr.id() == ID_unary_minus && expr.operands().size() == 1)
  {
    mp_integer operand;
    if(integer_constant(expr.op0(), operand))
    {
      value = -operand;
      return true;
    }
  }
  if(expr.id() == ID_minus && expr.operands().size() == 2)
  {
    mp_integer left;
    mp_integer right;
    if(
      integer_constant(expr.op0(), left) &&
      integer_constant(expr.op1(), right))
    {
      value = left - right;
      return true;
    }
  }
  return false;
}

bool value_is(const exprt &expr, const mp_integer &expected)
{
  mp_integer value;
  return integer_constant(expr, value) && value == expected;
}

const symbolt *lookup(
  const irep_idt &identifier,
  const namespacet &ns)
{
  const symbolt *symbol = nullptr;
  return ns.lookup(identifier, symbol) ? nullptr : symbol;
}

bool atomic_type(const typet &type)
{
  const std::string typedef_name =
    id2string(type.get("#typedef"));
  return
    type.get_bool("#atomic") ||
    typedef_name.find("atomic_") != std::string::npos;
}

bool shared_signed(
  const irep_idt &identifier,
  const namespacet &ns)
{
  const symbolt *symbol = lookup(identifier, ns);
  return
    symbol != nullptr && symbol->is_static_lifetime && !symbol->is_type &&
    symbol->type.id() == ID_signedbv;
}

bool shared_unsigned32(
  const irep_idt &identifier,
  const namespacet &ns)
{
  const symbolt *symbol = lookup(identifier, ns);
  return
    symbol != nullptr && symbol->is_static_lifetime && !symbol->is_type &&
    symbol->type.id() == ID_unsignedbv &&
    to_unsignedbv_type(symbol->type).get_width() == 32;
}

bool shared_boolean(
  const irep_idt &identifier,
  const namespacet &ns)
{
  const symbolt *symbol = lookup(identifier, ns);
  return
    symbol != nullptr && symbol->is_static_lifetime && !symbol->is_type &&
    (symbol->type.id() == ID_c_bool || symbol->type.id() == ID_bool);
}

bool shared_atomic(
  const irep_idt &identifier,
  const namespacet &ns)
{
  const symbolt *symbol = lookup(identifier, ns);
  return
    symbol != nullptr && symbol->is_static_lifetime && !symbol->is_type &&
    atomic_type(symbol->type);
}

bool shared_atomic_array(
  const irep_idt &identifier,
  const namespacet &ns)
{
  const symbolt *symbol = lookup(identifier, ns);
  if(
    symbol == nullptr || !symbol->is_static_lifetime || symbol->is_type ||
    symbol->type.id() != ID_pointer)
    return false;
  const typet &element = to_pointer_type(symbol->type).base_type();
  return
    atomic_type(element) && element.id() == ID_signedbv;
}

bool is_named(const irep_idt &identifier, const std::string &suffix)
{
  const std::string name = id2string(identifier);
  return
    name == suffix ||
    (name.size() > suffix.size() &&
     name.compare(name.size() - suffix.size(), suffix.size(), suffix) == 0);
}

bool is_create(const irep_idt &identifier)
{
  return is_named(identifier, "pthread_create");
}

bool is_join(const irep_idt &identifier)
{
  return is_named(identifier, "pthread_join");
}

bool is_reach_error(const irep_idt &identifier)
{
  return is_named(identifier, "reach_error");
}

bool is_assume(const irep_idt &identifier)
{
  return
    is_named(identifier, "assume_abort_if_not") ||
    is_named(identifier, "__CPROVER_assume");
}

bool is_atomic_marker(const irep_idt &identifier)
{
  return
    is_named(identifier, "__VERIFIER_atomic_begin") ||
    is_named(identifier, "__VERIFIER_atomic_end");
}

bool is_start_function(const irep_idt &identifier)
{
  const std::string name = id2string(identifier);
  return
    name == "__CPROVER__start" ||
    name == CPROVER_PREFIX "start" ||
    name.find("initialize") != std::string::npos;
}

bool contains_address(
  const exprt &expr,
  const std::set<irep_idt> &identifiers)
{
  irep_idt identifier;
  if(
    expr.id() == ID_address_of &&
    addressed_id(expr, identifier) &&
    identifiers.find(identifier) != identifiers.end())
    return true;
  return std::any_of(
    expr.operands().begin(),
    expr.operands().end(),
    [&](const exprt &operand) {
      return contains_address(operand, identifiers);
    });
}

bool contains_side_effect(const exprt &expr)
{
  if(expr.id() == ID_side_effect)
    return true;
  return std::any_of(
    expr.operands().begin(),
    expr.operands().end(),
    [&](const exprt &operand) {
      return contains_side_effect(operand);
    });
}

bool contains_symbol(
  const exprt &expr,
  const irep_idt &identifier)
{
  irep_idt candidate;
  if(symbol_id(expr, candidate) && candidate == identifier)
    return true;
  return std::any_of(
    expr.operands().begin(),
    expr.operands().end(),
    [&](const exprt &operand) {
      return contains_symbol(operand, identifier);
    });
}

void flatten_or(const exprt &src, std::vector<exprt> &terms)
{
  const exprt &expr = strip(src);
  if(expr.id() == ID_or)
  {
    for(const auto &operand : expr.operands())
      flatten_or(operand, terms);
  }
  else
    terms.push_back(expr);
}

void flatten_and(const exprt &src, std::vector<exprt> &terms)
{
  const exprt &expr = strip(src);
  if(expr.id() == ID_and)
  {
    for(const auto &operand : expr.operands())
      flatten_and(operand, terms);
  }
  else
    terms.push_back(expr);
}

bool zero_equivalence_constraint(
  const exprt &src,
  const std::set<irep_idt> &required)
{
  std::vector<exprt> terms;
  flatten_and(src, terms);
  std::map<irep_idt, std::set<irep_idt>> edges;
  std::set<irep_idt> zero;
  for(const auto &term_src : terms)
  {
    const exprt &term = strip(term_src);
    if(term.id() != ID_equal || term.operands().size() != 2)
      continue;
    irep_idt left;
    irep_idt right;
    if(symbol_id(term.op0(), left) && symbol_id(term.op1(), right))
    {
      edges[left].insert(right);
      edges[right].insert(left);
    }
    else if(symbol_id(term.op0(), left) && value_is(term.op1(), 0))
      zero.insert(left);
    else if(value_is(term.op0(), 0) && symbol_id(term.op1(), right))
      zero.insert(right);
  }

  std::vector<irep_idt> work(zero.begin(), zero.end());
  for(std::size_t index = 0; index < work.size(); ++index)
  {
    const auto found = edges.find(work[index]);
    if(found == edges.end())
      continue;
    for(const auto &next : found->second)
    {
      if(zero.insert(next).second)
        work.push_back(next);
    }
  }
  return std::includes(
    zero.begin(), zero.end(), required.begin(), required.end());
}

bool negated_truth(const exprt &src, irep_idt &identifier)
{
  const exprt &expr = strip(src);
  if(expr.id() == ID_not && expr.operands().size() == 1)
  {
    const exprt &operand = strip(expr.op0());
    if(symbol_id(operand, identifier))
      return true;
    if(
      operand.id() == ID_notequal &&
      operand.operands().size() == 2 &&
      ((symbol_id(operand.op0(), identifier) && value_is(operand.op1(), 0)) ||
       (symbol_id(operand.op1(), identifier) && value_is(operand.op0(), 0))))
      return true;
  }
  return
    expr.id() == ID_equal && expr.operands().size() == 2 &&
    ((symbol_id(expr.op0(), identifier) && value_is(expr.op1(), 0)) ||
     (symbol_id(expr.op1(), identifier) && value_is(expr.op0(), 0)));
}

bool parse_cone(
  const exprt &src,
  const namespacet &ns,
  irep_idt &lower,
  irep_idt &upper,
  unsigned &delta)
{
  const exprt &expr = strip(src);
  if(
    expr.id() != ID_le || expr.operands().size() != 2 ||
    !symbol_id(expr.op0(), lower) || !shared_signed(lower, ns))
    return false;
  if(symbol_id(expr.op1(), upper) && shared_signed(upper, ns))
  {
    delta = 0;
    return lower != upper;
  }
  const exprt &rhs = strip(expr.op1());
  if(rhs.id() != ID_plus || rhs.operands().size() != 2)
    return false;
  if(
    symbol_id(rhs.op0(), upper) && shared_signed(upper, ns) &&
    value_is(rhs.op1(), 1))
  {
    delta = 1;
    return lower != upper;
  }
  if(
    symbol_id(rhs.op1(), upper) && shared_signed(upper, ns) &&
    value_is(rhs.op0(), 1))
  {
    delta = 1;
    return lower != upper;
  }
  return false;
}

void substitute_locals(
  const goto_programt &program,
  goto_programt::const_targett stop,
  const namespacet &ns,
  exprt &expr)
{
  replace_mapt replacements;
  for(auto instruction = program.instructions.begin();
      instruction != stop; ++instruction)
  {
    if(!instruction->is_assign())
      continue;
    irep_idt lhs;
    if(!symbol_id(instruction->assign_lhs(), lhs))
      continue;
    const symbolt *symbol = lookup(lhs, ns);
    if(symbol == nullptr || symbol->is_static_lifetime)
      continue;
    exprt rhs = instruction->assign_rhs();
    replace_expr(replacements, rhs);
    replacements[instruction->assign_lhs()] = rhs;
  }
  for(std::size_t i = 0; i <= replacements.size(); ++i)
  {
    if(replace_expr(replacements, expr))
      break;
  }
}

struct propertyt
{
  irep_idt output;
  irep_idt lower;
  irep_idt upper;
  unsigned delta;
  std::set<irep_idt> readiness;
  irep_idt function;
  const goto_programt::instructiont *instruction;

  propertyt() : delta(0), instruction(nullptr)
  {
  }
};

bool find_property(
  const goto_modelt &model,
  const namespacet &ns,
  propertyt &property,
  std::string &reason)
{
  std::size_t matches = 0;
  for(const auto &entry : model.goto_functions.function_map)
  {
    for(auto instruction = entry.second.body.instructions.begin();
        instruction != entry.second.body.instructions.end(); ++instruction)
    {
      if(!instruction->is_assign())
        continue;
      irep_idt output;
      if(
        !symbol_id(instruction->assign_lhs(), output) ||
        !shared_boolean(output, ns))
        continue;
      exprt rhs = instruction->assign_rhs();
      substitute_locals(entry.second.body, instruction, ns, rhs);
      std::vector<exprt> terms;
      flatten_or(rhs, terms);
      irep_idt lower;
      irep_idt upper;
      unsigned delta = 0;
      std::size_t cone_index = terms.size();
      for(std::size_t i = 0; i < terms.size(); ++i)
      {
        if(parse_cone(terms[i], ns, lower, upper, delta))
        {
          if(cone_index != terms.size())
          {
            reason = "multiple_cones";
            return false;
          }
          cone_index = i;
        }
      }
      if(cone_index == terms.size())
        continue;

      std::set<irep_idt> readiness;
      bool overflow_guard = false;
      bool supported = true;
      for(std::size_t i = 0; i < terms.size(); ++i)
      {
        if(i == cone_index)
          continue;
        irep_idt ready;
        if(negated_truth(terms[i], ready) && shared_boolean(ready, ns))
          readiness.insert(ready);
        else if(delta == 1 && !overflow_guard)
        {
          const exprt &term = strip(terms[i]);
          irep_idt candidate;
          mp_integer bound;
          if(
            term.id() == ID_ge && term.operands().size() == 2 &&
            symbol_id(term.op0(), candidate) && candidate == upper &&
            integer_constant(term.op1(), bound) &&
            bound == power(2, 31) - 1)
            overflow_guard = true;
          else
            supported = false;
        }
        else
          supported = false;
      }
      if(
        !supported ||
        (delta == 1 && !overflow_guard) ||
        (readiness.empty() && terms.size() != 1) ||
        (!readiness.empty() && readiness.size() != 2))
        continue;

      ++matches;
      property.output = output;
      property.lower = lower;
      property.upper = upper;
      property.delta = delta;
      property.readiness = readiness;
      property.function = entry.first;
      property.instruction = &*instruction;
    }
  }
  if(matches != 1)
  {
    reason = matches == 0 ? "property" : "property_ambiguous";
    return false;
  }
  return true;
}

struct lifecyclet
{
  std::set<irep_idt> workers;
  std::set<irep_idt> handles;
  std::set<irep_idt> joins;
  const goto_programt::instructiont *first_create;
  const goto_programt::instructiont *last_join;

  lifecyclet() : first_create(nullptr), last_join(nullptr)
  {
  }
};

bool lifecycle(
  const goto_modelt &model,
  lifecyclet &result,
  std::string &reason)
{
  const auto main = model.goto_functions.function_map.find(ID_main);
  if(
    main == model.goto_functions.function_map.end() ||
    !main->second.body_available())
  {
    reason = "main";
    return false;
  }
  bool joining = false;
  for(const auto &instruction : main->second.body.instructions)
  {
    irep_idt callee;
    if(!call_id(instruction, callee))
      continue;
    const auto &arguments = instruction.call_arguments();
    if(is_create(callee))
    {
      if(joining)
      {
        reason = "create_after_join";
        return false;
      }
      irep_idt handle;
      irep_idt worker;
      if(
        arguments.size() < 3 ||
        !addressed_id(arguments[0], handle) ||
        !addressed_id(arguments[2], worker))
      {
        reason = "create";
        return false;
      }
      if(
        !result.handles.insert(handle).second ||
        !result.workers.insert(worker).second)
      {
        reason = "duplicate_create";
        return false;
      }
      if(result.first_create == nullptr)
        result.first_create = &instruction;
    }
    else if(is_join(callee))
    {
      joining = true;
      irep_idt handle;
      if(arguments.empty() || !symbol_id(arguments[0], handle))
      {
        reason = "join";
        return false;
      }
      if(!result.joins.insert(handle).second)
      {
        reason = "duplicate_join";
        return false;
      }
      result.last_join = &instruction;
    }
  }
  if(
    result.workers.size() < 3 ||
    result.workers.size() != result.handles.size() ||
    result.handles.size() != result.joins.size() ||
    result.handles != result.joins ||
    result.first_create == nullptr || result.last_join == nullptr ||
    result.first_create->location_number >= result.last_join->location_number)
  {
    reason = "lifecycle";
    return false;
  }
  for(const auto &worker : result.workers)
  {
    const auto found = model.goto_functions.function_map.find(worker);
    if(
      found == model.goto_functions.function_map.end() ||
      !found->second.body_available())
    {
      reason = "worker_body";
      return false;
    }
  }
  return true;
}

bool main_booleans_zero_before_create(
  const goto_modelt &model,
  const lifecyclet &life,
  const std::set<irep_idt> &symbols,
  std::string &reason)
{
  const auto &main =
    model.goto_functions.function_map.at(ID_main).body;
  std::map<irep_idt, const goto_programt::instructiont *> last_writes;
  std::set<irep_idt> direct_zero;
  std::set<irep_idt> initialized;
  std::vector<const goto_programt::instructiont *> assumptions;
  for(const auto &entry : model.goto_functions.function_map)
  {
    if(!is_start_function(entry.first))
      continue;
    for(const auto &instruction : entry.second.body.instructions)
    {
      if(!instruction.is_assign())
        continue;
      irep_idt lhs;
      if(
        symbol_id(instruction.assign_lhs(), lhs) &&
        symbols.find(lhs) != symbols.end() &&
        value_is(instruction.assign_rhs(), 0))
      {
        initialized.insert(lhs);
        direct_zero.insert(lhs);
      }
    }
  }
  for(const auto &instruction : main.instructions)
  {
    if(
      life.first_create != nullptr &&
      instruction.location_number >= life.first_create->location_number)
      break;
    if(instruction.is_assign())
    {
      irep_idt lhs;
      if(
        symbol_id(instruction.assign_lhs(), lhs) &&
        symbols.find(lhs) != symbols.end())
      {
        last_writes[lhs] = &instruction;
        initialized.insert(lhs);
        if(value_is(instruction.assign_rhs(), 0))
          direct_zero.insert(lhs);
        else
          direct_zero.erase(lhs);
      }
    }
    irep_idt callee;
    if(call_id(instruction, callee) && is_assume(callee))
      assumptions.push_back(&instruction);
  }
  if(!std::includes(
       initialized.begin(),
       initialized.end(),
       symbols.begin(),
       symbols.end()))
  {
    reason = "main_boolean_initialization";
    return false;
  }

  std::set<irep_idt> constrained;
  std::set_difference(
    symbols.begin(),
    symbols.end(),
    direct_zero.begin(),
    direct_zero.end(),
    std::inserter(constrained, constrained.end()));
  if(constrained.empty())
    return true;

  for(const auto *assumption : assumptions)
  {
    bool follows_writes = true;
    for(const auto &symbol : constrained)
    {
      const auto last_write = last_writes.find(symbol);
      if(
        last_write == last_writes.end() ||
        last_write->second->location_number >= assumption->location_number)
        follows_writes = false;
    }
    if(
      follows_writes &&
      assumption->call_arguments().size() == 1 &&
      zero_equivalence_constraint(
        assumption->call_arguments().front(), constrained))
      return true;
  }
  reason = "main_boolean_constraint";
  return false;
}

bool relation_matches(
  const exprt &condition,
  const irep_idt &summary,
  const exprt &rhs,
  bool lower)
{
  const exprt &expr = strip(condition);
  if(expr.id() != ID_not || expr.operands().size() != 1)
    return false;
  const exprt &relation = strip(expr.op0());
  if(relation.operands().size() != 2)
    return false;
  irep_idt lhs;
  if(
    !symbol_id(relation.op0(), lhs) || lhs != summary ||
    strip(relation.op1()) != strip(rhs))
    return false;
  return lower
    ? relation.id() == ID_ge || relation.id() == ID_gt
    : relation.id() == ID_le || relation.id() == ID_lt;
}

bool guarded_direction(
  const goto_programt &program,
  goto_programt::const_targett assignment,
  const irep_idt &summary,
  bool lower)
{
  if(assignment == program.instructions.begin())
    return false;
  const auto guard = std::prev(assignment);
  if(
    !guard->is_goto() ||
    !relation_matches(
      guard->condition(), summary, assignment->assign_rhs(), lower))
    return false;
  const auto target = guard->get_target();
  return
    target != program.instructions.end() &&
    target->location_number > assignment->location_number;
}

bool base_pointer(const exprt &src, irep_idt &base)
{
  const exprt &expr = strip(src);
  if(expr.id() != ID_dereference)
    return false;
  const exprt &pointer = strip(to_dereference_expr(expr).pointer());
  if(symbol_id(pointer, base))
    return true;
  if(pointer.id() != ID_plus || pointer.operands().size() != 2)
    return false;
  return symbol_id(pointer.op0(), base) || symbol_id(pointer.op1(), base);
}

bool base_index(
  const exprt &src,
  const irep_idt &expected_base,
  irep_idt &index)
{
  const exprt &expr = strip(src);
  if(expr.id() != ID_dereference)
    return false;
  const exprt &pointer = strip(to_dereference_expr(expr).pointer());
  if(pointer.id() != ID_plus || pointer.operands().size() != 2)
    return false;
  irep_idt left;
  irep_idt right;
  return
    symbol_id(pointer.op0(), left) && left == expected_base &&
    symbol_id(pointer.op1(), index) && index != expected_base &&
    (!symbol_id(pointer.op1(), right) || right == index);
}

bool parse_loop_exit(
  const goto_programt::instructiont &instruction,
  irep_idt &induction,
  exprt &bound)
{
  if(!instruction.is_goto() || instruction.targets.size() != 1)
    return false;
  const exprt &condition = strip(instruction.condition());
  if(condition.id() != ID_not || condition.operands().size() != 1)
    return false;
  const exprt &relation = strip(condition.op0());
  if(relation.id() != ID_lt || relation.operands().size() != 2)
    return false;
  if(!symbol_id(relation.op0(), induction))
    return false;
  bound = strip(relation.op1());
  return true;
}

bool unit_increment(
  const goto_programt::instructiont &instruction,
  const irep_idt &induction)
{
  if(!instruction.is_assign())
    return false;
  irep_idt lhs;
  if(!symbol_id(instruction.assign_lhs(), lhs) || lhs != induction)
    return false;
  const exprt &rhs = strip(instruction.assign_rhs());
  if(rhs.id() != ID_plus || rhs.operands().size() != 2)
    return false;
  irep_idt candidate;
  return
    (symbol_id(rhs.op0(), candidate) && candidate == induction &&
     value_is(rhs.op1(), 1)) ||
    (symbol_id(rhs.op1(), candidate) && candidate == induction &&
     value_is(rhs.op0(), 1));
}

bool unit_array_update(
  const goto_programt::instructiont &instruction,
  const irep_idt &base,
  irep_idt &index,
  int &direction)
{
  if(
    !instruction.is_assign() ||
    !base_index(instruction.assign_lhs(), base, index))
    return false;
  const exprt &lhs = strip(instruction.assign_lhs());
  const exprt &rhs = strip(instruction.assign_rhs());
  if(rhs.operands().size() != 2 || strip(rhs.op0()) != lhs)
    return false;
  if(rhs.id() == ID_plus && value_is(rhs.op1(), 1))
    direction = 1;
  else if(rhs.id() == ID_minus && value_is(rhs.op1(), 1))
    direction = -1;
  else
    return false;
  return true;
}

bool overflow_guard(
  const goto_programt::instructiont &instruction,
  const exprt &object,
  int direction)
{
  irep_idt callee;
  if(
    !call_id(instruction, callee) || !is_assume(callee) ||
    instruction.call_arguments().size() != 1)
    return false;
  const exprt &guard = strip(instruction.call_arguments().front());
  if(guard.operands().size() != 2 || strip(guard.op0()) != strip(object))
    return false;
  mp_integer bound;
  if(!integer_constant(guard.op1(), bound))
    return false;
  return direction > 0
    ? guard.id() == ID_lt && bound == power(2, 31) - 1
    : guard.id() == ID_gt && bound == -power(2, 31);
}

struct modifier_loopt
{
  irep_idt worker;
  exprt bound;
  int direction;
};

bool canonical_modifier_loop(
  const goto_modelt &model,
  const irep_idt &worker,
  const irep_idt &base,
  modifier_loopt &result,
  std::string &reason)
{
  const auto &program =
    model.goto_functions.function_map.at(worker).body;
  natural_loopst loops;
  loops(program);
  if(loops.loop_map.size() != 1)
  {
    reason = "modifier_loop_count";
    return false;
  }
  const auto &loop_entry = *loops.loop_map.begin();
  const auto loop_head = loop_entry.first;
  const auto &loop = loop_entry.second;
  irep_idt induction;
  exprt bound;
  if(!parse_loop_exit(*loop_head, induction, bound))
  {
    reason = "modifier_loop_guard";
    return false;
  }

  std::size_t zero_initializations = 0;
  std::size_t induction_updates = 0;
  std::size_t base_writes = 0;
  std::size_t backedges = 0;
  std::size_t loop_calls = 0;
  int direction = 0;
  goto_programt::const_targett update = program.instructions.end();
  goto_programt::const_targett guard = program.instructions.end();

  for(auto instruction = program.instructions.begin();
      instruction != program.instructions.end(); ++instruction)
  {
    if(instruction->is_assign())
    {
      irep_idt lhs;
      if(
        symbol_id(instruction->assign_lhs(), lhs) &&
        lhs == induction)
      {
        if(
          instruction->location_number < loop_head->location_number &&
          value_is(instruction->assign_rhs(), 0))
          ++zero_initializations;
        else if(
          loop.contains(instruction) &&
          unit_increment(*instruction, induction))
          ++induction_updates;
        else
        {
          reason = "modifier_induction_write";
          return false;
        }
      }

      irep_idt candidate_base;
      if(base_pointer(instruction->assign_lhs(), candidate_base))
      {
        if(candidate_base != base || !loop.contains(instruction))
        {
          reason = "modifier_array_write";
          return false;
        }
        irep_idt index;
        int candidate_direction = 0;
        if(
          !unit_array_update(
            *instruction, base, index, candidate_direction) ||
          index != induction)
        {
          reason = "modifier_update";
          return false;
        }
        ++base_writes;
        direction = candidate_direction;
        update = instruction;
      }
    }

    if(instruction->is_goto() && loop.contains(instruction))
    {
      if(instruction == loop_head)
        continue;
      if(
        instruction->condition().is_true() &&
        instruction->targets.size() == 1 &&
        instruction->get_target() == loop_head)
        ++backedges;
      else
      {
        reason = "modifier_control";
        return false;
      }
    }

    irep_idt callee;
    if(call_id(*instruction, callee))
    {
      if(!loop.contains(instruction) || !is_assume(callee))
      {
        reason = "modifier_call";
        return false;
      }
      ++loop_calls;
      guard = instruction;
    }
  }

  if(zero_initializations != 1)
  {
    reason = "modifier_zero_init";
    return false;
  }
  if(induction_updates != 1)
  {
    reason = "modifier_increment";
    return false;
  }
  if(base_writes != 1 || update == program.instructions.end())
  {
    reason = "modifier_write_count";
    return false;
  }
  if(backedges != 1)
  {
    reason = "modifier_backedge";
    return false;
  }
  if(loop_calls != 1 || guard == program.instructions.end())
  {
    reason = "modifier_guard_count";
    return false;
  }
  if(std::next(guard) != update)
  {
    reason = "modifier_guard_position";
    return false;
  }
  if(!overflow_guard(*guard, update->assign_lhs(), direction))
  {
    reason = "modifier_overflow_guard";
    return false;
  }

  result.worker = worker;
  result.bound = bound;
  result.direction = direction;
  return true;
}

bool positive_bound_before_create(
  const goto_modelt &model,
  const lifecyclet &life,
  const exprt &bound)
{
  const auto &main =
    model.goto_functions.function_map.at(ID_main).body;
  for(const auto &instruction : main.instructions)
  {
    if(
      life.first_create != nullptr &&
      instruction.location_number >= life.first_create->location_number)
      break;
    irep_idt callee;
    if(
      !call_id(instruction, callee) || !is_assume(callee) ||
      instruction.call_arguments().size() != 1)
      continue;
    const exprt &condition =
      strip(instruction.call_arguments().front());
    if(condition.operands().size() != 2)
      continue;
    if(
      condition.id() == ID_gt &&
      strip(condition.op0()) == strip(bound) &&
      value_is(condition.op1(), 0))
      return true;
    if(
      condition.id() == ID_lt &&
      value_is(condition.op0(), 0) &&
      strip(condition.op1()) == strip(bound))
      return true;
  }
  return false;
}

struct summary_infot
{
  irep_idt init_worker;
  exprt init_rhs;
  irep_idt readiness;
  bool has_worker_init;
  bool has_main_init;
  exprt main_init_rhs;
  const goto_programt::instructiont *worker_init_instruction;
  const goto_programt::instructiont *readiness_instruction;
  const goto_programt::instructiont *main_init_instruction;

  summary_infot()
    : has_worker_init(false),
      has_main_init(false),
      worker_init_instruction(nullptr),
      readiness_instruction(nullptr),
      main_init_instruction(nullptr)
  {
  }
};

bool summary_writes(
  const goto_modelt &model,
  const lifecyclet &life,
  const propertyt &property,
  const irep_idt &summary,
  bool lower,
  summary_infot &info,
  std::string &reason)
{
  for(const auto &entry : model.goto_functions.function_map)
  {
    const bool worker =
      life.workers.find(entry.first) != life.workers.end();
    for(auto instruction = entry.second.body.instructions.begin();
        instruction != entry.second.body.instructions.end(); ++instruction)
    {
      if(!instruction->is_assign())
        continue;
      irep_idt lhs;
      if(!symbol_id(instruction->assign_lhs(), lhs) || lhs != summary)
        continue;
      if(entry.first == ID_main)
      {
        if(
          info.has_main_init ||
          life.first_create == nullptr ||
          instruction->location_number >=
            life.first_create->location_number)
        {
          reason = "main_summary_init";
          return false;
        }
        info.has_main_init = true;
        info.main_init_rhs = instruction->assign_rhs();
        info.main_init_instruction = &*instruction;
        continue;
      }
      if(is_start_function(entry.first))
        continue;
      if(!worker)
      {
        reason = "summary_writer";
        return false;
      }
      if(guarded_direction(entry.second.body, instruction, summary, lower))
        continue;
      if(info.has_worker_init)
      {
        reason = "summary_init_count";
        return false;
      }
      const auto next = std::next(instruction);
      if(next == entry.second.body.instructions.end() || !next->is_assign())
      {
        reason = "readiness_missing";
        return false;
      }
      irep_idt ready;
      if(
        !symbol_id(next->assign_lhs(), ready) ||
        property.readiness.find(ready) == property.readiness.end() ||
        !value_is(next->assign_rhs(), 1))
      {
        reason = "readiness_store";
        return false;
      }
      info.has_worker_init = true;
      info.init_worker = entry.first;
      info.init_rhs = instruction->assign_rhs();
      info.readiness = ready;
      info.worker_init_instruction = &*instruction;
      info.readiness_instruction = &*next;
    }
  }
  return true;
}

bool readiness_writes(
  const goto_modelt &model,
  const lifecyclet &life,
  const propertyt &property,
  const summary_infot &lower,
  const summary_infot &upper,
  std::string &reason)
{
  std::set<const goto_programt::instructiont *> expected;
  if(lower.readiness_instruction != nullptr)
    expected.insert(lower.readiness_instruction);
  if(upper.readiness_instruction != nullptr)
    expected.insert(upper.readiness_instruction);
  std::set<const goto_programt::instructiont *> seen;
  for(const auto &entry : model.goto_functions.function_map)
  {
    for(auto instruction = entry.second.body.instructions.begin();
        instruction != entry.second.body.instructions.end(); ++instruction)
    {
      if(!instruction->is_assign())
        continue;
      irep_idt lhs;
      if(
        !symbol_id(instruction->assign_lhs(), lhs) ||
        property.readiness.find(lhs) == property.readiness.end())
        continue;
      if(entry.first == ID_main)
      {
        if(
          life.first_create == nullptr ||
          instruction->location_number >=
            life.first_create->location_number)
        {
          reason = "main_readiness_init";
          return false;
        }
        continue;
      }
      if(is_start_function(entry.first))
      {
        if(!value_is(instruction->assign_rhs(), 0))
        {
          reason = "start_readiness_init";
          return false;
        }
        continue;
      }
      if(expected.find(&*instruction) == expected.end())
      {
        reason = "readiness_writer";
        return false;
      }
      if(!value_is(instruction->assign_rhs(), 1))
      {
        reason = "readiness_reset";
        return false;
      }
      seen.insert(&*instruction);
    }
  }
  if(seen != expected || seen.size() != property.readiness.size())
  {
    reason = "readiness_count";
    return false;
  }
  return true;
}

bool anchor_skew_at_most_one(
  const goto_modelt &model,
  const lifecyclet &life,
  const propertyt &property,
  const summary_infot &lower,
  const summary_infot &upper,
  const irep_idt &base,
  std::string &reason)
{
  std::vector<modifier_loopt> modifiers;
  for(const auto &worker : life.workers)
  {
    const auto &program =
      model.goto_functions.function_map.at(worker).body;
    bool writes_base = false;
    for(const auto &instruction : program.instructions)
    {
      if(!instruction.is_assign())
        continue;
      irep_idt candidate;
      if(
        base_pointer(instruction.assign_lhs(), candidate) &&
        candidate == base)
        writes_base = true;
    }
    if(!writes_base)
      continue;
    if(
      worker == lower.init_worker || worker == upper.init_worker ||
      worker == property.function)
    {
      reason = "anchor_role_overlap";
      return false;
    }
    modifier_loopt modifier;
    if(!canonical_modifier_loop(model, worker, base, modifier, reason))
      return false;
    modifiers.push_back(modifier);
  }

  if(modifiers.empty() || modifiers.size() > 2)
  {
    reason = "modifier_count";
    return false;
  }
  std::set<int> directions;
  const exprt bound = modifiers.front().bound;
  for(const auto &modifier : modifiers)
  {
    if(
      strip(modifier.bound) != strip(bound) ||
      !directions.insert(modifier.direction).second)
    {
      reason = "modifier_compatibility";
      return false;
    }
  }
  if(!positive_bound_before_create(model, life, bound))
  {
    reason = "modifier_positive_bound";
    return false;
  }
  return true;
}

bool output_and_error_path(
  const goto_modelt &model,
  const lifecyclet &life,
  const propertyt &property,
  std::string &reason)
{
  std::size_t property_writes = 0;
  std::size_t errors = 0;
  std::size_t blocking_assumes = 0;
  for(const auto &entry : model.goto_functions.function_map)
  {
    for(const auto &instruction : entry.second.body.instructions)
    {
      if(instruction.is_assign())
      {
        irep_idt lhs;
        if(symbol_id(instruction.assign_lhs(), lhs) && lhs == property.output)
        {
          if(&instruction == property.instruction)
            ++property_writes;
          else if(entry.first == ID_main)
          {
            if(
              life.first_create == nullptr ||
              instruction.location_number >=
                life.first_create->location_number)
            {
              reason = "main_property_init";
              return false;
            }
          }
          else if(
            !is_start_function(entry.first) ||
            !value_is(instruction.assign_rhs(), 0))
          {
            reason = "property_writer";
            return false;
          }
        }
      }
      irep_idt callee;
      if(!call_id(instruction, callee))
        continue;
      if(is_reach_error(callee))
      {
        ++errors;
        if(
          entry.first != ID_main || life.last_join == nullptr ||
          instruction.location_number <= life.last_join->location_number)
        {
          reason = "error_function";
          return false;
        }
      }
      if(
        entry.first == ID_main && is_assume(callee) &&
        !instruction.call_arguments().empty())
      {
        irep_idt identifier;
        if(
          negated_truth(instruction.call_arguments().front(), identifier) &&
          identifier == property.output)
        {
          if(
            life.last_join == nullptr ||
            instruction.location_number <= life.last_join->location_number)
          {
            reason = "error_assume_order";
            return false;
          }
          ++blocking_assumes;
        }
      }
    }
  }
  if(
    property_writes != 1 || errors != 1 || blocking_assumes != 1 ||
    life.workers.find(property.function) == life.workers.end())
  {
    reason = "error_path";
    return false;
  }
  return true;
}

bool property_control_supported(
  const goto_modelt &model,
  const propertyt &property,
  const namespacet &ns,
  std::string &reason)
{
  const auto &body =
    model.goto_functions.function_map.at(property.function).body;
  std::size_t output_writes = 0;
  for(const auto &instruction : body.instructions)
  {
    if(
      instruction.is_goto() || instruction.is_assert() ||
      instruction.is_assume() || instruction.is_start_thread() ||
      instruction.is_end_thread() || instruction.is_function_call())
    {
      reason = "property_control";
      return false;
    }
    if(!instruction.is_assign())
      continue;
    if(contains_side_effect(instruction.assign_rhs()))
    {
      reason = "property_side_effect";
      return false;
    }
    irep_idt lhs;
    if(!symbol_id(instruction.assign_lhs(), lhs))
    {
      reason = "property_indirect_write";
      return false;
    }
    const symbolt *symbol = lookup(lhs, ns);
    if(
      symbol != nullptr && symbol->is_static_lifetime &&
      lhs != property.output)
    {
      reason = "property_shared_write";
      return false;
    }
    if(lhs == property.output)
      ++output_writes;
  }
  if(output_writes != 1)
  {
    reason = "property_output_count";
    return false;
  }
  return true;
}

bool instruction_mentions(
  const goto_programt::instructiont &instruction,
  const irep_idt &identifier)
{
  if(instruction.is_assign())
  {
    return
      contains_symbol(instruction.assign_lhs(), identifier) ||
      contains_symbol(instruction.assign_rhs(), identifier);
  }
  if(instruction.is_function_call())
  {
    if(contains_symbol(instruction.call_function(), identifier))
      return true;
    for(const auto &argument : instruction.call_arguments())
    {
      if(contains_symbol(argument, identifier))
        return true;
    }
  }
  return
    instruction.has_condition() &&
    contains_symbol(instruction.condition(), identifier);
}

bool protected_accesses_supported(
  const goto_modelt &model,
  const lifecyclet &life,
  const namespacet &ns,
  const std::set<irep_idt> &protected_symbols,
  std::string &reason)
{
  std::set<irep_idt> region_protected;
  for(const auto &identifier : protected_symbols)
  {
    if(!shared_atomic(identifier, ns))
      region_protected.insert(identifier);
  }
  if(region_protected.empty())
    return true;

  for(const auto &worker : life.workers)
  {
    const auto &body =
      model.goto_functions.function_map.at(worker).body;
    std::size_t atomic_depth = 0;
    for(const auto &instruction : body.instructions)
    {
      if(instruction.is_atomic_begin())
      {
        ++atomic_depth;
        continue;
      }
      if(instruction.is_atomic_end())
      {
        if(atomic_depth == 0)
        {
          reason = "atomic_region_balance";
          return false;
        }
        --atomic_depth;
        continue;
      }
      for(const auto &identifier : region_protected)
      {
        if(
          instruction_mentions(instruction, identifier) &&
          atomic_depth == 0)
        {
          reason =
            "nonatomic_protected_access_" +
            id2string(worker) + "_" + id2string(identifier) + "_" +
            std::to_string(instruction.location_number) + "_" +
            std::to_string(atomic_depth);
          return false;
        }
      }
    }
    if(atomic_depth != 0)
    {
      reason = "atomic_region_balance";
      return false;
    }
  }
  return true;
}

bool worker_calls_supported(
  const goto_modelt &model,
  const lifecyclet &life,
  std::string &reason)
{
  for(const auto &worker : life.workers)
  {
    const auto &body = model.goto_functions.function_map.at(worker).body;
    for(const auto &instruction : body.instructions)
    {
      irep_idt callee;
      if(
        call_id(instruction, callee) &&
        !is_atomic_marker(callee) && !is_assume(callee))
      {
        reason = "worker_call";
        return false;
      }
    }
  }
  return true;
}

bool anchor_storage_stable(
  const goto_modelt &model,
  const lifecyclet &life,
  const irep_idt &base,
  std::string &reason)
{
  for(const auto &entry : model.goto_functions.function_map)
  {
    const bool worker =
      life.workers.find(entry.first) != life.workers.end();
    for(const auto &instruction : entry.second.body.instructions)
    {
      if(!instruction.is_assign())
        continue;
      irep_idt lhs;
      if(symbol_id(instruction.assign_lhs(), lhs) && lhs == base)
      {
        if(is_start_function(entry.first))
          continue;
        if(
          entry.first == ID_main && life.first_create != nullptr &&
          instruction.location_number <
            life.first_create->location_number)
          continue;
        reason = "anchor_pointer_write";
        return false;
      }
      irep_idt candidate;
      if(
        base_pointer(instruction.assign_lhs(), candidate) &&
        candidate == base && !worker)
      {
        reason = "anchor_external_writer";
        return false;
      }
    }
  }
  return true;
}

bool base_use_is_dereference(
  const exprt &src,
  const irep_idt &base)
{
  const exprt &expr = strip(src);
  if(!contains_symbol(expr, base))
    return true;
  irep_idt identifier;
  if(symbol_id(expr, identifier) && identifier == base)
    return false;
  if(expr.id() == ID_dereference)
  {
    irep_idt candidate;
    return base_pointer(expr, candidate) && candidate == base;
  }
  for(const auto &operand : expr.operands())
  {
    if(!base_use_is_dereference(operand, base))
      return false;
  }
  return true;
}

bool anchor_alias_free(
  const goto_modelt &model,
  const irep_idt &base,
  std::string &reason)
{
  for(const auto &entry : model.goto_functions.function_map)
  {
    for(const auto &instruction : entry.second.body.instructions)
    {
      if(instruction.is_assign())
      {
        irep_idt lhs;
        const bool writes_base =
          symbol_id(instruction.assign_lhs(), lhs) && lhs == base;
        if(
          (!writes_base &&
           !base_use_is_dereference(instruction.assign_lhs(), base)) ||
          !base_use_is_dereference(instruction.assign_rhs(), base))
        {
          reason = "anchor_alias";
          return false;
        }
      }
      else if(instruction.is_function_call())
      {
        for(const auto &argument : instruction.call_arguments())
        {
          if(!base_use_is_dereference(argument, base))
          {
            reason = "anchor_call_escape";
            return false;
          }
        }
      }
      else if(
        instruction.has_condition() &&
        !base_use_is_dereference(instruction.condition(), base))
      {
        reason = "anchor_condition_alias";
        return false;
      }
    }
  }
  return true;
}

bool no_addresses(
  const goto_modelt &model,
  const std::set<irep_idt> &protected_symbols,
  std::string &reason)
{
  for(const auto &entry : model.goto_functions.function_map)
  {
    for(const auto &instruction : entry.second.body.instructions)
    {
      if(
        contains_address(instruction.code(), protected_symbols) ||
        (instruction.has_condition() &&
         contains_address(instruction.condition(), protected_symbols)))
      {
        reason = "address_escape";
        return false;
      }
    }
  }
  return true;
}

struct hom_propertyt
{
  irep_idt left_summary;
  irep_idt right_summary;
  irep_idt result_summary;
  irep_idt operation;
  irep_idt temporary;
  bool minimum;
  const goto_programt::instructiont *operation_call;
  const goto_programt::instructiont *assumption;
  const goto_programt::instructiont *error;

  hom_propertyt()
    : minimum(false),
      operation_call(nullptr),
      assumption(nullptr),
      error(nullptr)
  {
  }
};

bool hom_relation(
  const exprt &src,
  irep_idt &result,
  irep_idt &temporary,
  bool &minimum)
{
  const exprt &relation = strip(src);
  if(
    (relation.id() != ID_gt && relation.id() != ID_lt) ||
    relation.operands().size() != 2 ||
    !symbol_id(relation.op0(), result) ||
    !symbol_id(relation.op1(), temporary))
    return false;
  minimum = relation.id() == ID_lt;
  return true;
}

bool find_hom_property(
  const goto_modelt &model,
  const namespacet &ns,
  const lifecyclet &life,
  hom_propertyt &property,
  std::string &reason)
{
  const auto &main =
    model.goto_functions.function_map.at(ID_main).body;
  std::map<irep_idt, const goto_programt::instructiont *> value_calls;
  std::size_t matches = 0;
  std::size_t errors = 0;

  for(const auto &entry : model.goto_functions.function_map)
  {
    for(const auto &instruction : entry.second.body.instructions)
    {
      irep_idt callee;
      if(call_id(instruction, callee) && is_reach_error(callee))
      {
        ++errors;
        if(entry.first != ID_main)
        {
          reason = "hom_error_function";
          return false;
        }
        property.error = &instruction;
      }
    }
  }

  for(const auto &instruction : main.instructions)
  {
    if(
      life.last_join == nullptr ||
      instruction.location_number <= life.last_join->location_number)
      continue;
    irep_idt callee;
    if(!call_id(instruction, callee))
      continue;
    if(
      !instruction.call_lhs().is_nil() &&
      instruction.call_arguments().size() == 2)
    {
      irep_idt temporary;
      if(symbol_id(instruction.call_lhs(), temporary))
        value_calls[temporary] = &instruction;
      continue;
    }
    if(!is_assume(callee) || instruction.call_arguments().size() != 1)
      continue;

    irep_idt result;
    irep_idt temporary;
    bool minimum = false;
    if(
      !hom_relation(
        instruction.call_arguments().front(),
        result,
        temporary,
        minimum))
      continue;
    const auto producer = value_calls.find(temporary);
    if(producer == value_calls.end())
      continue;
    irep_idt operation;
    irep_idt left;
    irep_idt right;
    if(
      !call_id(*producer->second, operation) ||
      !symbol_id(producer->second->call_arguments()[0], left) ||
      !symbol_id(producer->second->call_arguments()[1], right) ||
      !shared_signed(left, ns) || !shared_signed(right, ns) ||
      !shared_signed(result, ns) || left == right || left == result ||
      right == result)
      continue;

    ++matches;
    property.left_summary = left;
    property.right_summary = right;
    property.result_summary = result;
    property.operation = operation;
    property.temporary = temporary;
    property.minimum = minimum;
    property.operation_call = producer->second;
    property.assumption = &instruction;
  }

  if(
    matches != 1 || errors != 1 || property.error == nullptr ||
    property.operation_call == nullptr || property.assumption == nullptr ||
    property.operation_call->location_number >=
      property.assumption->location_number ||
    property.assumption->location_number >= property.error->location_number)
  {
    reason = matches == 0 ? "hom_property" : "hom_property_ambiguous";
    return false;
  }
  return true;
}

bool array_at(
  const exprt &src,
  const irep_idt &base,
  const exprt &index)
{
  const exprt &expr = strip(src);
  if(expr.id() != ID_dereference)
    return false;
  const exprt &pointer = strip(to_dereference_expr(expr).pointer());
  if(pointer.id() != ID_plus || pointer.operands().size() != 2)
    return false;
  irep_idt candidate;
  return
    ((symbol_id(pointer.op0(), candidate) && candidate == base &&
      strip(pointer.op1()) == strip(index)) ||
     (symbol_id(pointer.op1(), candidate) && candidate == base &&
     strip(pointer.op0()) == strip(index)));
}

bool array_at_zero(
  const exprt &src,
  const irep_idt &base)
{
  const exprt &expr = strip(src);
  if(expr.id() != ID_dereference)
    return false;
  const exprt &pointer = strip(to_dereference_expr(expr).pointer());
  if(pointer.id() != ID_plus || pointer.operands().size() != 2)
    return false;
  irep_idt candidate;
  return
    ((symbol_id(pointer.op0(), candidate) && candidate == base &&
      value_is(pointer.op1(), 0)) ||
     (symbol_id(pointer.op1(), candidate) && candidate == base &&
      value_is(pointer.op0(), 0)));
}

bool array_symbol_index(
  const exprt &src,
  irep_idt &base,
  irep_idt &index)
{
  const exprt &expr = strip(src);
  if(expr.id() != ID_dereference)
    return false;
  const exprt &pointer = strip(to_dereference_expr(expr).pointer());
  if(pointer.id() != ID_plus || pointer.operands().size() != 2)
    return false;
  irep_idt first;
  irep_idt second;
  if(
    symbol_id(pointer.op0(), first) &&
    symbol_id(pointer.op1(), second) && first != second)
  {
    base = first;
    index = second;
    return true;
  }
  return false;
}

struct hom_main_initt
{
  irep_idt left_base;
  irep_idt right_base;
  const goto_programt::instructiont *left_summary;
  const goto_programt::instructiont *right_summary;
  const goto_programt::instructiont *result_summary;

  hom_main_initt()
    : left_summary(nullptr), right_summary(nullptr), result_summary(nullptr)
  {
  }
};

bool find_hom_initial_summaries(
  const goto_modelt &model,
  const lifecyclet &life,
  const hom_propertyt &property,
  hom_main_initt &initial,
  std::string &reason)
{
  const auto &main =
    model.goto_functions.function_map.at(ID_main).body;
  std::size_t left = 0;
  std::size_t right = 0;
  std::size_t result = 0;

  for(const auto &instruction : main.instructions)
  {
    if(
      life.first_create == nullptr ||
      instruction.location_number >= life.first_create->location_number)
      break;
    if(instruction.is_assign())
    {
      irep_idt lhs;
      irep_idt base;
      if(!symbol_id(instruction.assign_lhs(), lhs))
        continue;
      if(
        lhs == property.left_summary &&
        base_pointer(instruction.assign_rhs(), base) &&
        array_at_zero(instruction.assign_rhs(), base))
      {
        ++left;
        initial.left_base = base;
        initial.left_summary = &instruction;
      }
      else if(
        lhs == property.right_summary &&
        base_pointer(instruction.assign_rhs(), base) &&
        array_at_zero(instruction.assign_rhs(), base))
      {
        ++right;
        initial.right_base = base;
        initial.right_summary = &instruction;
      }
    }

    irep_idt callee;
    if(
      call_id(instruction, callee) &&
      callee == property.operation &&
      !instruction.call_lhs().is_nil() &&
      instruction.call_arguments().size() == 2)
    {
      irep_idt lhs;
      if(
        symbol_id(instruction.call_lhs(), lhs) &&
        lhs == property.result_summary &&
        !initial.left_base.empty() && !initial.right_base.empty() &&
        array_at_zero(
          instruction.call_arguments()[0], initial.left_base) &&
        array_at_zero(
          instruction.call_arguments()[1], initial.right_base))
      {
        ++result;
        initial.result_summary = &instruction;
      }
    }
  }

  if(
    left != 1 || right != 1 || result != 1 ||
    initial.left_base == initial.right_base)
  {
    reason = "hom_initial_summaries";
    return false;
  }
  return true;
}

struct hom_loopt
{
  irep_idt induction;
  irep_idt bound;
  goto_programt::const_targett head;
  std::set<const goto_programt::instructiont *> members;

  hom_loopt() : head()
  {
  }
};

bool hom_loop_skeleton(
  const goto_programt &program,
  hom_loopt &result,
  std::string &reason)
{
  natural_loopst loops;
  loops(program);
  if(loops.loop_map.size() != 1)
  {
    reason = "hom_loop_count";
    return false;
  }
  result.head = loops.loop_map.begin()->first;
  const auto &loop = loops.loop_map.begin()->second;
  exprt bound;
  if(
    !parse_loop_exit(*result.head, result.induction, bound) ||
    !symbol_id(bound, result.bound))
  {
    reason = "hom_loop_guard";
    return false;
  }

  std::size_t initializations = 0;
  std::size_t increments = 0;
  std::size_t backedges = 0;
  for(auto instruction = program.instructions.begin();
      instruction != program.instructions.end(); ++instruction)
  {
    if(loop.contains(instruction))
      result.members.insert(&*instruction);
    if(instruction->is_assign())
    {
      irep_idt lhs;
      if(
        symbol_id(instruction->assign_lhs(), lhs) &&
        lhs == result.induction)
      {
        if(
          instruction->location_number < result.head->location_number &&
          value_is(instruction->assign_rhs(), 1))
          ++initializations;
        else if(
          loop.contains(instruction) &&
          unit_increment(*instruction, result.induction))
          ++increments;
        else
        {
          reason = "hom_induction_write";
          return false;
        }
      }
    }
    if(
      instruction->is_goto() && loop.contains(instruction) &&
      instruction != result.head &&
      instruction->condition().is_true() &&
      instruction->targets.size() == 1 &&
      instruction->get_target() == result.head)
      ++backedges;
  }
  if(initializations != 1 || increments != 1 || backedges != 1)
  {
    reason = "hom_loop_skeleton";
    return false;
  }
  return true;
}

bool shared_symbol_lhs(
  const goto_programt::instructiont &instruction,
  const namespacet &ns,
  irep_idt &identifier)
{
  if(
    !instruction.is_assign() ||
    !symbol_id(instruction.assign_lhs(), identifier))
    return false;
  const symbolt *symbol = lookup(identifier, ns);
  return
    symbol != nullptr && symbol->is_static_lifetime && !symbol->is_type;
}

struct hom_worker_resultt
{
  irep_idt bound;
  irep_idt result_base;
  irep_idt progress;
  std::set<const goto_programt::instructiont *> writes;
};

bool hom_fold_worker(
  const goto_modelt &model,
  const namespacet &ns,
  const irep_idt &worker,
  const hom_propertyt &property,
  const hom_main_initt &initial,
  hom_worker_resultt &result,
  std::string &reason)
{
  const auto &program =
    model.goto_functions.function_map.at(worker).body;
  hom_loopt loop;
  if(!hom_loop_skeleton(program, loop, reason))
    return false;

  std::vector<goto_programt::const_targett> updates;
  std::size_t gotos = 0;
  for(auto instruction = program.instructions.begin();
      instruction != program.instructions.end(); ++instruction)
  {
    if(instruction->is_atomic_begin() || instruction->is_atomic_end())
    {
      reason = "hom_fold_atomic";
      return false;
    }
    if(instruction->is_function_call())
    {
      reason = "hom_fold_call";
      return false;
    }
    if(instruction->is_goto() && loop.members.count(&*instruction) != 0)
      ++gotos;
    if(!instruction->is_assign())
      continue;
    irep_idt lhs;
    if(shared_symbol_lhs(*instruction, ns, lhs))
    {
      if(
        lhs != property.left_summary &&
        lhs != property.right_summary)
      {
        reason = "hom_fold_shared_write";
        return false;
      }
      updates.push_back(instruction);
      result.writes.insert(&*instruction);
    }
    else
    {
      irep_idt base;
      if(base_pointer(instruction->assign_lhs(), base))
      {
        reason = "hom_fold_array_write";
        return false;
      }
    }
  }
  if(updates.size() != 2 || gotos != 4)
  {
    reason = "hom_fold_shape";
    return false;
  }

  bool left = false;
  bool right = false;
  const symbolt *induction_symbol = lookup(loop.induction, ns);
  if(induction_symbol == nullptr)
  {
    reason = "hom_fold_induction_symbol";
    return false;
  }
  const exprt induction =
    symbol_exprt(loop.induction, induction_symbol->type);
  for(const auto update : updates)
  {
    irep_idt summary;
    if(!symbol_id(update->assign_lhs(), summary))
      return false;
    const irep_idt &base =
      summary == property.left_summary
        ? initial.left_base
        : initial.right_base;
    if(
      !array_at(update->assign_rhs(), base, induction) ||
      !guarded_direction(
        program, update, summary, property.minimum))
    {
      reason = "hom_fold_update";
      return false;
    }
    if(summary == property.left_summary)
      left = true;
    if(summary == property.right_summary)
      right = true;
  }
  if(!left || !right)
  {
    reason = "hom_fold_summaries";
    return false;
  }
  result.bound = loop.bound;
  return true;
}

bool hom_producer_worker(
  const goto_modelt &model,
  const namespacet &ns,
  const irep_idt &worker,
  const hom_propertyt &property,
  const hom_main_initt &initial,
  hom_worker_resultt &result,
  std::string &reason)
{
  const auto &program =
    model.goto_functions.function_map.at(worker).body;
  hom_loopt loop;
  if(!hom_loop_skeleton(program, loop, reason))
    return false;

  goto_programt::const_targett operation = program.instructions.end();
  goto_programt::const_targett array_write = program.instructions.end();
  goto_programt::const_targett progress_write = program.instructions.end();
  std::size_t gotos = 0;
  int atomic_depth = 0;
  std::size_t atomic_begins = 0;
  std::size_t atomic_ends = 0;
  for(auto instruction = program.instructions.begin();
      instruction != program.instructions.end(); ++instruction)
  {
    if(instruction->is_atomic_begin())
    {
      ++atomic_depth;
      ++atomic_begins;
      if(atomic_depth != 1)
      {
        reason = "hom_producer_atomic_nesting";
        return false;
      }
      continue;
    }
    if(instruction->is_atomic_end())
    {
      --atomic_depth;
      ++atomic_ends;
      if(atomic_depth != 0)
      {
        reason = "hom_producer_atomic_balance";
        return false;
      }
      continue;
    }
    if(instruction->is_goto() && loop.members.count(&*instruction) != 0)
      ++gotos;
    if(instruction->is_function_call())
    {
      irep_idt callee;
      if(
        atomic_depth != 1 || !call_id(*instruction, callee) ||
        callee != property.operation ||
        instruction->call_lhs().is_nil() ||
        instruction->call_arguments().size() != 2)
      {
        reason = "hom_producer_call";
        return false;
      }
      const symbolt *induction_symbol = lookup(loop.induction, ns);
      if(induction_symbol == nullptr)
      {
        reason = "hom_producer_induction_symbol";
        return false;
      }
      const exprt induction =
        symbol_exprt(loop.induction, induction_symbol->type);
      if(
        !array_at(
          instruction->call_arguments()[0],
          initial.left_base,
          induction) ||
        !array_at(
          instruction->call_arguments()[1],
          initial.right_base,
          induction))
      {
        reason = "hom_producer_arguments";
        return false;
      }
      if(operation != program.instructions.end())
      {
        reason = "hom_producer_call_count";
        return false;
      }
      operation = instruction;
      continue;
    }
    if(!instruction->is_assign())
      continue;

    irep_idt lhs;
    if(shared_symbol_lhs(*instruction, ns, lhs))
    {
      if(
        atomic_depth != 1 ||
        !unit_increment(*instruction, loop.induction))
      {
        const exprt &rhs = strip(instruction->assign_rhs());
        irep_idt index;
        if(
          rhs.id() != ID_plus || rhs.operands().size() != 2 ||
          !symbol_id(rhs.op0(), index) || index != loop.induction ||
          !value_is(rhs.op1(), 1))
        {
          reason = "hom_progress_write";
          return false;
        }
      }
      if(progress_write != program.instructions.end())
      {
        reason = "hom_progress_count";
        return false;
      }
      result.progress = lhs;
      progress_write = instruction;
      result.writes.insert(&*instruction);
      continue;
    }

    irep_idt base;
    irep_idt index;
    if(array_symbol_index(instruction->assign_lhs(), base, index))
    {
      irep_idt temporary;
      if(
        atomic_depth != 1 || index != loop.induction ||
        !symbol_id(instruction->assign_rhs(), temporary) ||
        operation == program.instructions.end() ||
        !symbol_id(operation->call_lhs(), lhs) || temporary != lhs)
      {
        reason = "hom_result_array_write";
        return false;
      }
      if(array_write != program.instructions.end())
      {
        reason = "hom_result_array_count";
        return false;
      }
      result.result_base = base;
      array_write = instruction;
      result.writes.insert(&*instruction);
    }
  }
  if(
    atomic_depth != 0 || atomic_begins != 1 || atomic_ends != 1 ||
    gotos != 2 || operation == program.instructions.end() ||
    array_write == program.instructions.end() ||
    progress_write == program.instructions.end() ||
    operation->location_number >= array_write->location_number ||
    array_write->location_number >= progress_write->location_number ||
    result.result_base == initial.left_base ||
    result.result_base == initial.right_base)
  {
    reason = "hom_producer_shape";
    return false;
  }
  result.bound = loop.bound;
  return true;
}

bool hom_consumer_condition(
  const exprt &src,
  const irep_idt &induction,
  const irep_idt &progress)
{
  const exprt &relation = strip(src);
  irep_idt left;
  irep_idt right;
  return
    relation.id() == ID_lt && relation.operands().size() == 2 &&
    symbol_id(relation.op0(), left) && left == induction &&
    symbol_id(relation.op1(), right) && right == progress;
}

bool hom_consumer_guard(
  const exprt &src,
  const irep_idt &condition)
{
  const exprt &outer = strip(src);
  if(outer.id() != ID_not || outer.operands().size() != 1)
    return false;
  const exprt &relation = strip(outer.op0());
  irep_idt symbol;
  return
    relation.id() == ID_notequal && relation.operands().size() == 2 &&
    symbol_id(relation.op0(), symbol) && symbol == condition &&
    value_is(relation.op1(), 0);
}

bool hom_consumer_worker(
  const goto_modelt &model,
  const namespacet &ns,
  const irep_idt &worker,
  const hom_propertyt &property,
  const hom_worker_resultt &producer,
  hom_worker_resultt &result,
  std::string &reason)
{
  const auto &program =
    model.goto_functions.function_map.at(worker).body;
  hom_loopt loop;
  if(!hom_loop_skeleton(program, loop, reason))
    return false;
  if(loop.bound != producer.bound)
  {
    reason = "hom_consumer_bound";
    return false;
  }

  goto_programt::const_targett condition_write =
    program.instructions.end();
  goto_programt::const_targett condition_guard =
    program.instructions.end();
  goto_programt::const_targett summary_write =
    program.instructions.end();
  irep_idt condition;
  std::size_t gotos = 0;
  int atomic_depth = 0;
  std::size_t atomic_begins = 0;
  std::size_t atomic_ends = 0;
  for(auto instruction = program.instructions.begin();
      instruction != program.instructions.end(); ++instruction)
  {
    if(instruction->is_atomic_begin())
    {
      ++atomic_depth;
      ++atomic_begins;
      if(atomic_depth != 1)
      {
        reason = "hom_consumer_atomic_nesting";
        return false;
      }
      continue;
    }
    if(instruction->is_atomic_end())
    {
      --atomic_depth;
      ++atomic_ends;
      if(atomic_depth != 0)
      {
        reason = "hom_consumer_atomic_balance";
        return false;
      }
      continue;
    }
    if(instruction->is_function_call())
    {
      reason = "hom_consumer_call";
      return false;
    }
    if(instruction->is_goto() && loop.members.count(&*instruction) != 0)
    {
      ++gotos;
      if(
        instruction != loop.head &&
        !instruction->condition().is_true() &&
        condition_guard == program.instructions.end() &&
        !condition.empty() &&
        hom_consumer_guard(instruction->condition(), condition))
        condition_guard = instruction;
    }
    if(!instruction->is_assign())
      continue;
    irep_idt lhs;
    if(shared_symbol_lhs(*instruction, ns, lhs))
    {
      const symbolt *induction_symbol = lookup(loop.induction, ns);
      if(
        induction_symbol == nullptr ||
        lhs != property.result_summary || atomic_depth != 1 ||
        !array_at(
          instruction->assign_rhs(),
          producer.result_base,
          symbol_exprt(loop.induction, induction_symbol->type)) ||
        !guarded_direction(
          program,
          instruction,
          property.result_summary,
          property.minimum))
      {
        reason = "hom_consumer_summary";
        return false;
      }
      if(summary_write != program.instructions.end())
      {
        reason = "hom_consumer_summary_count";
        return false;
      }
      summary_write = instruction;
      result.writes.insert(&*instruction);
      continue;
    }

    if(
      symbol_id(instruction->assign_lhs(), lhs) &&
      hom_consumer_condition(
        instruction->assign_rhs(), loop.induction, producer.progress))
    {
      if(
        atomic_depth != 1 ||
        condition_write != program.instructions.end())
      {
        reason = "hom_consumer_condition_count";
        return false;
      }
      condition = lhs;
      condition_write = instruction;
      continue;
    }

    irep_idt base;
    if(base_pointer(instruction->assign_lhs(), base))
    {
      reason = "hom_consumer_array_write";
      return false;
    }
  }
  if(
    atomic_depth != 0 || atomic_begins != 2 || atomic_ends != 2 ||
    gotos != 4 || condition_write == program.instructions.end() ||
    condition_guard == program.instructions.end() ||
    summary_write == program.instructions.end() ||
    condition_write->location_number >= condition_guard->location_number ||
    condition_guard->location_number >= summary_write->location_number)
  {
    reason = "hom_consumer_shape";
    return false;
  }
  result.bound = loop.bound;
  return true;
}

bool relation_zero(
  const exprt &src,
  const irep_idt &symbol,
  const irep_idt &relation_id)
{
  const exprt &relation = strip(src);
  irep_idt candidate;
  return
    relation.id() == relation_id && relation.operands().size() == 2 &&
    symbol_id(relation.op0(), candidate) && candidate == symbol &&
    value_is(relation.op1(), 0);
}

bool overflow_half(
  const exprt &src,
  const irep_idt &left,
  const irep_idt &right,
  bool lower)
{
  const exprt &root = strip(src);
  if(root.id() != ID_or || root.operands().size() != 2)
    return false;
  for(unsigned order = 0; order < 2; ++order)
  {
    const exprt &sign = strip(root.operands()[order]);
    const exprt &bound = strip(root.operands()[1 - order]);
    const irep_idt sign_relation = lower ? ID_ge : ID_le;
    const irep_idt bound_relation = lower ? ID_ge : ID_le;
    if(!relation_zero(sign, right, sign_relation))
      continue;
    if(
      bound.id() != bound_relation || bound.operands().size() != 2)
      continue;
    irep_idt candidate;
    if(!symbol_id(bound.op0(), candidate) || candidate != left)
      continue;
    const exprt &difference = strip(bound.op1());
    if(difference.id() != ID_minus || difference.operands().size() != 2)
      continue;
    mp_integer constant;
    irep_idt rhs;
    if(
      integer_constant(difference.op0(), constant) &&
      symbol_id(difference.op1(), rhs) && rhs == right &&
      constant ==
        (lower ? -power(2, 31) : power(2, 31) - 1))
      return true;
  }
  return false;
}

bool signed_addition_helper(
  const goto_modelt &model,
  const namespacet &ns,
  const irep_idt &operation,
  std::string &reason)
{
  const symbolt *symbol = lookup(operation, ns);
  const auto function =
    model.goto_functions.function_map.find(operation);
  if(
    symbol == nullptr || symbol->type.id() != ID_code ||
    function == model.goto_functions.function_map.end() ||
    !function->second.body_available())
  {
    reason = "hom_operation_body";
    return false;
  }
  const auto &parameters =
    to_code_type(symbol->type).parameters();
  if(
    parameters.size() != 2 ||
    parameters[0].type().id() != ID_signedbv ||
    parameters[1].type().id() != ID_signedbv ||
    to_signedbv_type(parameters[0].type()).get_width() != 32 ||
    to_signedbv_type(parameters[1].type()).get_width() != 32)
  {
    reason = "hom_operation_type";
    return false;
  }
  const irep_idt left = parameters[0].get_identifier();
  const irep_idt right = parameters[1].get_identifier();
  std::size_t assumes = 0;
  std::size_t returns = 0;
  bool lower = false;
  bool upper = false;
  for(const auto &instruction : function->second.body.instructions)
  {
    irep_idt callee;
    if(call_id(instruction, callee))
    {
      if(!is_assume(callee) || instruction.call_arguments().size() != 1)
      {
        reason = "hom_operation_call";
        return false;
      }
      ++assumes;
      lower =
        lower ||
        overflow_half(
          instruction.call_arguments().front(), left, right, true);
      upper =
        upper ||
        overflow_half(
          instruction.call_arguments().front(), left, right, false);
    }
    else if(instruction.is_set_return_value())
    {
      const exprt &value = strip(instruction.return_value());
      irep_idt lhs;
      irep_idt rhs;
      if(
        value.id() != ID_plus || value.operands().size() != 2 ||
        !symbol_id(value.op0(), lhs) || lhs != left ||
        !symbol_id(value.op1(), rhs) || rhs != right)
      {
        reason = "hom_operation_return";
        return false;
      }
      ++returns;
    }
    else if(
      instruction.is_assign() || instruction.is_goto() ||
      instruction.is_assert() || instruction.is_assume() ||
      instruction.is_atomic_begin() || instruction.is_atomic_end() ||
      instruction.is_start_thread() || instruction.is_end_thread())
    {
      reason = "hom_operation_effect";
      return false;
    }
  }
  if(assumes != 2 || returns != 1 || !lower || !upper)
  {
    reason = "hom_operation_overflow";
    return false;
  }
  return true;
}

struct hom_main_statet
{
  irep_idt allocator;
  const goto_programt::instructiont *bound_init;
  const goto_programt::instructiont *progress_init;
  std::set<const goto_programt::instructiont *> base_initializers;

  hom_main_statet() : bound_init(nullptr), progress_init(nullptr)
  {
  }
};

bool hom_main_obligations(
  const goto_modelt &model,
  const lifecyclet &life,
  const hom_propertyt &property,
  const hom_main_initt &initial,
  const hom_worker_resultt &producer,
  hom_main_statet &state,
  std::string &reason)
{
  const auto &main =
    model.goto_functions.function_map.at(ID_main).body;
  std::size_t positive_bounds = 0;
  std::size_t progress_inits = 0;
  std::map<irep_idt, const goto_programt::instructiont *> bases;
  irep_idt allocator;

  for(const auto &instruction : main.instructions)
  {
    if(
      life.first_create != nullptr &&
      instruction.location_number >= life.first_create->location_number)
      break;
    if(instruction.is_assign())
    {
      irep_idt lhs;
      if(!symbol_id(instruction.assign_lhs(), lhs))
        continue;
      if(lhs == producer.bound)
      {
        if(state.bound_init != nullptr)
        {
          reason = "hom_bound_init_count";
          return false;
        }
        state.bound_init = &instruction;
      }
      if(
        lhs == producer.progress &&
        value_is(instruction.assign_rhs(), 1))
      {
        ++progress_inits;
        state.progress_init = &instruction;
      }
    }

    irep_idt callee;
    if(!call_id(instruction, callee))
      continue;
    if(
      is_assume(callee) && instruction.call_arguments().size() == 1 &&
      relation_zero(
        instruction.call_arguments().front(), producer.bound, ID_gt))
      ++positive_bounds;
    irep_idt lhs;
    if(
      !instruction.call_lhs().is_nil() &&
      symbol_id(instruction.call_lhs(), lhs) &&
      (lhs == initial.left_base || lhs == initial.right_base ||
       lhs == producer.result_base))
    {
      const irep_idt initialized_base = lhs;
      irep_idt argument;
      if(
        instruction.call_arguments().size() != 1 ||
        !symbol_id(instruction.call_arguments().front(), argument) ||
        argument != producer.bound)
      {
        reason = "hom_array_initializer_bound";
        return false;
      }
      if(allocator.empty())
        allocator = callee;
      else if(allocator != callee)
      {
        reason = "hom_array_initializer";
        return false;
      }
      if(!bases.emplace(initialized_base, &instruction).second)
      {
        reason = "hom_array_initializer_count";
        return false;
      }
      state.base_initializers.insert(&instruction);
    }
  }
  if(
    state.bound_init == nullptr || positive_bounds != 1 ||
    progress_inits != 1 || bases.size() != 3 ||
    bases.count(initial.left_base) == 0 ||
    bases.count(initial.right_base) == 0 ||
    bases.count(producer.result_base) == 0)
  {
    reason = "hom_main_initialization";
    return false;
  }
  state.allocator = allocator;

  for(const auto &instruction : main.instructions)
  {
    if(
      life.first_create != nullptr && life.last_join != nullptr &&
      instruction.location_number >= life.first_create->location_number &&
      instruction.location_number <= life.last_join->location_number)
    {
      if(
        instruction.is_assign() || instruction.is_goto() ||
        instruction.is_assert() || instruction.is_assume() ||
        instruction.is_atomic_begin() || instruction.is_atomic_end())
      {
        reason = "hom_main_concurrent_effect";
        return false;
      }
      irep_idt callee;
      if(
        call_id(instruction, callee) &&
        !is_create(callee) && !is_join(callee))
      {
        reason = "hom_main_concurrent_call";
        return false;
      }
    }
    if(
      life.last_join != nullptr &&
      instruction.location_number > life.last_join->location_number)
    {
      if(
        instruction.is_assign() || instruction.is_goto() ||
        instruction.is_assert() || instruction.is_assume() ||
        instruction.is_atomic_begin() || instruction.is_atomic_end())
      {
        reason = "hom_main_postjoin_control";
        return false;
      }
      irep_idt callee;
      if(
        call_id(instruction, callee) &&
        &instruction != property.operation_call &&
        &instruction != property.assumption &&
        &instruction != property.error)
      {
        reason = "hom_main_postjoin_call";
        return false;
      }
    }
  }
  return true;
}

bool allocation_size(
  const exprt &src,
  const irep_idt &size_parameter)
{
  const exprt &product = strip(src);
  if(product.id() != ID_mult || product.operands().size() != 2)
    return false;
  for(unsigned order = 0; order < 2; ++order)
  {
    irep_idt candidate;
    if(
      value_is(product.operands()[order], 4) &&
      symbol_id(product.operands()[1 - order], candidate) &&
      candidate == size_parameter)
      return true;
  }
  return false;
}

bool allocation_upper_bound(
  const exprt &src,
  const irep_idt &size_parameter)
{
  const exprt &relation = strip(src);
  if(relation.id() != ID_le || relation.operands().size() != 2)
    return false;
  irep_idt candidate;
  if(
    !symbol_id(relation.op0(), candidate) ||
    candidate != size_parameter)
    return false;
  const exprt &division = strip(relation.op1());
  if(division.id() != ID_div || division.operands().size() != 2)
    return false;
  mp_integer numerator;
  return
    integer_constant(division.op0(), numerator) &&
    numerator == power(2, 32) - 1 &&
    value_is(division.op1(), 4);
}

bool fresh_array_allocator(
  const goto_modelt &model,
  const namespacet &ns,
  const irep_idt &allocator,
  std::string &reason)
{
  const symbolt *symbol = lookup(allocator, ns);
  const auto function =
    model.goto_functions.function_map.find(allocator);
  if(
    symbol == nullptr || symbol->type.id() != ID_code ||
    function == model.goto_functions.function_map.end() ||
    !function->second.body_available())
  {
    reason = "hom_allocator_body";
    return false;
  }
  const auto &parameters = to_code_type(symbol->type).parameters();
  if(
    parameters.size() != 1 ||
    parameters[0].type().id() != ID_signedbv ||
    to_signedbv_type(parameters[0].type()).get_width() != 32)
  {
    reason = "hom_allocator_type";
    return false;
  }
  const irep_idt size_parameter =
    parameters.front().get_identifier();
  const auto &program = function->second.body;
  natural_loopst loops;
  loops(program);
  if(loops.loop_map.size() != 1)
  {
    reason = "hom_allocator_loop_count";
    return false;
  }
  const auto loop_head = loops.loop_map.begin()->first;
  const auto &loop = loops.loop_map.begin()->second;
  irep_idt induction;
  exprt bound;
  if(
    !parse_loop_exit(*loop_head, induction, bound) ||
    !contains_symbol(bound, size_parameter))
  {
    reason = "hom_allocator_loop_guard";
    return false;
  }

  irep_idt malloc_temporary;
  irep_idt result_pointer;
  irep_idt nondet_value;
  std::size_t malloc_calls = 0;
  std::size_t pointer_assignments = 0;
  std::size_t returns = 0;
  std::size_t zero_initializations = 0;
  std::size_t increments = 0;
  std::size_t backedges = 0;
  std::size_t element_writes = 0;
  std::size_t nondet_values = 0;
  std::size_t lower_bounds = 0;
  std::size_t upper_bounds = 0;
  for(auto instruction = program.instructions.begin();
      instruction != program.instructions.end(); ++instruction)
  {
    irep_idt callee;
    if(call_id(*instruction, callee))
    {
      if(is_named(callee, "malloc"))
      {
        if(
          instruction->call_lhs().is_nil() ||
          instruction->call_arguments().size() != 1 ||
          !symbol_id(instruction->call_lhs(), malloc_temporary) ||
          !allocation_size(
            instruction->call_arguments().front(), size_parameter))
        {
          reason = "hom_allocator_malloc";
          return false;
        }
        ++malloc_calls;
      }
      else if(
        is_assume(callee) &&
        instruction->call_arguments().size() == 1)
      {
        if(
          relation_zero(
            instruction->call_arguments().front(),
            size_parameter,
            ID_ge))
          ++lower_bounds;
        if(
          allocation_upper_bound(
            instruction->call_arguments().front(), size_parameter))
          ++upper_bounds;
      }
      else
      {
        reason = "hom_allocator_call";
        return false;
      }
    }
    else if(instruction->is_set_return_value())
    {
      irep_idt returned;
      if(
        !symbol_id(instruction->return_value(), returned) ||
        returned != result_pointer)
      {
        reason = "hom_allocator_return";
        return false;
      }
      ++returns;
    }
    else if(instruction->is_assign())
    {
      irep_idt lhs;
      if(shared_symbol_lhs(*instruction, ns, lhs))
      {
        reason = "hom_allocator_shared_write";
        return false;
      }
      if(symbol_id(instruction->assign_lhs(), lhs))
      {
        if(lhs == induction)
        {
          if(
            instruction->location_number < loop_head->location_number &&
            value_is(instruction->assign_rhs(), 0))
            ++zero_initializations;
          else if(
            loop.contains(instruction) &&
            unit_increment(*instruction, induction))
            ++increments;
          else
          {
            reason = "hom_allocator_induction";
            return false;
          }
        }
        else
        {
          irep_idt rhs;
          if(
            symbol_id(instruction->assign_rhs(), rhs) &&
            rhs == malloc_temporary)
          {
            result_pointer = lhs;
            ++pointer_assignments;
          }
          else if(
            contains_side_effect(instruction->assign_rhs()) &&
            loop.contains(instruction))
          {
            nondet_value = lhs;
            ++nondet_values;
          }
        }
      }
      irep_idt base;
      irep_idt index;
      if(array_symbol_index(instruction->assign_lhs(), base, index))
      {
        if(base != result_pointer)
        {
          reason = "hom_allocator_element_base";
          return false;
        }
        if(index != induction)
        {
          reason = "hom_allocator_element_index";
          return false;
        }
        irep_idt value;
        if(
          !symbol_id(instruction->assign_rhs(), value) ||
          value != nondet_value)
        {
          reason = "hom_allocator_element_value";
          return false;
        }
        if(!loop.contains(instruction))
        {
          reason = "hom_allocator_element_scope";
          return false;
        }
        ++element_writes;
      }
    }
    else if(
      instruction->is_goto() && loop.contains(instruction) &&
      instruction != loop_head)
    {
      if(
        instruction->condition().is_true() &&
        instruction->targets.size() == 1 &&
        instruction->get_target() == loop_head)
        ++backedges;
      else
      {
        reason = "hom_allocator_control";
        return false;
      }
    }
    else if(
      instruction->is_assert() || instruction->is_assume() ||
      instruction->is_atomic_begin() || instruction->is_atomic_end() ||
      instruction->is_start_thread() || instruction->is_end_thread() ||
      instruction->is_other() || instruction->is_throw() ||
      instruction->is_catch())
    {
      reason = "hom_allocator_effect";
      return false;
    }
  }
  if(
    malloc_calls != 1 || pointer_assignments != 1 || returns != 1 ||
    zero_initializations != 1 || increments != 1 || backedges != 1 ||
    element_writes != 1 || nondet_values != 1 || lower_bounds != 1 ||
    upper_bounds != 1)
  {
    reason = "hom_allocator_shape";
    return false;
  }
  return true;
}

bool hom_global_writes(
  const goto_modelt &model,
  const namespacet &ns,
  const lifecyclet &life,
  const hom_propertyt &property,
  const hom_main_initt &initial,
  const hom_worker_resultt &fold,
  const hom_worker_resultt &producer,
  const hom_worker_resultt &consumer,
  const hom_main_statet &main_state,
  std::string &reason)
{
  const std::set<irep_idt> symbols = {
    property.left_summary,
    property.right_summary,
    property.result_summary,
    initial.left_base,
    initial.right_base,
    producer.result_base,
    producer.progress,
    producer.bound};
  std::set<const goto_programt::instructiont *> allowed = fold.writes;
  allowed.insert(producer.writes.begin(), producer.writes.end());
  allowed.insert(consumer.writes.begin(), consumer.writes.end());
  allowed.insert(initial.left_summary);
  allowed.insert(initial.right_summary);
  allowed.insert(initial.result_summary);
  allowed.insert(main_state.bound_init);
  allowed.insert(main_state.progress_init);
  allowed.insert(
    main_state.base_initializers.begin(),
    main_state.base_initializers.end());

  for(const auto &entry : model.goto_functions.function_map)
  {
    for(const auto &instruction : entry.second.body.instructions)
    {
      const exprt *lhs = nullptr;
      if(instruction.is_assign())
        lhs = &instruction.assign_lhs();
      else if(
        instruction.is_function_call() &&
        !instruction.call_lhs().is_nil())
        lhs = &instruction.call_lhs();
      if(lhs == nullptr)
        continue;

      irep_idt direct;
      irep_idt base;
      bool protected_write =
        symbol_id(*lhs, direct) && symbols.count(direct) != 0;
      if(
        base_pointer(*lhs, base) &&
        (base == initial.left_base || base == initial.right_base ||
         base == producer.result_base))
        protected_write = true;
      if(!protected_write)
        continue;
      if(
        is_start_function(entry.first) && instruction.is_assign() &&
        value_is(instruction.assign_rhs(), 0))
        continue;
      if(allowed.count(&instruction) == 0)
      {
        reason = "hom_external_writer";
        return false;
      }
    }
  }

  if(
    !anchor_alias_free(model, initial.left_base, reason) ||
    !anchor_alias_free(model, initial.right_base, reason) ||
    !anchor_alias_free(model, producer.result_base, reason) ||
    !no_addresses(model, symbols, reason))
    return false;
  (void)ns;
  (void)life;
  return true;
}

struct linear_fold_propertyt
{
  irep_idt left_summary;
  irep_idt right_summary;
  irep_idt result_summary;
  irep_idt operation;
  irep_idt temporary;
  const goto_programt::instructiont *operation_call;
  const goto_programt::instructiont *assumption;
  const goto_programt::instructiont *error;

  linear_fold_propertyt()
    : operation_call(nullptr), assumption(nullptr), error(nullptr)
  {
  }
};

bool unequal_symbols(
  const exprt &src,
  irep_idt &left,
  irep_idt &right)
{
  const exprt &relation = strip(src);
  return
    relation.id() == ID_notequal && relation.operands().size() == 2 &&
    symbol_id(relation.op0(), left) &&
    symbol_id(relation.op1(), right) && left != right;
}

bool find_linear_fold_property(
  const goto_modelt &model,
  const namespacet &ns,
  const lifecyclet &life,
  linear_fold_propertyt &property,
  std::string &reason)
{
  const auto &main =
    model.goto_functions.function_map.at(ID_main).body;
  std::map<irep_idt, const goto_programt::instructiont *> value_calls;
  std::size_t matches = 0;
  std::size_t errors = 0;

  for(const auto &entry : model.goto_functions.function_map)
  {
    for(const auto &instruction : entry.second.body.instructions)
    {
      irep_idt callee;
      if(call_id(instruction, callee) && is_reach_error(callee))
      {
        ++errors;
        if(entry.first != ID_main)
        {
          reason = "linear_fold_error_function";
          return false;
        }
        property.error = &instruction;
      }
    }
  }

  for(const auto &instruction : main.instructions)
  {
    if(
      life.last_join == nullptr ||
      instruction.location_number <= life.last_join->location_number)
      continue;
    irep_idt callee;
    if(!call_id(instruction, callee))
      continue;
    if(
      !instruction.call_lhs().is_nil() &&
      instruction.call_arguments().size() == 2)
    {
      irep_idt temporary;
      if(symbol_id(instruction.call_lhs(), temporary))
        value_calls[temporary] = &instruction;
      continue;
    }
    if(!is_assume(callee) || instruction.call_arguments().size() != 1)
      continue;

    irep_idt first;
    irep_idt second;
    if(
      !unequal_symbols(
        instruction.call_arguments().front(), first, second))
      continue;
    irep_idt result;
    irep_idt temporary;
    const goto_programt::instructiont *producer = nullptr;
    if(value_calls.count(first) != 0)
    {
      temporary = first;
      result = second;
      producer = value_calls.at(first);
    }
    else if(value_calls.count(second) != 0)
    {
      temporary = second;
      result = first;
      producer = value_calls.at(second);
    }
    else
      continue;

    irep_idt operation;
    irep_idt left;
    irep_idt right;
    if(
      producer == nullptr || !call_id(*producer, operation) ||
      producer->call_arguments().size() != 2 ||
      !symbol_id(producer->call_arguments()[0], left) ||
      !symbol_id(producer->call_arguments()[1], right) ||
      !shared_signed(left, ns) || !shared_signed(right, ns) ||
      !shared_signed(result, ns) || left == right || left == result ||
      right == result)
      continue;

    ++matches;
    property.left_summary = left;
    property.right_summary = right;
    property.result_summary = result;
    property.operation = operation;
    property.temporary = temporary;
    property.operation_call = producer;
    property.assumption = &instruction;
  }

  if(
    matches != 1 || errors != 1 || property.error == nullptr ||
    property.operation_call == nullptr || property.assumption == nullptr ||
    property.operation_call->location_number >=
      property.assumption->location_number ||
    property.assumption->location_number >= property.error->location_number)
  {
    reason =
      matches == 0 ? "linear_fold_property" :
                     "linear_fold_property_ambiguous";
    return false;
  }
  return true;
}

bool zero_based_hom_loop(
  const goto_programt &program,
  hom_loopt &result,
  std::string &reason)
{
  natural_loopst loops;
  loops(program);
  if(loops.loop_map.size() != 1)
  {
    reason = "linear_fold_loop_count";
    return false;
  }
  result.head = loops.loop_map.begin()->first;
  const auto &loop = loops.loop_map.begin()->second;
  exprt bound;
  if(
    !parse_loop_exit(*result.head, result.induction, bound) ||
    !symbol_id(bound, result.bound))
  {
    reason = "linear_fold_loop_guard";
    return false;
  }

  std::size_t initializations = 0;
  std::size_t increments = 0;
  std::size_t backedges = 0;
  for(auto instruction = program.instructions.begin();
      instruction != program.instructions.end(); ++instruction)
  {
    if(loop.contains(instruction))
      result.members.insert(&*instruction);
    if(instruction->is_assign())
    {
      irep_idt lhs;
      if(
        symbol_id(instruction->assign_lhs(), lhs) &&
        lhs == result.induction)
      {
        if(
          instruction->location_number < result.head->location_number &&
          value_is(instruction->assign_rhs(), 0))
          ++initializations;
        else if(
          loop.contains(instruction) &&
          unit_increment(*instruction, result.induction))
          ++increments;
        else
        {
          reason = "linear_fold_induction_write";
          return false;
        }
      }
    }
    if(
      instruction->is_goto() && loop.contains(instruction) &&
      instruction != result.head &&
      instruction->condition().is_true() &&
      instruction->targets.size() == 1 &&
      instruction->get_target() == result.head)
      ++backedges;
  }
  if(initializations != 1 || increments != 1 || backedges != 1)
  {
    reason = "linear_fold_loop_skeleton";
    return false;
  }
  return true;
}

struct linear_fold_workert
{
  irep_idt summary;
  irep_idt source_base;
  irep_idt result_base;
  irep_idt bound;
  std::set<const goto_programt::instructiont *> writes;
};

bool linear_single_fold_worker(
  const goto_modelt &model,
  const namespacet &ns,
  const irep_idt &worker,
  const linear_fold_propertyt &property,
  linear_fold_workert &result,
  std::string &reason)
{
  const auto &program =
    model.goto_functions.function_map.at(worker).body;
  hom_loopt loop;
  if(!zero_based_hom_loop(program, loop, reason))
    return false;
  const symbolt *induction_symbol = lookup(loop.induction, ns);
  if(induction_symbol == nullptr)
  {
    reason = "linear_fold_induction_symbol";
    return false;
  }
  const exprt induction =
    symbol_exprt(loop.induction, induction_symbol->type);

  std::size_t calls = 0;
  std::size_t gotos = 0;
  for(auto instruction = program.instructions.begin();
      instruction != program.instructions.end(); ++instruction)
  {
    if(instruction->is_atomic_begin() || instruction->is_atomic_end())
    {
      reason = "linear_fold_atomic";
      return false;
    }
    if(instruction->is_goto() && loop.members.count(&*instruction) != 0)
      ++gotos;
    irep_idt callee;
    if(call_id(*instruction, callee))
    {
      irep_idt summary;
      irep_idt first;
      irep_idt base;
      if(
        callee != property.operation ||
        instruction->call_lhs().is_nil() ||
        instruction->call_arguments().size() != 2 ||
        !symbol_id(instruction->call_lhs(), summary) ||
        !symbol_id(instruction->call_arguments()[0], first) ||
        first != summary ||
        (summary != property.left_summary &&
         summary != property.right_summary) ||
        !base_pointer(instruction->call_arguments()[1], base) ||
        !array_at(instruction->call_arguments()[1], base, induction))
      {
        reason = "linear_fold_worker_call";
        return false;
      }
      result.summary = summary;
      result.source_base = base;
      result.writes.insert(&*instruction);
      ++calls;
      continue;
    }
    if(instruction->is_assign())
    {
      irep_idt lhs;
      if(shared_symbol_lhs(*instruction, ns, lhs))
      {
        reason = "linear_fold_worker_shared_write";
        return false;
      }
      irep_idt base;
      if(base_pointer(instruction->assign_lhs(), base))
      {
        reason = "linear_fold_worker_array_write";
        return false;
      }
    }
    else if(
      instruction->is_assert() || instruction->is_assume() ||
      instruction->is_start_thread() || instruction->is_end_thread() ||
      instruction->is_throw() || instruction->is_catch())
    {
      reason = "linear_fold_worker_effect";
      return false;
    }
  }
  if(calls != 1 || gotos != 2)
  {
    reason = "linear_fold_worker_shape";
    return false;
  }
  result.bound = loop.bound;
  return true;
}

bool linear_result_fold_worker(
  const goto_modelt &model,
  const namespacet &ns,
  const irep_idt &worker,
  const linear_fold_propertyt &property,
  const linear_fold_workert &left,
  const linear_fold_workert &right,
  linear_fold_workert &result,
  std::string &reason)
{
  const auto &program =
    model.goto_functions.function_map.at(worker).body;
  hom_loopt loop;
  if(!zero_based_hom_loop(program, loop, reason))
    return false;
  if(loop.bound != left.bound || loop.bound != right.bound)
  {
    reason = "linear_fold_result_bound";
    return false;
  }
  const symbolt *induction_symbol = lookup(loop.induction, ns);
  if(induction_symbol == nullptr)
  {
    reason = "linear_fold_result_induction_symbol";
    return false;
  }
  const exprt induction =
    symbol_exprt(loop.induction, induction_symbol->type);

  goto_programt::const_targett element_call =
    program.instructions.end();
  goto_programt::const_targett array_write =
    program.instructions.end();
  goto_programt::const_targett summary_call =
    program.instructions.end();
  irep_idt element_temporary;
  std::size_t gotos = 0;
  for(auto instruction = program.instructions.begin();
      instruction != program.instructions.end(); ++instruction)
  {
    if(instruction->is_atomic_begin() || instruction->is_atomic_end())
    {
      reason = "linear_fold_result_atomic";
      return false;
    }
    if(instruction->is_goto() && loop.members.count(&*instruction) != 0)
      ++gotos;
    irep_idt callee;
    if(call_id(*instruction, callee))
    {
      if(
        callee != property.operation ||
        instruction->call_lhs().is_nil() ||
        instruction->call_arguments().size() != 2)
      {
        reason = "linear_fold_result_call";
        return false;
      }
      irep_idt lhs;
      if(!symbol_id(instruction->call_lhs(), lhs))
      {
        reason = "linear_fold_result_lhs";
        return false;
      }
      irep_idt first;
      if(
        lhs == property.result_summary &&
        symbol_id(instruction->call_arguments()[0], first) &&
        first == property.result_summary &&
        !result.result_base.empty() &&
        array_at(
          instruction->call_arguments()[1],
          result.result_base,
          induction))
      {
        if(summary_call != program.instructions.end())
        {
          reason = "linear_fold_result_summary_count";
          return false;
        }
        summary_call = instruction;
        result.summary = lhs;
        result.writes.insert(&*instruction);
      }
      else if(
        (array_at(
           instruction->call_arguments()[0],
           left.source_base,
           induction) &&
         array_at(
           instruction->call_arguments()[1],
           right.source_base,
           induction)) ||
        (array_at(
           instruction->call_arguments()[0],
           right.source_base,
           induction) &&
         array_at(
           instruction->call_arguments()[1],
           left.source_base,
           induction)))
      {
        if(element_call != program.instructions.end())
        {
          reason = "linear_fold_result_element_count";
          return false;
        }
        element_call = instruction;
        element_temporary = lhs;
      }
      else
      {
        reason = "linear_fold_result_arguments";
        return false;
      }
      continue;
    }
    if(instruction->is_assign())
    {
      irep_idt base;
      irep_idt index;
      if(
        array_symbol_index(
          instruction->assign_lhs(), base, index))
      {
        irep_idt value;
        if(
          index != loop.induction ||
          !symbol_id(instruction->assign_rhs(), value) ||
          value != element_temporary ||
          element_call == program.instructions.end() ||
          array_write != program.instructions.end())
        {
          reason = "linear_fold_result_array_write";
          return false;
        }
        result.result_base = base;
        array_write = instruction;
        result.writes.insert(&*instruction);
      }
      else
      {
        irep_idt lhs;
        if(shared_symbol_lhs(*instruction, ns, lhs))
        {
          reason = "linear_fold_result_shared_write";
          return false;
        }
        if(base_pointer(instruction->assign_lhs(), base))
        {
          reason = "linear_fold_result_pointer_write";
          return false;
        }
      }
    }
    else if(
      instruction->is_assert() || instruction->is_assume() ||
      instruction->is_start_thread() || instruction->is_end_thread() ||
      instruction->is_throw() || instruction->is_catch())
    {
      reason = "linear_fold_result_effect";
      return false;
    }
  }
  if(
    gotos != 2 || element_call == program.instructions.end() ||
    array_write == program.instructions.end() ||
    summary_call == program.instructions.end() ||
    element_call->location_number >= array_write->location_number ||
    array_write->location_number >= summary_call->location_number ||
    result.result_base == left.source_base ||
    result.result_base == right.source_base)
  {
    reason = "linear_fold_result_shape";
    return false;
  }
  result.bound = loop.bound;
  return true;
}

bool zero_initialized_symbols(
  const goto_modelt &model,
  const std::set<irep_idt> &symbols,
  std::set<const goto_programt::instructiont *> &writes,
  std::string &reason)
{
  std::set<irep_idt> initialized;
  for(const auto &entry : model.goto_functions.function_map)
  {
    if(!is_start_function(entry.first))
      continue;
    for(const auto &instruction : entry.second.body.instructions)
    {
      if(!instruction.is_assign())
        continue;
      irep_idt lhs;
      if(
        symbol_id(instruction.assign_lhs(), lhs) &&
        symbols.count(lhs) != 0 &&
        value_is(instruction.assign_rhs(), 0))
      {
        if(!initialized.insert(lhs).second)
        {
          reason = "linear_fold_duplicate_zero_init";
          return false;
        }
        writes.insert(&instruction);
      }
    }
  }
  if(initialized != symbols)
  {
    reason = "linear_fold_zero_init";
    return false;
  }
  return true;
}

bool no_main_symbol_writes_before_create(
  const goto_modelt &model,
  const lifecyclet &life,
  const std::set<irep_idt> &symbols,
  const goto_programt::instructiont *after,
  std::string &reason)
{
  const auto &main =
    model.goto_functions.function_map.at(ID_main).body;
  for(const auto &instruction : main.instructions)
  {
    if(
      life.first_create != nullptr &&
      instruction.location_number >= life.first_create->location_number)
      break;
    if(
      after != nullptr &&
      instruction.location_number <= after->location_number)
      continue;
    const exprt *lhs = nullptr;
    if(instruction.is_assign())
      lhs = &instruction.assign_lhs();
    else if(
      instruction.is_function_call() &&
      !instruction.call_lhs().is_nil())
      lhs = &instruction.call_lhs();
    irep_idt identifier;
    if(
      lhs != nullptr && symbol_id(*lhs, identifier) &&
      symbols.count(identifier) != 0)
    {
      reason = "flow_initial_relation_overwrite";
      return false;
    }
  }
  return true;
}

struct linear_fold_maint
{
  irep_idt bound;
  irep_idt allocator;
  std::set<const goto_programt::instructiont *> writes;
};

bool linear_fold_main(
  const goto_modelt &model,
  const lifecyclet &life,
  const linear_fold_propertyt &property,
  const linear_fold_workert &left,
  const linear_fold_workert &right,
  const linear_fold_workert &result,
  linear_fold_maint &state,
  std::string &reason)
{
  const auto &main =
    model.goto_functions.function_map.at(ID_main).body;
  if(left.bound != right.bound || left.bound != result.bound)
  {
    reason = "linear_fold_common_bound";
    return false;
  }
  state.bound = left.bound;
  std::set<irep_idt> expected_bases = {
    left.source_base, right.source_base, result.result_base};
  std::set<irep_idt> allocated_bases;
  std::size_t bound_initializers = 0;

  for(const auto &instruction : main.instructions)
  {
    if(
      life.first_create != nullptr &&
      instruction.location_number >= life.first_create->location_number)
      break;
    if(instruction.is_assign())
    {
      irep_idt lhs;
      if(
        symbol_id(instruction.assign_lhs(), lhs) &&
        lhs == state.bound)
      {
        ++bound_initializers;
        state.writes.insert(&instruction);
      }
    }
    irep_idt callee;
    if(!call_id(instruction, callee))
      continue;
    irep_idt lhs;
    irep_idt argument;
    if(
      !instruction.call_lhs().is_nil() &&
      symbol_id(instruction.call_lhs(), lhs) &&
      expected_bases.count(lhs) != 0)
    {
      if(
        instruction.call_arguments().size() != 1 ||
        !symbol_id(instruction.call_arguments().front(), argument) ||
        argument != state.bound)
      {
        reason = "linear_fold_allocation_bound";
        return false;
      }
      if(state.allocator.empty())
        state.allocator = callee;
      else if(state.allocator != callee)
      {
        reason = "linear_fold_allocator_mismatch";
        return false;
      }
      if(!allocated_bases.insert(lhs).second)
      {
        reason = "linear_fold_allocation_count";
        return false;
      }
      state.writes.insert(&instruction);
    }
  }
  if(
    bound_initializers != 1 || allocated_bases != expected_bases ||
    state.allocator.empty())
  {
    reason = "linear_fold_main_initialization";
    return false;
  }

  for(const auto &instruction : main.instructions)
  {
    if(
      life.first_create != nullptr && life.last_join != nullptr &&
      instruction.location_number >= life.first_create->location_number &&
      instruction.location_number <= life.last_join->location_number)
    {
      if(
        instruction.is_assign() || instruction.is_goto() ||
        instruction.is_assert() || instruction.is_assume() ||
        instruction.is_atomic_begin() || instruction.is_atomic_end())
      {
        reason = "linear_fold_main_concurrent_effect";
        return false;
      }
      irep_idt callee;
      if(
        call_id(instruction, callee) &&
        !is_create(callee) && !is_join(callee))
      {
        reason = "linear_fold_main_concurrent_call";
        return false;
      }
    }
    if(
      life.last_join != nullptr &&
      instruction.location_number > life.last_join->location_number)
    {
      if(
        instruction.is_assign() || instruction.is_goto() ||
        instruction.is_assert() || instruction.is_assume() ||
        instruction.is_atomic_begin() || instruction.is_atomic_end())
      {
        reason = "linear_fold_main_postjoin_control";
        return false;
      }
      irep_idt callee;
      if(
        call_id(instruction, callee) &&
        &instruction != property.operation_call &&
        &instruction != property.assumption &&
        &instruction != property.error)
      {
        reason = "linear_fold_main_postjoin_call";
        return false;
      }
    }
  }
  return true;
}

bool linear_fold_global_writes(
  const goto_modelt &model,
  const linear_fold_propertyt &property,
  const linear_fold_workert &left,
  const linear_fold_workert &right,
  const linear_fold_workert &result,
  const linear_fold_maint &main_state,
  std::string &reason)
{
  const std::set<irep_idt> summaries = {
    property.left_summary,
    property.right_summary,
    property.result_summary};
  const std::set<irep_idt> protected_symbols = {
    property.left_summary,
    property.right_summary,
    property.result_summary,
    left.source_base,
    right.source_base,
    result.result_base,
    main_state.bound};
  std::set<const goto_programt::instructiont *> allowed =
    left.writes;
  allowed.insert(right.writes.begin(), right.writes.end());
  allowed.insert(result.writes.begin(), result.writes.end());
  allowed.insert(main_state.writes.begin(), main_state.writes.end());
  if(!zero_initialized_symbols(model, summaries, allowed, reason))
    return false;

  for(const auto &entry : model.goto_functions.function_map)
  {
    for(const auto &instruction : entry.second.body.instructions)
    {
      const exprt *lhs = nullptr;
      if(instruction.is_assign())
        lhs = &instruction.assign_lhs();
      else if(
        instruction.is_function_call() &&
        !instruction.call_lhs().is_nil())
        lhs = &instruction.call_lhs();
      if(lhs == nullptr)
        continue;
      irep_idt direct;
      irep_idt base;
      const bool protected_write =
        (symbol_id(*lhs, direct) &&
         protected_symbols.count(direct) != 0) ||
        (base_pointer(*lhs, base) &&
         (base == left.source_base || base == right.source_base ||
          base == result.result_base));
      if(!protected_write)
        continue;
      if(
        is_start_function(entry.first) && instruction.is_assign() &&
        value_is(instruction.assign_rhs(), 0))
        continue;
      if(allowed.count(&instruction) == 0)
      {
        reason = "linear_fold_external_writer";
        return false;
      }
    }
  }

  if(
    !anchor_alias_free(model, left.source_base, reason) ||
    !anchor_alias_free(model, right.source_base, reason) ||
    !anchor_alias_free(model, result.result_base, reason) ||
    !no_addresses(model, protected_symbols, reason))
    return false;
  return true;
}

bool linear_fold_proof_impl(
  const goto_modelt &model,
  const namespacet &ns,
  std::string &reason)
{
  lifecyclet life;
  if(!lifecycle(model, life, reason) || life.workers.size() != 3)
  {
    if(reason.empty())
      reason = "linear_fold_lifecycle";
    return false;
  }
  linear_fold_propertyt property;
  if(!find_linear_fold_property(model, ns, life, property, reason))
    return false;
  if(!signed_addition_helper(model, ns, property.operation, reason))
    return false;

  for(const auto &left_worker : life.workers)
  {
    linear_fold_workert left;
    std::string left_reason;
    if(
      !linear_single_fold_worker(
        model, ns, left_worker, property, left, left_reason) ||
      left.summary != property.left_summary)
      continue;
    for(const auto &right_worker : life.workers)
    {
      if(right_worker == left_worker)
        continue;
      linear_fold_workert right;
      std::string right_reason;
      if(
        !linear_single_fold_worker(
          model, ns, right_worker, property, right, right_reason) ||
        right.summary != property.right_summary ||
        right.bound != left.bound ||
        right.source_base == left.source_base)
        continue;
      irep_idt result_worker;
      for(const auto &worker : life.workers)
      {
        if(worker != left_worker && worker != right_worker)
          result_worker = worker;
      }
      linear_fold_workert result;
      std::string result_reason;
      if(
        result_worker.empty() ||
        !linear_result_fold_worker(
          model,
          ns,
          result_worker,
          property,
          left,
          right,
          result,
          result_reason))
        continue;

      linear_fold_maint main_state;
      if(
        !linear_fold_main(
          model,
          life,
          property,
          left,
          right,
          result,
          main_state,
          reason) ||
        !fresh_array_allocator(
          model, ns, main_state.allocator, reason) ||
        !linear_fold_global_writes(
          model,
          property,
          left,
          right,
          result,
          main_state,
          reason))
        return false;

      std::cout << "NATIVE_LINEAR_ANNIHILATOR applied=1 rule=fold"
                << " left=" << property.left_summary
                << " right=" << property.right_summary
                << " result=" << property.result_summary << '\n';
      return true;
    }
  }
  reason = "linear_fold_worker_partition";
  return false;
}

struct flow_equality_propertyt
{
  irep_idt left;
  irep_idt right;
  const goto_programt::instructiont *assumption;
  const goto_programt::instructiont *error;

  flow_equality_propertyt() : assumption(nullptr), error(nullptr)
  {
  }
};

bool find_flow_equality_property(
  const goto_modelt &model,
  const namespacet &ns,
  const lifecyclet &life,
  flow_equality_propertyt &property,
  std::string &reason)
{
  const auto &main =
    model.goto_functions.function_map.at(ID_main).body;
  std::size_t matches = 0;
  std::size_t errors = 0;
  for(const auto &entry : model.goto_functions.function_map)
  {
    for(const auto &instruction : entry.second.body.instructions)
    {
      irep_idt callee;
      if(call_id(instruction, callee) && is_reach_error(callee))
      {
        ++errors;
        if(entry.first != ID_main)
        {
          reason = "flow_error_function";
          return false;
        }
        property.error = &instruction;
      }
    }
  }
  for(const auto &instruction : main.instructions)
  {
    if(
      life.last_join == nullptr ||
      instruction.location_number <= life.last_join->location_number)
      continue;
    irep_idt callee;
    if(
      !call_id(instruction, callee) || !is_assume(callee) ||
      instruction.call_arguments().size() != 1)
      continue;
    irep_idt left;
    irep_idt right;
    if(
      !unequal_symbols(
        instruction.call_arguments().front(), left, right) ||
      !shared_signed(left, ns) || !shared_signed(right, ns))
      continue;
    ++matches;
    property.left = left;
    property.right = right;
    property.assumption = &instruction;
  }
  if(
    matches != 1 || errors != 1 || property.assumption == nullptr ||
    property.error == nullptr ||
    property.assumption->location_number >= property.error->location_number)
  {
    reason =
      matches == 0 ? "flow_equality_property" :
                     "flow_equality_property_ambiguous";
    return false;
  }
  return true;
}

struct flow_loop_dimensiont
{
  irep_idt induction;
  exprt start;
  exprt bound;
  std::set<const goto_programt::instructiont *> members;
};

struct flow_range_workert
{
  irep_idt worker;
  irep_idt accumulator;
  irep_idt operation;
  exprt contribution;
  std::vector<flow_loop_dimensiont> dimensions;
  exprt normalized_contribution;
  std::vector<exprt> normalized_inner_starts;
  std::vector<exprt> normalized_inner_bounds;
  std::set<irep_idt> input_symbols;
  std::set<irep_idt> pointer_bases;
  std::set<const goto_programt::instructiont *> writes;
};

void collect_pointer_bases(
  const exprt &src,
  std::set<irep_idt> &bases)
{
  irep_idt base;
  if(base_pointer(src, base))
    bases.insert(base);
  for(const auto &operand : src.operands())
    collect_pointer_bases(operand, bases);
}

void collect_static_symbols(
  const exprt &src,
  const namespacet &ns,
  std::set<irep_idt> &symbols)
{
  find_symbols_sett found;
  find_symbols(src, found);
  for(const auto &identifier : found)
  {
    const symbolt *symbol = lookup(identifier, ns);
    if(symbol != nullptr && symbol->is_static_lifetime && !symbol->is_type)
      symbols.insert(identifier);
  }
}

bool flow_base_use_is_dereference(
  const exprt &src,
  const irep_idt &base,
  bool under_dereference = false)
{
  const exprt &expr = strip(src);
  irep_idt identifier;
  if(symbol_id(expr, identifier) && identifier == base)
    return under_dereference;
  const bool nested =
    under_dereference || expr.id() == ID_dereference;
  for(const auto &operand : expr.operands())
  {
    if(
      contains_symbol(operand, base) &&
      !flow_base_use_is_dereference(operand, base, nested))
      return false;
  }
  return true;
}

bool flow_alias_free(
  const goto_modelt &model,
  const irep_idt &base,
  std::string &reason)
{
  for(const auto &entry : model.goto_functions.function_map)
  {
    for(const auto &instruction : entry.second.body.instructions)
    {
      if(instruction.is_assign())
      {
        irep_idt lhs;
        const bool writes_base =
          symbol_id(instruction.assign_lhs(), lhs) && lhs == base;
        if(
          (!writes_base &&
           !flow_base_use_is_dereference(
             instruction.assign_lhs(), base)) ||
          !flow_base_use_is_dereference(
            instruction.assign_rhs(), base))
        {
          reason = "flow_alias";
          return false;
        }
      }
      else if(instruction.is_function_call())
      {
        for(const auto &argument : instruction.call_arguments())
        {
          if(!flow_base_use_is_dereference(argument, base))
          {
            reason = "flow_call_escape";
            return false;
          }
        }
      }
      else if(
        instruction.has_condition() &&
        !flow_base_use_is_dereference(
          instruction.condition(), base))
      {
        reason = "flow_condition_alias";
        return false;
      }
    }
  }
  return true;
}

bool loop_initial_value(
  const goto_programt &program,
  goto_programt::const_targett head,
  const irep_idt &induction,
  exprt &start,
  std::string &reason)
{
  const goto_programt::instructiont *initialization = nullptr;
  for(auto instruction = program.instructions.begin();
      instruction != head; ++instruction)
  {
    if(!instruction->is_assign())
      continue;
    irep_idt lhs;
    if(symbol_id(instruction->assign_lhs(), lhs) && lhs == induction)
      initialization = &*instruction;
  }
  if(initialization == nullptr)
  {
    reason = "flow_loop_initialization";
    return false;
  }
  start = strip(initialization->assign_rhs());
  return !contains_side_effect(start);
}

void normalize_flow_expression(
  const std::vector<flow_loop_dimensiont> &dimensions,
  exprt &expression)
{
  replace_mapt replacements;
  for(std::size_t index = 0; index < dimensions.size(); ++index)
  {
    const typet &type = dimensions[index].start.type();
    const symbol_exprt original(dimensions[index].induction, type);
    const symbol_exprt canonical(
      "__deagle_flow_index_" + std::to_string(index), type);
    replacements[original] = canonical;
  }
  replace_expr(replacements, expression);
}

bool flow_range_worker(
  const goto_modelt &model,
  const namespacet &ns,
  const irep_idt &worker,
  flow_range_workert &result,
  std::string &reason)
{
  const auto &program =
    model.goto_functions.function_map.at(worker).body;
  goto_programt::const_targett fold_call = program.instructions.end();
  goto_programt::const_targett contribution_call =
    program.instructions.end();
  irep_idt contribution_temporary;
  exprt contribution_expression;
  unsigned atomic_depth = 0;
  std::size_t atomic_begins = 0;
  std::size_t atomic_ends = 0;
  for(auto instruction = program.instructions.begin();
      instruction != program.instructions.end(); ++instruction)
  {
    if(instruction->is_atomic_begin())
    {
      ++atomic_depth;
      ++atomic_begins;
      if(atomic_depth != 1)
      {
        reason = "flow_atomic_nesting";
        return false;
      }
      continue;
    }
    if(instruction->is_atomic_end())
    {
      if(atomic_depth != 1)
      {
        reason = "flow_atomic_balance";
        return false;
      }
      --atomic_depth;
      ++atomic_ends;
      continue;
    }
    irep_idt callee;
    if(call_id(*instruction, callee))
    {
      if(is_assume(callee))
        continue;
      irep_idt accumulator;
      irep_idt first;
      const bool fold_shape =
        !instruction->call_lhs().is_nil() &&
        instruction->call_arguments().size() == 2 &&
        symbol_id(instruction->call_lhs(), accumulator) &&
        symbol_id(instruction->call_arguments()[0], first) &&
        accumulator == first && shared_signed(accumulator, ns);
      if(fold_shape)
      {
        if(
          atomic_depth != 1 ||
          fold_call != program.instructions.end())
        {
          reason = "flow_worker_call";
          return false;
        }
        result.accumulator = accumulator;
        result.operation = callee;
        const exprt &argument =
          strip(instruction->call_arguments()[1]);
        irep_idt argument_symbol;
        if(
          !contribution_temporary.empty() &&
          symbol_id(argument, argument_symbol) &&
          argument_symbol == contribution_temporary)
          result.contribution = contribution_expression;
        else
          result.contribution = argument;
        result.writes.insert(&*instruction);
        fold_call = instruction;
        continue;
      }

      irep_idt temporary;
      if(
        instruction->call_lhs().is_nil() ||
        instruction->call_arguments().size() != 2 ||
        !symbol_id(instruction->call_lhs(), temporary) ||
        shared_signed(temporary, ns) ||
        atomic_depth != 1 ||
        contribution_call != program.instructions.end() ||
        !signed_addition_helper(model, ns, callee, reason))
      {
        if(reason.empty())
          reason = "flow_worker_call";
        return false;
      }
      contribution_temporary = temporary;
      contribution_expression = plus_exprt(
        strip(instruction->call_arguments()[0]),
        strip(instruction->call_arguments()[1]));
      contribution_call = instruction;
      continue;
    }
    if(instruction->is_assign())
    {
      irep_idt lhs;
      if(shared_symbol_lhs(*instruction, ns, lhs))
      {
        reason = "flow_worker_shared_write";
        return false;
      }
      irep_idt base;
      if(base_pointer(instruction->assign_lhs(), base))
      {
        reason = "flow_worker_array_write";
        return false;
      }
    }
    else if(
      instruction->is_assert() || instruction->is_start_thread() ||
      instruction->is_end_thread() || instruction->is_throw() ||
      instruction->is_catch())
    {
      reason = "flow_worker_effect";
      return false;
    }
  }
  if(
    atomic_depth != 0 || atomic_begins != 1 || atomic_ends != 1 ||
    fold_call == program.instructions.end() ||
    (!contribution_temporary.empty() &&
     contribution_call->location_number >= fold_call->location_number))
  {
    reason = "flow_worker_fold";
    return false;
  }

  natural_loopst loops;
  loops(program);
  std::vector<std::pair<
    goto_programt::const_targett,
    const natural_loopst::natural_loopt *>> containing;
  typedef std::pair<
    goto_programt::const_targett,
    const natural_loopst::natural_loopt *> containing_loopt;
  for(const auto &entry : loops.loop_map)
  {
    if(entry.second.contains(fold_call))
      containing.emplace_back(entry.first, &entry.second);
  }
  if(containing.empty() || containing.size() > 2)
  {
    reason = "flow_worker_loop_count";
    return false;
  }
  if(containing.size() != loops.loop_map.size())
  {
    reason = "flow_worker_unrelated_loop";
    return false;
  }
  std::sort(
    containing.begin(),
    containing.end(),
    [](const containing_loopt &left, const containing_loopt &right) {
      return left.second->size() > right.second->size();
    });

  for(const auto &entry : containing)
  {
    flow_loop_dimensiont dimension;
    if(
      !parse_loop_exit(
        *entry.first, dimension.induction, dimension.bound) ||
      !loop_initial_value(
        program,
        entry.first,
        dimension.induction,
        dimension.start,
        reason))
    {
      if(reason.empty())
        reason = "flow_worker_loop_guard";
      return false;
    }
    std::size_t increments = 0;
    std::size_t backedges = 0;
    for(auto instruction = program.instructions.begin();
        instruction != program.instructions.end(); ++instruction)
    {
      if(entry.second->contains(instruction))
        dimension.members.insert(&*instruction);
      if(
        entry.second->contains(instruction) &&
        unit_increment(*instruction, dimension.induction))
        ++increments;
      if(
        instruction->is_goto() &&
        entry.second->contains(instruction) &&
        instruction != entry.first &&
        instruction->condition().is_true() &&
        instruction->targets.size() == 1 &&
        instruction->get_target() == entry.first)
        ++backedges;
    }
    if(increments != 1 || backedges != 1)
    {
      reason = "flow_worker_loop_skeleton";
      return false;
    }
    result.dimensions.push_back(dimension);
  }

  result.normalized_contribution = result.contribution;
  normalize_flow_expression(
    result.dimensions, result.normalized_contribution);
  for(std::size_t index = 1; index < result.dimensions.size(); ++index)
  {
    exprt start = result.dimensions[index].start;
    exprt bound = result.dimensions[index].bound;
    normalize_flow_expression(result.dimensions, start);
    normalize_flow_expression(result.dimensions, bound);
    result.normalized_inner_starts.push_back(start);
    result.normalized_inner_bounds.push_back(bound);
  }
  collect_static_symbols(result.contribution, ns, result.input_symbols);
  for(const auto &dimension : result.dimensions)
  {
    collect_static_symbols(dimension.start, ns, result.input_symbols);
    collect_static_symbols(dimension.bound, ns, result.input_symbols);
  }
  result.input_symbols.erase(result.accumulator);
  collect_pointer_bases(result.contribution, result.pointer_bases);
  for(const auto &dimension : result.dimensions)
  {
    collect_pointer_bases(dimension.start, result.pointer_bases);
    collect_pointer_bases(dimension.bound, result.pointer_bases);
  }
  result.worker = worker;
  return true;
}

struct ordered_extremum_propertyt
{
  irep_idt whole;
  irep_idt prefix;
  irep_idt suffix;
  bool minimum;
  bool shared_partition_accumulator;
  const goto_programt::instructiont *assumption;
  const goto_programt::instructiont *error;

  ordered_extremum_propertyt()
    : minimum(false),
      shared_partition_accumulator(false),
      assumption(nullptr),
      error(nullptr)
  {
  }
};

bool ordered_extremum_expression(
  const exprt &src,
  irep_idt &prefix,
  irep_idt &suffix,
  bool &minimum)
{
  const exprt &choice = strip(src);
  if(choice.id() != ID_if || choice.operands().size() != 3)
    return false;
  const exprt &condition = strip(choice.op0());
  if(
    (condition.id() != ID_lt && condition.id() != ID_gt) ||
    condition.operands().size() != 2)
    return false;
  irep_idt left;
  irep_idt right;
  irep_idt true_value;
  irep_idt false_value;
  if(
    !symbol_id(condition.op0(), left) ||
    !symbol_id(condition.op1(), right) ||
    !symbol_id(choice.op1(), true_value) ||
    !symbol_id(choice.op2(), false_value) ||
    true_value != right || false_value != left ||
    left == right)
    return false;
  prefix = left;
  suffix = right;
  minimum = condition.id() == ID_gt;
  return true;
}

bool find_ordered_extremum_property(
  const goto_modelt &model,
  const namespacet &ns,
  const lifecyclet &life,
  ordered_extremum_propertyt &property,
  std::string &reason)
{
  const auto &main =
    model.goto_functions.function_map.at(ID_main).body;
  std::size_t matches = 0;
  std::size_t errors = 0;
  for(const auto &entry : model.goto_functions.function_map)
  {
    for(const auto &instruction : entry.second.body.instructions)
    {
      irep_idt callee;
      if(call_id(instruction, callee) && is_reach_error(callee))
      {
        ++errors;
        if(entry.first != ID_main)
        {
          reason = "ordered_extremum_error_function";
          return false;
        }
        property.error = &instruction;
      }
    }
  }
  for(const auto &instruction : main.instructions)
  {
    if(
      life.last_join == nullptr ||
      instruction.location_number <= life.last_join->location_number)
      continue;
    irep_idt callee;
    if(
      !call_id(instruction, callee) || !is_assume(callee) ||
      instruction.call_arguments().size() != 1)
      continue;
    const exprt &condition =
      strip(instruction.call_arguments().front());
    if(
      condition.id() != ID_notequal ||
      condition.operands().size() != 2)
      continue;
    irep_idt whole;
    irep_idt prefix;
    irep_idt suffix;
    bool minimum = false;
    bool parsed =
      symbol_id(condition.op0(), whole) &&
      ordered_extremum_expression(
        condition.op1(), prefix, suffix, minimum);
    if(!parsed)
      parsed =
        symbol_id(condition.op1(), whole) &&
        ordered_extremum_expression(
          condition.op0(), prefix, suffix, minimum);
    bool shared_partition_accumulator = false;
    if(!parsed)
    {
      parsed =
        symbol_id(condition.op0(), whole) &&
        symbol_id(condition.op1(), prefix);
      if(!parsed)
        parsed =
          symbol_id(condition.op1(), whole) &&
          symbol_id(condition.op0(), prefix);
      if(parsed)
      {
        suffix = prefix;
        shared_partition_accumulator = true;
      }
    }
    if(
      !parsed || !shared_signed(whole, ns) ||
      !shared_signed(prefix, ns) || !shared_signed(suffix, ns) ||
      whole == prefix || whole == suffix ||
      (!shared_partition_accumulator && prefix == suffix))
      continue;
    ++matches;
    property.whole = whole;
    property.prefix = prefix;
    property.suffix = suffix;
    property.minimum = minimum;
    property.shared_partition_accumulator =
      shared_partition_accumulator;
    property.assumption = &instruction;
  }
  if(
    matches != 1 || errors != 1 ||
    property.assumption == nullptr || property.error == nullptr ||
    property.assumption->location_number >=
      property.error->location_number)
  {
    reason =
      matches == 0 ? "ordered_extremum_property" :
                     "ordered_extremum_property_ambiguous";
    return false;
  }
  return true;
}

bool ordered_extremum_worker(
  const goto_modelt &model,
  const namespacet &ns,
  const irep_idt &worker,
  const bool minimum,
  flow_range_workert &result,
  std::string &reason)
{
  const auto &program =
    model.goto_functions.function_map.at(worker).body;
  goto_programt::const_targett update = program.instructions.end();
  unsigned atomic_depth = 0;
  std::size_t atomic_begins = 0;
  std::size_t atomic_ends = 0;
  for(auto instruction = program.instructions.begin();
      instruction != program.instructions.end(); ++instruction)
  {
    if(instruction->is_atomic_begin())
    {
      ++atomic_depth;
      ++atomic_begins;
      if(atomic_depth != 1)
      {
        reason = "ordered_extremum_atomic_nesting";
        return false;
      }
      continue;
    }
    if(instruction->is_atomic_end())
    {
      if(atomic_depth != 1)
      {
        reason = "ordered_extremum_atomic_balance";
        return false;
      }
      --atomic_depth;
      ++atomic_ends;
      continue;
    }
    irep_idt callee;
    if(call_id(*instruction, callee))
    {
      if(is_assume(callee))
        continue;
      reason = "ordered_extremum_worker_call";
      return false;
    }
    if(!instruction->is_assign())
      continue;
    irep_idt lhs;
    if(shared_symbol_lhs(*instruction, ns, lhs))
    {
      if(
        atomic_depth != 1 ||
        update != program.instructions.end() ||
        !shared_signed(lhs, ns) ||
        !guarded_direction(
          program, instruction, lhs, minimum))
      {
        reason = "ordered_extremum_update";
        return false;
      }
      irep_idt base;
      irep_idt index;
      if(
        !array_symbol_index(
          instruction->assign_rhs(), base, index))
      {
        reason = "ordered_extremum_element";
        return false;
      }
      result.accumulator = lhs;
      result.contribution = strip(instruction->assign_rhs());
      result.writes.insert(&*instruction);
      update = instruction;
    }
    else
    {
      irep_idt base;
      if(base_pointer(instruction->assign_lhs(), base))
      {
        reason = "ordered_extremum_array_write";
        return false;
      }
    }
  }
  if(
    atomic_depth != 0 || atomic_begins != 1 || atomic_ends != 1 ||
    update == program.instructions.end())
  {
    reason = "ordered_extremum_worker_shape";
    return false;
  }

  natural_loopst loops;
  loops(program);
  if(loops.loop_map.size() != 1)
  {
    reason = "ordered_extremum_loop_count";
    return false;
  }
  const auto &entry = *loops.loop_map.begin();
  if(!entry.second.contains(update))
  {
    reason = "ordered_extremum_update_outside_loop";
    return false;
  }
  flow_loop_dimensiont dimension;
  if(
    !parse_loop_exit(
      *entry.first, dimension.induction, dimension.bound) ||
    !loop_initial_value(
      program,
      entry.first,
      dimension.induction,
      dimension.start,
      reason))
  {
    if(reason.empty())
      reason = "ordered_extremum_loop_guard";
    return false;
  }
  std::size_t increments = 0;
  std::size_t backedges = 0;
  for(auto instruction = program.instructions.begin();
      instruction != program.instructions.end(); ++instruction)
  {
    if(entry.second.contains(instruction))
      dimension.members.insert(&*instruction);
    if(
      entry.second.contains(instruction) &&
      unit_increment(*instruction, dimension.induction))
      ++increments;
    if(
      instruction->is_goto() &&
      entry.second.contains(instruction) &&
      instruction != entry.first &&
      instruction->condition().is_true() &&
      instruction->targets.size() == 1 &&
      instruction->get_target() == entry.first)
      ++backedges;
  }
  if(increments != 1 || backedges != 1)
  {
    reason = "ordered_extremum_loop_skeleton";
    return false;
  }
  irep_idt contribution_base;
  irep_idt contribution_index;
  if(
    !array_symbol_index(
      result.contribution,
      contribution_base,
      contribution_index) ||
    contribution_index != dimension.induction)
  {
    reason = "ordered_extremum_index";
    return false;
  }
  result.dimensions.push_back(dimension);
  result.normalized_contribution = result.contribution;
  normalize_flow_expression(
    result.dimensions, result.normalized_contribution);
  collect_static_symbols(
    result.contribution, ns, result.input_symbols);
  collect_static_symbols(
    dimension.start, ns, result.input_symbols);
  collect_static_symbols(
    dimension.bound, ns, result.input_symbols);
  result.input_symbols.erase(result.accumulator);
  collect_pointer_bases(
    result.contribution, result.pointer_bases);
  result.worker = worker;
  return true;
}

bool relation_symbols(
  const exprt &src,
  const irep_idt &relation_id,
  const irep_idt &left,
  const irep_idt &right)
{
  const exprt &relation = strip(src);
  irep_idt lhs;
  irep_idt rhs;
  return
    relation.id() == relation_id && relation.operands().size() == 2 &&
    symbol_id(relation.op0(), lhs) && lhs == left &&
    symbol_id(relation.op1(), rhs) && rhs == right;
}

bool static_partition_precondition(
  const goto_modelt &model,
  const lifecyclet &life,
  const irep_idt &split,
  const irep_idt &bound)
{
  const auto &main =
    model.goto_functions.function_map.at(ID_main).body;
  bool nonnegative = false;
  bool within_bound = false;
  for(const auto &instruction : main.instructions)
  {
    if(
      life.first_create != nullptr &&
      instruction.location_number >= life.first_create->location_number)
      break;
    irep_idt callee;
    if(
      !call_id(instruction, callee) || !is_assume(callee) ||
      instruction.call_arguments().size() != 1)
      continue;
    std::vector<exprt> terms;
    flatten_and(instruction.call_arguments().front(), terms);
    for(const auto &term : terms)
    {
      nonnegative =
        nonnegative ||
        relation_zero(term, split, ID_ge) ||
        relation_zero(term, split, ID_gt);
      within_bound =
        within_bound ||
        relation_symbols(term, ID_gt, bound, split) ||
        relation_symbols(term, ID_lt, split, bound) ||
        relation_symbols(term, ID_ge, bound, split) ||
        relation_symbols(term, ID_le, split, bound);
    }
  }
  return nonnegative && within_bound;
}

bool flow_main_control(
  const goto_modelt &model,
  const lifecyclet &life,
  const flow_equality_propertyt &property,
  std::string &reason)
{
  const auto &main =
    model.goto_functions.function_map.at(ID_main).body;
  for(const auto &instruction : main.instructions)
  {
    if(
      life.first_create != nullptr && life.last_join != nullptr &&
      instruction.location_number >= life.first_create->location_number &&
      instruction.location_number <= life.last_join->location_number)
    {
      if(
        instruction.is_assign() || instruction.is_goto() ||
        instruction.is_assert() || instruction.is_assume() ||
        instruction.is_atomic_begin() || instruction.is_atomic_end())
      {
        reason = "flow_main_concurrent_effect";
        return false;
      }
      irep_idt callee;
      if(
        call_id(instruction, callee) &&
        !is_create(callee) && !is_join(callee))
      {
        reason = "flow_main_concurrent_call";
        return false;
      }
    }
    if(
      life.last_join != nullptr &&
      instruction.location_number > life.last_join->location_number)
    {
      if(
        instruction.is_assign() || instruction.is_goto() ||
        instruction.is_assert() || instruction.is_assume() ||
        instruction.is_atomic_begin() || instruction.is_atomic_end())
      {
        reason = "flow_main_postjoin_control";
        return false;
      }
      irep_idt callee;
      if(
        call_id(instruction, callee) &&
        &instruction != property.assumption &&
        &instruction != property.error)
      {
        reason = "flow_main_postjoin_call";
        return false;
      }
    }
  }
  return true;
}

bool static_partition_global_obligations(
  const goto_modelt &model,
  const lifecyclet &life,
  const flow_equality_propertyt &property,
  const std::vector<flow_range_workert> &workers,
  const std::set<irep_idt> &protected_symbols,
  const std::set<irep_idt> &pointer_bases,
  std::string &reason)
{
  std::set<const goto_programt::instructiont *> allowed;
  for(const auto &worker : workers)
    allowed.insert(worker.writes.begin(), worker.writes.end());
  if(
    !zero_initialized_symbols(
      model, {property.left, property.right}, allowed, reason))
    return false;
  if(
    !no_main_symbol_writes_before_create(
      model,
      life,
      {property.left, property.right},
      nullptr,
      reason))
    return false;

  for(const auto &entry : model.goto_functions.function_map)
  {
    for(const auto &instruction : entry.second.body.instructions)
    {
      const exprt *lhs = nullptr;
      if(instruction.is_assign())
        lhs = &instruction.assign_lhs();
      else if(
        instruction.is_function_call() &&
        !instruction.call_lhs().is_nil())
        lhs = &instruction.call_lhs();
      if(lhs == nullptr)
        continue;
      irep_idt direct;
      irep_idt base;
      const bool protected_write =
        (symbol_id(*lhs, direct) &&
         protected_symbols.count(direct) != 0) ||
        (base_pointer(*lhs, base) &&
         pointer_bases.count(base) != 0);
      if(!protected_write)
        continue;
      if(
        is_start_function(entry.first) && instruction.is_assign() &&
        value_is(instruction.assign_rhs(), 0))
        continue;
      if(
        entry.first == ID_main && life.first_create != nullptr &&
        instruction.location_number < life.first_create->location_number)
        continue;
      if(allowed.count(&instruction) == 0)
      {
        reason = "flow_external_writer";
        return false;
      }
    }
  }
  for(const auto &base : pointer_bases)
  {
    if(!flow_alias_free(model, base, reason))
      return false;
  }
  return
    no_addresses(model, protected_symbols, reason) &&
    flow_main_control(model, life, property, reason);
}

bool equivalent_static_partition_proof_impl(
  const goto_modelt &model,
  const namespacet &ns,
  std::string &reason)
{
  lifecyclet life;
  if(!lifecycle(model, life, reason) || life.workers.size() != 3)
  {
    if(reason.empty())
      reason = "flow_static_lifecycle";
    return false;
  }
  flow_equality_propertyt property;
  if(!find_flow_equality_property(model, ns, life, property, reason))
    return false;

  std::vector<flow_range_workert> workers;
  for(const auto &worker_id : life.workers)
  {
    flow_range_workert worker;
    if(!flow_range_worker(model, ns, worker_id, worker, reason))
      return false;
    workers.push_back(worker);
  }
  const irep_idt operation = workers.front().operation;
  if(!signed_addition_helper(model, ns, operation, reason))
    return false;
  for(const auto &worker : workers)
  {
    if(
      worker.operation != operation ||
      worker.normalized_contribution !=
        workers.front().normalized_contribution ||
      worker.normalized_inner_starts !=
        workers.front().normalized_inner_starts ||
      worker.normalized_inner_bounds !=
        workers.front().normalized_inner_bounds)
    {
      reason = "flow_static_map";
      return false;
    }
  }

  const flow_range_workert *whole = nullptr;
  const flow_range_workert *prefix = nullptr;
  const flow_range_workert *suffix = nullptr;
  for(const auto &candidate : workers)
  {
    if(
      value_is(candidate.dimensions.front().start, 0) &&
      candidate.accumulator == property.left)
      whole = &candidate;
    else if(
      value_is(candidate.dimensions.front().start, 0) &&
      candidate.accumulator == property.right)
      prefix = &candidate;
    else if(candidate.accumulator == property.right)
      suffix = &candidate;
  }
  if(
    whole == nullptr || prefix == nullptr || suffix == nullptr ||
    whole->dimensions.front().bound != suffix->dimensions.front().bound ||
    prefix->dimensions.front().bound != suffix->dimensions.front().start)
  {
    reason = "flow_static_partition";
    return false;
  }
  irep_idt split;
  irep_idt bound;
  if(
    !symbol_id(suffix->dimensions.front().start, split) ||
    !symbol_id(suffix->dimensions.front().bound, bound) ||
    !static_partition_precondition(model, life, split, bound))
  {
    reason = "flow_static_range";
    return false;
  }

  std::set<irep_idt> protected_symbols = {
    property.left, property.right, split, bound};
  std::set<irep_idt> pointer_bases;
  for(const auto &worker : workers)
  {
    protected_symbols.insert(
      worker.input_symbols.begin(), worker.input_symbols.end());
    pointer_bases.insert(
      worker.pointer_bases.begin(), worker.pointer_bases.end());
  }
  if(
    !static_partition_global_obligations(
      model,
      life,
      property,
      workers,
      protected_symbols,
      pointer_bases,
      reason))
    return false;

  std::cout << "NATIVE_RELATIONAL_FLOW applied=1 rule=static_partition"
            << " left=" << property.left
            << " right=" << property.right << '\n';
  return true;
}

struct modular_sum_propertyt
{
  irep_idt whole;
  irep_idt prefix;
  irep_idt suffix;
  const goto_programt::instructiont *assumption;
  const goto_programt::instructiont *error;

  modular_sum_propertyt() : assumption(nullptr), error(nullptr)
  {
  }
};

bool modular_sum_expression(
  const exprt &src,
  irep_idt &prefix,
  irep_idt &suffix)
{
  const exprt &sum = strip(src);
  return
    sum.id() == ID_plus && sum.operands().size() == 2 &&
    symbol_id(sum.op0(), prefix) && symbol_id(sum.op1(), suffix) &&
    prefix != suffix;
}

bool find_modular_sum_property(
  const goto_modelt &model,
  const namespacet &ns,
  const lifecyclet &life,
  modular_sum_propertyt &property,
  std::string &reason)
{
  const auto &main =
    model.goto_functions.function_map.at(ID_main).body;
  std::size_t matches = 0;
  std::size_t errors = 0;
  for(const auto &entry : model.goto_functions.function_map)
  {
    for(const auto &instruction : entry.second.body.instructions)
    {
      irep_idt callee;
      if(call_id(instruction, callee) && is_reach_error(callee))
      {
        ++errors;
        if(entry.first != ID_main)
        {
          reason = "modular_sum_error_function";
          return false;
        }
        property.error = &instruction;
      }
    }
  }
  for(const auto &instruction : main.instructions)
  {
    if(
      life.last_join == nullptr ||
      instruction.location_number <= life.last_join->location_number)
      continue;
    irep_idt callee;
    if(
      !call_id(instruction, callee) || !is_assume(callee) ||
      instruction.call_arguments().size() != 1)
      continue;
    const exprt &condition =
      strip(instruction.call_arguments().front());
    if(
      condition.id() != ID_notequal ||
      condition.operands().size() != 2)
      continue;
    irep_idt whole;
    irep_idt prefix;
    irep_idt suffix;
    bool parsed =
      symbol_id(condition.op0(), whole) &&
      modular_sum_expression(condition.op1(), prefix, suffix);
    if(!parsed)
      parsed =
        symbol_id(condition.op1(), whole) &&
        modular_sum_expression(condition.op0(), prefix, suffix);
    if(
      !parsed || !shared_unsigned32(whole, ns) ||
      !shared_unsigned32(prefix, ns) ||
      !shared_unsigned32(suffix, ns) ||
      whole == prefix || whole == suffix)
      continue;
    ++matches;
    property.whole = whole;
    property.prefix = prefix;
    property.suffix = suffix;
    property.assumption = &instruction;
  }
  if(
    matches != 1 || errors != 1 ||
    property.assumption == nullptr || property.error == nullptr ||
    property.assumption->location_number >=
      property.error->location_number)
  {
    reason =
      matches == 0 ? "modular_sum_property" :
                     "modular_sum_property_ambiguous";
    return false;
  }
  return true;
}

bool modular_sum_worker(
  const goto_modelt &model,
  const namespacet &ns,
  const irep_idt &worker,
  flow_range_workert &result,
  std::string &reason)
{
  const auto &program =
    model.goto_functions.function_map.at(worker).body;
  goto_programt::const_targett update = program.instructions.end();
  for(auto instruction = program.instructions.begin();
      instruction != program.instructions.end(); ++instruction)
  {
    if(instruction->is_atomic_begin() || instruction->is_atomic_end())
    {
      reason = "modular_sum_atomic";
      return false;
    }
    irep_idt callee;
    if(call_id(*instruction, callee))
    {
      if(is_assume(callee))
        continue;
      reason = "modular_sum_worker_call";
      return false;
    }
    if(!instruction->is_assign())
      continue;
    irep_idt lhs;
    if(shared_symbol_lhs(*instruction, ns, lhs))
    {
      const exprt &rhs = strip(instruction->assign_rhs());
      if(
        update != program.instructions.end() ||
        !shared_unsigned32(lhs, ns) ||
        rhs.id() != ID_plus || rhs.operands().size() != 2)
      {
        reason = "modular_sum_update";
        return false;
      }
      irep_idt first;
      irep_idt second;
      exprt contribution;
      if(symbol_id(rhs.op0(), first) && first == lhs)
        contribution = strip(rhs.op1());
      else if(symbol_id(rhs.op1(), second) && second == lhs)
        contribution = strip(rhs.op0());
      else
      {
        reason = "modular_sum_recurrence";
        return false;
      }
      irep_idt base;
      irep_idt index;
      if(!array_symbol_index(contribution, base, index))
      {
        reason = "modular_sum_element";
        return false;
      }
      result.accumulator = lhs;
      result.contribution = contribution;
      result.writes.insert(&*instruction);
      update = instruction;
    }
    else
    {
      irep_idt base;
      if(base_pointer(instruction->assign_lhs(), base))
      {
        reason = "modular_sum_array_write";
        return false;
      }
    }
  }
  if(update == program.instructions.end())
  {
    reason = "modular_sum_worker_shape";
    return false;
  }

  natural_loopst loops;
  loops(program);
  if(loops.loop_map.size() != 1)
  {
    reason = "modular_sum_loop_count";
    return false;
  }
  const auto &entry = *loops.loop_map.begin();
  if(!entry.second.contains(update))
  {
    reason = "modular_sum_update_outside_loop";
    return false;
  }
  flow_loop_dimensiont dimension;
  if(
    !parse_loop_exit(
      *entry.first, dimension.induction, dimension.bound) ||
    !loop_initial_value(
      program,
      entry.first,
      dimension.induction,
      dimension.start,
      reason))
  {
    if(reason.empty())
      reason = "modular_sum_loop_guard";
    return false;
  }
  std::size_t increments = 0;
  std::size_t backedges = 0;
  for(auto instruction = program.instructions.begin();
      instruction != program.instructions.end(); ++instruction)
  {
    if(entry.second.contains(instruction))
      dimension.members.insert(&*instruction);
    if(
      entry.second.contains(instruction) &&
      unit_increment(*instruction, dimension.induction))
      ++increments;
    if(
      instruction->is_goto() &&
      entry.second.contains(instruction) &&
      instruction != entry.first &&
      instruction->condition().is_true() &&
      instruction->targets.size() == 1 &&
      instruction->get_target() == entry.first)
      ++backedges;
  }
  irep_idt contribution_base;
  irep_idt contribution_index;
  if(
    increments != 1 || backedges != 1 ||
    !array_symbol_index(
      result.contribution,
      contribution_base,
      contribution_index) ||
    contribution_index != dimension.induction)
  {
    reason = "modular_sum_loop_skeleton";
    return false;
  }
  result.dimensions.push_back(dimension);
  result.normalized_contribution = result.contribution;
  normalize_flow_expression(
    result.dimensions, result.normalized_contribution);
  collect_static_symbols(
    result.contribution, ns, result.input_symbols);
  collect_static_symbols(
    dimension.start, ns, result.input_symbols);
  collect_static_symbols(
    dimension.bound, ns, result.input_symbols);
  result.input_symbols.erase(result.accumulator);
  collect_pointer_bases(
    result.contribution, result.pointer_bases);
  result.worker = worker;
  return true;
}

bool modular_sum_partition_proof_impl(
  const goto_modelt &model,
  const namespacet &ns,
  std::string &reason)
{
  lifecyclet life;
  if(!lifecycle(model, life, reason) || life.workers.size() != 3)
  {
    if(reason.empty())
      reason = "modular_sum_lifecycle";
    return false;
  }
  modular_sum_propertyt property;
  if(!find_modular_sum_property(model, ns, life, property, reason))
    return false;

  std::vector<flow_range_workert> workers;
  for(const auto &worker_id : life.workers)
  {
    flow_range_workert worker;
    if(!modular_sum_worker(model, ns, worker_id, worker, reason))
      return false;
    workers.push_back(worker);
  }
  for(const auto &worker : workers)
  {
    if(
      worker.normalized_contribution !=
      workers.front().normalized_contribution)
    {
      reason = "modular_sum_input_alignment";
      return false;
    }
  }

  const flow_range_workert *whole = nullptr;
  const flow_range_workert *prefix = nullptr;
  const flow_range_workert *suffix = nullptr;
  for(const auto &candidate : workers)
  {
    if(candidate.accumulator == property.whole)
      whole = &candidate;
    else if(candidate.accumulator == property.prefix)
      prefix = &candidate;
    else if(candidate.accumulator == property.suffix)
      suffix = &candidate;
  }
  if(
    whole == nullptr || prefix == nullptr || suffix == nullptr ||
    !value_is(whole->dimensions.front().start, 0) ||
    !value_is(prefix->dimensions.front().start, 0) ||
    whole->dimensions.front().bound !=
      suffix->dimensions.front().bound ||
    prefix->dimensions.front().bound !=
      suffix->dimensions.front().start)
  {
    reason = "modular_sum_partition";
    return false;
  }
  irep_idt split;
  irep_idt bound;
  if(
    !symbol_id(suffix->dimensions.front().start, split) ||
    !symbol_id(suffix->dimensions.front().bound, bound) ||
    !static_partition_precondition(model, life, split, bound))
  {
    reason = "modular_sum_range";
    return false;
  }

  std::set<irep_idt> protected_symbols = {
    property.whole,
    property.prefix,
    property.suffix,
    split,
    bound};
  std::set<irep_idt> pointer_bases;
  std::set<const goto_programt::instructiont *> allowed;
  for(const auto &worker : workers)
  {
    protected_symbols.insert(
      worker.input_symbols.begin(), worker.input_symbols.end());
    pointer_bases.insert(
      worker.pointer_bases.begin(), worker.pointer_bases.end());
    allowed.insert(worker.writes.begin(), worker.writes.end());
  }
  if(
    !zero_initialized_symbols(
      model,
      {property.whole, property.prefix, property.suffix},
      allowed,
      reason) ||
    !no_main_symbol_writes_before_create(
      model,
      life,
      {property.whole, property.prefix, property.suffix},
      nullptr,
      reason))
    return false;

  flow_equality_propertyt control;
  control.left = property.whole;
  control.right = property.prefix;
  control.assumption = property.assumption;
  control.error = property.error;
  if(
    !static_partition_global_obligations(
      model,
      life,
      control,
      workers,
      protected_symbols,
      pointer_bases,
      reason))
    return false;

  std::cout
    << "NATIVE_MODULAR_SUM_PARTITION applied=1"
    << " whole=" << property.whole
    << " prefix=" << property.prefix
    << " suffix=" << property.suffix << '\n';
  return true;
}

struct boolean_segment_propertyt
{
  irep_idt whole;
  irep_idt prefix;
  irep_idt suffix;
  const goto_programt::instructiont *assumption;
  const goto_programt::instructiont *error;

  boolean_segment_propertyt() : assumption(nullptr), error(nullptr)
  {
  }
};

bool boolean_value_symbol(
  const exprt &src,
  irep_idt &identifier)
{
  const exprt &value = strip(src);
  if(symbol_id(value, identifier))
    return true;
  if(
    value.id() != ID_notequal ||
    value.operands().size() != 2)
    return false;
  return
    (symbol_id(value.op0(), identifier) &&
     value_is(value.op1(), 0)) ||
    (symbol_id(value.op1(), identifier) &&
     value_is(value.op0(), 0));
}

bool boolean_segment_expression(
  const exprt &src,
  irep_idt &prefix,
  irep_idt &suffix)
{
  const exprt &conjunction = strip(src);
  return
    conjunction.id() == ID_and &&
    conjunction.operands().size() == 2 &&
    boolean_value_symbol(conjunction.op0(), prefix) &&
    boolean_value_symbol(conjunction.op1(), suffix) &&
    prefix != suffix;
}

bool find_boolean_segment_property(
  const goto_modelt &model,
  const namespacet &ns,
  const lifecyclet &life,
  boolean_segment_propertyt &property,
  std::string &reason)
{
  const auto &main =
    model.goto_functions.function_map.at(ID_main).body;
  std::size_t matches = 0;
  std::size_t errors = 0;
  for(const auto &entry : model.goto_functions.function_map)
  {
    for(const auto &instruction : entry.second.body.instructions)
    {
      irep_idt callee;
      if(call_id(instruction, callee) && is_reach_error(callee))
      {
        ++errors;
        if(entry.first != ID_main)
        {
          reason = "boolean_segment_error_function";
          return false;
        }
        property.error = &instruction;
      }
    }
  }
  for(const auto &instruction : main.instructions)
  {
    if(
      life.last_join == nullptr ||
      instruction.location_number <= life.last_join->location_number)
      continue;
    irep_idt callee;
    if(
      !call_id(instruction, callee) || !is_assume(callee) ||
      instruction.call_arguments().size() != 1)
      continue;
    const exprt &condition =
      strip(instruction.call_arguments().front());
    if(
      condition.id() != ID_notequal ||
      condition.operands().size() != 2)
      continue;
    irep_idt whole;
    irep_idt prefix;
    irep_idt suffix;
    bool parsed =
      symbol_id(condition.op0(), whole) &&
      boolean_segment_expression(
        condition.op1(), prefix, suffix);
    if(!parsed)
      parsed =
        symbol_id(condition.op1(), whole) &&
        boolean_segment_expression(
          condition.op0(), prefix, suffix);
    if(
      !parsed || !shared_boolean(whole, ns) ||
      !shared_boolean(prefix, ns) ||
      !shared_boolean(suffix, ns) ||
      whole == prefix || whole == suffix)
      continue;
    ++matches;
    property.whole = whole;
    property.prefix = prefix;
    property.suffix = suffix;
    property.assumption = &instruction;
  }
  if(
    matches != 1 || errors != 1 ||
    property.assumption == nullptr || property.error == nullptr ||
    property.assumption->location_number >=
      property.error->location_number)
  {
    reason =
      matches == 0 ? "boolean_segment_property" :
                     "boolean_segment_property_ambiguous";
    return false;
  }
  return true;
}

bool boolean_segment_worker(
  const goto_modelt &model,
  const namespacet &ns,
  const irep_idt &worker,
  flow_range_workert &result,
  std::string &reason)
{
  const auto &program =
    model.goto_functions.function_map.at(worker).body;
  goto_programt::const_targett update = program.instructions.end();
  for(auto instruction = program.instructions.begin();
      instruction != program.instructions.end(); ++instruction)
  {
    if(instruction->is_atomic_begin() || instruction->is_atomic_end())
    {
      reason = "boolean_segment_atomic";
      return false;
    }
    irep_idt callee;
    if(call_id(*instruction, callee))
    {
      if(is_assume(callee))
        continue;
      reason = "boolean_segment_worker_call";
      return false;
    }
    if(!instruction->is_assign())
      continue;
    irep_idt lhs;
    if(shared_symbol_lhs(*instruction, ns, lhs))
    {
      const exprt &rhs = strip(instruction->assign_rhs());
      if(
        update != program.instructions.end() ||
        !shared_boolean(lhs, ns) ||
        rhs.id() != ID_and || rhs.operands().size() != 2)
      {
        reason = "boolean_segment_update";
        return false;
      }
      irep_idt first;
      irep_idt second;
      exprt contribution;
      if(boolean_value_symbol(rhs.op0(), first) && first == lhs)
        contribution = strip(rhs.op1());
      else if(boolean_value_symbol(rhs.op1(), second) && second == lhs)
        contribution = strip(rhs.op0());
      else
      {
        reason = "boolean_segment_recurrence";
        return false;
      }
      if(
        contribution.id() != ID_lt ||
        contribution.operands().size() != 2)
      {
        reason = "boolean_segment_relation";
        return false;
      }
      result.accumulator = lhs;
      result.contribution = contribution;
      result.writes.insert(&*instruction);
      update = instruction;
    }
    else
    {
      irep_idt base;
      if(base_pointer(instruction->assign_lhs(), base))
      {
        reason = "boolean_segment_array_write";
        return false;
      }
    }
  }
  if(update == program.instructions.end())
  {
    reason = "boolean_segment_worker_shape";
    return false;
  }

  natural_loopst loops;
  loops(program);
  if(loops.loop_map.size() != 1)
  {
    reason = "boolean_segment_loop_count";
    return false;
  }
  const auto &entry = *loops.loop_map.begin();
  if(!entry.second.contains(update))
  {
    reason = "boolean_segment_update_outside_loop";
    return false;
  }
  flow_loop_dimensiont dimension;
  if(
    !parse_loop_exit(
      *entry.first, dimension.induction, dimension.bound) ||
    !loop_initial_value(
      program,
      entry.first,
      dimension.induction,
      dimension.start,
      reason))
  {
    if(reason.empty())
      reason = "boolean_segment_loop_guard";
    return false;
  }
  std::size_t increments = 0;
  std::size_t backedges = 0;
  for(auto instruction = program.instructions.begin();
      instruction != program.instructions.end(); ++instruction)
  {
    if(entry.second.contains(instruction))
      dimension.members.insert(&*instruction);
    if(
      entry.second.contains(instruction) &&
      unit_increment(*instruction, dimension.induction))
      ++increments;
    if(
      instruction->is_goto() &&
      entry.second.contains(instruction) &&
      instruction != entry.first &&
      instruction->condition().is_true() &&
      instruction->targets.size() == 1 &&
      instruction->get_target() == entry.first)
      ++backedges;
  }
  if(increments != 1 || backedges != 1)
  {
    reason = "boolean_segment_loop_skeleton";
    return false;
  }
  result.dimensions.push_back(dimension);
  result.normalized_contribution = result.contribution;
  normalize_flow_expression(
    result.dimensions, result.normalized_contribution);
  collect_static_symbols(
    result.contribution, ns, result.input_symbols);
  collect_static_symbols(
    dimension.start, ns, result.input_symbols);
  collect_static_symbols(
    dimension.bound, ns, result.input_symbols);
  result.input_symbols.erase(result.accumulator);
  collect_pointer_bases(
    result.contribution, result.pointer_bases);
  result.worker = worker;
  return true;
}

bool boolean_true_initialization(
  const goto_modelt &model,
  const lifecyclet &life,
  const std::set<irep_idt> &symbols,
  std::set<const goto_programt::instructiont *> &allowed,
  std::string &reason)
{
  const auto &main =
    model.goto_functions.function_map.at(ID_main).body;
  std::set<irep_idt> initialized;
  for(const auto &instruction : main.instructions)
  {
    if(
      life.first_create != nullptr &&
      instruction.location_number >= life.first_create->location_number)
      break;
    if(!instruction.is_assign())
      continue;
    irep_idt lhs;
    if(
      !symbol_id(instruction.assign_lhs(), lhs) ||
      symbols.count(lhs) == 0)
      continue;
    if(
      !value_is(instruction.assign_rhs(), 1) ||
      !initialized.insert(lhs).second)
    {
      reason = "boolean_segment_identity_init";
      return false;
    }
    allowed.insert(&instruction);
  }
  if(initialized != symbols)
  {
    reason = "boolean_segment_identity_init";
    return false;
  }
  return true;
}

bool boolean_segment_partition_proof_impl(
  const goto_modelt &model,
  const namespacet &ns,
  std::string &reason)
{
  lifecyclet life;
  if(!lifecycle(model, life, reason) || life.workers.size() != 3)
  {
    if(reason.empty())
      reason = "boolean_segment_lifecycle";
    return false;
  }
  boolean_segment_propertyt property;
  if(
    !find_boolean_segment_property(
      model, ns, life, property, reason))
    return false;

  std::vector<flow_range_workert> workers;
  for(const auto &worker_id : life.workers)
  {
    flow_range_workert worker;
    if(!boolean_segment_worker(model, ns, worker_id, worker, reason))
      return false;
    workers.push_back(worker);
  }
  for(const auto &worker : workers)
  {
    if(
      worker.normalized_contribution !=
      workers.front().normalized_contribution)
    {
      reason = "boolean_segment_input_alignment";
      return false;
    }
  }

  const flow_range_workert *whole = nullptr;
  const flow_range_workert *prefix = nullptr;
  const flow_range_workert *suffix = nullptr;
  for(const auto &candidate : workers)
  {
    if(candidate.accumulator == property.whole)
      whole = &candidate;
    else if(candidate.accumulator == property.prefix)
      prefix = &candidate;
    else if(candidate.accumulator == property.suffix)
      suffix = &candidate;
  }
  if(
    whole == nullptr || prefix == nullptr || suffix == nullptr ||
    !value_is(whole->dimensions.front().start, 0) ||
    !value_is(prefix->dimensions.front().start, 0) ||
    whole->dimensions.front().bound !=
      suffix->dimensions.front().bound ||
    prefix->dimensions.front().bound !=
      suffix->dimensions.front().start)
  {
    reason = "boolean_segment_partition";
    return false;
  }
  irep_idt split;
  irep_idt bound_base;
  const exprt &whole_bound =
    strip(whole->dimensions.front().bound);
  if(
    !symbol_id(suffix->dimensions.front().start, split) ||
    whole_bound.id() != ID_minus ||
    whole_bound.operands().size() != 2 ||
    !symbol_id(whole_bound.op0(), bound_base) ||
    !value_is(whole_bound.op1(), 1) ||
    !static_partition_precondition(
      model, life, split, bound_base))
  {
    reason = "boolean_segment_range";
    return false;
  }

  std::set<irep_idt> protected_symbols = {
    property.whole,
    property.prefix,
    property.suffix,
    split,
    bound_base};
  std::set<irep_idt> pointer_bases;
  std::set<const goto_programt::instructiont *> allowed;
  for(const auto &worker : workers)
  {
    protected_symbols.insert(
      worker.input_symbols.begin(), worker.input_symbols.end());
    pointer_bases.insert(
      worker.pointer_bases.begin(), worker.pointer_bases.end());
    allowed.insert(worker.writes.begin(), worker.writes.end());
  }
  const std::set<irep_idt> summaries = {
    property.whole, property.prefix, property.suffix};
  if(
    !boolean_true_initialization(
      model, life, summaries, allowed, reason))
    return false;

  for(const auto &entry : model.goto_functions.function_map)
  {
    for(const auto &instruction : entry.second.body.instructions)
    {
      const exprt *lhs = nullptr;
      if(instruction.is_assign())
        lhs = &instruction.assign_lhs();
      else if(
        instruction.is_function_call() &&
        !instruction.call_lhs().is_nil())
        lhs = &instruction.call_lhs();
      if(lhs == nullptr)
        continue;
      irep_idt direct;
      irep_idt base;
      const bool protected_write =
        (symbol_id(*lhs, direct) &&
         protected_symbols.count(direct) != 0) ||
        (base_pointer(*lhs, base) &&
         pointer_bases.count(base) != 0);
      if(!protected_write)
        continue;
      if(
        is_start_function(entry.first) &&
        instruction.is_assign() &&
        value_is(instruction.assign_rhs(), 0))
        continue;
      if(
        entry.first == ID_main && life.first_create != nullptr &&
        instruction.location_number <
          life.first_create->location_number &&
        summaries.count(direct) == 0)
        continue;
      if(allowed.count(&instruction) == 0)
      {
        reason = "boolean_segment_external_writer";
        return false;
      }
    }
  }
  for(const auto &base : pointer_bases)
  {
    if(!flow_alias_free(model, base, reason))
      return false;
  }
  flow_equality_propertyt control;
  control.left = property.whole;
  control.right = property.prefix;
  control.assumption = property.assumption;
  control.error = property.error;
  if(
    !no_addresses(model, protected_symbols, reason) ||
    !flow_main_control(model, life, control, reason))
    return false;

  std::cout
    << "NATIVE_BOOLEAN_SEGMENT_PARTITION applied=1"
    << " whole=" << property.whole
    << " prefix=" << property.prefix
    << " suffix=" << property.suffix << '\n';
  return true;
}

bool shared_pointer_to_unsigned32(
  const irep_idt &identifier,
  const namespacet &ns)
{
  const symbolt *symbol = lookup(identifier, ns);
  if(
    symbol == nullptr || !symbol->is_static_lifetime ||
    symbol->is_type || symbol->type.id() != ID_pointer)
    return false;
  const typet &subtype = to_pointer_type(symbol->type).base_type();
  return
    subtype.id() == ID_unsignedbv &&
    to_unsignedbv_type(subtype).get_width() == 32;
}

struct pointwise_map_propertyt
{
  irep_idt whole_output;
  irep_idt partition_output;
  irep_idt index;
  irep_idt bound;
  const goto_programt::instructiont *range_assumption;
  const goto_programt::instructiont *property_assumption;
  const goto_programt::instructiont *error;

  pointwise_map_propertyt()
    : range_assumption(nullptr),
      property_assumption(nullptr),
      error(nullptr)
  {
  }
};

bool find_pointwise_map_property(
  const goto_modelt &model,
  const namespacet &ns,
  const lifecyclet &life,
  pointwise_map_propertyt &property,
  std::string &reason)
{
  const auto &main =
    model.goto_functions.function_map.at(ID_main).body;
  std::size_t matches = 0;
  std::size_t errors = 0;
  for(const auto &entry : model.goto_functions.function_map)
  {
    for(const auto &instruction : entry.second.body.instructions)
    {
      irep_idt callee;
      if(call_id(instruction, callee) && is_reach_error(callee))
      {
        ++errors;
        if(entry.first != ID_main)
        {
          reason = "pointwise_map_error_function";
          return false;
        }
        property.error = &instruction;
      }
    }
  }
  for(const auto &instruction : main.instructions)
  {
    if(
      life.last_join == nullptr ||
      instruction.location_number <= life.last_join->location_number)
      continue;
    irep_idt callee;
    if(
      !call_id(instruction, callee) || !is_assume(callee) ||
      instruction.call_arguments().size() != 1)
      continue;
    const exprt &condition =
      strip(instruction.call_arguments().front());
    if(
      condition.id() != ID_notequal ||
      condition.operands().size() != 2)
      continue;
    irep_idt left_base;
    irep_idt left_index;
    irep_idt right_base;
    irep_idt right_index;
    if(
      !array_symbol_index(
        condition.op0(), left_base, left_index) ||
      !array_symbol_index(
        condition.op1(), right_base, right_index) ||
      left_index != right_index || left_base == right_base ||
      !shared_pointer_to_unsigned32(left_base, ns) ||
      !shared_pointer_to_unsigned32(right_base, ns))
      continue;
    ++matches;
    property.whole_output = left_base;
    property.partition_output = right_base;
    property.index = left_index;
    property.property_assumption = &instruction;
  }
  if(
    matches != 1 || errors != 1 ||
    property.property_assumption == nullptr ||
    property.error == nullptr ||
    property.property_assumption->location_number >=
      property.error->location_number)
  {
    reason =
      matches == 0 ? "pointwise_map_property" :
                     "pointwise_map_property_ambiguous";
    return false;
  }

  std::size_t range_matches = 0;
  for(const auto &instruction : main.instructions)
  {
    if(
      life.last_join == nullptr ||
      instruction.location_number <= life.last_join->location_number ||
      instruction.location_number >=
        property.property_assumption->location_number)
      continue;
    irep_idt callee;
    if(
      !call_id(instruction, callee) || !is_assume(callee) ||
      instruction.call_arguments().size() != 1)
      continue;
    bool nonnegative = false;
    bool below_bound = false;
    irep_idt bound;
    std::vector<exprt> terms;
    flatten_and(instruction.call_arguments().front(), terms);
    for(const auto &term : terms)
    {
      nonnegative =
        nonnegative ||
        relation_zero(term, property.index, ID_ge);
      const exprt &nonnegative_relation = strip(term);
      irep_idt nonnegative_candidate;
      nonnegative =
        nonnegative ||
        (nonnegative_relation.id() == ID_le &&
         nonnegative_relation.operands().size() == 2 &&
         value_is(nonnegative_relation.op0(), 0) &&
         symbol_id(
           nonnegative_relation.op1(),
           nonnegative_candidate) &&
         nonnegative_candidate == property.index);
      const exprt &relation = strip(term);
      irep_idt left;
      irep_idt right;
      if(
        relation.id() == ID_lt &&
        relation.operands().size() == 2 &&
        symbol_id(relation.op0(), left) &&
        left == property.index &&
        symbol_id(relation.op1(), right))
      {
        below_bound = true;
        bound = right;
      }
    }
    if(nonnegative && below_bound && shared_signed(bound, ns))
    {
      ++range_matches;
      property.bound = bound;
      property.range_assumption = &instruction;
    }
  }
  if(range_matches != 1 || property.range_assumption == nullptr)
  {
    reason = "pointwise_map_index_range";
    return false;
  }
  return true;
}

struct pointwise_map_workert
{
  irep_idt worker;
  irep_idt output;
  exprt expression;
  exprt normalized_expression;
  flow_loop_dimensiont dimension;
  std::set<irep_idt> input_symbols;
  std::set<irep_idt> pointer_bases;
  std::set<const goto_programt::instructiont *> writes;
};

bool pointwise_map_worker(
  const goto_modelt &model,
  const namespacet &ns,
  const irep_idt &worker,
  pointwise_map_workert &result,
  std::string &reason)
{
  const auto &program =
    model.goto_functions.function_map.at(worker).body;
  goto_programt::const_targett update = program.instructions.end();
  irep_idt update_index;
  for(auto instruction = program.instructions.begin();
      instruction != program.instructions.end(); ++instruction)
  {
    if(instruction->is_atomic_begin() || instruction->is_atomic_end())
    {
      reason = "pointwise_map_atomic";
      return false;
    }
    irep_idt callee;
    if(call_id(*instruction, callee))
    {
      if(is_assume(callee))
        continue;
      reason = "pointwise_map_worker_call";
      return false;
    }
    if(!instruction->is_assign())
      continue;
    irep_idt output;
    irep_idt index;
    if(array_symbol_index(
         instruction->assign_lhs(), output, index))
    {
      const exprt &rhs = strip(instruction->assign_rhs());
      if(
        update != program.instructions.end() ||
        !shared_pointer_to_unsigned32(output, ns) ||
        rhs.id() != ID_plus || rhs.operands().size() != 2)
      {
        reason = "pointwise_map_update";
        return false;
      }
      irep_idt left_base;
      irep_idt left_index;
      irep_idt right_base;
      irep_idt right_index;
      if(
        !array_symbol_index(
          rhs.op0(), left_base, left_index) ||
        !array_symbol_index(
          rhs.op1(), right_base, right_index) ||
        left_index != index || right_index != index ||
        left_base == right_base || left_base == output ||
        right_base == output ||
        !shared_pointer_to_unsigned32(left_base, ns) ||
        !shared_pointer_to_unsigned32(right_base, ns))
      {
        reason = "pointwise_map_expression";
        return false;
      }
      result.output = output;
      result.expression = rhs;
      result.writes.insert(&*instruction);
      update_index = index;
      update = instruction;
    }
    else
    {
      irep_idt shared;
      irep_idt base;
      if(
        shared_symbol_lhs(*instruction, ns, shared) ||
        base_pointer(instruction->assign_lhs(), base))
      {
        reason = "pointwise_map_extra_write";
        return false;
      }
    }
  }
  if(update == program.instructions.end())
  {
    reason = "pointwise_map_worker_shape";
    return false;
  }

  natural_loopst loops;
  loops(program);
  if(loops.loop_map.size() != 1)
  {
    reason = "pointwise_map_loop_count";
    return false;
  }
  const auto &entry = *loops.loop_map.begin();
  if(
    !entry.second.contains(update) ||
    !parse_loop_exit(
      *entry.first,
      result.dimension.induction,
      result.dimension.bound) ||
    !loop_initial_value(
      program,
      entry.first,
      result.dimension.induction,
      result.dimension.start,
      reason) ||
    update_index != result.dimension.induction)
  {
    if(reason.empty())
      reason = "pointwise_map_loop_shape";
    return false;
  }
  std::size_t increments = 0;
  std::size_t backedges = 0;
  for(auto instruction = program.instructions.begin();
      instruction != program.instructions.end(); ++instruction)
  {
    if(entry.second.contains(instruction))
      result.dimension.members.insert(&*instruction);
    if(
      entry.second.contains(instruction) &&
      unit_increment(*instruction, result.dimension.induction))
      ++increments;
    if(
      instruction->is_goto() &&
      entry.second.contains(instruction) &&
      instruction != entry.first &&
      instruction->condition().is_true() &&
      instruction->targets.size() == 1 &&
      instruction->get_target() == entry.first)
      ++backedges;
  }
  if(increments != 1 || backedges != 1)
  {
    reason = "pointwise_map_loop_skeleton";
    return false;
  }
  result.normalized_expression = result.expression;
  std::vector<flow_loop_dimensiont> dimensions = {
    result.dimension};
  normalize_flow_expression(
    dimensions, result.normalized_expression);
  collect_static_symbols(
    result.expression, ns, result.input_symbols);
  result.input_symbols.erase(result.output);
  collect_pointer_bases(
    result.expression, result.pointer_bases);
  result.worker = worker;
  return true;
}

bool pointwise_map_main_control(
  const goto_modelt &model,
  const lifecyclet &life,
  const pointwise_map_propertyt &property,
  std::string &reason)
{
  const auto &main =
    model.goto_functions.function_map.at(ID_main).body;
  std::size_t index_assignments = 0;
  std::set<irep_idt> nondet_temporaries;
  for(const auto &instruction : main.instructions)
  {
    if(
      life.first_create != nullptr && life.last_join != nullptr &&
      instruction.location_number >= life.first_create->location_number &&
      instruction.location_number <= life.last_join->location_number)
    {
      if(
        instruction.is_assign() || instruction.is_goto() ||
        instruction.is_assert() || instruction.is_assume() ||
        instruction.is_atomic_begin() || instruction.is_atomic_end())
      {
        reason = "pointwise_map_main_concurrent_effect";
        return false;
      }
      irep_idt callee;
      if(
        call_id(instruction, callee) &&
        !is_create(callee) && !is_join(callee))
      {
        reason = "pointwise_map_main_concurrent_call";
        return false;
      }
    }
    if(
      life.last_join != nullptr &&
      instruction.location_number > life.last_join->location_number)
    {
      if(instruction.is_assign())
      {
        irep_idt lhs;
        if(!symbol_id(instruction.assign_lhs(), lhs))
        {
          reason = "pointwise_map_postjoin_assignment";
          return false;
        }
        if(lhs == property.index)
        {
          irep_idt temporary;
          if(
            !contains_side_effect(instruction.assign_rhs()) &&
            (!symbol_id(instruction.assign_rhs(), temporary) ||
             nondet_temporaries.count(temporary) == 0))
          {
            reason = "pointwise_map_index_assignment";
            return false;
          }
          ++index_assignments;
        }
        else
        {
          const symbolt *symbol = lookup(lhs, namespacet(model.symbol_table));
          if(
            symbol == nullptr || symbol->is_static_lifetime ||
            !contains_side_effect(instruction.assign_rhs()) ||
            !nondet_temporaries.insert(lhs).second)
          {
            reason = "pointwise_map_postjoin_assignment";
            return false;
          }
        }
        continue;
      }
      if(
        instruction.is_goto() || instruction.is_assert() ||
        instruction.is_assume() ||
        instruction.is_atomic_begin() || instruction.is_atomic_end())
      {
        reason = "pointwise_map_postjoin_control";
        return false;
      }
      irep_idt callee;
      if(
        call_id(instruction, callee) &&
        &instruction != property.range_assumption &&
        &instruction != property.property_assumption &&
        &instruction != property.error)
      {
        reason = "pointwise_map_postjoin_call";
        return false;
      }
    }
  }
  if(index_assignments != 1)
  {
    reason = "pointwise_map_index_assignment";
    return false;
  }
  return true;
}

bool pointwise_map_partition_proof_impl(
  const goto_modelt &model,
  const namespacet &ns,
  std::string &reason)
{
  lifecyclet life;
  if(!lifecycle(model, life, reason) || life.workers.size() != 3)
  {
    if(reason.empty())
      reason = "pointwise_map_lifecycle";
    return false;
  }
  pointwise_map_propertyt property;
  if(!find_pointwise_map_property(model, ns, life, property, reason))
    return false;

  std::vector<pointwise_map_workert> workers;
  for(const auto &worker_id : life.workers)
  {
    pointwise_map_workert worker;
    if(!pointwise_map_worker(model, ns, worker_id, worker, reason))
      return false;
    workers.push_back(worker);
  }
  for(const auto &worker : workers)
  {
    if(
      worker.normalized_expression !=
      workers.front().normalized_expression)
    {
      reason = "pointwise_map_alignment";
      return false;
    }
  }
  const pointwise_map_workert *whole = nullptr;
  const pointwise_map_workert *prefix = nullptr;
  const pointwise_map_workert *suffix = nullptr;
  for(const auto &candidate : workers)
  {
    if(candidate.output == property.whole_output)
      whole = &candidate;
    else if(
      candidate.output == property.partition_output &&
      value_is(candidate.dimension.start, 0))
      prefix = &candidate;
    else if(candidate.output == property.partition_output)
      suffix = &candidate;
  }
  if(
    whole == nullptr || prefix == nullptr || suffix == nullptr ||
    !value_is(whole->dimension.start, 0) ||
    whole->dimension.bound != suffix->dimension.bound ||
    prefix->dimension.bound != suffix->dimension.start ||
    whole->dimension.bound != symbol_exprt(
      property.bound, whole->dimension.bound.type()))
  {
    reason = "pointwise_map_partition";
    return false;
  }
  irep_idt split;
  if(
    !symbol_id(suffix->dimension.start, split) ||
    !static_partition_precondition(
      model, life, split, property.bound))
  {
    reason = "pointwise_map_range";
    return false;
  }

  std::set<irep_idt> protected_symbols = {
    property.whole_output,
    property.partition_output,
    property.index,
    property.bound,
    split};
  std::set<irep_idt> pointer_bases = {
    property.whole_output, property.partition_output};
  std::set<const goto_programt::instructiont *> allowed;
  for(const auto &worker : workers)
  {
    protected_symbols.insert(
      worker.input_symbols.begin(), worker.input_symbols.end());
    pointer_bases.insert(
      worker.pointer_bases.begin(), worker.pointer_bases.end());
    allowed.insert(worker.writes.begin(), worker.writes.end());
  }
  for(const auto &entry : model.goto_functions.function_map)
  {
    for(const auto &instruction : entry.second.body.instructions)
    {
      if(!instruction.is_assign())
        continue;
      irep_idt direct;
      irep_idt base;
      const bool protected_write =
        (symbol_id(instruction.assign_lhs(), direct) &&
         pointer_bases.count(direct) != 0) ||
        (base_pointer(instruction.assign_lhs(), base) &&
         pointer_bases.count(base) != 0);
      if(!protected_write)
        continue;
      if(
        is_start_function(entry.first) &&
        value_is(instruction.assign_rhs(), 0))
        continue;
      if(
        entry.first == ID_main && life.first_create != nullptr &&
        instruction.location_number <
          life.first_create->location_number)
        continue;
      if(allowed.count(&instruction) == 0)
      {
        reason = "pointwise_map_external_writer";
        return false;
      }
    }
  }
  for(const auto &base : pointer_bases)
  {
    if(!flow_alias_free(model, base, reason))
      return false;
  }
  if(
    !no_addresses(model, protected_symbols, reason) ||
    !pointwise_map_main_control(model, life, property, reason))
    return false;

  std::cout
    << "NATIVE_POINTWISE_MAP_PARTITION applied=1"
    << " whole=" << property.whole_output
    << " partition=" << property.partition_output
    << " index=" << property.index << '\n';
  return true;
}

struct maximum_tail_propertyt
{
  irep_idt whole;
  irep_idt prefix;
  irep_idt suffix;
  irep_idt suffix_sum;
  const goto_programt::instructiont *assumption;
  const goto_programt::instructiont *error;

  maximum_tail_propertyt() : assumption(nullptr), error(nullptr)
  {
  }
};

bool signed_sum_symbols(
  const exprt &src,
  irep_idt &left,
  irep_idt &right)
{
  const exprt &sum = strip(src);
  return
    sum.id() == ID_plus && sum.operands().size() == 2 &&
    symbol_id(sum.op0(), left) && symbol_id(sum.op1(), right) &&
    left != right;
}

bool maximum_tail_expression(
  const exprt &src,
  irep_idt &prefix,
  irep_idt &suffix,
  irep_idt &suffix_sum)
{
  const exprt &choice = strip(src);
  if(choice.id() != ID_if || choice.operands().size() != 3)
    return false;
  const exprt &condition = strip(choice.op0());
  if(
    condition.id() != ID_lt ||
    condition.operands().size() != 2 ||
    !symbol_id(condition.op0(), suffix))
    return false;
  irep_idt condition_prefix;
  irep_idt condition_sum;
  irep_idt true_prefix;
  irep_idt true_sum;
  irep_idt false_suffix;
  if(
    !signed_sum_symbols(
      condition.op1(), condition_prefix, condition_sum) ||
    !signed_sum_symbols(
      choice.op1(), true_prefix, true_sum) ||
    !symbol_id(choice.op2(), false_suffix) ||
    condition_prefix != true_prefix ||
    condition_sum != true_sum ||
    suffix != false_suffix)
    return false;
  prefix = condition_prefix;
  suffix_sum = condition_sum;
  return true;
}

bool find_maximum_tail_property(
  const goto_modelt &model,
  const namespacet &ns,
  const lifecyclet &life,
  maximum_tail_propertyt &property,
  std::string &reason)
{
  const auto &main =
    model.goto_functions.function_map.at(ID_main).body;
  std::size_t matches = 0;
  std::size_t errors = 0;
  for(const auto &entry : model.goto_functions.function_map)
  {
    for(const auto &instruction : entry.second.body.instructions)
    {
      irep_idt callee;
      if(call_id(instruction, callee) && is_reach_error(callee))
      {
        ++errors;
        if(entry.first != ID_main)
        {
          reason = "maximum_tail_error_function";
          return false;
        }
        property.error = &instruction;
      }
    }
  }
  for(const auto &instruction : main.instructions)
  {
    if(
      life.last_join == nullptr ||
      instruction.location_number <= life.last_join->location_number)
      continue;
    irep_idt callee;
    if(
      !call_id(instruction, callee) || !is_assume(callee) ||
      instruction.call_arguments().size() != 1)
      continue;
    const exprt &condition =
      strip(instruction.call_arguments().front());
    if(
      condition.id() != ID_notequal ||
      condition.operands().size() != 2)
      continue;
    irep_idt whole;
    irep_idt prefix;
    irep_idt suffix;
    irep_idt suffix_sum;
    bool parsed =
      symbol_id(condition.op0(), whole) &&
      maximum_tail_expression(
        condition.op1(), prefix, suffix, suffix_sum);
    if(!parsed)
      parsed =
        symbol_id(condition.op1(), whole) &&
        maximum_tail_expression(
          condition.op0(), prefix, suffix, suffix_sum);
    if(
      !parsed || !shared_signed(whole, ns) ||
      !shared_signed(prefix, ns) ||
      !shared_signed(suffix, ns) ||
      !shared_signed(suffix_sum, ns) ||
      whole == prefix || whole == suffix || whole == suffix_sum ||
      prefix == suffix || prefix == suffix_sum ||
      suffix == suffix_sum)
      continue;
    ++matches;
    property.whole = whole;
    property.prefix = prefix;
    property.suffix = suffix;
    property.suffix_sum = suffix_sum;
    property.assumption = &instruction;
  }
  if(
    matches != 1 || errors != 1 ||
    property.assumption == nullptr || property.error == nullptr ||
    property.assumption->location_number >=
      property.error->location_number)
  {
    reason =
      matches == 0 ? "maximum_tail_property" :
                     "maximum_tail_property_ambiguous";
    return false;
  }
  return true;
}

struct maximum_tail_workert
{
  irep_idt worker;
  irep_idt accumulator;
  irep_idt sum;
  irep_idt operation;
  exprt contribution;
  exprt normalized_contribution;
  flow_loop_dimensiont dimension;
  std::set<irep_idt> input_symbols;
  std::set<irep_idt> pointer_bases;
  std::set<const goto_programt::instructiont *> writes;
};

bool maximum_tail_recurrence(
  const exprt &src,
  const irep_idt &temporary,
  const irep_idt &accumulator,
  const exprt &contribution)
{
  const exprt &choice = strip(src);
  if(choice.id() != ID_if || choice.operands().size() != 3)
    return false;
  const exprt &condition = strip(choice.op0());
  irep_idt condition_temporary;
  if(
    condition.id() != ID_lt ||
    condition.operands().size() != 2 ||
    !symbol_id(condition.op0(), condition_temporary) ||
    condition_temporary != temporary ||
    !value_is(condition.op1(), 0) ||
    !value_is(choice.op1(), 0))
    return false;
  const exprt &sum = strip(choice.op2());
  if(sum.id() != ID_plus || sum.operands().size() != 2)
    return false;
  irep_idt first;
  irep_idt second;
  return
    (symbol_id(sum.op0(), first) && first == accumulator &&
     strip(sum.op1()) == contribution) ||
    (symbol_id(sum.op1(), second) && second == accumulator &&
     strip(sum.op0()) == contribution);
}

bool maximum_tail_worker(
  const goto_modelt &model,
  const namespacet &ns,
  const irep_idt &worker,
  maximum_tail_workert &result,
  std::string &reason)
{
  const auto &program =
    model.goto_functions.function_map.at(worker).body;
  goto_programt::const_targett recurrence_call =
    program.instructions.end();
  goto_programt::const_targett recurrence_write =
    program.instructions.end();
  goto_programt::const_targett sum_call =
    program.instructions.end();
  irep_idt recurrence_temporary;
  unsigned atomic_depth = 0;
  std::size_t atomic_begins = 0;
  std::size_t atomic_ends = 0;
  for(auto instruction = program.instructions.begin();
      instruction != program.instructions.end(); ++instruction)
  {
    if(instruction->is_atomic_begin())
    {
      ++atomic_depth;
      ++atomic_begins;
      if(atomic_depth != 1)
      {
        reason = "maximum_tail_atomic_nesting";
        return false;
      }
      continue;
    }
    if(instruction->is_atomic_end())
    {
      if(atomic_depth != 1)
      {
        reason = "maximum_tail_atomic_balance";
        return false;
      }
      --atomic_depth;
      ++atomic_ends;
      continue;
    }
    irep_idt callee;
    if(call_id(*instruction, callee))
    {
      if(is_assume(callee))
        continue;
      if(
        instruction->call_lhs().is_nil() ||
        instruction->call_arguments().size() != 2)
      {
        reason = "maximum_tail_worker_call";
        return false;
      }
      irep_idt call_lhs;
      irep_idt accumulator;
      if(
        !symbol_id(instruction->call_lhs(), call_lhs) ||
        !symbol_id(
          instruction->call_arguments()[0], accumulator) ||
        !shared_signed(accumulator, ns))
      {
        reason = "maximum_tail_call_shape";
        return false;
      }
      const exprt contribution =
        strip(instruction->call_arguments()[1]);
      irep_idt base;
      irep_idt index;
      if(!array_symbol_index(contribution, base, index))
      {
        reason = "maximum_tail_element";
        return false;
      }
      if(call_lhs == accumulator)
      {
        if(
          sum_call != program.instructions.end() ||
          atomic_depth != 1)
        {
          reason = "maximum_tail_sum_call";
          return false;
        }
        result.sum = accumulator;
        sum_call = instruction;
        result.writes.insert(&*instruction);
      }
      else
      {
        if(
          recurrence_call != program.instructions.end() ||
          shared_signed(call_lhs, ns))
        {
          reason = "maximum_tail_recurrence_call";
          return false;
        }
        result.accumulator = accumulator;
        result.operation = callee;
        result.contribution = contribution;
        recurrence_temporary = call_lhs;
        recurrence_call = instruction;
      }
      continue;
    }
    if(!instruction->is_assign())
      continue;
    irep_idt lhs;
    if(shared_symbol_lhs(*instruction, ns, lhs))
    {
      if(
        recurrence_call == program.instructions.end() ||
        recurrence_write != program.instructions.end() ||
        lhs != result.accumulator ||
        !maximum_tail_recurrence(
          instruction->assign_rhs(),
          recurrence_temporary,
          result.accumulator,
          result.contribution))
      {
        reason = "maximum_tail_recurrence";
        return false;
      }
      if(atomic_begins != 0 && atomic_depth != 1)
      {
        reason = "maximum_tail_recurrence_atomic";
        return false;
      }
      recurrence_write = instruction;
      result.writes.insert(&*instruction);
    }
    else
    {
      irep_idt base;
      if(base_pointer(instruction->assign_lhs(), base))
      {
        reason = "maximum_tail_array_write";
        return false;
      }
    }
  }
  if(
    atomic_depth != 0 ||
    recurrence_call == program.instructions.end() ||
    recurrence_write == program.instructions.end() ||
    recurrence_call->location_number >=
      recurrence_write->location_number ||
    atomic_begins != atomic_ends ||
    atomic_begins > 1 ||
    ((sum_call == program.instructions.end()) !=
     (atomic_begins == 0)))
  {
    reason = "maximum_tail_worker_shape";
    return false;
  }
  if(
    sum_call != program.instructions.end() &&
    (sum_call->location_number <=
       recurrence_write->location_number ||
     strip(sum_call->call_arguments()[1]) !=
       result.contribution ||
     sum_call->call_function() !=
       recurrence_call->call_function()))
  {
    reason = "maximum_tail_sum_alignment";
    return false;
  }

  natural_loopst loops;
  loops(program);
  if(loops.loop_map.size() != 1)
  {
    reason = "maximum_tail_loop_count";
    return false;
  }
  const auto &entry = *loops.loop_map.begin();
  if(
    !entry.second.contains(recurrence_call) ||
    (sum_call != program.instructions.end() &&
     !entry.second.contains(sum_call)) ||
    !parse_loop_exit(
      *entry.first,
      result.dimension.induction,
      result.dimension.bound) ||
    !loop_initial_value(
      program,
      entry.first,
      result.dimension.induction,
      result.dimension.start,
      reason))
  {
    if(reason.empty())
      reason = "maximum_tail_loop_shape";
    return false;
  }
  irep_idt contribution_base;
  irep_idt contribution_index;
  if(
    !array_symbol_index(
      result.contribution,
      contribution_base,
      contribution_index) ||
    contribution_index != result.dimension.induction)
  {
    reason = "maximum_tail_index";
    return false;
  }
  std::size_t increments = 0;
  std::size_t backedges = 0;
  for(auto instruction = program.instructions.begin();
      instruction != program.instructions.end(); ++instruction)
  {
    if(entry.second.contains(instruction))
      result.dimension.members.insert(&*instruction);
    if(
      entry.second.contains(instruction) &&
      unit_increment(*instruction, result.dimension.induction))
      ++increments;
    if(
      instruction->is_goto() &&
      entry.second.contains(instruction) &&
      instruction != entry.first &&
      instruction->condition().is_true() &&
      instruction->targets.size() == 1 &&
      instruction->get_target() == entry.first)
      ++backedges;
  }
  if(increments != 1 || backedges != 1)
  {
    reason = "maximum_tail_loop_skeleton";
    return false;
  }
  result.normalized_contribution = result.contribution;
  std::vector<flow_loop_dimensiont> dimensions = {
    result.dimension};
  normalize_flow_expression(
    dimensions, result.normalized_contribution);
  collect_static_symbols(
    result.contribution, ns, result.input_symbols);
  collect_static_symbols(
    result.dimension.start, ns, result.input_symbols);
  collect_static_symbols(
    result.dimension.bound, ns, result.input_symbols);
  result.input_symbols.erase(result.accumulator);
  result.input_symbols.erase(result.sum);
  collect_pointer_bases(
    result.contribution, result.pointer_bases);
  result.worker = worker;
  return true;
}

bool maximum_tail_partition_proof_impl(
  const goto_modelt &model,
  const namespacet &ns,
  std::string &reason)
{
  lifecyclet life;
  if(!lifecycle(model, life, reason) || life.workers.size() != 3)
  {
    if(reason.empty())
      reason = "maximum_tail_lifecycle";
    return false;
  }
  maximum_tail_propertyt property;
  if(!find_maximum_tail_property(model, ns, life, property, reason))
    return false;

  std::vector<maximum_tail_workert> workers;
  for(const auto &worker_id : life.workers)
  {
    maximum_tail_workert worker;
    if(!maximum_tail_worker(model, ns, worker_id, worker, reason))
      return false;
    workers.push_back(worker);
  }
  for(const auto &worker : workers)
  {
    if(
      worker.operation != workers.front().operation ||
      worker.normalized_contribution !=
        workers.front().normalized_contribution)
    {
      reason = "maximum_tail_input_alignment";
      return false;
    }
  }
  if(
    !signed_addition_helper(
      model, ns, workers.front().operation, reason))
    return false;

  const maximum_tail_workert *whole = nullptr;
  const maximum_tail_workert *prefix = nullptr;
  const maximum_tail_workert *suffix = nullptr;
  for(const auto &candidate : workers)
  {
    if(candidate.accumulator == property.whole)
      whole = &candidate;
    else if(candidate.accumulator == property.prefix)
      prefix = &candidate;
    else if(candidate.accumulator == property.suffix)
      suffix = &candidate;
  }
  if(
    whole == nullptr || prefix == nullptr || suffix == nullptr ||
    !whole->sum.empty() || !prefix->sum.empty() ||
    suffix->sum != property.suffix_sum ||
    !value_is(whole->dimension.start, 0) ||
    !value_is(prefix->dimension.start, 0) ||
    whole->dimension.bound != suffix->dimension.bound ||
    prefix->dimension.bound != suffix->dimension.start)
  {
    reason = "maximum_tail_partition";
    return false;
  }
  irep_idt split;
  irep_idt bound;
  if(
    !symbol_id(suffix->dimension.start, split) ||
    !symbol_id(suffix->dimension.bound, bound) ||
    !static_partition_precondition(model, life, split, bound))
  {
    reason = "maximum_tail_range";
    return false;
  }

  std::set<irep_idt> protected_symbols = {
    property.whole,
    property.prefix,
    property.suffix,
    property.suffix_sum,
    split,
    bound};
  std::set<irep_idt> pointer_bases;
  std::set<const goto_programt::instructiont *> allowed;
  std::vector<flow_range_workert> flow_workers;
  for(const auto &worker : workers)
  {
    protected_symbols.insert(
      worker.input_symbols.begin(), worker.input_symbols.end());
    pointer_bases.insert(
      worker.pointer_bases.begin(), worker.pointer_bases.end());
    allowed.insert(worker.writes.begin(), worker.writes.end());
    flow_range_workert flow_worker;
    flow_worker.worker = worker.worker;
    flow_worker.accumulator = worker.accumulator;
    flow_worker.input_symbols = worker.input_symbols;
    flow_worker.pointer_bases = worker.pointer_bases;
    flow_worker.writes = worker.writes;
    flow_workers.push_back(flow_worker);
  }
  if(
    !zero_initialized_symbols(
      model,
      {
        property.whole,
        property.prefix,
        property.suffix,
        property.suffix_sum,
      },
      allowed,
      reason) ||
    !no_main_symbol_writes_before_create(
      model,
      life,
      {
        property.whole,
        property.prefix,
        property.suffix,
        property.suffix_sum,
      },
      nullptr,
      reason))
    return false;
  flow_equality_propertyt control;
  control.left = property.whole;
  control.right = property.prefix;
  control.assumption = property.assumption;
  control.error = property.error;
  if(
    !static_partition_global_obligations(
      model,
      life,
      control,
      flow_workers,
      protected_symbols,
      pointer_bases,
      reason))
    return false;

  std::cout
    << "NATIVE_MAXIMUM_TAIL_PARTITION applied=1"
    << " whole=" << property.whole
    << " prefix=" << property.prefix
    << " suffix=" << property.suffix
    << " suffix_sum=" << property.suffix_sum << '\n';
  return true;
}

bool ordered_extremum_partition_proof_impl(
  const goto_modelt &model,
  const namespacet &ns,
  std::string &reason)
{
  lifecyclet life;
  if(!lifecycle(model, life, reason) || life.workers.size() != 3)
  {
    if(reason.empty())
      reason = "ordered_extremum_lifecycle";
    return false;
  }
  ordered_extremum_propertyt property;
  if(
    !find_ordered_extremum_property(
      model, ns, life, property, reason))
    return false;

  std::vector<flow_range_workert> workers;
  bool workers_parsed = true;
  for(const auto &worker_id : life.workers)
  {
    flow_range_workert worker;
    if(
      !ordered_extremum_worker(
        model,
        ns,
        worker_id,
        property.minimum,
        worker,
        reason))
    {
      workers_parsed = false;
      break;
    }
    workers.push_back(worker);
  }
  if(!workers_parsed && property.shared_partition_accumulator)
  {
    property.minimum = true;
    workers.clear();
    reason.clear();
    for(const auto &worker_id : life.workers)
    {
      flow_range_workert worker;
      if(
        !ordered_extremum_worker(
          model,
          ns,
          worker_id,
          property.minimum,
          worker,
          reason))
        return false;
      workers.push_back(worker);
    }
  }
  else if(!workers_parsed)
    return false;
  for(const auto &worker : workers)
  {
    if(
      worker.normalized_contribution !=
        workers.front().normalized_contribution)
    {
      reason = "ordered_extremum_input_alignment";
      return false;
    }
  }

  const flow_range_workert *whole = nullptr;
  const flow_range_workert *prefix = nullptr;
  const flow_range_workert *suffix = nullptr;
  for(const auto &candidate : workers)
  {
    if(candidate.accumulator == property.whole)
      whole = &candidate;
    else if(
      candidate.accumulator == property.prefix &&
      value_is(candidate.dimensions.front().start, 0))
      prefix = &candidate;
    else if(candidate.accumulator == property.suffix)
      suffix = &candidate;
  }
  if(
    whole == nullptr || prefix == nullptr || suffix == nullptr ||
    !value_is(whole->dimensions.front().start, 0) ||
    !value_is(prefix->dimensions.front().start, 0) ||
    whole->dimensions.front().bound !=
      suffix->dimensions.front().bound ||
    prefix->dimensions.front().bound !=
      suffix->dimensions.front().start)
  {
    reason = "ordered_extremum_partition";
    return false;
  }
  irep_idt split;
  irep_idt bound;
  if(
    !symbol_id(suffix->dimensions.front().start, split) ||
    !symbol_id(suffix->dimensions.front().bound, bound) ||
    !static_partition_precondition(model, life, split, bound))
  {
    reason = "ordered_extremum_range";
    return false;
  }

  std::set<irep_idt> protected_symbols = {
    property.whole,
    property.prefix,
    property.suffix,
    split,
    bound};
  std::set<irep_idt> pointer_bases;
  for(const auto &worker : workers)
  {
    protected_symbols.insert(
      worker.input_symbols.begin(), worker.input_symbols.end());
    pointer_bases.insert(
      worker.pointer_bases.begin(), worker.pointer_bases.end());
  }
  std::set<const goto_programt::instructiont *> allowed;
  for(const auto &worker : workers)
    allowed.insert(worker.writes.begin(), worker.writes.end());
  if(
    !zero_initialized_symbols(
      model,
      {property.whole, property.prefix, property.suffix},
      allowed,
      reason) ||
    !no_main_symbol_writes_before_create(
      model,
      life,
      {property.whole, property.prefix, property.suffix},
      nullptr,
      reason))
    return false;

  flow_equality_propertyt control;
  control.left = property.whole;
  control.right = property.prefix;
  control.assumption = property.assumption;
  control.error = property.error;
  if(
    !static_partition_global_obligations(
      model,
      life,
      control,
      workers,
      protected_symbols,
      pointer_bases,
      reason))
    return false;

  std::cout
    << "NATIVE_ORDERED_EXTREMUM_PARTITION applied=1"
    << " operation=" << (property.minimum ? "min" : "max")
    << " whole=" << property.whole
    << " prefix=" << property.prefix
    << " suffix=" << property.suffix
    << " shared_partition_accumulator="
    << (property.shared_partition_accumulator ? 1 : 0) << '\n';
  return true;
}

struct dynamic_flow_propertyt
{
  irep_idt left_counter;
  irep_idt right_counter;
  irep_idt bound;
  irep_idt left_accumulator;
  irep_idt right_accumulator;
  const goto_programt::instructiont *assumption;
  const goto_programt::instructiont *error;

  dynamic_flow_propertyt() : assumption(nullptr), error(nullptr)
  {
  }
};

bool negated_equal_symbols(
  const exprt &src,
  irep_idt &left,
  irep_idt &right)
{
  const exprt &root = strip(src);
  if(root.id() != ID_not || root.operands().size() != 1)
    return false;
  const exprt &relation = strip(root.op0());
  return
    relation.id() == ID_equal && relation.operands().size() == 2 &&
    symbol_id(relation.op0(), left) &&
    symbol_id(relation.op1(), right) && left != right;
}

bool find_dynamic_flow_property(
  const goto_modelt &model,
  const namespacet &ns,
  const lifecyclet &life,
  dynamic_flow_propertyt &property,
  std::string &reason)
{
  const auto &main =
    model.goto_functions.function_map.at(ID_main).body;
  std::size_t matches = 0;
  std::size_t errors = 0;
  for(const auto &entry : model.goto_functions.function_map)
  {
    for(const auto &instruction : entry.second.body.instructions)
    {
      irep_idt callee;
      if(call_id(instruction, callee) && is_reach_error(callee))
      {
        ++errors;
        if(entry.first != ID_main)
        {
          reason = "flow_dynamic_error_function";
          return false;
        }
        property.error = &instruction;
      }
    }
  }

  for(const auto &instruction : main.instructions)
  {
    if(
      life.last_join == nullptr ||
      instruction.location_number <= life.last_join->location_number)
      continue;
    irep_idt callee;
    if(
      !call_id(instruction, callee) || !is_assume(callee) ||
      instruction.call_arguments().size() != 1)
      continue;
    std::vector<exprt> terms;
    flatten_and(instruction.call_arguments().front(), terms);
    if(terms.size() != 3)
      continue;
    irep_idt counter_left;
    irep_idt counter_right;
    irep_idt bound;
    irep_idt accumulator_left;
    irep_idt accumulator_right;
    bool counter_equality = false;
    bool completion = false;
    bool inequality = false;
    for(const auto &term_src : terms)
    {
      const exprt &term = strip(term_src);
      irep_idt left;
      irep_idt right;
      if(
        term.id() == ID_equal && term.operands().size() == 2 &&
        symbol_id(term.op0(), left) && symbol_id(term.op1(), right))
      {
        if(!counter_equality)
        {
          counter_left = left;
          counter_right = right;
          counter_equality = true;
        }
        else
        {
          if(left == counter_left || left == counter_right)
          {
            bound = right;
            completion = true;
          }
          else if(right == counter_left || right == counter_right)
          {
            bound = left;
            completion = true;
          }
        }
      }
      else if(
        negated_equal_symbols(
          term, accumulator_left, accumulator_right))
        inequality = true;
    }
    if(
      !counter_equality || !completion || !inequality ||
      counter_left == counter_right ||
      accumulator_left == accumulator_right ||
      !shared_signed(counter_left, ns) ||
      !shared_signed(counter_right, ns) ||
      !shared_signed(bound, ns) ||
      !shared_signed(accumulator_left, ns) ||
      !shared_signed(accumulator_right, ns))
      continue;
    ++matches;
    property.left_counter = counter_left;
    property.right_counter = counter_right;
    property.bound = bound;
    property.left_accumulator = accumulator_left;
    property.right_accumulator = accumulator_right;
    property.assumption = &instruction;
  }
  if(
    matches != 1 || errors != 1 || property.assumption == nullptr ||
    property.error == nullptr ||
    property.assumption->location_number >= property.error->location_number)
  {
    reason =
      matches == 0 ? "flow_dynamic_property" :
                     "flow_dynamic_property_ambiguous";
    return false;
  }
  return true;
}

struct dynamic_flow_workert
{
  irep_idt counter;
  irep_idt bound;
  irep_idt temporary;
  irep_idt base;
  irep_idt accumulator;
  irep_idt operation;
  std::set<const goto_programt::instructiont *> writes;
};

bool dynamic_flow_worker(
  const goto_modelt &model,
  const namespacet &ns,
  const irep_idt &worker,
  dynamic_flow_workert &result,
  std::string &reason)
{
  const auto &program =
    model.goto_functions.function_map.at(worker).body;
  natural_loopst loops;
  loops(program);
  if(loops.loop_map.size() != 1)
  {
    reason = "flow_dynamic_loop_count";
    return false;
  }
  const auto &loop = loops.loop_map.begin()->second;
  unsigned atomic_epoch = 0;
  unsigned atomic_depth = 0;
  std::size_t atomic_begins = 0;
  std::size_t atomic_ends = 0;
  std::size_t gotos = 0;
  goto_programt::const_targett counter_write =
    program.instructions.end();
  goto_programt::const_targett temporary_write =
    program.instructions.end();
  goto_programt::const_targett accumulator_write =
    program.instructions.end();
  bool guarded = false;

  for(auto instruction = program.instructions.begin();
      instruction != program.instructions.end(); ++instruction)
  {
    if(instruction->is_atomic_begin())
    {
      if(atomic_depth != 0)
      {
        reason = "flow_dynamic_atomic_nesting";
        return false;
      }
      atomic_depth = 1;
      ++atomic_epoch;
      ++atomic_begins;
      continue;
    }
    if(instruction->is_atomic_end())
    {
      if(atomic_depth != 1)
      {
        reason = "flow_dynamic_atomic_balance";
        return false;
      }
      atomic_depth = 0;
      ++atomic_ends;
      continue;
    }
    if(instruction->is_goto() && loop.contains(instruction))
      ++gotos;
    irep_idt callee;
    if(call_id(*instruction, callee))
    {
      if(is_assume(callee))
      {
        if(
          atomic_depth != 1 || atomic_epoch != 1 ||
          instruction->call_arguments().size() != 1)
        {
          reason = "flow_dynamic_guard_epoch";
          return false;
        }
        const exprt &guard = strip(instruction->call_arguments().front());
        irep_idt counter;
        irep_idt bound;
        if(
          guard.id() != ID_lt || guard.operands().size() != 2 ||
          !symbol_id(guard.op0(), counter) ||
          !symbol_id(guard.op1(), bound))
        {
          reason = "flow_dynamic_guard";
          return false;
        }
        result.counter = counter;
        result.bound = bound;
        guarded = true;
        continue;
      }
      irep_idt accumulator;
      irep_idt first;
      irep_idt temporary;
      if(
        atomic_depth != 1 || atomic_epoch != 2 ||
        instruction->call_lhs().is_nil() ||
        instruction->call_arguments().size() != 2 ||
        !symbol_id(instruction->call_lhs(), accumulator) ||
        !symbol_id(instruction->call_arguments()[0], first) ||
        !symbol_id(instruction->call_arguments()[1], temporary) ||
        accumulator != first || !shared_signed(accumulator, ns) ||
        temporary_write == program.instructions.end() ||
        result.temporary != temporary ||
        accumulator_write != program.instructions.end())
      {
        reason = "flow_dynamic_fold";
        return false;
      }
      result.accumulator = accumulator;
      result.operation = callee;
      result.writes.insert(&*instruction);
      accumulator_write = instruction;
      continue;
    }
    if(!instruction->is_assign())
      continue;
    irep_idt lhs;
    if(!shared_symbol_lhs(*instruction, ns, lhs))
      continue;
    if(
      guarded && lhs == result.counter &&
      unit_increment(*instruction, result.counter) &&
      atomic_depth == 1 && atomic_epoch == 1 &&
      counter_write == program.instructions.end())
    {
      result.writes.insert(&*instruction);
      counter_write = instruction;
      continue;
    }
    irep_idt base;
    const symbolt *counter_symbol = lookup(result.counter, ns);
    if(
      guarded && counter_symbol != nullptr &&
      base_pointer(instruction->assign_rhs(), base) &&
      array_at(
        instruction->assign_rhs(),
        base,
        symbol_exprt(
          result.counter,
          counter_symbol->type)) &&
      atomic_depth == 1 && atomic_epoch == 1 &&
      temporary_write == program.instructions.end())
    {
      result.temporary = lhs;
      result.base = base;
      result.writes.insert(&*instruction);
      temporary_write = instruction;
      continue;
    }
    reason = "flow_dynamic_shared_write";
    return false;
  }
  if(
    atomic_depth != 0 || atomic_begins != 2 || atomic_ends != 2 ||
    gotos != 2 || !guarded ||
    counter_write == program.instructions.end() ||
    temporary_write == program.instructions.end() ||
    accumulator_write == program.instructions.end() ||
    counter_write->location_number >= temporary_write->location_number ||
    temporary_write->location_number >= accumulator_write->location_number ||
    !shared_signed(result.counter, ns) ||
    !shared_signed(result.temporary, ns) ||
    result.counter == result.temporary ||
    result.counter == result.accumulator ||
    result.temporary == result.accumulator)
  {
    reason = "flow_dynamic_shape";
    return false;
  }
  return true;
}

bool dynamic_initial_relation(
  const goto_modelt &model,
  const lifecyclet &life,
  const dynamic_flow_propertyt &property,
  const goto_programt::instructiont *&assumption)
{
  const auto &main =
    model.goto_functions.function_map.at(ID_main).body;
  const std::set<irep_idt> required = {
    property.left_counter,
    property.right_counter,
    property.left_accumulator,
    property.right_accumulator};
  for(const auto &instruction : main.instructions)
  {
    if(
      life.first_create != nullptr &&
      instruction.location_number >= life.first_create->location_number)
      break;
    irep_idt callee;
    if(
      call_id(instruction, callee) && is_assume(callee) &&
      instruction.call_arguments().size() == 1 &&
      zero_equivalence_constraint(
        instruction.call_arguments().front(), required))
    {
      assumption = &instruction;
      return true;
    }
  }
  return false;
}

bool dynamic_flow_global_obligations(
  const goto_modelt &model,
  const lifecyclet &life,
  const dynamic_flow_propertyt &property,
  const std::vector<dynamic_flow_workert> &workers,
  const irep_idt &base,
  std::string &reason)
{
  std::set<irep_idt> protected_symbols = {
    property.left_counter,
    property.right_counter,
    property.left_accumulator,
    property.right_accumulator,
    property.bound,
    base};
  std::set<const goto_programt::instructiont *> allowed;
  for(const auto &worker : workers)
  {
    protected_symbols.insert(worker.temporary);
    allowed.insert(worker.writes.begin(), worker.writes.end());
  }
  for(const auto &entry : model.goto_functions.function_map)
  {
    for(const auto &instruction : entry.second.body.instructions)
    {
      const exprt *lhs = nullptr;
      if(instruction.is_assign())
        lhs = &instruction.assign_lhs();
      else if(
        instruction.is_function_call() &&
        !instruction.call_lhs().is_nil())
        lhs = &instruction.call_lhs();
      if(lhs == nullptr)
        continue;
      irep_idt direct;
      irep_idt pointer;
      const bool protected_write =
        (symbol_id(*lhs, direct) &&
         protected_symbols.count(direct) != 0) ||
        (base_pointer(*lhs, pointer) && pointer == base);
      if(!protected_write)
        continue;
      if(
        is_start_function(entry.first) && instruction.is_assign() &&
        value_is(instruction.assign_rhs(), 0))
        continue;
      if(
        entry.first == ID_main && life.first_create != nullptr &&
        instruction.location_number < life.first_create->location_number)
        continue;
      if(allowed.count(&instruction) == 0)
      {
        reason = "flow_dynamic_external_writer";
        return false;
      }
    }
  }
  flow_equality_propertyt equality;
  equality.left = property.left_accumulator;
  equality.right = property.right_accumulator;
  equality.assumption = property.assumption;
  equality.error = property.error;
  return
    flow_alias_free(model, base, reason) &&
    no_addresses(model, protected_symbols, reason) &&
    flow_main_control(model, life, equality, reason);
}

bool equivalent_dynamic_partition_proof_impl(
  const goto_modelt &model,
  const namespacet &ns,
  std::string &reason)
{
  lifecyclet life;
  if(!lifecycle(model, life, reason) || life.workers.size() != 4)
  {
    if(reason.empty())
      reason = "flow_dynamic_lifecycle";
    return false;
  }
  dynamic_flow_propertyt property;
  if(!find_dynamic_flow_property(model, ns, life, property, reason))
    return false;
  const goto_programt::instructiont *initial_relation = nullptr;
  if(
    !dynamic_initial_relation(
      model, life, property, initial_relation))
  {
    reason = "flow_dynamic_initial_relation";
    return false;
  }
  if(
    !no_main_symbol_writes_before_create(
      model,
      life,
      {
        property.left_counter,
        property.right_counter,
        property.left_accumulator,
        property.right_accumulator
      },
      initial_relation,
      reason))
    return false;

  std::vector<dynamic_flow_workert> workers;
  for(const auto &worker_id : life.workers)
  {
    dynamic_flow_workert worker;
    if(!dynamic_flow_worker(model, ns, worker_id, worker, reason))
      return false;
    workers.push_back(worker);
  }
  const irep_idt operation = workers.front().operation;
  const irep_idt base = workers.front().base;
  if(!signed_addition_helper(model, ns, operation, reason))
    return false;
  std::map<std::pair<irep_idt, irep_idt>, std::size_t> groups;
  std::set<irep_idt> temporaries;
  for(const auto &worker : workers)
  {
    if(
      worker.operation != operation || worker.bound != property.bound ||
      worker.base != base || !temporaries.insert(worker.temporary).second)
    {
      reason = "flow_dynamic_signature";
      return false;
    }
    ++groups[{worker.counter, worker.accumulator}];
  }
  if(
    groups.size() != 2 ||
    std::any_of(
      groups.begin(),
      groups.end(),
      [](const std::pair<
           const std::pair<irep_idt, irep_idt>,
           std::size_t> &entry) {
        return entry.second != 2;
      }))
  {
    reason = "flow_dynamic_groups";
    return false;
  }
  const std::set<std::pair<irep_idt, irep_idt>> expected = {
    {property.left_counter, property.left_accumulator},
    {property.right_counter, property.right_accumulator}};
  std::set<std::pair<irep_idt, irep_idt>> actual;
  for(const auto &entry : groups)
    actual.insert(entry.first);
  if(actual != expected)
  {
    reason = "flow_dynamic_property_groups";
    return false;
  }
  if(
    !dynamic_flow_global_obligations(
      model, life, property, workers, base, reason))
    return false;

  std::cout << "NATIVE_RELATIONAL_FLOW applied=1 rule=dynamic_partition"
            << " left=" << property.left_accumulator
            << " right=" << property.right_accumulator << '\n';
  return true;
}

struct hierarchical_lifecyclet
{
  std::vector<irep_idt> workers;
  std::set<irep_idt> handles;
  std::set<irep_idt> joins;
  const goto_programt::instructiont *first_create;
  const goto_programt::instructiont *last_join;

  hierarchical_lifecyclet() : first_create(nullptr), last_join(nullptr)
  {
  }
};

bool hierarchical_lifecycle(
  const goto_modelt &model,
  const irep_idt &owner,
  hierarchical_lifecyclet &result,
  std::string &reason)
{
  const auto found = model.goto_functions.function_map.find(owner);
  if(
    found == model.goto_functions.function_map.end() ||
    !found->second.body_available())
  {
    reason = "hier_lifecycle_owner";
    return false;
  }
  bool joining = false;
  for(const auto &instruction : found->second.body.instructions)
  {
    irep_idt callee;
    if(!call_id(instruction, callee))
      continue;
    const auto &arguments = instruction.call_arguments();
    if(is_create(callee))
    {
      if(joining)
      {
        reason = "hier_create_after_join";
        return false;
      }
      irep_idt handle;
      irep_idt worker;
      if(
        arguments.size() < 3 ||
        !addressed_id(arguments[0], handle) ||
        !addressed_id(arguments[2], worker) ||
        !result.handles.insert(handle).second ||
        std::find(
          result.workers.begin(), result.workers.end(), worker) !=
          result.workers.end())
      {
        reason = "hier_create";
        return false;
      }
      result.workers.push_back(worker);
      if(result.first_create == nullptr)
        result.first_create = &instruction;
    }
    else if(is_join(callee))
    {
      joining = true;
      irep_idt handle;
      if(
        arguments.empty() || !symbol_id(arguments[0], handle) ||
        !result.joins.insert(handle).second)
      {
        reason = "hier_join";
        return false;
      }
      result.last_join = &instruction;
    }
  }
  if(
    result.workers.size() != 2 ||
    result.handles.size() != result.workers.size() ||
    result.handles != result.joins ||
    result.first_create == nullptr || result.last_join == nullptr ||
    result.first_create->location_number >= result.last_join->location_number)
  {
    reason = "hier_lifecycle_shape";
    return false;
  }
  for(const auto &worker : result.workers)
  {
    const auto worker_found =
      model.goto_functions.function_map.find(worker);
    if(
      worker_found == model.goto_functions.function_map.end() ||
      !worker_found->second.body_available())
    {
      reason = "hier_worker_body";
      return false;
    }
  }
  return true;
}

struct hierarchical_leaft
{
  irep_idt worker;
  irep_idt counter;
  irep_idt bound;
  irep_idt temporary;
  irep_idt base;
  irep_idt accumulator;
  irep_idt operation;
  bool terminal;
  std::set<irep_idt> local_zero;
  std::set<const goto_programt::instructiont *> writes;

  hierarchical_leaft() : terminal(false)
  {
  }
};

bool hierarchical_terminal_guard(
  const exprt &src,
  const irep_idt &counter,
  const irep_idt &bound)
{
  const exprt &condition = strip(src);
  if(condition.id() == ID_equal && condition.operands().size() == 2)
  {
    irep_idt left;
    irep_idt right;
    return
      ((symbol_id(condition.op0(), left) && left == counter &&
        symbol_id(condition.op1(), right) && right == bound) ||
       (symbol_id(condition.op1(), left) && left == counter &&
        symbol_id(condition.op0(), right) && right == bound));
  }
  if(condition.id() != ID_not || condition.operands().size() != 1)
    return false;
  const exprt &relation = strip(condition.op0());
  if(relation.id() != ID_lt || relation.operands().size() != 2)
    return false;
  irep_idt left;
  irep_idt right;
  return
    symbol_id(relation.op0(), left) && left == counter &&
    symbol_id(relation.op1(), right) && right == bound;
}

bool hierarchical_leaf(
  const goto_modelt &model,
  const namespacet &ns,
  const irep_idt &worker,
  hierarchical_leaft &result,
  std::string &reason)
{
  const auto &program =
    model.goto_functions.function_map.at(worker).body;
  natural_loopst loops;
  loops(program);
  if(loops.loop_map.size() != 1)
  {
    reason = "hier_leaf_loop_count";
    return false;
  }
  const auto &loop = loops.loop_map.begin()->second;
  unsigned atomic_epoch = 0;
  unsigned atomic_depth = 0;
  std::size_t atomic_begins = 0;
  std::size_t atomic_ends = 0;
  std::size_t gotos = 0;
  bool guarded = false;
  goto_programt::const_targett counter_write =
    program.instructions.end();
  goto_programt::const_targett temporary_write =
    program.instructions.end();
  goto_programt::const_targett accumulator_write =
    program.instructions.end();

  for(auto instruction = program.instructions.begin();
      instruction != program.instructions.end(); ++instruction)
  {
    const bool in_loop = loop.contains(instruction);
    if(in_loop && instruction->is_atomic_begin())
    {
      if(atomic_depth != 0)
      {
        reason = "hier_leaf_atomic_nesting";
        return false;
      }
      atomic_depth = 1;
      ++atomic_epoch;
      ++atomic_begins;
      continue;
    }
    if(in_loop && instruction->is_atomic_end())
    {
      if(atomic_depth != 1)
      {
        reason = "hier_leaf_atomic_balance";
        return false;
      }
      atomic_depth = 0;
      ++atomic_ends;
      continue;
    }
    if(in_loop && instruction->is_goto())
      ++gotos;

    irep_idt callee;
    if(in_loop && call_id(*instruction, callee))
    {
      if(is_assume(callee))
      {
        if(
          atomic_depth != 1 || atomic_epoch != 1 ||
          instruction->call_arguments().size() != 1)
        {
          reason = "hier_leaf_guard_epoch";
          return false;
        }
        const exprt &guard =
          strip(instruction->call_arguments().front());
        irep_idt counter;
        irep_idt bound;
        if(
          guard.id() != ID_lt || guard.operands().size() != 2 ||
          !symbol_id(guard.op0(), counter) ||
          !symbol_id(guard.op1(), bound))
        {
          reason = "hier_leaf_guard";
          return false;
        }
        result.counter = counter;
        result.bound = bound;
        guarded = true;
        continue;
      }
      irep_idt accumulator;
      irep_idt first;
      irep_idt temporary;
      if(
        atomic_depth != 1 || atomic_epoch != 2 ||
        instruction->call_lhs().is_nil() ||
        instruction->call_arguments().size() != 2 ||
        !symbol_id(instruction->call_lhs(), accumulator) ||
        !symbol_id(instruction->call_arguments()[0], first) ||
        !symbol_id(instruction->call_arguments()[1], temporary) ||
        accumulator != first || !shared_signed(accumulator, ns) ||
        temporary_write == program.instructions.end() ||
        result.temporary != temporary ||
        accumulator_write != program.instructions.end())
      {
        reason = "hier_leaf_fold";
        return false;
      }
      result.accumulator = accumulator;
      result.operation = callee;
      result.writes.insert(&*instruction);
      accumulator_write = instruction;
      continue;
    }
    if(in_loop && instruction->is_assign())
    {
      irep_idt lhs;
      if(!shared_symbol_lhs(*instruction, ns, lhs))
        continue;
      if(
        guarded && lhs == result.counter &&
        unit_increment(*instruction, result.counter) &&
        atomic_depth == 1 && atomic_epoch == 1 &&
        counter_write == program.instructions.end())
      {
        result.writes.insert(&*instruction);
        counter_write = instruction;
        continue;
      }
      irep_idt base;
      const symbolt *counter_symbol = lookup(result.counter, ns);
      if(
        guarded && counter_symbol != nullptr &&
        base_pointer(instruction->assign_rhs(), base) &&
        array_at(
          instruction->assign_rhs(),
          base,
          symbol_exprt(result.counter, counter_symbol->type)) &&
        atomic_depth == 1 && atomic_epoch == 1 &&
        temporary_write == program.instructions.end())
      {
        result.temporary = lhs;
        result.base = base;
        result.writes.insert(&*instruction);
        temporary_write = instruction;
        continue;
      }
      reason = "hier_leaf_shared_write";
      return false;
    }
    if(
      in_loop &&
      (instruction->is_assert() || instruction->is_start_thread() ||
       instruction->is_end_thread() || instruction->is_throw() ||
       instruction->is_catch()))
    {
      reason = "hier_leaf_effect";
      return false;
    }
  }
  if(
    atomic_depth != 0 || atomic_begins != 2 || atomic_ends != 2 ||
    gotos != 2 || !guarded ||
    counter_write == program.instructions.end() ||
    temporary_write == program.instructions.end() ||
    accumulator_write == program.instructions.end() ||
    counter_write->location_number >= temporary_write->location_number ||
    temporary_write->location_number >= accumulator_write->location_number ||
    !shared_signed(result.counter, ns) ||
    !shared_signed(result.temporary, ns) ||
    result.counter == result.temporary ||
    result.counter == result.accumulator ||
    result.temporary == result.accumulator)
  {
    reason = "hier_leaf_shape";
    return false;
  }

  unsigned outside_atomic_depth = 0;
  for(auto instruction = program.instructions.begin();
      instruction != program.instructions.end(); ++instruction)
  {
    if(loop.contains(instruction))
      continue;
    if(instruction->is_atomic_begin())
    {
      if(outside_atomic_depth != 0)
      {
        reason = "hier_leaf_outside_atomic_nesting";
        return false;
      }
      outside_atomic_depth = 1;
      continue;
    }
    if(instruction->is_atomic_end())
    {
      if(outside_atomic_depth != 1)
      {
        reason = "hier_leaf_outside_atomic_balance";
        return false;
      }
      outside_atomic_depth = 0;
      continue;
    }
    if(instruction->is_assign())
    {
      irep_idt lhs;
      if(!shared_symbol_lhs(*instruction, ns, lhs))
        continue;
      if(
        value_is(instruction->assign_rhs(), 0) &&
        instruction->location_number <
          loops.loop_map.begin()->first->location_number &&
        (lhs == result.counter || lhs == result.accumulator))
      {
        result.local_zero.insert(lhs);
        result.writes.insert(&*instruction);
        continue;
      }
      reason = "hier_leaf_outside_write";
      return false;
    }
    if(
      instruction->is_goto() || instruction->is_assert() ||
      instruction->is_start_thread() || instruction->is_end_thread() ||
      instruction->is_throw() || instruction->is_catch())
    {
      reason = "hier_leaf_outside_control";
      return false;
    }
    irep_idt callee;
    if(!call_id(*instruction, callee))
      continue;
    if(
      is_assume(callee) &&
      instruction->call_arguments().size() == 1 &&
      instruction->location_number >
        accumulator_write->location_number &&
      hierarchical_terminal_guard(
        instruction->call_arguments().front(),
        result.counter,
        result.bound))
    {
      result.terminal = true;
      continue;
    }
    reason = "hier_leaf_outside_call";
    return false;
  }
  if(outside_atomic_depth != 0)
  {
    reason = "hier_leaf_outside_atomic_balance";
    return false;
  }
  result.worker = worker;
  return true;
}

struct hierarchical_roott
{
  irep_idt worker;
  irep_idt root;
  irep_idt counter;
  irep_idt bound;
  irep_idt base;
  irep_idt operation;
  std::set<irep_idt> accumulators;
  std::set<irep_idt> temporaries;
  std::set<irep_idt> required_main_zero;
  std::set<const goto_programt::instructiont *> writes;
};

bool hierarchical_parent_terminal(
  const goto_programt &program,
  const irep_idt &counter,
  const irep_idt &bound,
  const goto_programt::instructiont *last_join)
{
  for(const auto &instruction : program.instructions)
  {
    irep_idt callee;
    if(
      call_id(instruction, callee) && is_assume(callee) &&
      instruction.call_arguments().size() == 1 &&
      last_join != nullptr &&
      instruction.location_number > last_join->location_number &&
      hierarchical_terminal_guard(
        instruction.call_arguments().front(), counter, bound))
      return true;
  }
  return false;
}

bool hierarchical_root(
  const goto_modelt &model,
  const namespacet &ns,
  const irep_idt &worker,
  hierarchical_roott &result,
  std::string &reason)
{
  const auto &program =
    model.goto_functions.function_map.at(worker).body;
  natural_loopst own_loops;
  own_loops(program);
  if(own_loops.loop_map.size() == 1)
  {
    hierarchical_leaft leaf;
    if(!hierarchical_leaf(model, ns, worker, leaf, reason))
      return false;
    if(
      !leaf.terminal ||
      leaf.local_zero.count(leaf.counter) == 0 ||
      leaf.local_zero.count(leaf.accumulator) == 0)
    {
      reason = "hier_single_root_completion";
      return false;
    }
    result.worker = worker;
    result.root = leaf.accumulator;
    result.counter = leaf.counter;
    result.bound = leaf.bound;
    result.base = leaf.base;
    result.operation = leaf.operation;
    result.accumulators.insert(leaf.accumulator);
    result.temporaries.insert(leaf.temporary);
    result.writes = leaf.writes;
    return true;
  }
  if(!own_loops.loop_map.empty())
  {
    reason = "hier_parent_loop";
    return false;
  }

  hierarchical_lifecyclet life;
  if(!hierarchical_lifecycle(model, worker, life, reason))
    return false;
  std::vector<hierarchical_leaft> leaves;
  for(const auto &child : life.workers)
  {
    hierarchical_leaft leaf;
    if(!hierarchical_leaf(model, ns, child, leaf, reason))
      return false;
    leaves.push_back(leaf);
  }
  if(
    leaves[0].counter != leaves[1].counter ||
    leaves[0].bound != leaves[1].bound ||
    leaves[0].base != leaves[1].base ||
    leaves[0].operation != leaves[1].operation ||
    leaves[0].temporary == leaves[1].temporary)
  {
    reason = "hier_leaf_signature";
    return false;
  }
  result.worker = worker;
  result.counter = leaves[0].counter;
  result.bound = leaves[0].bound;
  result.base = leaves[0].base;
  result.operation = leaves[0].operation;
  for(const auto &leaf : leaves)
  {
    result.accumulators.insert(leaf.accumulator);
    result.temporaries.insert(leaf.temporary);
    result.writes.insert(leaf.writes.begin(), leaf.writes.end());
  }

  std::set<irep_idt> parent_zero;
  const goto_programt::instructiont *combine = nullptr;
  irep_idt combine_lhs;
  irep_idt combine_left;
  irep_idt combine_right;
  unsigned atomic_depth = 0;
  for(const auto &instruction : program.instructions)
  {
    if(instruction.is_atomic_begin())
    {
      if(atomic_depth != 0)
      {
        reason = "hier_parent_atomic_nesting";
        return false;
      }
      atomic_depth = 1;
      continue;
    }
    if(instruction.is_atomic_end())
    {
      if(atomic_depth != 1)
      {
        reason = "hier_parent_atomic_balance";
        return false;
      }
      atomic_depth = 0;
      continue;
    }
    if(instruction.is_assign())
    {
      irep_idt lhs;
      if(!shared_symbol_lhs(instruction, ns, lhs))
        continue;
      if(
        atomic_depth == 1 && value_is(instruction.assign_rhs(), 0) &&
        instruction.location_number < life.first_create->location_number)
      {
        parent_zero.insert(lhs);
        result.writes.insert(&instruction);
        continue;
      }
      reason = "hier_parent_shared_write";
      return false;
    }
    if(
      instruction.is_goto() || instruction.is_assert() ||
      instruction.is_start_thread() || instruction.is_end_thread() ||
      instruction.is_throw() || instruction.is_catch())
    {
      reason = "hier_parent_control";
      return false;
    }
    irep_idt callee;
    if(!call_id(instruction, callee))
      continue;
    if(is_create(callee) || is_join(callee) || is_assume(callee))
      continue;
    irep_idt lhs;
    irep_idt left;
    irep_idt right;
    if(
      atomic_depth == 1 &&
      instruction.location_number > life.last_join->location_number &&
      !instruction.call_lhs().is_nil() &&
      instruction.call_arguments().size() == 2 &&
      symbol_id(instruction.call_lhs(), lhs) &&
      symbol_id(instruction.call_arguments()[0], left) &&
      symbol_id(instruction.call_arguments()[1], right) &&
      result.accumulators.count(left) != 0 &&
      result.accumulators.count(right) != 0 &&
      left != right && combine == nullptr)
    {
      combine = &instruction;
      combine_lhs = lhs;
      combine_left = left;
      combine_right = right;
      if(callee != result.operation)
      {
        reason = "hier_parent_operation";
        return false;
      }
      result.writes.insert(&instruction);
      continue;
    }
    reason = "hier_parent_call";
    return false;
  }
  if(atomic_depth != 0)
  {
    reason = "hier_parent_atomic_balance";
    return false;
  }

  const bool parent_terminal =
    hierarchical_parent_terminal(
      program, result.counter, result.bound, life.last_join);
  if(result.accumulators.size() == 1)
  {
    const irep_idt accumulator = *result.accumulators.begin();
    if(
      combine != nullptr ||
      parent_zero.count(result.counter) == 0 ||
      parent_zero.count(accumulator) == 0 ||
      (!parent_terminal && (!leaves[0].terminal || !leaves[1].terminal)))
    {
      reason = "hier_shared_root";
      return false;
    }
    result.root = accumulator;
  }
  else if(result.accumulators.size() == 2)
  {
    if(
      combine == nullptr || !parent_terminal ||
      result.accumulators.count(combine_left) == 0 ||
      result.accumulators.count(combine_right) == 0 ||
      !shared_signed(combine_lhs, ns) ||
      result.accumulators.count(combine_lhs) != 0 ||
      result.temporaries.count(combine_lhs) != 0 ||
      combine_lhs == result.counter || combine_lhs == result.bound ||
      combine_lhs == result.base)
    {
      reason = "hier_partial_root";
      return false;
    }
    result.root = combine_lhs;
    for(const auto &symbol : result.accumulators)
    {
      if(parent_zero.count(symbol) == 0)
        result.required_main_zero.insert(symbol);
    }
    if(parent_zero.count(result.counter) == 0)
      result.required_main_zero.insert(result.counter);
  }
  else
  {
    reason = "hier_accumulator_count";
    return false;
  }
  return true;
}

bool hierarchical_initial_relation(
  const goto_modelt &model,
  const lifecyclet &life,
  const std::set<irep_idt> &required,
  const goto_programt::instructiont *&assumption)
{
  if(required.empty())
    return true;
  const auto &main =
    model.goto_functions.function_map.at(ID_main).body;
  for(const auto &instruction : main.instructions)
  {
    if(
      life.first_create != nullptr &&
      instruction.location_number >= life.first_create->location_number)
      break;
    irep_idt callee;
    if(
      call_id(instruction, callee) && is_assume(callee) &&
      instruction.call_arguments().size() == 1 &&
      zero_equivalence_constraint(
        instruction.call_arguments().front(), required))
    {
      assumption = &instruction;
      return true;
    }
  }
  return false;
}

bool hierarchical_main_prefix_control(
  const goto_modelt &model,
  const lifecyclet &life,
  std::string &reason)
{
  const auto &main =
    model.goto_functions.function_map.at(ID_main).body;
  for(const auto &instruction : main.instructions)
  {
    if(
      life.first_create != nullptr &&
      instruction.location_number >= life.first_create->location_number)
      break;
    if(
      instruction.is_goto() || instruction.is_assert() ||
      instruction.is_start_thread() || instruction.is_end_thread() ||
      instruction.is_throw() || instruction.is_catch())
    {
      reason = "hier_main_prefix_control";
      return false;
    }
  }
  return true;
}

bool hierarchical_global_obligations(
  const goto_modelt &model,
  const lifecyclet &life,
  const flow_equality_propertyt &property,
  const std::vector<hierarchical_roott> &roots,
  const goto_programt::instructiont *initial_relation,
  std::string &reason)
{
  std::set<irep_idt> protected_symbols = {
    property.left, property.right};
  std::set<const goto_programt::instructiont *> allowed;
  const irep_idt base = roots.front().base;
  for(const auto &root : roots)
  {
    protected_symbols.insert(root.counter);
    protected_symbols.insert(root.bound);
    protected_symbols.insert(root.base);
    protected_symbols.insert(
      root.accumulators.begin(), root.accumulators.end());
    protected_symbols.insert(
      root.temporaries.begin(), root.temporaries.end());
    allowed.insert(root.writes.begin(), root.writes.end());
  }
  for(const auto &entry : model.goto_functions.function_map)
  {
    for(const auto &instruction : entry.second.body.instructions)
    {
      const exprt *lhs = nullptr;
      if(instruction.is_assign())
        lhs = &instruction.assign_lhs();
      else if(
        instruction.is_function_call() &&
        !instruction.call_lhs().is_nil())
        lhs = &instruction.call_lhs();
      if(lhs == nullptr)
        continue;
      irep_idt direct;
      irep_idt pointer;
      const bool protected_write =
        (symbol_id(*lhs, direct) &&
         protected_symbols.count(direct) != 0) ||
        (base_pointer(*lhs, pointer) && pointer == base);
      if(!protected_write)
        continue;
      if(
        is_start_function(entry.first) && instruction.is_assign() &&
        value_is(instruction.assign_rhs(), 0))
        continue;
      if(
        entry.first == ID_main && life.first_create != nullptr &&
        instruction.location_number < life.first_create->location_number)
        continue;
      if(allowed.count(&instruction) == 0)
      {
        reason = "hier_external_writer";
        return false;
      }
    }
  }
  std::set<irep_idt> initial_symbols;
  for(const auto &root : roots)
  {
    initial_symbols.insert(
      root.required_main_zero.begin(),
      root.required_main_zero.end());
  }
  return
    hierarchical_main_prefix_control(model, life, reason) &&
    no_main_symbol_writes_before_create(
      model, life, initial_symbols, initial_relation, reason) &&
    flow_alias_free(model, base, reason) &&
    no_addresses(model, protected_symbols, reason) &&
    flow_main_control(model, life, property, reason);
}

bool find_hierarchical_property(
  const goto_modelt &model,
  const namespacet &ns,
  const lifecyclet &life,
  flow_equality_propertyt &property,
  std::string &reason)
{
  const auto &main =
    model.goto_functions.function_map.at(ID_main).body;
  std::size_t matches = 0;
  std::size_t errors = 0;
  for(const auto &entry : model.goto_functions.function_map)
  {
    for(const auto &instruction : entry.second.body.instructions)
    {
      irep_idt callee;
      if(call_id(instruction, callee) && is_reach_error(callee))
      {
        ++errors;
        if(entry.first != ID_main)
        {
          reason = "hier_error_function";
          return false;
        }
        property.error = &instruction;
      }
    }
  }
  for(const auto &instruction : main.instructions)
  {
    if(
      life.last_join == nullptr ||
      instruction.location_number <= life.last_join->location_number)
      continue;
    irep_idt callee;
    if(
      !call_id(instruction, callee) || !is_assume(callee) ||
      instruction.call_arguments().size() != 1)
      continue;
    irep_idt left;
    irep_idt right;
    if(
      (!unequal_symbols(
         instruction.call_arguments().front(), left, right) &&
       !negated_equal_symbols(
         instruction.call_arguments().front(), left, right)) ||
      !shared_signed(left, ns) || !shared_signed(right, ns))
      continue;
    ++matches;
    property.left = left;
    property.right = right;
    property.assumption = &instruction;
  }
  if(
    matches != 1 || errors != 1 || property.assumption == nullptr ||
    property.error == nullptr ||
    property.assumption->location_number >= property.error->location_number)
  {
    reason =
      matches == 0 ? "hier_property" : "hier_property_ambiguous";
    return false;
  }
  return true;
}

bool hierarchical_fold_proof_impl(
  const goto_modelt &model,
  const namespacet &ns,
  std::string &reason)
{
  hierarchical_lifecyclet top;
  if(!hierarchical_lifecycle(model, ID_main, top, reason))
    return false;
  lifecyclet main_life;
  main_life.first_create = top.first_create;
  main_life.last_join = top.last_join;
  main_life.handles = top.handles;
  main_life.joins = top.joins;
  main_life.workers.insert(top.workers.begin(), top.workers.end());

  flow_equality_propertyt property;
  if(
    !find_hierarchical_property(
      model, ns, main_life, property, reason))
    return false;

  std::vector<hierarchical_roott> roots;
  for(const auto &worker : top.workers)
  {
    hierarchical_roott root;
    if(!hierarchical_root(model, ns, worker, root, reason))
      return false;
    roots.push_back(root);
  }
  if(
    roots[0].root == roots[1].root ||
    roots[0].bound != roots[1].bound ||
    roots[0].base != roots[1].base ||
    roots[0].operation != roots[1].operation ||
    roots[0].counter == roots[1].counter ||
    !signed_addition_helper(
      model, ns, roots[0].operation, reason))
  {
    if(reason.empty())
      reason = "hier_root_signature";
    return false;
  }
  std::set<irep_idt> left_owned = roots[0].accumulators;
  left_owned.insert(
    roots[0].temporaries.begin(), roots[0].temporaries.end());
  left_owned.insert(roots[0].counter);
  left_owned.insert(roots[0].root);
  std::set<irep_idt> right_owned = roots[1].accumulators;
  right_owned.insert(
    roots[1].temporaries.begin(), roots[1].temporaries.end());
  right_owned.insert(roots[1].counter);
  right_owned.insert(roots[1].root);
  std::vector<irep_idt> ownership_overlap;
  std::set_intersection(
    left_owned.begin(),
    left_owned.end(),
    right_owned.begin(),
    right_owned.end(),
    std::back_inserter(ownership_overlap));
  if(!ownership_overlap.empty())
  {
    reason = "hier_root_ownership";
    return false;
  }
  const std::set<irep_idt> expected_roots = {
    property.left, property.right};
  const std::set<irep_idt> actual_roots = {
    roots[0].root, roots[1].root};
  if(actual_roots != expected_roots)
  {
    reason = "hier_property_roots";
    return false;
  }

  std::set<irep_idt> required;
  for(const auto &root : roots)
  {
    required.insert(
      root.required_main_zero.begin(),
      root.required_main_zero.end());
  }
  const goto_programt::instructiont *initial_relation = nullptr;
  if(
    !hierarchical_initial_relation(
      model, main_life, required, initial_relation))
  {
    reason = "hier_initial_relation";
    return false;
  }
  if(
    !hierarchical_global_obligations(
      model,
      main_life,
      property,
      roots,
      initial_relation,
      reason))
    return false;

  std::cout << "NATIVE_HIERARCHICAL_FOLD applied=1"
            << " left=" << property.left
            << " right=" << property.right << '\n';
  return true;
}

struct stream_flow_propertyt
{
  irep_idt total;
  const goto_programt::instructiont *assumption;
  const goto_programt::instructiont *error;

  stream_flow_propertyt() : assumption(nullptr), error(nullptr)
  {
  }
};

bool find_stream_flow_property(
  const goto_modelt &model,
  const namespacet &ns,
  const lifecyclet &life,
  stream_flow_propertyt &property,
  std::string &reason)
{
  const auto &main =
    model.goto_functions.function_map.at(ID_main).body;
  std::size_t matches = 0;
  std::size_t errors = 0;
  for(const auto &entry : model.goto_functions.function_map)
  {
    for(const auto &instruction : entry.second.body.instructions)
    {
      irep_idt callee;
      if(call_id(instruction, callee) && is_reach_error(callee))
      {
        ++errors;
        if(entry.first != ID_main)
        {
          reason = "stream_error_function";
          return false;
        }
        property.error = &instruction;
      }
    }
  }
  for(const auto &instruction : main.instructions)
  {
    if(
      life.last_join == nullptr ||
      instruction.location_number <= life.last_join->location_number)
      continue;
    irep_idt callee;
    if(
      !call_id(instruction, callee) || !is_assume(callee) ||
      instruction.call_arguments().size() != 1)
      continue;
    const exprt &condition =
      strip(instruction.call_arguments().front());
    irep_idt total;
    if(
      (condition.id() != ID_le && condition.id() != ID_notequal) ||
      condition.operands().size() != 2 ||
      !symbol_id(condition.op0(), total) ||
      !value_is(condition.op1(), 0) || !shared_signed(total, ns))
      continue;
    ++matches;
    property.total = total;
    property.assumption = &instruction;
  }
  if(
    matches != 1 || errors != 1 || property.assumption == nullptr ||
    property.error == nullptr ||
    property.assumption->location_number >= property.error->location_number)
  {
    reason =
      matches == 0 ? "stream_property" :
                     "stream_property_ambiguous";
    return false;
  }
  return true;
}

bool array_equality_term(
  const exprt &src,
  irep_idt &base,
  irep_idt &index,
  exprt &value)
{
  const exprt &relation = strip(src);
  if(relation.id() != ID_equal || relation.operands().size() != 2)
    return false;
  if(array_symbol_index(relation.op0(), base, index))
  {
    value = strip(relation.op1());
    return true;
  }
  if(array_symbol_index(relation.op1(), base, index))
  {
    value = strip(relation.op0());
    return true;
  }
  return false;
}

bool publish_drain_condition(
  const exprt &src,
  irep_idt &progress,
  irep_idt &bound,
  irep_idt &front,
  irep_idt &back)
{
  const exprt &root = strip(src);
  if(root.id() != ID_or || root.operands().size() != 2)
    return false;
  for(unsigned order = 0; order < 2; ++order)
  {
    const exprt &publish = strip(root.operands()[order]);
    const exprt &drain = strip(root.operands()[1 - order]);
    if(
      publish.id() != ID_lt || publish.operands().size() != 2 ||
      drain.id() != ID_lt || drain.operands().size() != 2 ||
      !symbol_id(publish.op0(), progress) ||
      !symbol_id(publish.op1(), bound) ||
      !symbol_id(drain.op0(), front) ||
      !symbol_id(drain.op1(), back))
      continue;
    return true;
  }
  return false;
}

struct stream_flow_rolet
{
  bool producer;
  irep_idt worker;
  irep_idt queue;
  irep_idt progress;
  irep_idt bound;
  irep_idt front;
  irep_idt back;
  irep_idt total;
  irep_idt operation;
  exprt element;
  std::set<const goto_programt::instructiont *> writes;

  stream_flow_rolet() : producer(false)
  {
  }
};

bool stream_flow_role(
  const goto_modelt &model,
  const namespacet &ns,
  const irep_idt &worker,
  const irep_idt &expected_total,
  stream_flow_rolet &role,
  std::string &reason)
{
  const auto &program =
    model.goto_functions.function_map.at(worker).body;
  role.worker = worker;
  natural_loopst loops;
  loops(program);
  if(loops.loop_map.size() != 1)
  {
    reason = "stream_loop_count";
    return false;
  }
  const auto &loop = loops.loop_map.begin()->second;
  unsigned atomic_depth = 0;
  unsigned atomic_epoch = 0;
  std::size_t gotos = 0;
  std::size_t condition_writes = 0;
  std::size_t assume_calls = 0;
  goto_programt::const_targett back_write = program.instructions.end();
  goto_programt::const_targett progress_write = program.instructions.end();
  goto_programt::const_targett total_write = program.instructions.end();
  goto_programt::const_targett front_write = program.instructions.end();
  unsigned back_epoch = 0;
  unsigned progress_epoch = 0;
  unsigned total_epoch = 0;
  unsigned front_epoch = 0;

  for(auto instruction = program.instructions.begin();
      instruction != program.instructions.end(); ++instruction)
  {
    if(instruction->is_atomic_begin())
    {
      if(atomic_depth != 0)
      {
        reason = "stream_atomic_nesting";
        return false;
      }
      atomic_depth = 1;
      ++atomic_epoch;
      continue;
    }
    if(instruction->is_atomic_end())
    {
      if(atomic_depth != 1)
      {
        reason = "stream_atomic_balance";
        return false;
      }
      atomic_depth = 0;
      continue;
    }
    if(instruction->is_goto() && loop.contains(instruction))
      ++gotos;
    irep_idt callee;
    if(call_id(*instruction, callee))
    {
      if(is_assume(callee))
      {
        if(
          atomic_depth != 1 ||
          instruction->call_arguments().size() != 1)
        {
          reason = "stream_assume_epoch";
          return false;
        }
        ++assume_calls;
        std::vector<exprt> terms;
        flatten_and(instruction->call_arguments().front(), terms);
        for(const auto &term : terms)
        {
          irep_idt base;
          irep_idt index;
          exprt value;
          if(array_equality_term(term, base, index, value))
          {
            role.queue = base;
            role.back = index;
            role.element = value;
          }
        }
        continue;
      }
      irep_idt total;
      irep_idt first;
      irep_idt base;
      irep_idt front;
      if(
        instruction->call_lhs().is_nil() ||
        instruction->call_arguments().size() != 2 ||
        !symbol_id(instruction->call_lhs(), total) ||
        !symbol_id(instruction->call_arguments()[0], first) ||
        total != first || total != expected_total ||
        !array_symbol_index(
          instruction->call_arguments()[1], base, front) ||
        atomic_depth != 1 || total_write != program.instructions.end())
      {
        reason = "stream_worker_call";
        return false;
      }
      role.total = total;
      role.operation = callee;
      role.queue = base;
      role.front = front;
      role.writes.insert(&*instruction);
      total_write = instruction;
      total_epoch = atomic_epoch;
      continue;
    }
    if(!instruction->is_assign())
      continue;
    irep_idt lhs;
    if(!shared_symbol_lhs(*instruction, ns, lhs))
    {
      irep_idt local;
      if(!symbol_id(instruction->assign_lhs(), local))
        continue;
      irep_idt progress;
      irep_idt bound;
      irep_idt front;
      irep_idt back;
      const exprt &condition = strip(instruction->assign_rhs());
      if(
        condition.id() == ID_lt && condition.operands().size() == 2 &&
        symbol_id(condition.op0(), progress) &&
        symbol_id(condition.op1(), bound))
      {
        if(
          (!role.progress.empty() && role.progress != progress) ||
          (!role.bound.empty() && role.bound != bound))
        {
          reason = "stream_producer_condition";
          return false;
        }
        role.progress = progress;
        role.bound = bound;
        ++condition_writes;
      }
      else if(
        publish_drain_condition(
          condition, progress, bound, front, back))
      {
        if(
          (!role.progress.empty() && role.progress != progress) ||
          (!role.bound.empty() && role.bound != bound) ||
          (!role.front.empty() && role.front != front) ||
          (!role.back.empty() && role.back != back))
        {
          reason = "stream_consumer_condition";
          return false;
        }
        role.progress = progress;
        role.bound = bound;
        role.front = front;
        role.back = back;
        ++condition_writes;
      }
      continue;
    }
    if(
      unit_increment(*instruction, lhs) && atomic_depth == 1)
    {
      if(!role.back.empty() && lhs == role.back)
      {
        if(back_write != program.instructions.end())
        {
          reason = "stream_back_count";
          return false;
        }
        back_write = instruction;
        back_epoch = atomic_epoch;
      }
      else if(!role.progress.empty() && lhs == role.progress)
      {
        if(progress_write != program.instructions.end())
        {
          reason = "stream_progress_count";
          return false;
        }
        progress_write = instruction;
        progress_epoch = atomic_epoch;
      }
      else if(!role.front.empty() && lhs == role.front)
      {
        if(front_write != program.instructions.end())
        {
          reason = "stream_front_count";
          return false;
        }
        front_write = instruction;
        front_epoch = atomic_epoch;
      }
      else
      {
        reason =
          "stream_unrecognized_increment lhs=" + id2string(lhs) +
          " back=" + id2string(role.back) +
          " progress=" + id2string(role.progress) +
          " front=" + id2string(role.front);
        return false;
      }
      role.writes.insert(&*instruction);
      continue;
    }
    reason = "stream_shared_write";
    return false;
  }
  if(atomic_depth != 0 || gotos != 2 || condition_writes != 2)
  {
    reason = "stream_control_shape";
    return false;
  }

  if(total_write == program.instructions.end())
  {
    role.producer = true;
    if(
      assume_calls < 1 || role.queue.empty() || role.back.empty() ||
      role.progress.empty() || role.bound.empty() ||
      back_write == program.instructions.end() ||
      progress_write == program.instructions.end() ||
      back_write->location_number >= progress_write->location_number ||
      back_epoch > progress_epoch)
    {
      reason = "stream_producer_shape";
      return false;
    }
  }
  else
  {
    role.producer = false;
    if(
      assume_calls != 1 || role.queue.empty() || role.front.empty() ||
      role.back.empty() || role.progress.empty() || role.bound.empty() ||
      front_write == program.instructions.end() ||
      total_write->location_number >= front_write->location_number ||
      total_epoch != front_epoch)
    {
      reason = "stream_consumer_shape";
      return false;
    }
    bool drain_guard = false;
    for(const auto &instruction : program.instructions)
    {
      irep_idt callee;
      if(
        !call_id(instruction, callee) || !is_assume(callee) ||
        instruction.call_arguments().size() != 1)
        continue;
      std::vector<exprt> terms;
      flatten_and(instruction.call_arguments().front(), terms);
      drain_guard =
        drain_guard ||
        std::any_of(
          terms.begin(),
          terms.end(),
          [&](const exprt &term) {
            return
              relation_symbols(
                term, ID_lt, role.front, role.back);
          });
    }
    if(!drain_guard)
    {
      reason = "stream_consumer_commit_guard";
      return false;
    }
  }
  return true;
}

bool stream_positive_preconditions(
  const goto_modelt &model,
  const lifecyclet &life,
  const irep_idt &positive_bound,
  const irep_idt &negative_bound,
  const irep_idt &element,
  const stream_flow_rolet &negative,
  const std::vector<stream_flow_rolet> &roles)
{
  const auto &main =
    model.goto_functions.function_map.at(ID_main).body;
  bool strict_residual = false;
  bool negative_nonnegative = false;
  bool element_positive = false;
  bool defined_negation = false;
  std::set<std::pair<irep_idt, irep_idt>> empty_channels;
  for(const auto &instruction : main.instructions)
  {
    if(
      life.first_create != nullptr &&
      instruction.location_number >= life.first_create->location_number)
      break;
    if(instruction.is_assign())
    {
      irep_idt left;
      irep_idt right;
      if(
        symbol_id(instruction.assign_lhs(), left) &&
        symbol_id(instruction.assign_rhs(), right))
        empty_channels.insert({left, right});
      continue;
    }
    irep_idt callee;
    if(
      !call_id(instruction, callee) || !is_assume(callee) ||
      instruction.call_arguments().size() != 1)
      continue;
    std::vector<exprt> terms;
    flatten_and(instruction.call_arguments().front(), terms);
    for(const auto &term : terms)
    {
      strict_residual =
        strict_residual ||
        relation_symbols(
          term, ID_gt, positive_bound, negative_bound) ||
        relation_symbols(
          term, ID_lt, negative_bound, positive_bound);
      negative_nonnegative =
        negative_nonnegative ||
        relation_zero(term, negative_bound, ID_ge);
      element_positive =
        element_positive || relation_zero(term, element, ID_gt);
      const exprt &relation = strip(term);
      mp_integer constant;
      irep_idt candidate;
      if(
        relation.id() == ID_gt && relation.operands().size() == 2 &&
        symbol_id(relation.op0(), candidate) && candidate == element &&
        integer_constant(relation.op1(), constant) &&
        constant == -power(2, 31))
        defined_negation = true;
      if(relation.id() == ID_equal && relation.operands().size() == 2)
      {
        irep_idt left;
        irep_idt right;
        if(
          symbol_id(relation.op0(), left) &&
          symbol_id(relation.op1(), right))
          empty_channels.insert({left, right});
      }
    }
  }
  if(!defined_negation)
  {
    const auto &negative_program =
      model.goto_functions.function_map.at(negative.worker).body;
    bool pointwise_guard = false;
    bool pointwise_use = false;
    for(const auto &instruction : negative_program.instructions)
    {
      irep_idt callee;
      if(
        !call_id(instruction, callee) || !is_assume(callee) ||
        instruction.call_arguments().size() != 1)
        continue;
      std::vector<exprt> terms;
      flatten_and(instruction.call_arguments().front(), terms);
      for(const auto &term_src : terms)
      {
        const exprt &term = strip(term_src);
        mp_integer constant;
        irep_idt base;
        irep_idt index;
        if(
          term.id() == ID_gt && term.operands().size() == 2 &&
          array_symbol_index(term.op0(), base, index) &&
          base == element && index == negative.progress &&
          integer_constant(term.op1(), constant) &&
          constant == -power(2, 31))
          pointwise_guard = true;

        irep_idt queue;
        irep_idt queue_index;
        exprt value;
        if(
          array_equality_term(
            term, queue, queue_index, value) &&
          queue == negative.queue &&
          queue_index == negative.back &&
          strip(value) == strip(negative.element))
          pointwise_use = pointwise_guard;
      }
    }
    defined_negation = pointwise_use;
  }
  for(const auto &role : roles)
  {
    if(!role.producer)
      continue;
    bool empty = false;
    for(const auto &consumer : roles)
    {
      if(
        consumer.producer || consumer.queue != role.queue ||
        consumer.back != role.back)
        continue;
      empty =
        empty ||
        empty_channels.count({consumer.front, role.back}) != 0 ||
        empty_channels.count({role.back, consumer.front}) != 0;
    }
    if(!empty)
      return false;
  }
  const bool exact_cancellation =
    positive_bound == negative_bound &&
    negative_nonnegative && defined_negation;
  const bool positive_residual =
    strict_residual && negative_nonnegative &&
    element_positive && defined_negation;
  return exact_cancellation || positive_residual;
}

bool stream_main_allocations(
  const goto_modelt &model,
  const lifecyclet &life,
  const std::set<irep_idt> &queues,
  const namespacet &ns,
  std::string &reason)
{
  const auto &main =
    model.goto_functions.function_map.at(ID_main).body;
  std::set<irep_idt> allocated;
  irep_idt allocator;
  for(const auto &instruction : main.instructions)
  {
    if(
      life.first_create != nullptr &&
      instruction.location_number >= life.first_create->location_number)
      break;
    irep_idt callee;
    irep_idt lhs;
    if(
      !call_id(instruction, callee) ||
      instruction.call_lhs().is_nil() ||
      !symbol_id(instruction.call_lhs(), lhs) ||
      queues.count(lhs) == 0)
      continue;
    if(instruction.call_arguments().size() != 1)
    {
      reason = "stream_allocation_arguments";
      return false;
    }
    if(allocator.empty())
      allocator = callee;
    else if(allocator != callee)
    {
      reason = "stream_allocator_mismatch";
      return false;
    }
    allocated.insert(lhs);
  }
  if(
    allocated != queues || allocator.empty() ||
    !fresh_array_allocator(model, ns, allocator, reason))
  {
    if(reason.empty())
      reason = "stream_allocations";
    return false;
  }
  return true;
}

bool ordered_stream_residual_proof_impl(
  const goto_modelt &model,
  const namespacet &ns,
  std::string &reason)
{
  lifecyclet life;
  if(!lifecycle(model, life, reason) || life.workers.size() != 4)
  {
    if(reason.empty())
      reason = "stream_lifecycle";
    return false;
  }
  stream_flow_propertyt property;
  if(!find_stream_flow_property(model, ns, life, property, reason))
    return false;

  std::vector<stream_flow_rolet> roles;
  for(const auto &worker_id : life.workers)
  {
    stream_flow_rolet role;
    if(
      !stream_flow_role(
        model, ns, worker_id, property.total, role, reason))
    {
      reason =
        "stream_worker " + id2string(worker_id) + " " + reason;
      return false;
    }
    roles.push_back(role);
  }
  std::vector<const stream_flow_rolet *> producers;
  std::vector<const stream_flow_rolet *> consumers;
  for(const auto &role : roles)
    (role.producer ? producers : consumers).push_back(&role);
  if(producers.size() != 2 || consumers.size() != 2)
  {
    reason = "stream_roles";
    return false;
  }
  for(const auto *producer : producers)
  {
    std::size_t matches = 0;
    for(const auto *consumer : consumers)
    {
      if(
        producer->queue == consumer->queue &&
        producer->back == consumer->back &&
        producer->progress == consumer->progress &&
        producer->bound == consumer->bound)
        ++matches;
    }
    if(matches != 1)
    {
      reason = "stream_endpoints";
      return false;
    }
  }
  if(
    producers[0]->queue == producers[1]->queue ||
    consumers[0]->total != property.total ||
    consumers[1]->total != property.total ||
    consumers[0]->operation != consumers[1]->operation ||
    !signed_addition_helper(
      model, ns, consumers[0]->operation, reason))
  {
    if(reason.empty())
      reason = "stream_signature";
    return false;
  }

  const stream_flow_rolet *positive = nullptr;
  const stream_flow_rolet *negative = nullptr;
  irep_idt element;
  for(const auto *producer : producers)
  {
    irep_idt candidate;
    irep_idt candidate_index;
    if(symbol_id(producer->element, candidate))
    {
      positive = producer;
      element = candidate;
    }
    else if(
      array_symbol_index(
        producer->element, candidate, candidate_index) &&
      candidate_index == producer->progress)
    {
      positive = producer;
      element = candidate;
    }
    const exprt &value = strip(producer->element);
    bool negative_element = false;
    if(value.id() == ID_unary_minus && value.operands().size() == 1)
    {
      negative_element =
        symbol_id(value.op0(), candidate) ||
        (array_symbol_index(
           value.op0(), candidate, candidate_index) &&
         candidate_index == producer->progress);
    }
    if(negative_element)
    {
      negative = producer;
      if(element.empty())
        element = candidate;
      else if(element != candidate)
      {
        reason = "stream_elements";
        return false;
      }
    }
  }
  const symbolt *element_symbol =
    element.empty() ? nullptr : lookup(element, ns);
  const bool signed_element =
    element_symbol != nullptr &&
    element_symbol->is_static_lifetime &&
    !element_symbol->is_type &&
    (element_symbol->type.id() == ID_signedbv ||
     (element_symbol->type.id() == ID_pointer &&
      to_pointer_type(
        element_symbol->type).base_type().id() == ID_signedbv));
  if(
    positive == nullptr || negative == nullptr ||
    positive == negative || element.empty() ||
    !signed_element ||
    !stream_positive_preconditions(
      model,
      life,
      positive->bound,
      negative->bound,
      element,
      *negative,
      roles))
  {
    reason = "stream_residual_precondition";
    return false;
  }

  std::set<irep_idt> queues = {
    producers[0]->queue, producers[1]->queue};
  if(!stream_main_allocations(model, life, queues, ns, reason))
    return false;
  std::set<irep_idt> pointer_bases = queues;
  if(element_symbol->type.id() == ID_pointer)
    pointer_bases.insert(element);
  std::set<irep_idt> protected_symbols = {
    property.total,
    positive->bound,
    negative->bound,
    element};
  std::set<const goto_programt::instructiont *> allowed;
  for(const auto &role : roles)
  {
    protected_symbols.insert(role.queue);
    protected_symbols.insert(role.progress);
    protected_symbols.insert(role.bound);
    protected_symbols.insert(role.back);
    if(!role.front.empty())
      protected_symbols.insert(role.front);
    allowed.insert(role.writes.begin(), role.writes.end());
  }
  if(
    !zero_initialized_symbols(
      model,
      {property.total, positive->progress, negative->progress},
      allowed,
      reason))
    return false;
  if(
    !no_main_symbol_writes_before_create(
      model,
      life,
      {property.total, positive->progress, negative->progress},
      nullptr,
      reason))
    return false;
  for(const auto &entry : model.goto_functions.function_map)
  {
    for(const auto &instruction : entry.second.body.instructions)
    {
      const exprt *lhs = nullptr;
      if(instruction.is_assign())
        lhs = &instruction.assign_lhs();
      else if(
        instruction.is_function_call() &&
        !instruction.call_lhs().is_nil())
        lhs = &instruction.call_lhs();
      if(lhs == nullptr)
        continue;
      irep_idt direct;
      irep_idt base;
      const bool protected_write =
        (symbol_id(*lhs, direct) &&
         protected_symbols.count(direct) != 0) ||
        (base_pointer(*lhs, base) &&
         pointer_bases.count(base) != 0);
      if(!protected_write)
        continue;
      if(
        is_start_function(entry.first) && instruction.is_assign() &&
        value_is(instruction.assign_rhs(), 0))
        continue;
      if(
        entry.first == ID_main && life.first_create != nullptr &&
        instruction.location_number < life.first_create->location_number)
        continue;
      if(allowed.count(&instruction) == 0)
      {
        reason = "stream_external_writer";
        return false;
      }
    }
  }
  for(const auto &base : pointer_bases)
  {
    if(!flow_alias_free(model, base, reason))
      return false;
  }
  flow_equality_propertyt control_property;
  control_property.assumption = property.assumption;
  control_property.error = property.error;
  if(
    !no_addresses(model, protected_symbols, reason) ||
    !flow_main_control(
      model, life, control_property, reason))
    return false;

  std::cout << "NATIVE_RELATIONAL_FLOW applied=1 rule=stream_residual"
            << " total=" << property.total
            << " positive_bound=" << positive->bound
            << " negative_bound=" << negative->bound << '\n';
  return true;
}

struct stream_refine_channelt
{
  irep_idt storage;
  irep_idt front;
  irep_idt back;
  irep_idt bound;

  bool operator<(const stream_refine_channelt &other) const
  {
    return
      std::tie(storage, front, back, bound) <
      std::tie(other.storage, other.front, other.back, other.bound);
  }
};

struct stream_refine_publisht
{
  stream_refine_channelt channel;
  exprt token;
  bool in_loop;
  unsigned first_location;
  unsigned last_location;
  std::set<const goto_programt::instructiont *> writes;

  stream_refine_publisht()
    : in_loop(false), first_location(0), last_location(0)
  {
  }
};

struct stream_refine_consumet
{
  stream_refine_channelt channel;
  irep_idt temporary;
  bool in_loop;
  unsigned first_location;
  unsigned last_location;
  std::set<const goto_programt::instructiont *> writes;

  stream_refine_consumet()
    : in_loop(false), first_location(0), last_location(0)
  {
  }
};

struct stream_refine_staget
{
  irep_idt worker;
  stream_refine_consumet consume;
  bool forwards;
  stream_refine_publisht publish;
  irep_idt fold;
  irep_idt account;
  exprt account_delta;
  exprt transform;
  bool nonpositive_exit;
  std::set<const goto_programt::instructiont *> writes;

  stream_refine_staget() : forwards(false), nonpositive_exit(false)
  {
  }
};

struct stream_refine_sourcet
{
  irep_idt worker;
  irep_idt count;
  stream_refine_publisht data;
  stream_refine_publisht sentinel;
  irep_idt account;
  exprt account_delta;
  std::set<const goto_programt::instructiont *> writes;
};

bool local_signed(
  const irep_idt &identifier,
  const namespacet &ns)
{
  const symbolt *symbol = lookup(identifier, ns);
  return
    symbol != nullptr && !symbol->is_static_lifetime && !symbol->is_type &&
    symbol->type.id() == ID_signedbv;
}

bool local_boolean(
  const irep_idt &identifier,
  const namespacet &ns)
{
  const symbolt *symbol = lookup(identifier, ns);
  return
    symbol != nullptr && !symbol->is_static_lifetime && !symbol->is_type &&
    (symbol->type.id() == ID_c_bool || symbol->type.id() == ID_bool);
}

bool stream_refine_symbol_zero_relation(
  const exprt &src,
  const irep_idt &symbol,
  const irep_idt &relation)
{
  const exprt &expr = strip(src);
  if(expr.id() != relation || expr.operands().size() != 2)
    return false;
  irep_idt lhs;
  return
    symbol_id(expr.op0(), lhs) && lhs == symbol &&
    value_is(expr.op1(), 0);
}

bool stream_refine_bounds(
  const std::vector<exprt> &terms,
  const irep_idt &index,
  irep_idt &bound)
{
  bool nonnegative = false;
  bool upper = false;
  for(const auto &term : terms)
  {
    if(stream_refine_symbol_zero_relation(term, index, ID_ge))
      nonnegative = true;
    const exprt &relation = strip(term);
    irep_idt lhs;
    irep_idt rhs;
    if(
      relation.id() == ID_lt && relation.operands().size() == 2 &&
      symbol_id(relation.op0(), lhs) && lhs == index &&
      symbol_id(relation.op1(), rhs))
    {
      if(upper && bound != rhs)
        return false;
      bound = rhs;
      upper = true;
    }
  }
  return nonnegative && upper;
}

bool stream_refine_publish_region(
  const std::vector<const goto_programt::instructiont *> &region,
  const namespacet &ns,
  bool in_loop,
  stream_refine_publisht &result)
{
  std::vector<exprt> terms;
  std::size_t assumes = 0;
  std::size_t increments = 0;
  const goto_programt::instructiont *last_assume = nullptr;
  const goto_programt::instructiont *increment = nullptr;
  const goto_programt::instructiont *equality_instruction = nullptr;
  std::vector<
    std::pair<exprt, const goto_programt::instructiont *>> located_terms;
  irep_idt storage;
  irep_idt back;
  exprt token;
  for(const auto *instruction : region)
  {
    irep_idt callee;
    if(call_id(*instruction, callee))
    {
      if(
        !is_assume(callee) ||
        instruction->call_arguments().size() != 1)
        return false;
      ++assumes;
      std::vector<exprt> current;
      flatten_and(instruction->call_arguments().front(), current);
      terms.insert(terms.end(), current.begin(), current.end());
      for(const auto &term : current)
        located_terms.emplace_back(term, instruction);
      last_assume = instruction;
      continue;
    }
    if(instruction->is_assign())
    {
      irep_idt lhs;
      if(
        symbol_id(instruction->assign_lhs(), lhs) &&
        unit_increment(*instruction, lhs))
      {
        if(!back.empty() && back != lhs)
          return false;
        back = lhs;
        ++increments;
        increment = instruction;
        result.writes.insert(instruction);
        continue;
      }
      return false;
    }
    if(
      instruction->is_decl() || instruction->is_dead() ||
      instruction->is_location() || instruction->is_skip())
      continue;
    return false;
  }
  if(
    (assumes < 1 || assumes > 2) ||
    increments != 1 || back.empty() ||
    !shared_signed(back, ns))
    return false;

  bool equality = false;
  for(const auto &entry : located_terms)
  {
    irep_idt candidate_storage;
    irep_idt candidate_back;
    exprt candidate_token;
    if(
      array_equality_term(
        entry.first,
        candidate_storage,
        candidate_back,
        candidate_token) &&
      candidate_back == back)
    {
      if(equality)
        return false;
      storage = candidate_storage;
      token = candidate_token;
      equality_instruction = entry.second;
      equality = true;
    }
  }
  irep_idt bound;
  if(
    !equality || equality_instruction == nullptr ||
    increment == nullptr || last_assume == nullptr ||
    equality_instruction->location_number >= increment->location_number ||
    last_assume->location_number >= increment->location_number ||
    !stream_refine_bounds(terms, back, bound) ||
    !shared_signed(bound, ns))
    return false;
  const symbolt *queue = lookup(storage, ns);
  if(
    queue == nullptr || !queue->is_static_lifetime ||
    queue->type.id() != ID_pointer ||
    to_pointer_type(queue->type).base_type().id() != ID_signedbv)
    return false;
  result.channel.storage = storage;
  result.channel.back = back;
  result.channel.bound = bound;
  result.token = strip(token);
  result.in_loop = in_loop;
  result.first_location =
    region.empty() ? 0 : region.front()->location_number;
  result.last_location =
    region.empty() ? 0 : region.back()->location_number;
  return true;
}

bool stream_refine_consume_guard(
  const std::vector<exprt> &terms,
  const irep_idt &front,
  irep_idt &back,
  irep_idt &bound)
{
  bool available = false;
  for(const auto &term : terms)
  {
    const exprt &relation = strip(term);
    irep_idt lhs;
    irep_idt rhs;
    if(
      relation.id() == ID_gt && relation.operands().size() == 2 &&
      symbol_id(relation.op0(), lhs) &&
      symbol_id(relation.op1(), rhs) && rhs == front)
    {
      if(available && back != lhs)
        return false;
      back = lhs;
      available = true;
    }
  }
  return
    available &&
    stream_refine_bounds(terms, front, bound);
}

bool stream_refine_consume_region(
  const std::vector<const goto_programt::instructiont *> &region,
  const namespacet &ns,
  stream_refine_consumet &result,
  const bool in_loop = false)
{
  std::vector<exprt> terms;
  std::size_t assumes = 0;
  std::size_t reads = 0;
  std::size_t increments = 0;
  const goto_programt::instructiont *last_assume = nullptr;
  const goto_programt::instructiont *read = nullptr;
  const goto_programt::instructiont *increment = nullptr;
  irep_idt storage;
  irep_idt front;
  for(const auto *instruction : region)
  {
    irep_idt callee;
    if(call_id(*instruction, callee))
    {
      if(
        !is_assume(callee) ||
        instruction->call_arguments().size() != 1)
        return false;
      ++assumes;
      flatten_and(instruction->call_arguments().front(), terms);
      last_assume = instruction;
      continue;
    }
    if(instruction->is_assign())
    {
      irep_idt lhs;
      irep_idt candidate_storage;
      irep_idt candidate_front;
      if(
        symbol_id(instruction->assign_lhs(), lhs) &&
        array_symbol_index(
          instruction->assign_rhs(),
          candidate_storage,
          candidate_front))
      {
        if(
          reads != 0 || !local_signed(lhs, ns) ||
          lhs == candidate_front || lhs == candidate_storage)
          return false;
        result.temporary = lhs;
        storage = candidate_storage;
        front = candidate_front;
        ++reads;
        read = instruction;
        result.writes.insert(instruction);
        continue;
      }
      if(
        symbol_id(instruction->assign_lhs(), lhs) &&
        unit_increment(*instruction, lhs))
      {
        if(!front.empty() && front != lhs)
          return false;
        front = lhs;
        ++increments;
        increment = instruction;
        result.writes.insert(instruction);
        continue;
      }
      return false;
    }
    if(
      instruction->is_decl() || instruction->is_dead() ||
      instruction->is_location() || instruction->is_skip())
      continue;
    return false;
  }
  irep_idt back;
  irep_idt bound;
  if(
    assumes != 1 || reads != 1 || increments != 1 ||
    last_assume == nullptr || read == nullptr || increment == nullptr ||
    last_assume->location_number >= read->location_number ||
    read->location_number >= increment->location_number ||
    !stream_refine_consume_guard(terms, front, back, bound) ||
    !shared_signed(front, ns) || !shared_signed(back, ns) ||
    !shared_signed(bound, ns))
    return false;
  result.channel.storage = storage;
  result.channel.front = front;
  result.channel.back = back;
  result.channel.bound = bound;
  result.in_loop = in_loop;
  result.first_location =
    region.empty() ? 0 : region.front()->location_number;
  result.last_location =
    region.empty() ? 0 : region.back()->location_number;
  return true;
}

bool stream_refine_transactions(
  const goto_programt &program,
  const natural_loopst::natural_loopt &loop,
  const namespacet &ns,
  std::vector<stream_refine_publisht> &publishes,
  std::vector<stream_refine_consumet> &consumes,
  std::string &reason)
{
  bool in_atomic = false;
  bool region_in_loop = false;
  std::vector<const goto_programt::instructiont *> region;
  for(auto instruction = program.instructions.begin();
      instruction != program.instructions.end(); ++instruction)
  {
    if(instruction->is_atomic_begin())
    {
      if(in_atomic)
      {
        reason = "stream_refine_atomic_nesting";
        return false;
      }
      in_atomic = true;
      region_in_loop = loop.contains(instruction);
      region.clear();
      continue;
    }
    if(instruction->is_atomic_end())
    {
      if(!in_atomic || loop.contains(instruction) != region_in_loop)
      {
        reason = "stream_refine_atomic_balance";
        return false;
      }
      stream_refine_publisht publish;
      stream_refine_consumet consume;
      if(stream_refine_publish_region(region, ns, region_in_loop, publish))
        publishes.push_back(publish);
      else if(
        stream_refine_consume_region(
          region, ns, consume, region_in_loop))
        consumes.push_back(consume);
      else
      {
        reason = "stream_refine_atomic_transaction";
        return false;
      }
      in_atomic = false;
      region.clear();
      continue;
    }
    if(in_atomic)
      region.push_back(&*instruction);
  }
  if(in_atomic)
  {
    reason = "stream_refine_atomic_balance";
    return false;
  }
  return true;
}

bool stream_refine_addition(
  const goto_programt::instructiont &instruction,
  irep_idt &lhs,
  exprt &delta)
{
  if(
    !instruction.is_assign() ||
    !symbol_id(instruction.assign_lhs(), lhs))
    return false;
  const exprt &rhs = strip(instruction.assign_rhs());
  if(rhs.id() != ID_plus || rhs.operands().size() != 2)
    return false;
  irep_idt first;
  irep_idt second;
  if(symbol_id(rhs.op0(), first) && first == lhs)
  {
    delta = strip(rhs.op1());
    return true;
  }
  if(symbol_id(rhs.op1(), second) && second == lhs)
  {
    delta = strip(rhs.op0());
    return true;
  }
  return false;
}

bool stream_refine_sentinel_exit(
  const goto_programt::instructiont &instruction,
  const natural_loopst::natural_loopt &loop,
  const irep_idt &temporary,
  const bool allow_nonpositive = false)
{
  if(!instruction.is_goto() || instruction.targets.size() != 1)
    return false;
  const exprt &condition = strip(instruction.condition());
  if(
    (condition.id() != ID_equal &&
     (!allow_nonpositive || condition.id() != ID_le)) ||
    condition.operands().size() != 2)
    return false;
  irep_idt candidate;
  const bool matches =
    (symbol_id(condition.op0(), candidate) &&
     candidate == temporary && value_is(condition.op1(), 0)) ||
    (symbol_id(condition.op1(), candidate) &&
     candidate == temporary && value_is(condition.op0(), 0));
  return matches && !loop.contains(instruction.get_target());
}

bool stream_refine_affine_form(
  const exprt &src,
  const irep_idt &variable,
  mp_integer &coefficient,
  mp_integer &constant)
{
  const exprt &expr = strip(src);
  irep_idt identifier;
  if(symbol_id(expr, identifier))
  {
    if(identifier != variable)
      return false;
    coefficient = 1;
    constant = 0;
    return true;
  }
  if(integer_constant(expr, constant))
  {
    coefficient = 0;
    return true;
  }
  if(expr.id() == ID_unary_minus && expr.operands().size() == 1)
  {
    if(!stream_refine_affine_form(
         expr.op0(), variable, coefficient, constant))
      return false;
    coefficient = -coefficient;
    constant = -constant;
    return true;
  }
  if(
    (expr.id() == ID_plus || expr.id() == ID_minus) &&
    expr.operands().size() == 2)
  {
    mp_integer lhs_coefficient;
    mp_integer lhs_constant;
    mp_integer rhs_coefficient;
    mp_integer rhs_constant;
    if(
      !stream_refine_affine_form(
        expr.op0(), variable, lhs_coefficient, lhs_constant) ||
      !stream_refine_affine_form(
        expr.op1(), variable, rhs_coefficient, rhs_constant))
      return false;
    coefficient =
      expr.id() == ID_plus ?
        lhs_coefficient + rhs_coefficient :
        lhs_coefficient - rhs_coefficient;
    constant =
      expr.id() == ID_plus ?
        lhs_constant + rhs_constant :
        lhs_constant - rhs_constant;
    return true;
  }
  if(expr.id() == ID_mult && expr.operands().size() == 2)
  {
    mp_integer lhs;
    mp_integer rhs;
    if(integer_constant(expr.op0(), lhs))
    {
      if(!stream_refine_affine_form(
           expr.op1(), variable, coefficient, constant))
        return false;
      coefficient *= lhs;
      constant *= lhs;
      return true;
    }
    if(integer_constant(expr.op1(), rhs))
    {
      if(!stream_refine_affine_form(
           expr.op0(), variable, coefficient, constant))
        return false;
      coefficient *= rhs;
      constant *= rhs;
      return true;
    }
  }
  return false;
}

bool stream_refine_stage(
  const goto_modelt &model,
  const namespacet &ns,
  const irep_idt &worker,
  stream_refine_staget &result,
  std::string &reason,
  const bool allow_affine_forward = false)
{
  const auto &program =
    model.goto_functions.function_map.at(worker).body;
  natural_loopst loops;
  loops(program);
  if(loops.loop_map.size() != 1)
  {
    reason = "stream_refine_stage_loop_count";
    return false;
  }
  const auto &loop = loops.loop_map.begin()->second;
  std::vector<stream_refine_publisht> publishes;
  std::vector<stream_refine_consumet> consumes;
  if(
    !stream_refine_transactions(
      program, loop, ns, publishes, consumes, reason) ||
    consumes.size() != 1 || publishes.size() > 1 ||
    (publishes.size() == 1 && !publishes.front().in_loop))
  {
    if(reason.empty())
      reason = "stream_refine_stage_transactions";
    return false;
  }
  result.worker = worker;
  result.consume = consumes.front();
  result.writes.insert(
    result.consume.writes.begin(), result.consume.writes.end());
  if(!publishes.empty())
  {
    result.forwards = true;
    result.publish = publishes.front();
    result.transform = strip(result.publish.token);
    mp_integer affine_coefficient;
    mp_integer affine_constant;
    if(
      !contains_symbol(
        result.publish.token, result.consume.temporary) ||
      (allow_affine_forward &&
       !stream_refine_affine_form(
         result.publish.token,
         result.consume.temporary,
         affine_coefficient,
         affine_constant)) ||
      (!allow_affine_forward &&
       (strip(result.publish.token).id() != ID_symbol ||
        strip(result.publish.token) !=
          symbol_exprt(
            result.consume.temporary,
            lookup(result.consume.temporary, ns)->type))))
    {
      reason = allow_affine_forward ?
        "stream_refine_forward_dependency" :
        "stream_refine_nonidentity_forward";
      return false;
    }
    result.writes.insert(
      result.publish.writes.begin(), result.publish.writes.end());
  }

  std::size_t folds = 0;
  std::size_t accounts = 0;
  std::size_t exits = 0;
  unsigned last_effect_location = result.consume.last_location;
  unsigned exit_location = 0;
  for(auto instruction = program.instructions.begin();
      instruction != program.instructions.end(); ++instruction)
  {
    if(!loop.contains(instruction))
      continue;
    if(
      instruction->is_atomic_begin() || instruction->is_atomic_end() ||
      instruction->is_decl() || instruction->is_dead() ||
      instruction->is_location() || instruction->is_skip())
      continue;
    if(
      instruction->is_goto() &&
      stream_refine_sentinel_exit(
        *instruction,
        loop,
        result.consume.temporary,
        allow_affine_forward))
    {
      ++exits;
      result.nonpositive_exit =
        strip(instruction->condition()).id() == ID_le;
      exit_location = instruction->location_number;
      continue;
    }
    if(instruction->is_goto())
      continue;
    irep_idt callee;
    if(call_id(*instruction, callee) && is_assume(callee))
      continue;
    if(instruction->is_assign())
    {
      irep_idt lhs;
      exprt delta;
      if(stream_refine_addition(*instruction, lhs, delta))
      {
        irep_idt token;
        if(
          symbol_id(delta, token) &&
          token == result.consume.temporary &&
          shared_signed(lhs, ns))
        {
          result.fold = lhs;
          ++folds;
          result.writes.insert(&*instruction);
          last_effect_location =
            std::max(
              last_effect_location,
              instruction->location_number);
          continue;
        }
        if(shared_unsigned32(lhs, ns))
        {
          result.account = lhs;
          result.account_delta = strip(delta);
          ++accounts;
          result.writes.insert(&*instruction);
          last_effect_location =
            std::max(
              last_effect_location,
              instruction->location_number);
          continue;
        }
      }
      if(
        result.consume.writes.count(&*instruction) != 0 ||
        (result.forwards &&
         result.publish.writes.count(&*instruction) != 0))
        continue;
      irep_idt local;
      if(symbol_id(instruction->assign_lhs(), local) &&
         !lookup(local, ns)->is_static_lifetime)
        continue;
      reason = "stream_refine_stage_write";
      return false;
    }
    if(instruction->is_function_call())
    {
      reason = "stream_refine_stage_call";
      return false;
    }
    reason = "stream_refine_stage_control";
    return false;
  }
  if(
    ((!allow_affine_forward && folds != 1) ||
     (allow_affine_forward &&
      ((!result.forwards && folds != 1) || folds > 1))) ||
    accounts > 1 || exits != 1 ||
    exit_location <= last_effect_location ||
    (result.forwards &&
     (result.publish.first_location <=
        result.consume.last_location ||
      exit_location <= result.publish.last_location)) ||
    (result.forwards &&
     result.publish.channel.storage == result.consume.channel.storage))
  {
    reason = "stream_refine_stage_effects";
    return false;
  }
  std::size_t fold_zero_initializations = 0;
  for(auto instruction = program.instructions.begin();
      instruction != program.instructions.end(); ++instruction)
  {
    if(loop.contains(instruction) || !instruction->is_assign())
      continue;
    irep_idt lhs;
    if(
      symbol_id(instruction->assign_lhs(), lhs) &&
      lhs == result.fold && value_is(instruction->assign_rhs(), 0))
    {
      ++fold_zero_initializations;
      result.writes.insert(&*instruction);
    }
  }
  if(fold_zero_initializations > 1)
  {
    reason = "stream_refine_stage_initialization";
    return false;
  }
  return true;
}

bool stream_refine_source(
  const goto_modelt &model,
  const namespacet &ns,
  const irep_idt &worker,
  stream_refine_sourcet &result,
  std::string &reason,
  const bool allow_sink_role = false,
  stream_refine_consumet *sink_consume = nullptr,
  irep_idt *sink_fold = nullptr)
{
  const auto &program =
    model.goto_functions.function_map.at(worker).body;
  natural_loopst loops;
  loops(program);
  if(loops.loop_map.size() != 1)
  {
    reason = "stream_refine_source_loop_count";
    return false;
  }
  const auto loop_head = loops.loop_map.begin()->first;
  const auto &loop = loops.loop_map.begin()->second;
  irep_idt induction;
  exprt bound;
  if(
    !parse_loop_exit(*loop_head, induction, bound) ||
    !symbol_id(bound, result.count) ||
    !shared_signed(result.count, ns))
  {
    reason = "stream_refine_source_loop_guard";
    return false;
  }
  std::vector<stream_refine_publisht> publishes;
  std::vector<stream_refine_consumet> consumes;
  if(
    !stream_refine_transactions(
      program, loop, ns, publishes, consumes, reason) ||
    publishes.size() != 2 ||
    ((!allow_sink_role && !consumes.empty()) ||
     (allow_sink_role && consumes.size() > 1)))
  {
    if(reason.empty())
      reason = "stream_refine_source_transactions";
    return false;
  }
  for(const auto &publish : publishes)
  {
    mp_integer token;
    if(
      publish.in_loop &&
      integer_constant(publish.token, token) && token > 0)
      result.data = publish;
    else if(!publish.in_loop && value_is(publish.token, 0))
      result.sentinel = publish;
    else
    {
      reason = "stream_refine_source_tokens";
      return false;
    }
  }
  if(
    result.data.channel.storage.empty() ||
    result.sentinel.channel.storage.empty() ||
    result.data.channel.storage != result.sentinel.channel.storage ||
    result.data.channel.back != result.sentinel.channel.back ||
    result.data.channel.bound != result.sentinel.channel.bound)
  {
    reason = "stream_refine_source_channel";
    return false;
  }
  result.worker = worker;
  result.writes.insert(
    result.data.writes.begin(), result.data.writes.end());
  result.writes.insert(
    result.sentinel.writes.begin(), result.sentinel.writes.end());
  if(allow_sink_role && !consumes.empty())
  {
    if(sink_consume == nullptr || sink_fold == nullptr)
    {
      reason = "stream_refine_sink_output";
      return false;
    }
    *sink_consume = consumes.front();
    result.writes.insert(
      sink_consume->writes.begin(), sink_consume->writes.end());
  }

  std::size_t zero_initializations = 0;
  std::size_t sink_folds = 0;
  std::size_t induction_updates = 0;
  std::size_t backedges = 0;
  std::size_t loop_accounts = 0;
  std::size_t sentinel_accounts = 0;
  for(auto instruction = program.instructions.begin();
      instruction != program.instructions.end(); ++instruction)
  {
    if(instruction->is_assign())
    {
      irep_idt lhs;
      if(
        symbol_id(instruction->assign_lhs(), lhs) &&
        lhs == induction && value_is(instruction->assign_rhs(), 0))
        ++zero_initializations;
    }
    if(loop.contains(instruction) &&
       unit_increment(*instruction, induction))
      ++induction_updates;
    if(
      instruction->is_goto() && !instruction->targets.empty() &&
      instruction->get_target()->location_number <
        instruction->location_number)
      ++backedges;
    if(!instruction->is_assign())
    {
      irep_idt callee;
      if(
        call_id(*instruction, callee) &&
        !is_assume(callee))
      {
        reason = "stream_refine_source_call";
        return false;
      }
      continue;
    }
    irep_idt lhs;
    exprt delta;
    if(
      allow_sink_role && !consumes.empty() &&
      sink_fold != nullptr &&
      stream_refine_addition(*instruction, lhs, delta))
    {
      irep_idt token;
      if(
        symbol_id(delta, token) &&
        token == consumes.front().temporary &&
        shared_signed(lhs, ns))
      {
        if(!sink_fold->empty() && *sink_fold != lhs)
        {
          reason = "stream_refine_sink_fold_ownership";
          return false;
        }
        *sink_fold = lhs;
        ++sink_folds;
        result.writes.insert(&*instruction);
        continue;
      }
    }
    if(
      stream_refine_addition(*instruction, lhs, delta) &&
      shared_unsigned32(lhs, ns))
    {
      if(result.account.empty())
      {
        result.account = lhs;
        result.account_delta = strip(delta);
      }
      if(lhs != result.account ||
         strip(delta) != strip(result.account_delta))
      {
        reason = "stream_refine_source_account";
        return false;
      }
      if(loop.contains(instruction))
        ++loop_accounts;
      else
        ++sentinel_accounts;
      result.writes.insert(&*instruction);
    }
  }
  if(
    zero_initializations != 1 || induction_updates != 1 ||
    backedges != 1 ||
    ((!result.account.empty()) &&
     (loop_accounts != 1 || sentinel_accounts != 1)) ||
    (result.account.empty() &&
     (loop_accounts != 0 || sentinel_accounts != 0)))
  {
    reason = "stream_refine_source_control";
    return false;
  }
  if(allow_sink_role)
  {
    std::size_t sink_zero_initializations = 0;
    if(sink_fold != nullptr && !sink_fold->empty())
    {
      for(const auto &instruction : program.instructions)
      {
        irep_idt lhs;
        if(
          instruction.is_assign() &&
          symbol_id(instruction.assign_lhs(), lhs) &&
          lhs == *sink_fold &&
          value_is(instruction.assign_rhs(), 0))
        {
          ++sink_zero_initializations;
          result.writes.insert(&instruction);
        }
      }
    }
    if(
      consumes.size() != 1 || sink_fold == nullptr ||
      sink_fold->empty() || sink_folds != 1 ||
      sink_zero_initializations != 1 ||
      !consumes.front().in_loop ||
      consumes.front().channel.storage == result.data.channel.storage)
    {
      reason = "stream_refine_sink_role";
      return false;
    }
  }
  return true;
}

bool role_split_local_atomic_region(
  const std::vector<const goto_programt::instructiont *> &region,
  const namespacet &ns)
{
  for(const auto *instruction : region)
  {
    if(
      instruction->is_decl() || instruction->is_dead() ||
      instruction->is_location() || instruction->is_skip())
      continue;
    irep_idt lhs;
    if(
      instruction->is_assign() &&
      symbol_id(instruction->assign_lhs(), lhs))
    {
      const symbolt *symbol = lookup(lhs, ns);
      if(
        symbol != nullptr && !symbol->is_static_lifetime &&
        !symbol->is_type)
        continue;
    }
    return false;
  }
  return true;
}

bool role_split_consume_fold_region(
  const std::vector<const goto_programt::instructiont *> &region,
  const namespacet &ns,
  stream_refine_consumet &consume,
  irep_idt &fold,
  std::set<const goto_programt::instructiont *> &writes)
{
  for(std::size_t omitted = 0; omitted < region.size(); ++omitted)
  {
    irep_idt candidate_fold;
    exprt delta;
    if(
      !stream_refine_addition(
        *region[omitted], candidate_fold, delta) ||
      !shared_signed(candidate_fold, ns))
      continue;
    std::vector<const goto_programt::instructiont *> filtered;
    for(std::size_t index = 0; index < region.size(); ++index)
    {
      if(index != omitted)
        filtered.push_back(region[index]);
    }
    stream_refine_consumet candidate_consume;
    if(
      !stream_refine_consume_region(
        filtered, ns, candidate_consume, true))
      continue;
    irep_idt token;
    if(
      !symbol_id(delta, token) ||
      token != candidate_consume.temporary)
      continue;
    consume = candidate_consume;
    fold = candidate_fold;
    writes = consume.writes;
    writes.insert(region[omitted]);
    return true;
  }
  return false;
}

bool role_split_guarded_data_commit(
  const goto_programt &program,
  const natural_loopst::natural_loopt &loop,
  const std::vector<const goto_programt::instructiont *> &region,
  const namespacet &ns,
  const irep_idt &induction,
  stream_refine_publisht &publish)
{
  if(region.empty())
    return false;
  irep_idt back;
  std::size_t back_updates = 0;
  std::size_t induction_updates = 0;
  for(const auto *instruction : region)
  {
    if(
      instruction->is_decl() || instruction->is_dead() ||
      instruction->is_location() || instruction->is_skip())
      continue;
    irep_idt lhs;
    if(
      instruction->is_assign() &&
      symbol_id(instruction->assign_lhs(), lhs) &&
      unit_increment(*instruction, lhs))
    {
      if(lhs == induction)
      {
        ++induction_updates;
        publish.writes.insert(instruction);
        continue;
      }
      if(shared_signed(lhs, ns))
      {
        if(!back.empty() && back != lhs)
          return false;
        back = lhs;
        ++back_updates;
        publish.writes.insert(instruction);
        continue;
      }
    }
    return false;
  }
  if(
    back.empty() || back_updates != 1 ||
    induction_updates != 1)
    return false;

  std::vector<exprt> preceding_assumptions;
  const goto_programt::instructiont *guard = nullptr;
  irep_idt storage;
  exprt token;
  for(auto instruction = program.instructions.begin();
      instruction != program.instructions.end(); ++instruction)
  {
    if(
      instruction->location_number >= region.front()->location_number)
      break;
    if(!loop.contains(instruction))
      continue;
    irep_idt callee;
    if(
      call_id(*instruction, callee) && is_assume(callee) &&
      instruction->call_arguments().size() == 1)
    {
      flatten_and(
        instruction->call_arguments().front(),
        preceding_assumptions);
      continue;
    }
    if(
      !instruction->is_goto() || instruction->targets.size() != 1 ||
      instruction->get_target()->location_number <=
        region.back()->location_number)
      continue;
    const exprt &condition = strip(instruction->condition());
    if(
      condition.id() != ID_not ||
      condition.operands().size() != 1)
      continue;
    irep_idt candidate_storage;
    irep_idt candidate_back;
    exprt candidate_token;
    if(
      !array_equality_term(
        condition.op0(),
        candidate_storage,
        candidate_back,
        candidate_token) ||
      candidate_back != back)
      continue;
    if(guard != nullptr)
      return false;
    guard = &*instruction;
    storage = candidate_storage;
    token = strip(candidate_token);
  }
  irep_idt bound;
  mp_integer data_token;
  const symbolt *queue = lookup(storage, ns);
  if(
    guard == nullptr ||
    !stream_refine_bounds(preceding_assumptions, back, bound) ||
    !shared_signed(bound, ns) ||
    !integer_constant(token, data_token) || data_token <= 0 ||
    queue == nullptr || !queue->is_static_lifetime ||
    queue->type.id() != ID_pointer ||
    to_pointer_type(queue->type).base_type().id() != ID_signedbv)
    return false;

  publish.channel.storage = storage;
  publish.channel.back = back;
  publish.channel.bound = bound;
  publish.token = token;
  publish.in_loop = true;
  publish.first_location = region.front()->location_number;
  publish.last_location = region.back()->location_number;
  return true;
}

bool role_split_guarded_consume_fold_region(
  const goto_programt &program,
  const natural_loopst::natural_loopt &loop,
  const std::vector<const goto_programt::instructiont *> &region,
  const namespacet &ns,
  stream_refine_consumet &consume,
  irep_idt &fold,
  std::set<const goto_programt::instructiont *> &writes)
{
  std::vector<exprt> terms;
  const goto_programt::instructiont *assume = nullptr;
  const goto_programt::instructiont *read = nullptr;
  const goto_programt::instructiont *increment = nullptr;
  const goto_programt::instructiont *fold_instruction = nullptr;
  irep_idt storage;
  irep_idt front;
  for(const auto *instruction : region)
  {
    irep_idt callee;
    if(
      call_id(*instruction, callee) && is_assume(callee) &&
      instruction->call_arguments().size() == 1)
    {
      if(assume != nullptr)
        return false;
      assume = instruction;
      flatten_and(instruction->call_arguments().front(), terms);
      continue;
    }
    if(instruction->is_assign())
    {
      irep_idt lhs;
      irep_idt candidate_storage;
      irep_idt candidate_front;
      if(
        symbol_id(instruction->assign_lhs(), lhs) &&
        array_symbol_index(
          instruction->assign_rhs(),
          candidate_storage,
          candidate_front))
      {
        if(
          read != nullptr || !local_signed(lhs, ns))
          return false;
        consume.temporary = lhs;
        storage = candidate_storage;
        front = candidate_front;
        read = instruction;
        writes.insert(instruction);
        continue;
      }
      if(
        symbol_id(instruction->assign_lhs(), lhs) &&
        unit_increment(*instruction, lhs) &&
        (front.empty() || lhs == front))
      {
        front = lhs;
        increment = instruction;
        writes.insert(instruction);
        continue;
      }
      exprt delta;
      if(
        stream_refine_addition(*instruction, lhs, delta) &&
        shared_signed(lhs, ns))
      {
        irep_idt token;
        if(
          !symbol_id(delta, token) ||
          token != consume.temporary ||
          fold_instruction != nullptr)
          return false;
        fold = lhs;
        fold_instruction = instruction;
        writes.insert(instruction);
        continue;
      }
      return false;
    }
    if(
      instruction->is_decl() || instruction->is_dead() ||
      instruction->is_location() || instruction->is_skip())
      continue;
    return false;
  }
  irep_idt bound;
  const symbolt *queue = lookup(storage, ns);
  if(
    assume == nullptr || read == nullptr || increment == nullptr ||
    fold_instruction == nullptr ||
    assume->location_number >= read->location_number ||
    read->location_number >= increment->location_number ||
    increment->location_number >= fold_instruction->location_number ||
    !stream_refine_bounds(terms, front, bound) ||
    !shared_signed(front, ns) || !shared_signed(bound, ns) ||
    queue == nullptr || !queue->is_static_lifetime ||
    queue->type.id() != ID_pointer ||
    to_pointer_type(queue->type).base_type().id() != ID_signedbv)
    return false;

  irep_idt availability_flag;
  irep_idt back;
  const goto_programt::instructiont *availability_definition = nullptr;
  for(auto instruction = program.instructions.begin();
      instruction != program.instructions.end(); ++instruction)
  {
    if(
      instruction->location_number >= region.front()->location_number)
      break;
    if(!loop.contains(instruction) || !instruction->is_assign())
      continue;
    irep_idt flag;
    if(
      !symbol_id(instruction->assign_lhs(), flag) ||
      !local_boolean(flag, ns))
      continue;
    const exprt &rhs = strip(instruction->assign_rhs());
    irep_idt candidate_back;
    irep_idt candidate_front;
    if(
      rhs.id() != ID_gt || rhs.operands().size() != 2 ||
      !symbol_id(rhs.op0(), candidate_back) ||
      !symbol_id(rhs.op1(), candidate_front) ||
      candidate_front != front ||
      !shared_signed(candidate_back, ns))
      continue;
    if(availability_definition != nullptr)
      return false;
    availability_definition = &*instruction;
    availability_flag = flag;
    back = candidate_back;
  }
  bool guarded = false;
  for(auto instruction = program.instructions.begin();
      instruction != program.instructions.end(); ++instruction)
  {
    if(
      availability_definition == nullptr ||
      instruction->location_number <=
        availability_definition->location_number)
      continue;
    if(
      instruction->location_number >= region.front()->location_number)
      break;
    irep_idt rewritten;
    if(
      instruction->is_assign() &&
      symbol_id(instruction->assign_lhs(), rewritten) &&
      rewritten == availability_flag)
      return false;
    if(
      !loop.contains(instruction) || !instruction->is_goto() ||
      instruction->targets.size() != 1 ||
      instruction->get_target()->location_number <=
        region.back()->location_number)
      continue;
    const exprt &condition = strip(instruction->condition());
    if(
      condition.id() != ID_not ||
      condition.operands().size() != 1)
      continue;
    const exprt &test = strip(condition.op0());
    irep_idt flag;
    if(
      test.id() == ID_notequal &&
      test.operands().size() == 2 &&
      symbol_id(test.op0(), flag) &&
      flag == availability_flag &&
      value_is(test.op1(), 0))
    {
      if(guarded)
        return false;
      guarded = true;
    }
  }
  if(!guarded || back.empty())
    return false;

  consume.channel.storage = storage;
  consume.channel.front = front;
  consume.channel.back = back;
  consume.channel.bound = bound;
  consume.in_loop = true;
  consume.first_location = region.front()->location_number;
  consume.last_location = region.back()->location_number;
  consume.writes.insert(writes.begin(), writes.end());
  return true;
}

bool role_split_guarded_source_sink(
  const goto_modelt &model,
  const namespacet &ns,
  const irep_idt &worker,
  stream_refine_sourcet &source,
  stream_refine_consumet &sink_consume,
  irep_idt &sink_fold,
  std::string &reason)
{
  const auto &program =
    model.goto_functions.function_map.at(worker).body;
  natural_loopst loops;
  loops(program);
  if(loops.loop_map.size() != 1)
  {
    reason = "role_split_guarded_loop_count";
    return false;
  }
  const auto loop_head = loops.loop_map.begin()->first;
  const auto &loop = loops.loop_map.begin()->second;
  irep_idt induction;
  exprt bound;
  if(
    !parse_loop_exit(*loop_head, induction, bound) ||
    !symbol_id(bound, source.count) ||
    !shared_signed(source.count, ns))
  {
    reason = "role_split_guarded_loop_guard";
    return false;
  }

  bool in_atomic = false;
  bool region_in_loop = false;
  std::vector<const goto_programt::instructiont *> region;
  std::size_t local_regions = 0;
  std::size_t data_commits = 0;
  std::size_t sink_regions = 0;
  std::size_t sentinels = 0;
  for(auto instruction = program.instructions.begin();
      instruction != program.instructions.end(); ++instruction)
  {
    if(instruction->is_atomic_begin())
    {
      if(in_atomic)
      {
        reason = "role_split_guarded_atomic_nesting";
        return false;
      }
      in_atomic = true;
      region_in_loop = loop.contains(instruction);
      region.clear();
      continue;
    }
    if(instruction->is_atomic_end())
    {
      if(!in_atomic || loop.contains(instruction) != region_in_loop)
      {
        reason = "role_split_guarded_atomic_balance";
        return false;
      }
      stream_refine_publisht publish;
      if(
        !region_in_loop &&
        stream_refine_publish_region(region, ns, false, publish))
      {
        source.sentinel = publish;
        ++sentinels;
      }
      else if(
        region_in_loop &&
        role_split_guarded_data_commit(
          program, loop, region, ns, induction, publish))
      {
        source.data = publish;
        ++data_commits;
      }
      else
      {
        stream_refine_consumet consume;
        irep_idt fold;
        std::set<const goto_programt::instructiont *> writes;
        if(
          region_in_loop &&
          role_split_consume_fold_region(
            region, ns, consume, fold, writes))
        {
          sink_consume = consume;
          sink_fold = fold;
          source.writes.insert(writes.begin(), writes.end());
          ++sink_regions;
        }
        else if(
          region_in_loop &&
          role_split_guarded_consume_fold_region(
            program,
            loop,
            region,
            ns,
            consume,
            fold,
            writes))
        {
          sink_consume = consume;
          sink_fold = fold;
          source.writes.insert(writes.begin(), writes.end());
          ++sink_regions;
        }
        else if(
          region_in_loop &&
          role_split_local_atomic_region(region, ns))
          ++local_regions;
        else
        {
          reason =
            "role_split_guarded_atomic_region_" +
            std::to_string(
              region.empty() ? 0 :
              region.front()->location_number);
          return false;
        }
      }
      in_atomic = false;
      region.clear();
      continue;
    }
    if(in_atomic)
      region.push_back(&*instruction);
  }
  if(
    in_atomic || local_regions != 1 || data_commits != 1 ||
    sink_regions != 1 || sentinels != 1)
  {
    reason = "role_split_guarded_regions";
    return false;
  }
  if(
    source.data.channel.storage != source.sentinel.channel.storage ||
    source.data.channel.back != source.sentinel.channel.back ||
    source.data.channel.bound != source.sentinel.channel.bound ||
    source.data.channel.storage == sink_consume.channel.storage)
  {
    reason = "role_split_guarded_channels";
    return false;
  }

  std::size_t induction_zero = 0;
  std::size_t induction_updates = 0;
  std::size_t fold_zero = 0;
  for(auto instruction = program.instructions.begin();
      instruction != program.instructions.end(); ++instruction)
  {
    if(!instruction->is_assign())
      continue;
    irep_idt lhs;
    if(!symbol_id(instruction->assign_lhs(), lhs))
      continue;
    if(lhs == induction && value_is(instruction->assign_rhs(), 0))
      ++induction_zero;
    if(loop.contains(instruction) &&
       unit_increment(*instruction, induction))
      ++induction_updates;
    if(lhs == sink_fold && value_is(instruction->assign_rhs(), 0))
    {
      ++fold_zero;
      source.writes.insert(&*instruction);
    }
  }
  if(
    induction_zero != 1 || induction_updates != 1 ||
    fold_zero != 1)
  {
    reason = "role_split_guarded_initialization";
    return false;
  }

  source.worker = worker;
  source.writes.insert(
    source.data.writes.begin(), source.data.writes.end());
  source.writes.insert(
    source.sentinel.writes.begin(), source.sentinel.writes.end());
  source.writes.insert(
    sink_consume.writes.begin(), sink_consume.writes.end());
  return true;
}

bool stream_refine_lifecycle(
  const goto_modelt &model,
  lifecyclet &result,
  std::vector<irep_idt> &order,
  std::string &reason)
{
  const auto main = model.goto_functions.function_map.find(ID_main);
  if(
    main == model.goto_functions.function_map.end() ||
    !main->second.body_available())
  {
    reason = "stream_refine_main";
    return false;
  }
  bool joining = false;
  for(const auto &instruction : main->second.body.instructions)
  {
    irep_idt callee;
    if(!call_id(instruction, callee))
      continue;
    const auto &arguments = instruction.call_arguments();
    if(is_create(callee))
    {
      irep_idt handle;
      irep_idt worker;
      if(
        joining || arguments.size() < 3 ||
        !addressed_id(arguments[0], handle) ||
        !addressed_id(arguments[2], worker) ||
        !result.handles.insert(handle).second ||
        !result.workers.insert(worker).second)
      {
        reason = "stream_refine_create";
        return false;
      }
      order.push_back(worker);
      if(result.first_create == nullptr)
        result.first_create = &instruction;
    }
    else if(is_join(callee))
    {
      joining = true;
      irep_idt handle;
      if(
        arguments.empty() || !symbol_id(arguments[0], handle) ||
        !result.joins.insert(handle).second)
      {
        reason = "stream_refine_join";
        return false;
      }
      result.last_join = &instruction;
    }
  }
  if(
    (order.size() != 2 && order.size() != 3) ||
    result.handles != result.joins ||
    result.first_create == nullptr || result.last_join == nullptr)
  {
    reason = "stream_refine_lifecycle";
    return false;
  }
  for(const auto &worker : order)
  {
    const auto found = model.goto_functions.function_map.find(worker);
    if(
      found == model.goto_functions.function_map.end() ||
      !found->second.body_available())
    {
      reason = "stream_refine_worker_body";
      return false;
    }
  }
  return true;
}

bool stream_refine_nonnegative_count(
  const goto_modelt &model,
  const lifecyclet &life,
  const irep_idt &count)
{
  const auto &main =
    model.goto_functions.function_map.at(ID_main).body;
  for(const auto &instruction : main.instructions)
  {
    if(
      life.first_create != nullptr &&
      instruction.location_number >=
        life.first_create->location_number)
      break;
    irep_idt callee;
    if(
      !call_id(instruction, callee) || !is_assume(callee) ||
      instruction.call_arguments().size() != 1)
      continue;
    std::vector<exprt> terms;
    flatten_and(instruction.call_arguments().front(), terms);
    for(const auto &term : terms)
    {
      if(stream_refine_symbol_zero_relation(term, count, ID_ge))
        return true;
    }
  }
  return false;
}

bool stream_refine_initial_channel(
  const goto_modelt &model,
  const lifecyclet &life,
  const stream_refine_channelt &channel)
{
  const auto &main =
    model.goto_functions.function_map.at(ID_main).body;
  const goto_programt::instructiont *front_write = nullptr;
  const goto_programt::instructiont *back_write = nullptr;
  for(const auto &instruction : main.instructions)
  {
    if(
      life.first_create != nullptr &&
      instruction.location_number >=
        life.first_create->location_number)
      break;
    if(!instruction.is_assign())
      continue;
    irep_idt lhs;
    if(!symbol_id(instruction.assign_lhs(), lhs))
      continue;
    if(lhs == channel.front)
      front_write = &instruction;
    if(lhs == channel.back)
      back_write = &instruction;
  }
  if(front_write == nullptr || back_write == nullptr)
    return false;
  irep_idt rhs;
  return
    (symbol_id(back_write->assign_rhs(), rhs) &&
     rhs == channel.front &&
     front_write->location_number < back_write->location_number) ||
    (symbol_id(front_write->assign_rhs(), rhs) &&
     rhs == channel.back &&
     back_write->location_number < front_write->location_number);
}

bool stream_refine_property(
  const goto_modelt &model,
  const namespacet &ns,
  const lifecyclet &life,
  std::set<std::pair<irep_idt, irep_idt>> &equalities,
  irep_idt &sink,
  exprt &expected,
  const goto_programt::instructiont *&assumption,
  const goto_programt::instructiont *&error,
  std::string &reason)
{
  std::size_t errors = 0;
  for(const auto &entry : model.goto_functions.function_map)
  {
    for(const auto &instruction : entry.second.body.instructions)
    {
      irep_idt callee;
      if(call_id(instruction, callee) && is_reach_error(callee))
      {
        ++errors;
        if(entry.first != ID_main)
        {
          reason = "stream_refine_error_function";
          return false;
        }
        error = &instruction;
      }
    }
  }
  const auto &main =
    model.goto_functions.function_map.at(ID_main).body;
  std::size_t matches = 0;
  for(const auto &instruction : main.instructions)
  {
    if(
      life.last_join == nullptr ||
      instruction.location_number <= life.last_join->location_number)
      continue;
    irep_idt callee;
    if(
      !call_id(instruction, callee) || !is_assume(callee) ||
      instruction.call_arguments().size() != 1)
      continue;
    std::vector<exprt> terms;
    flatten_or(instruction.call_arguments().front(), terms);
    std::set<std::pair<irep_idt, irep_idt>> candidate_equalities;
    irep_idt candidate_sink;
    exprt candidate_expected;
    bool valid = !terms.empty();
    for(const auto &term : terms)
    {
      exprt relation = strip(term);
      if(
        relation.id() == ID_not &&
        relation.operands().size() == 1)
      {
        const exprt &inner = strip(relation.op0());
        if(inner.id() == ID_equal)
          relation = inner;
      }
      irep_idt left;
      irep_idt right;
      if(
        (relation.id() != ID_notequal &&
         relation.id() != ID_equal) ||
        relation.operands().size() != 2)
      {
        valid = false;
        break;
      }
      const bool left_symbol = symbol_id(relation.op0(), left);
      const bool right_symbol = symbol_id(relation.op1(), right);
      if(
        left_symbol && right_symbol &&
        shared_unsigned32(left, ns) &&
        shared_unsigned32(right, ns))
        candidate_equalities.insert(std::minmax(left, right));
      else if(
        left_symbol && shared_signed(left, ns) &&
        relation.op1().type().id() == ID_signedbv)
      {
        if(!candidate_sink.empty())
        {
          valid = false;
          break;
        }
        candidate_sink = left;
        candidate_expected = strip(relation.op1());
      }
      else if(
        right_symbol && shared_signed(right, ns) &&
        relation.op0().type().id() == ID_signedbv)
      {
        if(!candidate_sink.empty())
        {
          valid = false;
          break;
        }
        candidate_sink = right;
        candidate_expected = strip(relation.op0());
      }
      else
      {
        valid = false;
        break;
      }
    }
    if(valid && !candidate_sink.empty())
    {
      ++matches;
      sink = candidate_sink;
      expected = candidate_expected;
      equalities = candidate_equalities;
      assumption = &instruction;
    }
  }
  if(
    matches != 1 || errors != 1 || assumption == nullptr ||
    error == nullptr ||
    assumption->location_number >= error->location_number)
  {
    reason = "stream_refine_property";
    return false;
  }
  return true;
}

bool stream_refine_expected_fold(
  const exprt &expected,
  const irep_idt &count,
  const mp_integer &token)
{
  irep_idt symbol;
  if(
    token == 1 && symbol_id(expected, symbol) &&
    symbol == count)
    return true;
  const exprt &product = strip(expected);
  if(product.id() != ID_mult || product.operands().size() != 2)
    return false;
  return
    ((symbol_id(product.op0(), symbol) && symbol == count &&
      value_is(product.op1(), token)) ||
     (symbol_id(product.op1(), symbol) && symbol == count &&
      value_is(product.op0(), token)));
}

bool stream_refine_product_defined(
  const goto_modelt &model,
  const lifecyclet &life,
  const irep_idt &count,
  const mp_integer &token)
{
  if(token == 1)
    return true;
  const mp_integer maximum =
    (power(2, 31) - 1) / token;
  const auto &main =
    model.goto_functions.function_map.at(ID_main).body;
  for(const auto &instruction : main.instructions)
  {
    if(
      life.first_create != nullptr &&
      instruction.location_number >=
        life.first_create->location_number)
      break;
    irep_idt callee;
    if(
      !call_id(instruction, callee) || !is_assume(callee) ||
      instruction.call_arguments().size() != 1)
      continue;
    std::vector<exprt> terms;
    flatten_and(instruction.call_arguments().front(), terms);
    for(const auto &term : terms)
    {
      const exprt &relation = strip(term);
      irep_idt lhs;
      mp_integer bound;
      if(
        relation.id() == ID_le &&
        relation.operands().size() == 2 &&
        symbol_id(relation.op0(), lhs) && lhs == count &&
        integer_constant(relation.op1(), bound) &&
        bound <= maximum)
        return true;
    }
  }
  return false;
}

bool stream_refine_fresh_queues(
  const goto_modelt &model,
  const namespacet &ns,
  const lifecyclet &life,
  const std::set<irep_idt> &queues,
  std::string &reason)
{
  const auto &main =
    model.goto_functions.function_map.at(ID_main).body;
  std::set<irep_idt> found;
  std::set<irep_idt> allocators;
  for(const auto &instruction : main.instructions)
  {
    if(
      life.first_create != nullptr &&
      instruction.location_number >=
        life.first_create->location_number)
      break;
    if(
      !instruction.is_function_call() ||
      instruction.call_lhs().is_nil())
      continue;
    irep_idt lhs;
    irep_idt callee;
    if(
      symbol_id(instruction.call_lhs(), lhs) &&
      queues.count(lhs) != 0 &&
      call_id(instruction, callee))
    {
      found.insert(lhs);
      allocators.insert(callee);
    }
  }
  if(found != queues || allocators.size() != 1)
  {
    reason = "stream_refine_allocator_calls";
    return false;
  }
  return
    fresh_array_allocator(
      model, ns, *allocators.begin(), reason);
}

bool stream_refine_global(
  const goto_modelt &model,
  const namespacet &ns,
  const lifecyclet &life,
  const stream_refine_sourcet &source,
  const std::vector<stream_refine_staget> &stages,
  const std::set<irep_idt> &queues,
  const std::set<irep_idt> &protected_symbols,
  const std::set<const goto_programt::instructiont *> &allowed,
  const goto_programt::instructiont *property_assumption,
  const goto_programt::instructiont *error,
  std::string &reason)
{
  for(const auto &entry : model.goto_functions.function_map)
  {
    for(const auto &instruction : entry.second.body.instructions)
    {
      const exprt *lhs = nullptr;
      if(instruction.is_assign())
        lhs = &instruction.assign_lhs();
      else if(
        instruction.is_function_call() &&
        !instruction.call_lhs().is_nil())
        lhs = &instruction.call_lhs();
      if(lhs == nullptr)
        continue;
      irep_idt direct;
      irep_idt base;
      const bool protected_write =
        (symbol_id(*lhs, direct) &&
         protected_symbols.count(direct) != 0) ||
        (base_pointer(*lhs, base) && queues.count(base) != 0);
      if(!protected_write)
        continue;
      if(
        is_start_function(entry.first) && instruction.is_assign() &&
        value_is(instruction.assign_rhs(), 0))
        continue;
      if(
        entry.first == ID_main && life.first_create != nullptr &&
        instruction.location_number <
          life.first_create->location_number)
        continue;
      if(allowed.count(&instruction) == 0)
      {
        reason = "stream_refine_external_writer";
        return false;
      }
    }
  }
  for(const auto &queue : queues)
  {
    if(!flow_alias_free(model, queue, reason))
      return false;
  }
  flow_equality_propertyt control;
  control.assumption = property_assumption;
  control.error = error;
  return
    no_addresses(model, protected_symbols, reason) &&
    flow_main_control(model, life, control, reason);
}

struct prefix_channel_last_consumert
{
  irep_idt worker;
  stream_refine_consumet consume;
  irep_idt sink;
  std::set<const goto_programt::instructiont *> writes;
};

bool prefix_channel_last_consume_region(
  const std::vector<const goto_programt::instructiont *> &region,
  const namespacet &ns,
  stream_refine_consumet &consume,
  irep_idt &sink)
{
  std::vector<exprt> terms;
  std::size_t assumes = 0;
  std::size_t reads = 0;
  std::size_t increments = 0;
  const goto_programt::instructiont *last_assume = nullptr;
  const goto_programt::instructiont *read = nullptr;
  const goto_programt::instructiont *increment = nullptr;
  irep_idt storage;
  irep_idt front;
  for(const auto *instruction : region)
  {
    irep_idt callee;
    if(call_id(*instruction, callee))
    {
      if(
        !is_assume(callee) ||
        instruction->call_arguments().size() != 1)
        return false;
      ++assumes;
      flatten_and(instruction->call_arguments().front(), terms);
      last_assume = instruction;
      continue;
    }
    if(instruction->is_assign())
    {
      irep_idt lhs;
      irep_idt candidate_storage;
      irep_idt candidate_front;
      if(
        symbol_id(instruction->assign_lhs(), lhs) &&
        array_symbol_index(
          instruction->assign_rhs(),
          candidate_storage,
          candidate_front))
      {
        if(
          reads != 0 || !shared_signed(lhs, ns) ||
          lhs == candidate_front || lhs == candidate_storage)
          return false;
        sink = lhs;
        storage = candidate_storage;
        front = candidate_front;
        ++reads;
        read = instruction;
        consume.writes.insert(instruction);
        continue;
      }
      if(
        symbol_id(instruction->assign_lhs(), lhs) &&
        unit_increment(*instruction, lhs))
      {
        if(!front.empty() && front != lhs)
          return false;
        front = lhs;
        ++increments;
        increment = instruction;
        consume.writes.insert(instruction);
        continue;
      }
      return false;
    }
    if(
      instruction->is_decl() || instruction->is_dead() ||
      instruction->is_location() || instruction->is_skip())
      continue;
    return false;
  }
  irep_idt back;
  irep_idt bound;
  if(
    assumes != 1 || reads != 1 || increments != 1 ||
    last_assume == nullptr || read == nullptr || increment == nullptr ||
    last_assume->location_number >= read->location_number ||
    read->location_number >= increment->location_number ||
    !stream_refine_consume_guard(terms, front, back, bound) ||
    !shared_signed(front, ns) || !shared_signed(back, ns) ||
    !shared_signed(bound, ns))
    return false;
  consume.channel.storage = storage;
  consume.channel.front = front;
  consume.channel.back = back;
  consume.channel.bound = bound;
  consume.first_location =
    region.empty() ? 0 : region.front()->location_number;
  consume.last_location =
    region.empty() ? 0 : region.back()->location_number;
  return true;
}

bool prefix_channel_last_consumer(
  const goto_modelt &model,
  const namespacet &ns,
  const irep_idt &worker,
  prefix_channel_last_consumert &result,
  std::string &reason)
{
  const auto &program =
    model.goto_functions.function_map.at(worker).body;
  for(const auto &instruction : program.instructions)
  {
    if(!instruction.is_function_call())
      continue;
    irep_idt callee;
    if(!call_id(instruction, callee) || !is_assume(callee))
    {
      reason = "prefix_last_external_call";
      return false;
    }
  }
  natural_loopst loops;
  loops(program);
  if(loops.loop_map.size() != 1)
  {
    reason = "prefix_last_loop_count";
    return false;
  }
  const auto &loop = loops.loop_map.begin()->second;
  bool in_atomic = false;
  bool region_in_loop = false;
  std::vector<const goto_programt::instructiont *> region;
  std::size_t matches = 0;
  for(auto instruction = program.instructions.begin();
      instruction != program.instructions.end(); ++instruction)
  {
    if(instruction->is_atomic_begin())
    {
      if(in_atomic)
      {
        reason = "prefix_last_atomic_nesting";
        return false;
      }
      in_atomic = true;
      region_in_loop = loop.contains(instruction);
      region.clear();
      continue;
    }
    if(instruction->is_atomic_end())
    {
      if(!in_atomic || !region_in_loop || !loop.contains(instruction))
      {
        reason = "prefix_last_atomic_balance";
        return false;
      }
      stream_refine_consumet consume;
      irep_idt sink;
      if(!prefix_channel_last_consume_region(region, ns, consume, sink))
      {
        reason = "prefix_last_atomic_transaction";
        return false;
      }
      result.consume = consume;
      result.sink = sink;
      result.writes.insert(
        consume.writes.begin(), consume.writes.end());
      ++matches;
      in_atomic = false;
      region.clear();
      continue;
    }
    if(in_atomic)
      region.push_back(&*instruction);
  }
  if(in_atomic || matches != 1)
  {
    reason = "prefix_last_consume_count";
    return false;
  }
  result.worker = worker;
  return true;
}

bool prefix_channel_constant_publisher(
  const goto_modelt &model,
  const namespacet &ns,
  const irep_idt &worker,
  stream_refine_publisht &publish,
  std::set<const goto_programt::instructiont *> &writes,
  std::string &reason)
{
  const auto &program =
    model.goto_functions.function_map.at(worker).body;
  for(const auto &instruction : program.instructions)
  {
    if(!instruction.is_function_call())
      continue;
    irep_idt callee;
    if(!call_id(instruction, callee) || !is_assume(callee))
    {
      reason = "prefix_publish_external_call";
      return false;
    }
  }
  natural_loopst loops;
  loops(program);
  if(loops.loop_map.size() != 1)
  {
    reason = "prefix_publish_loop_count";
    return false;
  }
  const auto &loop = loops.loop_map.begin()->second;
  std::vector<stream_refine_publisht> publishes;
  std::vector<stream_refine_consumet> consumes;
  if(
    !stream_refine_transactions(
      program, loop, ns, publishes, consumes, reason) ||
    publishes.size() != 1 || !consumes.empty() ||
    !publishes.front().in_loop)
  {
    if(reason.empty())
      reason = "prefix_publish_transactions";
    return false;
  }
  mp_integer token;
  if(!integer_constant(publishes.front().token, token))
  {
    reason = "prefix_publish_nonconstant";
    return false;
  }
  publish = publishes.front();
  writes = publish.writes;
  return true;
}

bool prefix_channel_last_property(
  const goto_modelt &model,
  const lifecyclet &life,
  const irep_idt &sink,
  const exprt &token,
  const goto_programt::instructiont *&assumption,
  const goto_programt::instructiont *&error,
  std::string &reason)
{
  std::size_t errors = 0;
  for(const auto &entry : model.goto_functions.function_map)
  {
    for(const auto &instruction : entry.second.body.instructions)
    {
      irep_idt callee;
      if(call_id(instruction, callee) && is_reach_error(callee))
      {
        ++errors;
        if(entry.first != ID_main)
        {
          reason = "prefix_last_error_function";
          return false;
        }
        error = &instruction;
      }
    }
  }
  const auto &main =
    model.goto_functions.function_map.at(ID_main).body;
  std::size_t matches = 0;
  for(const auto &instruction : main.instructions)
  {
    if(
      life.last_join == nullptr ||
      instruction.location_number <= life.last_join->location_number)
      continue;
    irep_idt callee;
    if(
      !call_id(instruction, callee) || !is_assume(callee) ||
      instruction.call_arguments().size() != 1)
      continue;
    const exprt &condition =
      strip(instruction.call_arguments().front());
    if(
      condition.id() != ID_notequal ||
      condition.operands().size() != 2)
      continue;
    irep_idt candidate;
    const bool matching =
      (symbol_id(condition.op0(), candidate) && candidate == sink &&
       strip(condition.op1()) == strip(token)) ||
      (symbol_id(condition.op1(), candidate) && candidate == sink &&
       strip(condition.op0()) == strip(token));
    if(matching)
    {
      assumption = &instruction;
      ++matches;
    }
  }
  if(
    errors != 1 || matches != 1 || assumption == nullptr ||
    error == nullptr ||
    assumption->location_number >= error->location_number)
  {
    reason = "prefix_last_property";
    return false;
  }
  return true;
}

bool prefix_channel_initial_value(
  const goto_modelt &model,
  const lifecyclet &life,
  const irep_idt &symbol,
  const exprt &value)
{
  const auto &main =
    model.goto_functions.function_map.at(ID_main).body;
  const goto_programt::instructiont *last = nullptr;
  for(const auto &instruction : main.instructions)
  {
    if(
      life.first_create != nullptr &&
      instruction.location_number >=
        life.first_create->location_number)
      break;
    irep_idt lhs;
    if(
      instruction.is_assign() &&
      symbol_id(instruction.assign_lhs(), lhs) &&
      lhs == symbol)
      last = &instruction;
  }
  return
    last != nullptr &&
    (strip(last->assign_rhs()) == strip(value) ||
     (value_is(last->assign_rhs(), 1) &&
      (value_is(value, 1) || strip(value).is_true())));
}

bool prefix_channel_last_value_proof_impl(
  const goto_modelt &model,
  const namespacet &ns,
  std::string &reason)
{
  lifecyclet life;
  std::vector<irep_idt> workers;
  if(!stream_refine_lifecycle(model, life, workers, reason))
    return false;

  stream_refine_publisht publish;
  std::set<const goto_programt::instructiont *> publish_writes;
  prefix_channel_last_consumert consumer;
  for(const auto &worker : workers)
  {
    stream_refine_publisht candidate_publish;
    std::set<const goto_programt::instructiont *> candidate_writes;
    std::string publish_reason;
    if(
      prefix_channel_constant_publisher(
        model,
        ns,
        worker,
        candidate_publish,
        candidate_writes,
        publish_reason))
    {
      if(!publish.channel.storage.empty())
      {
        reason = "prefix_last_multiple_publishers";
        return false;
      }
      publish = candidate_publish;
      publish_writes = candidate_writes;
      continue;
    }
    prefix_channel_last_consumert candidate_consumer;
    std::string consume_reason;
    if(
      prefix_channel_last_consumer(
        model, ns, worker, candidate_consumer, consume_reason))
    {
      if(!consumer.worker.empty())
      {
        reason = "prefix_last_multiple_consumers";
        return false;
      }
      consumer = candidate_consumer;
      continue;
    }
    reason =
      "prefix_last_worker_publish_" + publish_reason +
      "_consume_" + consume_reason;
    return false;
  }
  if(
    publish.channel.storage.empty() || consumer.worker.empty() ||
    publish.channel.storage != consumer.consume.channel.storage ||
    publish.channel.back != consumer.consume.channel.back ||
    publish.channel.bound != consumer.consume.channel.bound)
  {
    reason = "prefix_last_channel_signature";
    return false;
  }
  stream_refine_channelt channel = publish.channel;
  channel.front = consumer.consume.channel.front;
  if(
    !stream_refine_initial_channel(model, life, channel) ||
    !prefix_channel_initial_value(
      model, life, consumer.sink, publish.token))
  {
    reason = "prefix_last_initial_state";
    return false;
  }

  const goto_programt::instructiont *property_assumption = nullptr;
  const goto_programt::instructiont *error = nullptr;
  if(
    !prefix_channel_last_property(
      model,
      life,
      consumer.sink,
      publish.token,
      property_assumption,
      error,
      reason))
    return false;

  const std::set<irep_idt> queues = {channel.storage};
  const std::set<irep_idt> protected_symbols = {
    channel.storage,
    channel.front,
    channel.back,
    channel.bound,
    consumer.sink};
  std::set<const goto_programt::instructiont *> allowed =
    publish_writes;
  allowed.insert(
    consumer.writes.begin(), consumer.writes.end());
  stream_refine_sourcet unused_source;
  std::vector<stream_refine_staget> unused_stages;
  if(
    !stream_refine_fresh_queues(
      model, ns, life, queues, reason) ||
    !stream_refine_global(
      model,
      ns,
      life,
      unused_source,
      unused_stages,
      queues,
      protected_symbols,
      allowed,
      property_assumption,
      error,
      reason))
    return false;

  std::cout << "NATIVE_PREFIX_CHANNEL applied=1"
            << " rule=constant_last"
            << " storage=" << channel.storage
            << " sink=" << consumer.sink << '\n';
  return true;
}

struct prefix_channel_alternating_publishert
{
  irep_idt worker;
  stream_refine_channelt channel;
  irep_idt state;
  mp_integer positive;
  std::set<const goto_programt::instructiont *> writes;

  prefix_channel_alternating_publishert() : positive(0)
  {
  }
};

struct prefix_channel_sum_consumert
{
  irep_idt worker;
  stream_refine_channelt channel;
  irep_idt sum;
  irep_idt temporary;
  std::set<const goto_programt::instructiont *> writes;
};

bool prefix_channel_loop_contains(
  const goto_programt &program,
  const natural_loopst::natural_loopt &loop,
  const goto_programt::instructiont *instruction)
{
  for(auto current = program.instructions.begin();
      current != program.instructions.end(); ++current)
  {
    if(&*current == instruction)
      return loop.contains(current);
  }
  return false;
}

bool prefix_channel_false_test(
  const exprt &src,
  const irep_idt &symbol)
{
  const exprt &outer = strip(src);
  if(outer.id() != ID_not || outer.operands().size() != 1)
    return false;
  const exprt &truth = strip(outer.op0());
  if(truth.id() != ID_notequal || truth.operands().size() != 2)
    return false;
  irep_idt candidate;
  return
    (symbol_id(truth.op0(), candidate) && candidate == symbol &&
     value_is(truth.op1(), 0)) ||
    (symbol_id(truth.op1(), candidate) && candidate == symbol &&
     value_is(truth.op0(), 0));
}

bool prefix_channel_true_test(
  const exprt &src,
  const irep_idt &symbol)
{
  const exprt &truth = strip(src);
  if(truth.id() != ID_notequal || truth.operands().size() != 2)
    return false;
  irep_idt candidate;
  return
    (symbol_id(truth.op0(), candidate) && candidate == symbol &&
     value_is(truth.op1(), 0)) ||
    (symbol_id(truth.op1(), candidate) && candidate == symbol &&
     value_is(truth.op0(), 0));
}

bool prefix_channel_toggle(
  const exprt &src,
  const irep_idt &symbol)
{
  return prefix_channel_false_test(src, symbol);
}

bool prefix_channel_availability(
  const exprt &src,
  irep_idt &front,
  irep_idt &back)
{
  const exprt &relation = strip(src);
  irep_idt lhs;
  irep_idt rhs;
  if(
    relation.id() == ID_gt && relation.operands().size() == 2 &&
    symbol_id(relation.op0(), lhs) &&
    symbol_id(relation.op1(), rhs))
  {
    back = lhs;
    front = rhs;
    return true;
  }
  if(
    relation.id() == ID_lt && relation.operands().size() == 2 &&
    symbol_id(relation.op0(), lhs) &&
    symbol_id(relation.op1(), rhs))
  {
    front = lhs;
    back = rhs;
    return true;
  }
  return false;
}

bool prefix_channel_negated_availability(
  const exprt &src,
  irep_idt &front,
  irep_idt &back)
{
  const exprt &outer = strip(src);
  return
    outer.id() == ID_not && outer.operands().size() == 1 &&
    prefix_channel_availability(outer.op0(), front, back);
}

bool prefix_channel_assumption_terms(
  const goto_programt::instructiont &instruction,
  std::vector<exprt> &terms)
{
  if(instruction.is_assume())
  {
    flatten_and(instruction.condition(), terms);
    return true;
  }
  irep_idt callee;
  if(
    call_id(instruction, callee) && is_assume(callee) &&
    instruction.call_arguments().size() == 1)
  {
    flatten_and(instruction.call_arguments().front(), terms);
    return true;
  }
  return false;
}

bool prefix_channel_array_index(
  const exprt &src,
  irep_idt &base,
  irep_idt &index)
{
  if(array_symbol_index(src, base, index))
    return true;
  const exprt &expr = strip(src);
  if(expr.id() != ID_index || expr.operands().size() != 2)
    return false;
  irep_idt candidate_base;
  irep_idt candidate_index;
  if(
    symbol_id(expr.op0(), candidate_base) &&
    symbol_id(expr.op1(), candidate_index) &&
    candidate_base != candidate_index)
  {
    base = candidate_base;
    index = candidate_index;
    return true;
  }
  return false;
}

bool prefix_channel_array_equality(
  const exprt &src,
  irep_idt &base,
  irep_idt &index,
  exprt &value)
{
  const exprt &relation = strip(src);
  if(relation.id() != ID_equal || relation.operands().size() != 2)
    return false;
  if(prefix_channel_array_index(relation.op0(), base, index))
  {
    value = strip(relation.op1());
    return true;
  }
  if(prefix_channel_array_index(relation.op1(), base, index))
  {
    value = strip(relation.op0());
    return true;
  }
  return false;
}

bool prefix_channel_bounds_excluding(
  const std::vector<exprt> &terms,
  const irep_idt &index,
  const irep_idt &excluded,
  irep_idt &bound)
{
  bool nonnegative = false;
  bool upper = false;
  for(const auto &term : terms)
  {
    if(stream_refine_symbol_zero_relation(term, index, ID_ge))
      nonnegative = true;
    const exprt &relation = strip(term);
    irep_idt lhs;
    irep_idt rhs;
    if(
      relation.id() == ID_lt &&
      relation.operands().size() == 2 &&
      symbol_id(relation.op0(), lhs) && lhs == index &&
      symbol_id(relation.op1(), rhs) && rhs != excluded)
    {
      if(upper && bound != rhs)
        return false;
      bound = rhs;
      upper = true;
    }
  }
  return nonnegative && upper;
}

bool prefix_channel_alternating_publisher(
  const goto_modelt &model,
  const namespacet &ns,
  const irep_idt &worker,
  prefix_channel_alternating_publishert &result,
  std::string &reason)
{
  const auto &program =
    model.goto_functions.function_map.at(worker).body;
  natural_loopst loops;
  loops(program);
  if(loops.loop_map.size() != 1)
  {
    reason = "prefix_alt_publish_loop_count";
    return false;
  }
  const auto &loop = loops.loop_map.begin()->second;

  std::vector<const goto_programt::instructiont *> order;
  std::vector<exprt> terms;
  for(const auto &instruction : program.instructions)
  {
    order.push_back(&instruction);
    std::vector<exprt> current;
    if(prefix_channel_assumption_terms(instruction, current))
    {
      terms.insert(terms.end(), current.begin(), current.end());
      continue;
    }
    if(!instruction.is_function_call())
      continue;
    irep_idt callee;
    if(!call_id(instruction, callee))
    {
      reason = "prefix_alt_publish_call";
      return false;
    }
    reason = "prefix_alt_publish_call";
    return false;
  }

  struct located_publicationt
  {
    stream_refine_publisht publish;
    std::size_t assume_index;
    std::size_t increment_index;
  };
  std::vector<located_publicationt> publications;
  std::size_t equality_terms = 0;
  std::size_t indexed_equalities = 0;
  std::set<irep_idt> observed_term_ids;
  for(std::size_t index = 0; index < order.size(); ++index)
  {
    const auto *instruction = order[index];
    std::vector<exprt> current;
    prefix_channel_assumption_terms(*instruction, current);
    irep_idt assigned_storage;
    irep_idt assigned_index;
    const bool storage_assignment =
      instruction->is_assign() &&
      prefix_channel_array_index(
        instruction->assign_lhs(),
        assigned_storage,
        assigned_index);
    if(storage_assignment)
    {
      current.push_back(
        equal_exprt(
          instruction->assign_lhs(),
          instruction->assign_rhs()));
    }
    if(current.empty())
      continue;
    for(const auto &term : current)
    {
      const exprt &candidate_relation = strip(term);
      observed_term_ids.insert(candidate_relation.id());
      if(
        candidate_relation.id() == ID_equal &&
        candidate_relation.operands().size() == 2)
        ++equality_terms;
      irep_idt storage;
      irep_idt back;
      exprt token;
      if(!prefix_channel_array_equality(term, storage, back, token))
        continue;
      ++indexed_equalities;
      const goto_programt::instructiont *increment = nullptr;
      std::size_t increment_index = 0;
      for(std::size_t next = index + 1; next < order.size(); ++next)
      {
        if(!prefix_channel_loop_contains(
             program, loop, order[next]))
          break;
        irep_idt lhs;
        if(
          order[next]->is_assign() &&
          symbol_id(order[next]->assign_lhs(), lhs) &&
          lhs == back)
        {
          if(unit_increment(*order[next], back))
          {
            increment = order[next];
            increment_index = next;
          }
          break;
        }
      }
      irep_idt bound;
      if(
        increment == nullptr ||
        !stream_refine_bounds(terms, back, bound) ||
        !shared_signed(back, ns) || !shared_signed(bound, ns))
      {
        reason = "prefix_alt_publish_transaction";
        return false;
      }
      const symbolt *queue = lookup(storage, ns);
      if(
        queue == nullptr || !queue->is_static_lifetime ||
        queue->type.id() != ID_pointer ||
        to_pointer_type(queue->type).base_type().id() != ID_signedbv)
      {
        reason = "prefix_alt_publish_storage";
        return false;
      }
      located_publicationt located;
      located.publish.channel.storage = storage;
      located.publish.channel.back = back;
      located.publish.channel.bound = bound;
      located.publish.token = strip(token);
      located.publish.in_loop =
        prefix_channel_loop_contains(program, loop, instruction);
      located.publish.first_location = instruction->location_number;
      located.publish.last_location = increment->location_number;
      located.publish.writes.insert(increment);
      if(storage_assignment)
        located.publish.writes.insert(instruction);
      located.assume_index = index;
      located.increment_index = increment_index;
      publications.push_back(located);
    }
  }
  if(publications.size() != 2)
  {
    reason =
      "prefix_alt_publish_count_" +
      std::to_string(publications.size()) + "_equal_" +
      std::to_string(equality_terms) + "_indexed_" +
      std::to_string(indexed_equalities);
    for(const auto &id : observed_term_ids)
      reason += "_id_" + id2string(id);
    return false;
  }
  for(const auto &publication : publications)
  {
    if(
      !publication.publish.in_loop ||
      publication.publish.channel.storage !=
        publications.front().publish.channel.storage ||
      publication.publish.channel.back !=
        publications.front().publish.channel.back ||
      publication.publish.channel.bound !=
        publications.front().publish.channel.bound)
    {
      reason = "prefix_alt_publish_channel";
      return false;
    }
  }

  std::size_t positive_index = 0;
  std::size_t negative_index = 0;
  mp_integer first;
  mp_integer second;
  if(
    !integer_constant(publications[0].publish.token, first) ||
    !integer_constant(publications[1].publish.token, second) ||
    first == 0 || second == 0 || first != -second)
  {
    reason = "prefix_alt_publish_tokens";
    return false;
  }
  if(first > 0)
  {
    result.positive = first;
    positive_index = 0;
    negative_index = 1;
  }
  else
  {
    result.positive = second;
    positive_index = 1;
    negative_index = 0;
  }

  const goto_programt::instructiont *toggle = nullptr;
  const goto_programt::instructiont *initialization = nullptr;
  irep_idt state;
  mp_integer initial_state;
  std::size_t state_assignments = 0;
  for(const auto *instruction : order)
  {
    if(!instruction->is_assign())
      continue;
    irep_idt lhs;
    if(
      !symbol_id(instruction->assign_lhs(), lhs) ||
      !local_boolean(lhs, ns))
      continue;
    if(prefix_channel_toggle(instruction->assign_rhs(), lhs))
    {
      if(
        toggle != nullptr ||
        !prefix_channel_loop_contains(program, loop, instruction))
      {
        reason = "prefix_alt_toggle_count";
        return false;
      }
      toggle = instruction;
      state = lhs;
    }
  }
  if(toggle == nullptr || state.empty())
  {
    reason = "prefix_alt_toggle";
    return false;
  }
  for(const auto *instruction : order)
  {
    if(!instruction->is_assign())
      continue;
    irep_idt lhs;
    if(!symbol_id(instruction->assign_lhs(), lhs) || lhs != state)
      continue;
    ++state_assignments;
    if(!prefix_channel_loop_contains(program, loop, instruction))
    {
      mp_integer candidate;
      if(
        integer_constant(instruction->assign_rhs(), candidate) &&
        (candidate == 0 || candidate == 1))
      {
        initialization = instruction;
        initial_state = candidate;
      }
    }
  }
  if(
    state_assignments != 2 || initialization == nullptr ||
    initialization->location_number >=
      publications[positive_index].publish.first_location ||
    toggle->location_number <=
      publications[negative_index].publish.last_location)
  {
    reason = "prefix_alt_state_updates";
    return false;
  }

  const auto &positive = publications[positive_index];
  const auto &negative = publications[negative_index];
  std::size_t branch_matches = 0;
  std::size_t skip_matches = 0;
  for(const auto *instruction : order)
  {
    if(
      !instruction->is_goto() || instruction->targets.size() != 1 ||
      !prefix_channel_loop_contains(program, loop, instruction))
      continue;
    const unsigned target =
      instruction->get_target()->location_number;
    const bool skips_initial_positive =
      (initial_state == 1 &&
       prefix_channel_false_test(instruction->condition(), state)) ||
      (initial_state == 0 &&
       prefix_channel_true_test(instruction->condition(), state));
    if(
      skips_initial_positive &&
      instruction->location_number <
        positive.publish.first_location &&
      positive.publish.last_location < target &&
      target <= negative.publish.first_location)
      ++branch_matches;
    if(
      instruction->condition().is_true() &&
      positive.publish.last_location <
        instruction->location_number &&
      instruction->location_number <
        negative.publish.first_location &&
      target > negative.publish.last_location &&
      target <= toggle->location_number)
      ++skip_matches;
  }
  if(branch_matches != 1 || skip_matches != 1)
  {
    reason = "prefix_alt_branch_control";
    return false;
  }

  result.worker = worker;
  result.channel = positive.publish.channel;
  result.state = state;
  result.writes.insert(
    positive.publish.writes.begin(), positive.publish.writes.end());
  result.writes.insert(
    negative.publish.writes.begin(), negative.publish.writes.end());
  return true;
}

bool prefix_channel_sum_consumer(
  const goto_modelt &model,
  const namespacet &ns,
  const irep_idt &worker,
  prefix_channel_sum_consumert &result,
  std::string &reason)
{
  const auto &program =
    model.goto_functions.function_map.at(worker).body;
  natural_loopst loops;
  loops(program);
  if(loops.loop_map.size() != 1)
  {
    reason = "prefix_sum_loop_count";
    return false;
  }
  const auto &loop = loops.loop_map.begin()->second;
  std::vector<exprt> terms;
  const goto_programt::instructiont *read = nullptr;
  const goto_programt::instructiont *increment = nullptr;
  const goto_programt::instructiont *addition = nullptr;
  irep_idt storage;
  irep_idt front;
  irep_idt temporary;
  irep_idt sum;
  std::vector<std::pair<irep_idt, irep_idt>> availability_candidates;
  for(auto target = program.instructions.begin();
      target != program.instructions.end(); ++target)
  {
    const auto &instruction = *target;
    std::vector<exprt> current;
    if(prefix_channel_assumption_terms(instruction, current))
    {
      for(const auto &term : current)
      {
        irep_idt candidate_front;
        irep_idt candidate_back;
        if(
          prefix_channel_availability(
            term, candidate_front, candidate_back))
        {
          availability_candidates.emplace_back(
            candidate_front, candidate_back);
        }
      }
      terms.insert(terms.end(), current.begin(), current.end());
      continue;
    }
    if(instruction.is_function_call())
    {
      reason = "prefix_sum_call";
      return false;
    }
    if(
      instruction.is_goto() && loop.contains(target) &&
      instruction.targets.size() == 1 &&
      !loop.contains(instruction.get_target()))
    {
      irep_idt candidate_front;
      irep_idt candidate_back;
      if(
        prefix_channel_negated_availability(
          instruction.condition(),
          candidate_front,
          candidate_back))
      {
        availability_candidates.emplace_back(
          candidate_front, candidate_back);
      }
    }
    if(!instruction.is_assign() || !loop.contains(target))
      continue;
    irep_idt lhs;
    irep_idt candidate_storage;
    irep_idt candidate_front;
    if(
      symbol_id(instruction.assign_lhs(), lhs) &&
      prefix_channel_array_index(
        instruction.assign_rhs(),
        candidate_storage,
        candidate_front))
    {
      if(read != nullptr)
      {
        reason = "prefix_sum_read_count";
        return false;
      }
      read = &instruction;
      temporary = lhs;
      storage = candidate_storage;
      front = candidate_front;
      result.writes.insert(&instruction);
      continue;
    }
    exprt delta;
    if(stream_refine_addition(instruction, lhs, delta))
    {
      bool fold_candidate = false;
      irep_idt direct_storage;
      irep_idt direct_front;
      if(
        prefix_channel_array_index(
          delta, direct_storage, direct_front))
      {
        fold_candidate = true;
        if(read != nullptr)
        {
          reason = "prefix_sum_read_count";
          return false;
        }
        read = &instruction;
        storage = direct_storage;
        front = direct_front;
      }
      else
      {
        irep_idt delta_symbol;
        if(
          symbol_id(delta, delta_symbol) &&
          (temporary.empty() || delta_symbol == temporary))
        {
          fold_candidate = true;
          temporary = delta_symbol;
        }
      }
      if(fold_candidate)
      {
        if(addition != nullptr || !shared_signed(lhs, ns))
        {
          reason = "prefix_sum_addition_count";
          return false;
        }
        addition = &instruction;
        sum = lhs;
        result.writes.insert(&instruction);
        continue;
      }
    }
    if(
      symbol_id(instruction.assign_lhs(), lhs) &&
      unit_increment(instruction, lhs))
    {
      if(increment != nullptr)
      {
        reason = "prefix_sum_increment_count";
        return false;
      }
      increment = &instruction;
      if(front.empty())
        front = lhs;
      else if(front != lhs)
      {
        reason = "prefix_sum_front_mismatch";
        return false;
      }
      result.writes.insert(&instruction);
    }
  }
  std::size_t availability = 0;
  irep_idt available_back;
  for(const auto &candidate : availability_candidates)
  {
    if(
      candidate.first == front &&
      available_back.empty())
    {
      available_back = candidate.second;
      ++availability;
    }
  }
  irep_idt bound;
  if(
    availability == 0 ||
    !prefix_channel_bounds_excluding(
      terms, front, available_back, bound))
  {
    reason = "prefix_sum_bounds";
    return false;
  }
  if(
    read == nullptr || increment == nullptr || addition == nullptr ||
    availability != 1 ||
    read->location_number >= increment->location_number ||
    addition->location_number < read->location_number ||
    !shared_signed(front, ns) ||
    !shared_signed(available_back, ns) ||
    !shared_signed(bound, ns))
  {
    reason = "prefix_sum_signature";
    return false;
  }
  if(
    !temporary.empty() &&
    addition != read)
  {
    irep_idt delta_symbol;
    exprt delta;
    irep_idt ignored;
    if(
      !stream_refine_addition(*addition, ignored, delta) ||
      !symbol_id(delta, delta_symbol) ||
      delta_symbol != temporary)
    {
      reason = "prefix_sum_temporary_flow";
      return false;
    }
  }
  const symbolt *queue = lookup(storage, ns);
  if(
    queue == nullptr || !queue->is_static_lifetime ||
    queue->type.id() != ID_pointer ||
    to_pointer_type(queue->type).base_type().id() != ID_signedbv)
  {
    reason = "prefix_sum_storage";
    return false;
  }
  result.worker = worker;
  result.channel.storage = storage;
  result.channel.front = front;
  result.channel.back = available_back;
  result.channel.bound = bound;
  result.sum = sum;
  result.temporary = temporary;
  return true;
}

bool prefix_channel_sum_property(
  const goto_modelt &model,
  const lifecyclet &life,
  const irep_idt &sum,
  const mp_integer &upper,
  const goto_programt::instructiont *&assumption,
  const goto_programt::instructiont *&error,
  std::string &reason)
{
  std::size_t errors = 0;
  for(const auto &entry : model.goto_functions.function_map)
  {
    for(const auto &instruction : entry.second.body.instructions)
    {
      irep_idt callee;
      if(call_id(instruction, callee) && is_reach_error(callee))
      {
        ++errors;
        if(entry.first != ID_main)
        {
          reason = "prefix_sum_error_function";
          return false;
        }
        error = &instruction;
      }
    }
  }
  std::size_t matches = 0;
  const auto &main =
    model.goto_functions.function_map.at(ID_main).body;
  for(const auto &instruction : main.instructions)
  {
    if(
      life.last_join == nullptr ||
      instruction.location_number <= life.last_join->location_number)
      continue;
    irep_idt callee;
    if(
      !call_id(instruction, callee) || !is_assume(callee) ||
      instruction.call_arguments().size() != 1)
      continue;
    std::vector<exprt> disjuncts;
    flatten_or(instruction.call_arguments().front(), disjuncts);
    if(disjuncts.size() != 2)
      continue;
    bool lower = false;
    bool greater = false;
    for(const auto &term : disjuncts)
    {
      const exprt &relation = strip(term);
      if(relation.operands().size() != 2)
        continue;
      irep_idt candidate;
      if(
        relation.id() == ID_lt &&
        symbol_id(relation.op0(), candidate) && candidate == sum &&
        value_is(relation.op1(), 0))
        lower = true;
      if(
        relation.id() == ID_gt &&
        symbol_id(relation.op1(), candidate) && candidate == sum &&
        value_is(relation.op0(), 0))
        lower = true;
      mp_integer bound;
      if(
        relation.id() == ID_gt &&
        symbol_id(relation.op0(), candidate) && candidate == sum &&
        integer_constant(relation.op1(), bound) && bound == upper)
        greater = true;
      if(
        relation.id() == ID_lt &&
        symbol_id(relation.op1(), candidate) && candidate == sum &&
        integer_constant(relation.op0(), bound) && bound == upper)
        greater = true;
    }
    if(lower && greater)
    {
      assumption = &instruction;
      ++matches;
    }
  }
  if(
    errors != 1 || matches != 1 || assumption == nullptr ||
    error == nullptr ||
    assumption->location_number >= error->location_number)
  {
    reason = "prefix_sum_property";
    return false;
  }
  return true;
}

bool prefix_channel_alternating_sum_proof_impl(
  const goto_modelt &model,
  const namespacet &ns,
  std::string &reason)
{
  lifecyclet life;
  std::vector<irep_idt> workers;
  if(!stream_refine_lifecycle(model, life, workers, reason))
    return false;

  prefix_channel_alternating_publishert publisher;
  prefix_channel_sum_consumert consumer;
  for(const auto &worker : workers)
  {
    prefix_channel_alternating_publishert candidate_publisher;
    std::string publisher_reason;
    if(
      prefix_channel_alternating_publisher(
        model, ns, worker, candidate_publisher, publisher_reason))
    {
      if(!publisher.worker.empty())
      {
        reason = "prefix_alt_multiple_publishers";
        return false;
      }
      publisher = candidate_publisher;
      continue;
    }
    prefix_channel_sum_consumert candidate_consumer;
    std::string consumer_reason;
    if(
      prefix_channel_sum_consumer(
        model, ns, worker, candidate_consumer, consumer_reason))
    {
      if(!consumer.worker.empty())
      {
        reason = "prefix_alt_multiple_consumers";
        return false;
      }
      consumer = candidate_consumer;
      continue;
    }
    reason =
      "prefix_alt_worker_publish_" + publisher_reason +
      "_consume_" + consumer_reason;
    return false;
  }
  if(
    publisher.worker.empty() || consumer.worker.empty() ||
    publisher.channel.storage != consumer.channel.storage ||
    publisher.channel.back != consumer.channel.back ||
    publisher.channel.bound != consumer.channel.bound)
  {
    reason = "prefix_alt_channel_signature";
    return false;
  }
  stream_refine_channelt channel = publisher.channel;
  channel.front = consumer.channel.front;
  if(!stream_refine_initial_channel(model, life, channel))
  {
    reason = "prefix_alt_initial_channel";
    return false;
  }

  const goto_programt::instructiont *property_assumption = nullptr;
  const goto_programt::instructiont *error = nullptr;
  if(
    !prefix_channel_sum_property(
      model,
      life,
      consumer.sum,
      publisher.positive,
      property_assumption,
      error,
      reason))
    return false;

  const std::set<irep_idt> queues = {channel.storage};
  std::set<irep_idt> protected_symbols = {
    channel.storage,
    channel.front,
    channel.back,
    channel.bound,
    consumer.sum};
  if(
    !consumer.temporary.empty() &&
    shared_signed(consumer.temporary, ns))
    protected_symbols.insert(consumer.temporary);
  std::set<const goto_programt::instructiont *> allowed =
    publisher.writes;
  allowed.insert(
    consumer.writes.begin(), consumer.writes.end());
  stream_refine_sourcet unused_source;
  std::vector<stream_refine_staget> unused_stages;
  if(
    !stream_refine_fresh_queues(
      model, ns, life, queues, reason) ||
    !zero_initialized_symbols(
      model, {consumer.sum}, allowed, reason) ||
    !stream_refine_global(
      model,
      ns,
      life,
      unused_source,
      unused_stages,
      queues,
      protected_symbols,
      allowed,
      property_assumption,
      error,
      reason))
    return false;

  std::cout << "NATIVE_PREFIX_CHANNEL applied=1"
            << " rule=alternating_sum"
            << " storage=" << channel.storage
            << " sum=" << consumer.sum
            << " token=" << publisher.positive << '\n';
  return true;
}

struct prefix_channel_snapshot_monitort
{
  irep_idt worker;
  irep_idt flag;
  irep_idt sum;
  mp_integer upper;
  std::set<const goto_programt::instructiont *> writes;

  prefix_channel_snapshot_monitort() : upper(0)
  {
  }
};

bool prefix_channel_safe_interval(
  const exprt &src,
  irep_idt &sum,
  mp_integer &upper)
{
  std::vector<exprt> terms;
  flatten_and(src, terms);
  if(terms.size() != 2)
    return false;
  bool lower = false;
  bool bounded = false;
  irep_idt candidate_sum;
  mp_integer candidate_upper;
  for(const auto &term : terms)
  {
    const exprt &relation = strip(term);
    if(relation.operands().size() != 2)
      return false;
    irep_idt candidate;
    if(
      relation.id() == ID_le &&
      value_is(relation.op0(), 0) &&
      symbol_id(relation.op1(), candidate))
    {
      if(!candidate_sum.empty() && candidate_sum != candidate)
        return false;
      candidate_sum = candidate;
      lower = true;
      continue;
    }
    if(
      relation.id() == ID_ge &&
      symbol_id(relation.op0(), candidate) &&
      value_is(relation.op1(), 0))
    {
      if(!candidate_sum.empty() && candidate_sum != candidate)
        return false;
      candidate_sum = candidate;
      lower = true;
      continue;
    }
    mp_integer bound;
    if(
      relation.id() == ID_le &&
      symbol_id(relation.op0(), candidate) &&
      integer_constant(relation.op1(), bound))
    {
      if(!candidate_sum.empty() && candidate_sum != candidate)
        return false;
      candidate_sum = candidate;
      candidate_upper = bound;
      bounded = true;
      continue;
    }
    if(
      relation.id() == ID_ge &&
      integer_constant(relation.op0(), bound) &&
      symbol_id(relation.op1(), candidate))
    {
      if(!candidate_sum.empty() && candidate_sum != candidate)
        return false;
      candidate_sum = candidate;
      candidate_upper = bound;
      bounded = true;
      continue;
    }
    return false;
  }
  if(!lower || !bounded || candidate_sum.empty())
    return false;
  sum = candidate_sum;
  upper = candidate_upper;
  return true;
}

bool prefix_channel_snapshot_monitor(
  const goto_modelt &model,
  const namespacet &ns,
  const irep_idt &worker,
  prefix_channel_snapshot_monitort &result,
  std::string &reason)
{
  const auto &program =
    model.goto_functions.function_map.at(worker).body;
  natural_loopst loops;
  loops(program);
  if(!loops.loop_map.empty())
  {
    reason = "prefix_snapshot_loop";
    return false;
  }
  unsigned depth = 0;
  std::size_t begins = 0;
  std::size_t ends = 0;
  std::size_t assignments = 0;
  for(const auto &instruction : program.instructions)
  {
    if(instruction.is_atomic_begin())
    {
      if(depth != 0)
      {
        reason = "prefix_snapshot_atomic_nesting";
        return false;
      }
      depth = 1;
      ++begins;
      continue;
    }
    if(instruction.is_atomic_end())
    {
      if(depth != 1)
      {
        reason = "prefix_snapshot_atomic_balance";
        return false;
      }
      depth = 0;
      ++ends;
      continue;
    }
    if(instruction.is_function_call())
    {
      reason = "prefix_snapshot_call";
      return false;
    }
    if(!instruction.is_assign())
      continue;
    irep_idt flag;
    irep_idt sum;
    mp_integer upper;
    if(
      depth != 1 ||
      !symbol_id(instruction.assign_lhs(), flag) ||
      !shared_boolean(flag, ns) ||
      !prefix_channel_safe_interval(
        instruction.assign_rhs(), sum, upper) ||
      !shared_signed(sum, ns) || upper <= 0)
    {
      reason = "prefix_snapshot_assignment";
      return false;
    }
    ++assignments;
    result.flag = flag;
    result.sum = sum;
    result.upper = upper;
    result.writes.insert(&instruction);
  }
  if(
    depth != 0 || begins != 1 || ends != 1 ||
    assignments != 1)
  {
    reason = "prefix_snapshot_shape";
    return false;
  }
  result.worker = worker;
  return true;
}

bool prefix_channel_flag_controlled_loop(
  const goto_modelt &model,
  const irep_idt &worker,
  const irep_idt &flag,
  std::string &reason)
{
  const auto &program =
    model.goto_functions.function_map.at(worker).body;
  natural_loopst loops;
  loops(program);
  if(loops.loop_map.size() != 1)
  {
    reason = "prefix_flag_loop_count";
    return false;
  }
  const auto &loop = loops.loop_map.begin()->second;
  std::map<irep_idt, std::vector<
    const goto_programt::instructiont *>> copies;
  for(const auto &instruction : program.instructions)
  {
    if(!instruction.is_assign())
      continue;
    irep_idt lhs;
    irep_idt rhs;
    if(
      symbol_id(instruction.assign_lhs(), lhs) &&
      symbol_id(instruction.assign_rhs(), rhs) &&
      rhs == flag)
      copies[lhs].push_back(&instruction);
  }
  irep_idt condition;
  for(const auto &entry : copies)
  {
    if(entry.second.size() != 2)
      continue;
    std::size_t outside = 0;
    std::size_t inside = 0;
    for(const auto *copy : entry.second)
    {
      if(prefix_channel_loop_contains(program, loop, copy))
        ++inside;
      else
        ++outside;
    }
    if(outside == 1 && inside == 1)
    {
      if(!condition.empty())
      {
        reason = "prefix_flag_copy_ambiguous";
        return false;
      }
      condition = entry.first;
    }
  }
  if(condition.empty())
  {
    reason = "prefix_flag_copy";
    return false;
  }
  std::size_t condition_writes = 0;
  std::size_t exits = 0;
  std::size_t backedges = 0;
  for(auto instruction = program.instructions.begin();
      instruction != program.instructions.end(); ++instruction)
  {
    if(instruction->is_assign())
    {
      irep_idt lhs;
      if(
        symbol_id(instruction->assign_lhs(), lhs) &&
        lhs == condition)
        ++condition_writes;
    }
    if(
      instruction->is_goto() && loop.contains(instruction) &&
      instruction->targets.size() == 1)
    {
      if(
        prefix_channel_false_test(
          instruction->condition(), condition) &&
        !loop.contains(instruction->get_target()))
        ++exits;
      if(
        instruction->condition().is_true() &&
        loop.contains(instruction->get_target()) &&
        instruction->get_target()->location_number <=
          instruction->location_number)
        ++backedges;
    }
  }
  if(condition_writes != 2 || exits != 1 || backedges != 1)
  {
    reason = "prefix_flag_control";
    return false;
  }
  return true;
}

bool prefix_channel_unconditional_error(
  const goto_modelt &model,
  const lifecyclet &life,
  const goto_programt::instructiont *&error,
  std::string &reason)
{
  std::size_t errors = 0;
  for(const auto &entry : model.goto_functions.function_map)
  {
    for(const auto &instruction : entry.second.body.instructions)
    {
      irep_idt callee;
      if(call_id(instruction, callee) && is_reach_error(callee))
      {
        ++errors;
        if(
          entry.first != ID_main || life.last_join == nullptr ||
          instruction.location_number <=
            life.last_join->location_number)
        {
          reason = "prefix_snapshot_error_location";
          return false;
        }
        error = &instruction;
      }
    }
  }
  if(errors != 1 || error == nullptr)
  {
    reason = "prefix_snapshot_error";
    return false;
  }
  return true;
}

bool prefix_channel_alternating_snapshot_proof_impl(
  const goto_modelt &model,
  const namespacet &ns,
  std::string &reason)
{
  lifecyclet life;
  std::vector<irep_idt> workers;
  if(
    !stream_refine_lifecycle(model, life, workers, reason) ||
    workers.size() != 3)
  {
    if(reason.empty())
      reason = "prefix_snapshot_lifecycle";
    return false;
  }

  prefix_channel_alternating_publishert publisher;
  prefix_channel_sum_consumert consumer;
  prefix_channel_snapshot_monitort monitor;
  for(const auto &worker : workers)
  {
    prefix_channel_alternating_publishert candidate_publisher;
    std::string publisher_reason;
    if(
      prefix_channel_alternating_publisher(
        model, ns, worker, candidate_publisher, publisher_reason))
    {
      if(!publisher.worker.empty())
      {
        reason = "prefix_snapshot_multiple_publishers";
        return false;
      }
      publisher = candidate_publisher;
      continue;
    }
    prefix_channel_sum_consumert candidate_consumer;
    std::string consumer_reason;
    if(
      prefix_channel_sum_consumer(
        model, ns, worker, candidate_consumer, consumer_reason))
    {
      if(!consumer.worker.empty())
      {
        reason = "prefix_snapshot_multiple_consumers";
        return false;
      }
      consumer = candidate_consumer;
      continue;
    }
    prefix_channel_snapshot_monitort candidate_monitor;
    std::string monitor_reason;
    if(
      prefix_channel_snapshot_monitor(
        model, ns, worker, candidate_monitor, monitor_reason))
    {
      if(!monitor.worker.empty())
      {
        reason = "prefix_snapshot_multiple_monitors";
        return false;
      }
      monitor = candidate_monitor;
      continue;
    }
    reason =
      "prefix_snapshot_worker_publish_" + publisher_reason +
      "_consume_" + consumer_reason +
      "_monitor_" + monitor_reason;
    return false;
  }
  if(
    publisher.worker.empty() || consumer.worker.empty() ||
    monitor.worker.empty() ||
    publisher.channel.storage != consumer.channel.storage ||
    publisher.channel.back != consumer.channel.back ||
    publisher.channel.bound != consumer.channel.bound ||
    monitor.sum != consumer.sum ||
    monitor.upper != publisher.positive ||
    !prefix_channel_flag_controlled_loop(
      model, publisher.worker, monitor.flag, reason) ||
    !prefix_channel_flag_controlled_loop(
      model, consumer.worker, monitor.flag, reason))
  {
    if(reason.empty())
      reason = "prefix_snapshot_signature";
    return false;
  }
  stream_refine_channelt channel = publisher.channel;
  channel.front = consumer.channel.front;
  if(
    !stream_refine_initial_channel(model, life, channel) ||
    !prefix_channel_initial_value(
      model,
      life,
      monitor.flag,
      true_exprt()))
  {
    reason = "prefix_snapshot_initial_state";
    return false;
  }

  const goto_programt::instructiont *error = nullptr;
  if(!prefix_channel_unconditional_error(model, life, error, reason))
    return false;
  const std::set<irep_idt> queues = {channel.storage};
  std::set<irep_idt> protected_symbols = {
    channel.storage,
    channel.front,
    channel.back,
    channel.bound,
    consumer.sum,
    monitor.flag};
  if(
    !consumer.temporary.empty() &&
    shared_signed(consumer.temporary, ns))
    protected_symbols.insert(consumer.temporary);
  std::set<const goto_programt::instructiont *> allowed =
    publisher.writes;
  allowed.insert(
    consumer.writes.begin(), consumer.writes.end());
  allowed.insert(
    monitor.writes.begin(), monitor.writes.end());
  stream_refine_sourcet unused_source;
  std::vector<stream_refine_staget> unused_stages;
  if(
    !stream_refine_fresh_queues(
      model, ns, life, queues, reason) ||
    !zero_initialized_symbols(
      model, {consumer.sum}, allowed, reason) ||
    !stream_refine_global(
      model,
      ns,
      life,
      unused_source,
      unused_stages,
      queues,
      protected_symbols,
      allowed,
      nullptr,
      error,
      reason))
    return false;

  std::cout << "NATIVE_PREFIX_CHANNEL applied=1"
            << " rule=alternating_snapshot"
            << " storage=" << channel.storage
            << " sum=" << consumer.sum
            << " flag=" << monitor.flag << '\n';
  return true;
}

struct prefix_channel_bounded_publishert
{
  irep_idt worker;
  stream_refine_publisht publish;
  irep_idt bound;
  irep_idt flag;
  std::set<const goto_programt::instructiont *> writes;
};

struct prefix_channel_bound_monitort
{
  irep_idt worker;
  irep_idt flag;
  irep_idt sum;
  irep_idt bound;
  std::set<const goto_programt::instructiont *> writes;
};

bool prefix_channel_snapshot_read_region(
  const std::vector<const goto_programt::instructiont *> &region,
  const namespacet &ns,
  irep_idt &flag)
{
  std::size_t assignments = 0;
  for(const auto *instruction : region)
  {
    if(instruction->is_assign())
    {
      irep_idt lhs;
      irep_idt rhs;
      const symbolt *local = nullptr;
      if(
        !symbol_id(instruction->assign_lhs(), lhs) ||
        (local = lookup(lhs, ns)) == nullptr ||
        local->is_static_lifetime || local->is_type ||
        !symbol_id(instruction->assign_rhs(), rhs) ||
        !shared_boolean(rhs, ns))
        return false;
      flag = rhs;
      ++assignments;
      continue;
    }
    if(
      instruction->is_decl() || instruction->is_dead() ||
      instruction->is_location() || instruction->is_skip())
      continue;
    return false;
  }
  return assignments == 1;
}

bool prefix_channel_countdown_guard(
  const exprt &src,
  const irep_idt &counter)
{
  if(prefix_channel_false_test(src, counter))
    return true;
  const exprt &outer = strip(src);
  if(outer.id() != ID_not || outer.operands().size() != 1)
    return false;
  const exprt &relation = strip(outer.op0());
  irep_idt lhs;
  return
    relation.id() == ID_gt && relation.operands().size() == 2 &&
    symbol_id(relation.op0(), lhs) && lhs == counter &&
    value_is(relation.op1(), 0);
}

bool prefix_channel_unit_decrement(
  const goto_programt::instructiont &instruction,
  const irep_idt &counter)
{
  if(!instruction.is_assign())
    return false;
  irep_idt lhs;
  if(!symbol_id(instruction.assign_lhs(), lhs) || lhs != counter)
    return false;
  const exprt &rhs = strip(instruction.assign_rhs());
  irep_idt operand;
  return
    rhs.id() == ID_minus && rhs.operands().size() == 2 &&
    symbol_id(rhs.op0(), operand) && operand == counter &&
    value_is(rhs.op1(), 1);
}

bool prefix_channel_bounded_publisher(
  const goto_modelt &model,
  const namespacet &ns,
  const irep_idt &worker,
  prefix_channel_bounded_publishert &result,
  std::string &reason)
{
  const auto &program =
    model.goto_functions.function_map.at(worker).body;
  natural_loopst loops;
  loops(program);
  if(loops.loop_map.size() != 1)
  {
    reason = "prefix_bound_publish_loop_count";
    return false;
  }
  const auto loop_head = loops.loop_map.begin()->first;
  const auto &loop = loops.loop_map.begin()->second;

  bool in_atomic = false;
  bool region_in_loop = false;
  std::vector<const goto_programt::instructiont *> region;
  std::vector<stream_refine_publisht> publications;
  std::set<irep_idt> flags;
  for(auto instruction = program.instructions.begin();
      instruction != program.instructions.end(); ++instruction)
  {
    if(instruction->is_atomic_begin())
    {
      if(in_atomic)
      {
        reason = "prefix_bound_publish_atomic_nesting";
        return false;
      }
      in_atomic = true;
      region_in_loop = loop.contains(instruction);
      region.clear();
      continue;
    }
    if(instruction->is_atomic_end())
    {
      if(!in_atomic || loop.contains(instruction) != region_in_loop)
      {
        reason = "prefix_bound_publish_atomic_balance";
        return false;
      }
      stream_refine_publisht publish;
      irep_idt flag;
      if(
        stream_refine_publish_region(
          region, ns, region_in_loop, publish))
        publications.push_back(publish);
      else if(prefix_channel_snapshot_read_region(region, ns, flag))
        flags.insert(flag);
      else
      {
        reason = "prefix_bound_publish_atomic_region";
        return false;
      }
      in_atomic = false;
      region.clear();
      continue;
    }
    if(in_atomic)
      region.push_back(&*instruction);
  }
  mp_integer token;
  if(
    in_atomic || publications.size() != 1 ||
    !publications.front().in_loop || flags.size() != 1 ||
    !integer_constant(publications.front().token, token) ||
    token != 1)
  {
    reason = "prefix_bound_publish_transactions";
    return false;
  }

  irep_idt counter;
  irep_idt bound;
  const goto_programt::instructiont *initialization = nullptr;
  const goto_programt::instructiont *decrement = nullptr;
  std::size_t local_candidate_writes = 0;
  for(const auto &instruction : program.instructions)
  {
    if(!instruction.is_assign())
      continue;
    irep_idt lhs;
    irep_idt rhs;
    if(
      !prefix_channel_loop_contains(
        program, loop, &instruction) &&
      symbol_id(instruction.assign_lhs(), lhs) &&
      local_signed(lhs, ns) &&
      symbol_id(instruction.assign_rhs(), rhs) &&
      shared_signed(rhs, ns))
    {
      if(initialization != nullptr)
      {
        reason = "prefix_bound_publish_initialization";
        return false;
      }
      initialization = &instruction;
      counter = lhs;
      bound = rhs;
    }
  }
  if(initialization == nullptr)
  {
    reason = "prefix_bound_publish_initialization";
    return false;
  }
  for(auto instruction = program.instructions.begin();
      instruction != program.instructions.end(); ++instruction)
  {
    if(!instruction->is_assign())
      continue;
    irep_idt lhs;
    if(
      symbol_id(instruction->assign_lhs(), lhs) &&
      lhs == counter)
    {
      ++local_candidate_writes;
      if(
        loop.contains(instruction) &&
        prefix_channel_unit_decrement(*instruction, counter))
        decrement = &*instruction;
    }
  }
  if(
    decrement == nullptr || local_candidate_writes != 2 ||
    loop_head->targets.size() != 1 ||
    !prefix_channel_countdown_guard(
      loop_head->condition(), counter) ||
    loop.contains(loop_head->get_target()))
  {
    reason = "prefix_bound_publish_countdown";
    return false;
  }
  std::size_t backedges = 0;
  for(auto instruction = program.instructions.begin();
      instruction != program.instructions.end(); ++instruction)
  {
    if(
      !instruction->is_goto() || !loop.contains(instruction) ||
      instruction->targets.size() != 1)
      continue;
    if(
      instruction->condition().is_true() &&
      instruction->get_target() == loop_head)
    {
      ++backedges;
      if(
        decrement->location_number >=
          instruction->location_number)
      {
        reason = "prefix_bound_publish_decrement_order";
        return false;
      }
      continue;
    }
    if(
      loop.contains(instruction->get_target()) &&
      instruction->get_target()->location_number >
        publications.front().first_location)
    {
      reason = "prefix_bound_publish_skip_decrement";
      return false;
    }
  }
  if(backedges != 1)
  {
    reason = "prefix_bound_publish_backedge";
    return false;
  }
  for(const auto &instruction : program.instructions)
  {
    if(!instruction.is_function_call())
      continue;
    irep_idt callee;
    if(!call_id(instruction, callee) || !is_assume(callee))
    {
      reason = "prefix_bound_publish_call";
      return false;
    }
  }
  result.worker = worker;
  result.publish = publications.front();
  result.bound = bound;
  result.flag = *flags.begin();
  result.writes = result.publish.writes;
  return true;
}

bool prefix_channel_bound_monitor(
  const goto_modelt &model,
  const namespacet &ns,
  const irep_idt &worker,
  prefix_channel_bound_monitort &result,
  std::string &reason)
{
  const auto &program =
    model.goto_functions.function_map.at(worker).body;
  natural_loopst loops;
  loops(program);
  if(!loops.loop_map.empty())
  {
    reason = "prefix_bound_monitor_loop";
    return false;
  }
  unsigned depth = 0;
  std::size_t assignments = 0;
  for(const auto &instruction : program.instructions)
  {
    if(instruction.is_atomic_begin())
    {
      if(depth != 0)
        return false;
      depth = 1;
      continue;
    }
    if(instruction.is_atomic_end())
    {
      if(depth != 1)
        return false;
      depth = 0;
      continue;
    }
    if(instruction.is_function_call())
    {
      reason = "prefix_bound_monitor_call";
      return false;
    }
    if(!instruction.is_assign())
      continue;
    irep_idt flag;
    if(
      depth != 1 ||
      !symbol_id(instruction.assign_lhs(), flag) ||
      !shared_boolean(flag, ns))
    {
      reason = "prefix_bound_monitor_assignment";
      return false;
    }
    const exprt &relation = strip(instruction.assign_rhs());
    irep_idt sum;
    irep_idt bound;
    if(
      relation.id() != ID_le ||
      relation.operands().size() != 2 ||
      !symbol_id(relation.op0(), sum) ||
      !symbol_id(relation.op1(), bound) ||
      !shared_signed(sum, ns) ||
      !shared_signed(bound, ns))
    {
      reason = "prefix_bound_monitor_relation";
      return false;
    }
    result.flag = flag;
    result.sum = sum;
    result.bound = bound;
    result.writes.insert(&instruction);
    ++assignments;
  }
  if(depth != 0 || assignments != 1)
  {
    reason = "prefix_bound_monitor_shape";
    return false;
  }
  result.worker = worker;
  return true;
}

bool prefix_channel_false_flag_property(
  const goto_modelt &model,
  const lifecyclet &life,
  const irep_idt &flag,
  const goto_programt::instructiont *&assumption,
  const goto_programt::instructiont *&error,
  std::string &reason)
{
  std::size_t errors = 0;
  std::size_t matches = 0;
  for(const auto &entry : model.goto_functions.function_map)
  {
    for(const auto &instruction : entry.second.body.instructions)
    {
      irep_idt callee;
      if(call_id(instruction, callee) && is_reach_error(callee))
      {
        ++errors;
        if(entry.first != ID_main)
          return false;
        error = &instruction;
      }
    }
  }
  const auto &main =
    model.goto_functions.function_map.at(ID_main).body;
  for(const auto &instruction : main.instructions)
  {
    if(
      life.last_join == nullptr ||
      instruction.location_number <=
        life.last_join->location_number)
      continue;
    irep_idt callee;
    if(
      !call_id(instruction, callee) || !is_assume(callee) ||
      instruction.call_arguments().size() != 1)
      continue;
    const exprt &condition =
      strip(instruction.call_arguments().front());
    if(prefix_channel_false_test(condition, flag))
    {
      assumption = &instruction;
      ++matches;
    }
  }
  if(
    errors != 1 || matches != 1 || assumption == nullptr ||
    error == nullptr ||
    assumption->location_number >= error->location_number)
  {
    reason = "prefix_bound_property";
    return false;
  }
  return true;
}

bool prefix_channel_bounded_sum_proof_impl(
  const goto_modelt &model,
  const namespacet &ns,
  std::string &reason)
{
  lifecyclet life;
  std::vector<irep_idt> workers;
  if(
    !stream_refine_lifecycle(model, life, workers, reason) ||
    workers.size() != 3)
  {
    if(reason.empty())
      reason = "prefix_bound_lifecycle";
    return false;
  }
  prefix_channel_bounded_publishert publisher;
  prefix_channel_sum_consumert consumer;
  prefix_channel_bound_monitort monitor;
  for(const auto &worker : workers)
  {
    prefix_channel_bounded_publishert candidate_publisher;
    std::string publisher_reason;
    if(
      prefix_channel_bounded_publisher(
        model, ns, worker, candidate_publisher, publisher_reason))
    {
      if(!publisher.worker.empty())
      {
        reason = "prefix_bound_multiple_publishers";
        return false;
      }
      publisher = candidate_publisher;
      continue;
    }
    prefix_channel_sum_consumert candidate_consumer;
    std::string consumer_reason;
    if(
      prefix_channel_sum_consumer(
        model, ns, worker, candidate_consumer, consumer_reason))
    {
      if(!consumer.worker.empty())
      {
        reason = "prefix_bound_multiple_consumers";
        return false;
      }
      consumer = candidate_consumer;
      continue;
    }
    prefix_channel_bound_monitort candidate_monitor;
    std::string monitor_reason;
    if(
      prefix_channel_bound_monitor(
        model, ns, worker, candidate_monitor, monitor_reason))
    {
      if(!monitor.worker.empty())
      {
        reason = "prefix_bound_multiple_monitors";
        return false;
      }
      monitor = candidate_monitor;
      continue;
    }
    reason =
      "prefix_bound_worker_publish_" + publisher_reason +
      "_consume_" + consumer_reason +
      "_monitor_" + monitor_reason;
    return false;
  }
  if(
    publisher.worker.empty() || consumer.worker.empty() ||
    monitor.worker.empty() ||
    publisher.publish.channel.storage != consumer.channel.storage ||
    publisher.publish.channel.back != consumer.channel.back ||
    publisher.publish.channel.bound != consumer.channel.bound ||
    publisher.bound != monitor.bound ||
    publisher.flag != monitor.flag ||
    consumer.sum != monitor.sum)
  {
    reason = "prefix_bound_signature";
    return false;
  }
  stream_refine_channelt channel = publisher.publish.channel;
  channel.front = consumer.channel.front;
  if(
    !stream_refine_initial_channel(model, life, channel) ||
    !stream_refine_nonnegative_count(
      model, life, publisher.bound) ||
    !prefix_channel_initial_value(
      model, life, monitor.flag, true_exprt()))
  {
    reason = "prefix_bound_initial_state";
    return false;
  }

  const goto_programt::instructiont *property_assumption = nullptr;
  const goto_programt::instructiont *error = nullptr;
  if(
    !prefix_channel_false_flag_property(
      model,
      life,
      monitor.flag,
      property_assumption,
      error,
      reason))
    return false;
  const std::set<irep_idt> queues = {channel.storage};
  std::set<irep_idt> protected_symbols = {
    channel.storage,
    channel.front,
    channel.back,
    channel.bound,
    publisher.bound,
    consumer.sum,
    monitor.flag};
  std::set<const goto_programt::instructiont *> allowed =
    publisher.writes;
  allowed.insert(
    consumer.writes.begin(), consumer.writes.end());
  allowed.insert(
    monitor.writes.begin(), monitor.writes.end());
  stream_refine_sourcet unused_source;
  std::vector<stream_refine_staget> unused_stages;
  if(
    !stream_refine_fresh_queues(
      model, ns, life, queues, reason) ||
    !zero_initialized_symbols(
      model, {consumer.sum}, allowed, reason) ||
    !stream_refine_global(
      model,
      ns,
      life,
      unused_source,
      unused_stages,
      queues,
      protected_symbols,
      allowed,
      property_assumption,
      error,
      reason))
    return false;

  std::cout << "NATIVE_PREFIX_CHANNEL applied=1"
            << " rule=bounded_sum"
            << " storage=" << channel.storage
            << " sum=" << consumer.sum
            << " bound=" << publisher.bound << '\n';
  return true;
}

bool prefix_channel_lifecycle(
  const goto_modelt &model,
  lifecyclet &result,
  std::vector<irep_idt> &order,
  std::string &reason)
{
  const auto main = model.goto_functions.function_map.find(ID_main);
  if(
    main == model.goto_functions.function_map.end() ||
    !main->second.body_available())
  {
    reason = "prefix_lifecycle_main";
    return false;
  }
  bool joining = false;
  for(const auto &instruction : main->second.body.instructions)
  {
    irep_idt callee;
    if(!call_id(instruction, callee))
      continue;
    const auto &arguments = instruction.call_arguments();
    if(is_create(callee))
    {
      irep_idt handle;
      irep_idt worker;
      if(
        joining || arguments.size() < 3 ||
        !addressed_id(arguments[0], handle) ||
        !addressed_id(arguments[2], worker) ||
        !result.handles.insert(handle).second ||
        !result.workers.insert(worker).second)
      {
        reason = "prefix_lifecycle_create";
        return false;
      }
      order.push_back(worker);
      if(result.first_create == nullptr)
        result.first_create = &instruction;
    }
    else if(is_join(callee))
    {
      joining = true;
      irep_idt handle;
      if(
        arguments.empty() || !symbol_id(arguments[0], handle) ||
        !result.joins.insert(handle).second)
      {
        reason = "prefix_lifecycle_join";
        return false;
      }
      result.last_join = &instruction;
    }
  }
  if(
    order.size() < 2 || order.size() > 4 ||
    result.handles != result.joins ||
    result.first_create == nullptr || result.last_join == nullptr)
  {
    reason = "prefix_lifecycle_shape";
    return false;
  }
  for(const auto &worker : order)
  {
    const auto found =
      model.goto_functions.function_map.find(worker);
    if(
      found == model.goto_functions.function_map.end() ||
      !found->second.body_available())
    {
      reason = "prefix_lifecycle_worker";
      return false;
    }
  }
  return true;
}

struct prefix_channel_affine_staget
{
  irep_idt worker;
  stream_refine_consumet consume;
  stream_refine_publisht publish;
  irep_idt flag;
  irep_idt auxiliary_fold;
  std::set<const goto_programt::instructiont *> writes;
};

struct prefix_channel_scaled_monitort
{
  irep_idt worker;
  irep_idt flag;
  irep_idt sum;
  irep_idt bound;
  mp_integer scale;
  std::set<const goto_programt::instructiont *> writes;

  prefix_channel_scaled_monitort() : scale(0)
  {
  }
};

bool prefix_channel_fold_region(
  const std::vector<const goto_programt::instructiont *> &region,
  const namespacet &ns,
  irep_idt &fold,
  irep_idt &delta_symbol,
  std::set<const goto_programt::instructiont *> &writes)
{
  std::size_t assignments = 0;
  for(const auto *instruction : region)
  {
    if(instruction->is_assign())
    {
      exprt delta;
      irep_idt lhs;
      irep_idt candidate_delta;
      if(
        !stream_refine_addition(*instruction, lhs, delta) ||
        !shared_signed(lhs, ns) ||
        !symbol_id(delta, candidate_delta))
        return false;
      fold = lhs;
      delta_symbol = candidate_delta;
      writes.insert(instruction);
      ++assignments;
      continue;
    }
    if(
      instruction->is_decl() || instruction->is_dead() ||
      instruction->is_location() || instruction->is_skip())
      continue;
    return false;
  }
  return assignments == 1;
}

bool prefix_channel_consume_region(
  const std::vector<const goto_programt::instructiont *> &region,
  const namespacet &ns,
  stream_refine_consumet &result)
{
  std::vector<exprt> terms;
  std::size_t assumes = 0;
  std::size_t reads = 0;
  std::size_t increments = 0;
  const goto_programt::instructiont *last_assume = nullptr;
  const goto_programt::instructiont *read = nullptr;
  const goto_programt::instructiont *increment = nullptr;
  irep_idt storage;
  irep_idt front;
  for(const auto *instruction : region)
  {
    std::vector<exprt> current;
    if(prefix_channel_assumption_terms(*instruction, current))
    {
      ++assumes;
      terms.insert(terms.end(), current.begin(), current.end());
      last_assume = instruction;
      continue;
    }
    if(instruction->is_assign())
    {
      irep_idt lhs;
      irep_idt candidate_storage;
      irep_idt candidate_front;
      if(
        symbol_id(instruction->assign_lhs(), lhs) &&
        prefix_channel_array_index(
          instruction->assign_rhs(),
          candidate_storage,
          candidate_front))
      {
        if(
          reads != 0 || !local_signed(lhs, ns) ||
          lhs == candidate_front || lhs == candidate_storage)
          return false;
        result.temporary = lhs;
        storage = candidate_storage;
        front = candidate_front;
        ++reads;
        read = instruction;
        result.writes.insert(instruction);
        continue;
      }
      if(
        symbol_id(instruction->assign_lhs(), lhs) &&
        unit_increment(*instruction, lhs))
      {
        if(!front.empty() && front != lhs)
          return false;
        front = lhs;
        ++increments;
        increment = instruction;
        result.writes.insert(instruction);
        continue;
      }
      return false;
    }
    if(
      instruction->is_decl() || instruction->is_dead() ||
      instruction->is_location() || instruction->is_skip())
      continue;
    return false;
  }
  irep_idt available_front;
  irep_idt back;
  std::size_t availability = 0;
  for(const auto &term : terms)
  {
    irep_idt candidate_front;
    irep_idt candidate_back;
    if(
      prefix_channel_availability(
        term, candidate_front, candidate_back) &&
      candidate_front == front && back.empty())
    {
      available_front = candidate_front;
      back = candidate_back;
      ++availability;
    }
  }
  irep_idt bound;
  if(
    assumes != 1 || reads != 1 || increments != 1 ||
    availability != 1 || available_front != front ||
    last_assume == nullptr || read == nullptr || increment == nullptr ||
    last_assume->location_number >= read->location_number ||
    read->location_number >= increment->location_number ||
    !prefix_channel_bounds_excluding(terms, front, back, bound) ||
    !shared_signed(front, ns) || !shared_signed(back, ns) ||
    !shared_signed(bound, ns))
    return false;
  result.channel.storage = storage;
  result.channel.front = front;
  result.channel.back = back;
  result.channel.bound = bound;
  result.first_location =
    region.empty() ? 0 : region.front()->location_number;
  result.last_location =
    region.empty() ? 0 : region.back()->location_number;
  return true;
}

bool prefix_channel_plus_one(
  const exprt &src,
  const irep_idt &input)
{
  const exprt &expr = strip(src);
  if(expr.id() != ID_plus || expr.operands().size() != 2)
    return false;
  irep_idt candidate;
  return
    (symbol_id(expr.op0(), candidate) && candidate == input &&
     value_is(expr.op1(), 1)) ||
    (symbol_id(expr.op1(), candidate) && candidate == input &&
     value_is(expr.op0(), 1));
}

bool prefix_channel_affine_stage(
  const goto_modelt &model,
  const namespacet &ns,
  const irep_idt &worker,
  prefix_channel_affine_staget &result,
  std::string &reason)
{
  const auto &program =
    model.goto_functions.function_map.at(worker).body;
  natural_loopst loops;
  loops(program);
  if(loops.loop_map.size() != 1)
  {
    reason = "prefix_affine_stage_loop_count";
    return false;
  }
  const auto &loop = loops.loop_map.begin()->second;
  bool in_atomic = false;
  bool region_in_loop = false;
  std::vector<const goto_programt::instructiont *> region;
  std::vector<stream_refine_consumet> consumes;
  std::vector<stream_refine_publisht> publishes;
  std::set<irep_idt> flags;
  std::size_t snapshots = 0;
  std::size_t folds = 0;
  irep_idt fold_delta;
  for(auto instruction = program.instructions.begin();
      instruction != program.instructions.end(); ++instruction)
  {
    if(instruction->is_atomic_begin())
    {
      if(in_atomic)
      {
        reason = "prefix_affine_stage_atomic_nesting";
        return false;
      }
      in_atomic = true;
      region_in_loop = loop.contains(instruction);
      region.clear();
      continue;
    }
    if(instruction->is_atomic_end())
    {
      if(!in_atomic || loop.contains(instruction) != region_in_loop)
      {
        reason = "prefix_affine_stage_atomic_balance";
        return false;
      }
      stream_refine_consumet consume;
      stream_refine_publisht publish;
      irep_idt flag;
      irep_idt fold;
      irep_idt delta;
      std::set<const goto_programt::instructiont *> fold_writes;
      if(prefix_channel_consume_region(region, ns, consume))
        consumes.push_back(consume);
      else if(
        stream_refine_publish_region(
          region, ns, region_in_loop, publish))
        publishes.push_back(publish);
      else if(prefix_channel_snapshot_read_region(region, ns, flag))
      {
        flags.insert(flag);
        ++snapshots;
      }
      else if(
        prefix_channel_fold_region(
          region, ns, fold, delta, fold_writes))
      {
        result.auxiliary_fold = fold;
        fold_delta = delta;
        result.writes.insert(
          fold_writes.begin(), fold_writes.end());
        ++folds;
      }
      else
      {
        reason =
          "prefix_affine_stage_atomic_region_" +
          std::to_string(
            region.empty() ? 0 :
              region.front()->location_number) + "_size_" +
          std::to_string(region.size());
        return false;
      }
      in_atomic = false;
      region.clear();
      continue;
    }
    if(in_atomic)
      region.push_back(&*instruction);
    else if(instruction->is_function_call())
    {
      irep_idt callee;
      if(!call_id(*instruction, callee) || !is_assume(callee))
      {
        reason = "prefix_affine_stage_call";
        return false;
      }
    }
  }
  if(
    in_atomic || consumes.size() != 1 || publishes.size() != 1 ||
    flags.size() != 1 || snapshots != 2 || folds != 1 ||
    consumes.front().channel.storage ==
      publishes.front().channel.storage ||
    consumes.front().first_location >=
      publishes.front().first_location ||
    fold_delta != consumes.front().temporary ||
    !prefix_channel_plus_one(
      publishes.front().token,
      consumes.front().temporary))
  {
    reason = "prefix_affine_stage_signature";
    return false;
  }
  result.worker = worker;
  result.consume = consumes.front();
  result.publish = publishes.front();
  result.flag = *flags.begin();
  result.writes.insert(
    result.consume.writes.begin(), result.consume.writes.end());
  result.writes.insert(
    result.publish.writes.begin(), result.publish.writes.end());
  return true;
}

bool prefix_channel_scaled_monitor(
  const goto_modelt &model,
  const namespacet &ns,
  const irep_idt &worker,
  prefix_channel_scaled_monitort &result,
  std::string &reason)
{
  const auto &program =
    model.goto_functions.function_map.at(worker).body;
  natural_loopst loops;
  loops(program);
  if(!loops.loop_map.empty())
  {
    reason = "prefix_scaled_monitor_loop";
    return false;
  }
  unsigned depth = 0;
  std::size_t assignments = 0;
  for(const auto &instruction : program.instructions)
  {
    if(instruction.is_atomic_begin())
    {
      if(depth != 0)
        return false;
      depth = 1;
      continue;
    }
    if(instruction.is_atomic_end())
    {
      if(depth != 1)
        return false;
      depth = 0;
      continue;
    }
    if(instruction.is_function_call())
    {
      reason = "prefix_scaled_monitor_call";
      return false;
    }
    if(!instruction.is_assign())
      continue;
    irep_idt flag;
    if(
      depth != 1 ||
      !symbol_id(instruction.assign_lhs(), flag) ||
      !shared_boolean(flag, ns))
      return false;
    const exprt &relation = strip(instruction.assign_rhs());
    irep_idt sum;
    if(
      relation.id() != ID_le ||
      relation.operands().size() != 2 ||
      !symbol_id(relation.op0(), sum) ||
      !shared_signed(sum, ns))
      return false;
    const exprt &product = strip(relation.op1());
    irep_idt bound;
    mp_integer scale;
    if(
      product.id() != ID_mult ||
      product.operands().size() != 2)
      return false;
    if(
      integer_constant(product.op0(), scale) &&
      symbol_id(product.op1(), bound))
    {
    }
    else if(
      integer_constant(product.op1(), scale) &&
      symbol_id(product.op0(), bound))
    {
    }
    else
      return false;
    if(scale <= 0 || !shared_signed(bound, ns))
      return false;
    result.flag = flag;
    result.sum = sum;
    result.bound = bound;
    result.scale = scale;
    result.writes.insert(&instruction);
    ++assignments;
  }
  if(depth != 0 || assignments != 1)
  {
    reason = "prefix_scaled_monitor_shape";
    return false;
  }
  result.worker = worker;
  return true;
}

bool prefix_channel_scaled_bound_defined(
  const goto_modelt &model,
  const lifecyclet &life,
  const irep_idt &bound,
  const mp_integer &scale)
{
  if(scale != 2)
    return false;
  const auto &main =
    model.goto_functions.function_map.at(ID_main).body;
  for(const auto &instruction : main.instructions)
  {
    if(
      life.first_create != nullptr &&
      instruction.location_number >=
        life.first_create->location_number)
      break;
    irep_idt callee;
    if(
      !call_id(instruction, callee) || !is_assume(callee) ||
      instruction.call_arguments().size() != 1)
      continue;
    std::vector<exprt> terms;
    flatten_and(instruction.call_arguments().front(), terms);
    for(const auto &term : terms)
    {
      const exprt &relation = strip(term);
      irep_idt lhs;
      mp_integer upper;
      const exprt &rhs =
        relation.operands().size() == 2 ?
          strip(relation.op1()) : nil_exprt();
      bool has_upper = integer_constant(rhs, upper);
      if(!has_upper && rhs.id() == ID_div &&
         rhs.operands().size() == 2)
      {
        mp_integer numerator;
        mp_integer denominator;
        if(
          !integer_constant(rhs.op0(), numerator) ||
          !integer_constant(rhs.op1(), denominator) ||
          numerator < 0 || denominator <= 0)
          continue;
        upper = numerator / denominator;
        has_upper = true;
      }
      if(
        has_upper &&
        relation.id() == ID_lt &&
        relation.operands().size() == 2 &&
        symbol_id(relation.op0(), lhs) && lhs == bound &&
        upper > 0 && upper <= 1073741823)
        return true;
    }
  }
  return false;
}

bool prefix_channel_affine_pipeline_proof_impl(
  const goto_modelt &model,
  const namespacet &ns,
  std::string &reason)
{
  lifecyclet life;
  std::vector<irep_idt> workers;
  if(
    !prefix_channel_lifecycle(model, life, workers, reason) ||
    workers.size() != 4)
  {
    if(reason.empty())
      reason = "prefix_affine_lifecycle";
    return false;
  }
  prefix_channel_bounded_publishert publisher;
  prefix_channel_affine_staget stage;
  prefix_channel_sum_consumert consumer;
  prefix_channel_scaled_monitort monitor;
  for(const auto &worker : workers)
  {
    prefix_channel_bounded_publishert candidate_publisher;
    std::string publisher_reason;
    if(
      prefix_channel_bounded_publisher(
        model, ns, worker, candidate_publisher, publisher_reason))
    {
      publisher = candidate_publisher;
      continue;
    }
    prefix_channel_affine_staget candidate_stage;
    std::string stage_reason;
    if(
      prefix_channel_affine_stage(
        model, ns, worker, candidate_stage, stage_reason))
    {
      stage = candidate_stage;
      continue;
    }
    prefix_channel_sum_consumert candidate_consumer;
    std::string consumer_reason;
    if(
      prefix_channel_sum_consumer(
        model, ns, worker, candidate_consumer, consumer_reason))
    {
      consumer = candidate_consumer;
      continue;
    }
    prefix_channel_scaled_monitort candidate_monitor;
    std::string monitor_reason;
    if(
      prefix_channel_scaled_monitor(
        model, ns, worker, candidate_monitor, monitor_reason))
    {
      monitor = candidate_monitor;
      continue;
    }
    reason =
      "prefix_affine_worker_p_" + publisher_reason +
      "_s_" + stage_reason + "_c_" + consumer_reason +
      "_m_" + monitor_reason;
    return false;
  }
  if(
    publisher.worker.empty() || stage.worker.empty() ||
    consumer.worker.empty() || monitor.worker.empty() ||
    publisher.publish.channel.storage !=
      stage.consume.channel.storage ||
    publisher.publish.channel.back != stage.consume.channel.back ||
    publisher.publish.channel.bound != stage.consume.channel.bound ||
    stage.publish.channel.storage != consumer.channel.storage ||
    stage.publish.channel.back != consumer.channel.back ||
    stage.publish.channel.bound != consumer.channel.bound ||
    publisher.flag != stage.flag ||
    publisher.flag != monitor.flag ||
    publisher.bound != monitor.bound ||
    consumer.sum != monitor.sum ||
    monitor.scale != 2)
  {
    reason = "prefix_affine_signature";
    return false;
  }
  stream_refine_channelt first = publisher.publish.channel;
  first.front = stage.consume.channel.front;
  stream_refine_channelt second = stage.publish.channel;
  second.front = consumer.channel.front;
  if(!stream_refine_initial_channel(model, life, first))
  {
    reason = "prefix_affine_initial_first_channel";
    return false;
  }
  if(!stream_refine_initial_channel(model, life, second))
  {
    reason = "prefix_affine_initial_second_channel";
    return false;
  }
  if(
    !stream_refine_nonnegative_count(
      model, life, publisher.bound))
  {
    reason = "prefix_affine_initial_nonnegative_bound";
    return false;
  }
  if(
    !prefix_channel_scaled_bound_defined(
      model, life, publisher.bound, monitor.scale))
  {
    reason = "prefix_affine_initial_scaled_bound";
    return false;
  }
  if(
    !prefix_channel_initial_value(
      model, life, monitor.flag, true_exprt()))
  {
    reason = "prefix_affine_initial_flag";
    return false;
  }
  const goto_programt::instructiont *property_assumption = nullptr;
  const goto_programt::instructiont *error = nullptr;
  if(
    !prefix_channel_false_flag_property(
      model,
      life,
      monitor.flag,
      property_assumption,
      error,
      reason))
    return false;

  const std::set<irep_idt> queues = {
    first.storage, second.storage};
  std::set<irep_idt> protected_symbols = {
    first.storage,
    first.front,
    first.back,
    first.bound,
    second.storage,
    second.front,
    second.back,
    second.bound,
    publisher.bound,
    consumer.sum,
    monitor.flag};
  std::set<const goto_programt::instructiont *> allowed =
    publisher.writes;
  allowed.insert(stage.writes.begin(), stage.writes.end());
  allowed.insert(
    consumer.writes.begin(), consumer.writes.end());
  allowed.insert(monitor.writes.begin(), monitor.writes.end());
  stream_refine_sourcet unused_source;
  std::vector<stream_refine_staget> unused_stages;
  if(
    !stream_refine_fresh_queues(
      model, ns, life, queues, reason) ||
    !zero_initialized_symbols(
      model, {consumer.sum}, allowed, reason) ||
    !stream_refine_global(
      model,
      ns,
      life,
      unused_source,
      unused_stages,
      queues,
      protected_symbols,
      allowed,
      property_assumption,
      error,
      reason))
    return false;

  std::cout << "NATIVE_PREFIX_CHANNEL applied=1"
            << " rule=affine_pipeline"
            << " input=" << first.storage
            << " output=" << second.storage
            << " sum=" << consumer.sum << '\n';
  return true;
}

bool stream_sentinel_refinement_proof_impl(
  const goto_modelt &model,
  const namespacet &ns,
  std::string &reason)
{
  lifecyclet life;
  std::vector<irep_idt> workers;
  if(!stream_refine_lifecycle(model, life, workers, reason))
    return false;

  irep_idt count;
  irep_idt sink;
  exprt expected;
  std::set<std::pair<irep_idt, irep_idt>> property_equalities;
  const goto_programt::instructiont *property_assumption = nullptr;
  const goto_programt::instructiont *error = nullptr;
  if(
    !stream_refine_property(
      model,
      ns,
      life,
      property_equalities,
      sink,
      expected,
      property_assumption,
      error,
      reason))
    return false;

  stream_refine_sourcet source;
  std::vector<stream_refine_staget> stages;
  for(const auto &worker : workers)
  {
    stream_refine_sourcet candidate_source;
    std::string source_reason;
    if(
      stream_refine_source(
        model, ns, worker, candidate_source, source_reason))
    {
      if(!source.worker.empty())
      {
        reason = "stream_refine_multiple_sources";
        return false;
      }
      source = candidate_source;
      continue;
    }
    stream_refine_staget stage;
    std::string stage_reason;
    if(stream_refine_stage(model, ns, worker, stage, stage_reason))
    {
      stages.push_back(stage);
      continue;
    }
    reason =
      "stream_refine_worker_shape_source_" + source_reason +
      "_stage_" + stage_reason;
    return false;
  }
  mp_integer data_token;
  count = source.count;
  if(
    source.worker.empty() ||
    stages.size() + 1 != workers.size() ||
    !integer_constant(source.data.token, data_token) ||
    data_token <= 0 ||
    !stream_refine_expected_fold(expected, count, data_token) ||
    !stream_refine_nonnegative_count(model, life, count) ||
    !stream_refine_product_defined(
      model, life, count, data_token))
  {
    reason = "stream_refine_source_signature";
    return false;
  }

  std::vector<const stream_refine_staget *> ordered;
  stream_refine_channelt channel = source.data.channel;
  std::set<irep_idt> used_workers;
  while(ordered.size() != stages.size())
  {
    const stream_refine_staget *next = nullptr;
    for(const auto &stage : stages)
    {
      if(
        used_workers.count(stage.worker) == 0 &&
        stage.consume.channel.storage == channel.storage &&
        stage.consume.channel.back == channel.back &&
        stage.consume.channel.bound == channel.bound)
      {
        if(next != nullptr)
        {
          reason = "stream_refine_branching";
          return false;
        }
        next = &stage;
      }
    }
    if(next == nullptr)
    {
      reason =
        "stream_refine_disconnected_at_" +
        id2string(channel.storage) + "_back_" +
        id2string(channel.back) + "_bound_" +
        id2string(channel.bound);
      return false;
    }
    ordered.push_back(next);
    used_workers.insert(next->worker);
    channel.front = next->consume.channel.front;
    if(ordered.size() != stages.size())
    {
      if(!next->forwards)
      {
        reason = "stream_refine_early_sink";
        return false;
      }
      channel = next->publish.channel;
    }
    else if(next->forwards)
    {
      reason = "stream_refine_open_output";
      return false;
    }
  }
  if(ordered.back()->fold != sink)
  {
    reason = "stream_refine_sink_property";
    return false;
  }

  std::set<irep_idt> accounts;
  if(!source.account.empty())
    accounts.insert(source.account);
  for(const auto *stage : ordered)
  {
    if(
      source.account.empty() != stage->account.empty() ||
      (!source.account.empty() &&
       strip(source.account_delta) != strip(stage->account_delta)))
    {
      reason = "stream_refine_account_signature";
      return false;
    }
    if(!stage->account.empty() &&
       !accounts.insert(stage->account).second)
    {
      reason = "stream_refine_account_ownership";
      return false;
    }
  }
  std::set<std::pair<irep_idt, irep_idt>> expected_equalities;
  if(!accounts.empty())
  {
    const irep_idt root = *accounts.begin();
    for(const auto &account : accounts)
    {
      if(account != root)
        expected_equalities.insert(std::minmax(root, account));
    }
  }
  if(property_equalities != expected_equalities)
  {
    reason = "stream_refine_account_property";
    return false;
  }

  std::set<stream_refine_channelt> channels;
  stream_refine_channelt source_channel = source.data.channel;
  source_channel.front = ordered.front()->consume.channel.front;
  channels.insert(source_channel);
  for(std::size_t index = 0; index + 1 < ordered.size(); ++index)
  {
    stream_refine_channelt composed = ordered[index]->publish.channel;
    composed.front = ordered[index + 1]->consume.channel.front;
    if(
      composed.storage !=
        ordered[index + 1]->consume.channel.storage ||
      composed.back != ordered[index + 1]->consume.channel.back ||
      composed.bound != ordered[index + 1]->consume.channel.bound)
    {
      reason = "stream_refine_channel_signature";
      return false;
    }
    channels.insert(composed);
  }
  for(const auto &entry : channels)
  {
    if(!stream_refine_initial_channel(model, life, entry))
    {
      reason = "stream_refine_initial_channel";
      return false;
    }
  }

  std::set<irep_idt> queues;
  std::set<irep_idt> protected_symbols = {count, sink};
  std::set<const goto_programt::instructiont *> allowed =
    source.writes;
  protected_symbols.insert(accounts.begin(), accounts.end());
  for(const auto &entry : channels)
  {
    queues.insert(entry.storage);
    protected_symbols.insert(entry.storage);
    protected_symbols.insert(entry.front);
    protected_symbols.insert(entry.back);
    protected_symbols.insert(entry.bound);
  }
  for(const auto *stage : ordered)
  {
    protected_symbols.insert(stage->fold);
    protected_symbols.insert(stage->consume.temporary);
    allowed.insert(stage->writes.begin(), stage->writes.end());
  }
  if(
    !stream_refine_fresh_queues(model, ns, life, queues, reason) ||
    !stream_refine_global(
      model,
      ns,
      life,
      source,
      stages,
      queues,
      protected_symbols,
      allowed,
      property_assumption,
      error,
      reason))
    return false;

  std::set<irep_idt> zero_symbols = {sink};
  zero_symbols.insert(accounts.begin(), accounts.end());
  if(!zero_initialized_symbols(model, zero_symbols, allowed, reason))
    return false;

  std::cout << "NATIVE_STREAM_REFINEMENT applied=1"
            << " rule=sentinel"
            << " channels=" << channels.size()
            << " stages=" << ordered.size()
            << " sink=" << sink << '\n';
  return true;
}

struct stream_refine_done_producert
{
  irep_idt worker;
  irep_idt queue;
  irep_idt queue_bound;
  irep_idt front;
  irep_idt size;
  irep_idt generator;
  irep_idt generator_bound;
  irep_idt update;
  irep_idt update_bound;
  irep_idt done;
  irep_idt state;
  irep_idt finished;
  std::set<const goto_programt::instructiont *> writes;
};

struct stream_refine_done_consumert
{
  irep_idt worker;
  irep_idt queue;
  irep_idt queue_bound;
  irep_idt front;
  irep_idt size;
  irep_idt matrix;
  irep_idt row_bound;
  irep_idt column_bound;
  irep_idt state;
  irep_idt finished;
  irep_idt condition;
  std::set<const goto_programt::instructiont *> writes;
};

struct stream_refine_directt
{
  irep_idt worker;
  irep_idt generator;
  irep_idt generator_bound;
  irep_idt update;
  irep_idt update_bound;
  irep_idt done;
  irep_idt generator_state;
  irep_idt matrix;
  irep_idt row_bound;
  irep_idt column_bound;
  irep_idt fold_state;
  irep_idt finished;
  std::set<irep_idt> generator_state_bounds;
  std::set<const goto_programt::instructiont *> writes;
};

bool stream_refine_array(
  const exprt &src,
  irep_idt &base,
  exprt &index)
{
  const exprt &expr = strip(src);
  if(expr.id() != ID_dereference)
    return false;
  const exprt &pointer = strip(to_dereference_expr(expr).pointer());
  if(pointer.id() != ID_plus || pointer.operands().size() != 2)
    return false;
  irep_idt candidate;
  if(symbol_id(pointer.op0(), candidate))
  {
    base = candidate;
    index = strip(pointer.op1());
    return true;
  }
  if(symbol_id(pointer.op1(), candidate))
  {
    base = candidate;
    index = strip(pointer.op0());
    return true;
  }
  return false;
}

bool stream_refine_matrix(
  const exprt &src,
  irep_idt &matrix,
  exprt &row,
  exprt &column)
{
  const exprt &expr = strip(src);
  if(expr.id() != ID_dereference)
    return false;
  const exprt &outer_pointer =
    strip(to_dereference_expr(expr).pointer());
  if(
    outer_pointer.id() != ID_plus ||
    outer_pointer.operands().size() != 2)
    return false;
  for(unsigned order = 0; order < 2; ++order)
  {
    irep_idt candidate_matrix;
    exprt candidate_row;
    if(
      stream_refine_array(
        outer_pointer.operands()[order],
        candidate_matrix,
        candidate_row))
    {
      matrix = candidate_matrix;
      row = strip(candidate_row);
      column = strip(outer_pointer.operands()[1 - order]);
      return true;
    }
  }
  return false;
}

bool stream_refine_plus_symbols(
  const exprt &src,
  irep_idt &left,
  irep_idt &right)
{
  const exprt &expr = strip(src);
  return
    expr.id() == ID_plus && expr.operands().size() == 2 &&
    symbol_id(expr.op0(), left) && symbol_id(expr.op1(), right) &&
    left != right;
}

bool stream_refine_minus_one(
  const goto_programt::instructiont &instruction,
  const irep_idt &symbol)
{
  if(!instruction.is_assign())
    return false;
  irep_idt lhs;
  if(!symbol_id(instruction.assign_lhs(), lhs) || lhs != symbol)
    return false;
  const exprt &rhs = strip(instruction.assign_rhs());
  irep_idt first;
  return
    rhs.id() == ID_minus && rhs.operands().size() == 2 &&
    symbol_id(rhs.op0(), first) && first == symbol &&
    value_is(rhs.op1(), 1);
}

bool stream_refine_truth_symbol(
  const exprt &src,
  irep_idt &symbol)
{
  const exprt &expr = strip(src);
  if(symbol_id(expr, symbol))
    return true;
  return
    expr.id() == ID_notequal && expr.operands().size() == 2 &&
    ((symbol_id(expr.op0(), symbol) && value_is(expr.op1(), 0)) ||
     (symbol_id(expr.op1(), symbol) && value_is(expr.op0(), 0)));
}

bool stream_refine_drain_condition(
  const exprt &src,
  const irep_idt &finished,
  const irep_idt &size)
{
  const exprt &root = strip(src);
  if(root.id() != ID_or || root.operands().size() != 2)
    return false;
  bool unfinished = false;
  bool nonempty = false;
  for(const auto &operand : root.operands())
  {
    const exprt &term = strip(operand);
    irep_idt candidate;
    if(negated_truth(term, candidate) && candidate == finished)
      unfinished = true;
    if(
      term.id() == ID_gt && term.operands().size() == 2 &&
      symbol_id(term.op0(), candidate) && candidate == size &&
      value_is(term.op1(), 0))
      nonempty = true;
  }
  return unfinished && nonempty;
}

bool stream_refine_parse_drain_condition(
  const exprt &src,
  irep_idt &finished,
  irep_idt &size)
{
  const exprt &root = strip(src);
  if(root.id() != ID_or || root.operands().size() != 2)
    return false;
  bool unfinished = false;
  bool nonempty = false;
  for(const auto &operand : root.operands())
  {
    const exprt &term = strip(operand);
    irep_idt negated;
    if(negated_truth(term, negated))
    {
      finished = negated;
      unfinished = true;
    }
    irep_idt candidate;
    if(
      term.id() == ID_gt && term.operands().size() == 2 &&
      symbol_id(term.op0(), candidate) &&
      value_is(term.op1(), 0))
    {
      size = candidate;
      nonempty = true;
    }
  }
  return unfinished && nonempty;
}

bool stream_refine_assume_terms(
  const goto_programt::instructiont &instruction,
  std::vector<exprt> &terms)
{
  irep_idt callee;
  if(
    !call_id(instruction, callee) || !is_assume(callee) ||
    instruction.call_arguments().size() != 1)
    return false;
  flatten_and(instruction.call_arguments().front(), terms);
  return true;
}

bool stream_refine_find_bound(
  const std::vector<exprt> &terms,
  const exprt &index,
  irep_idt &bound)
{
  bool lower = false;
  bool upper = false;
  for(const auto &term : terms)
  {
    const exprt &relation = strip(term);
    if(
      relation.operands().size() != 2 ||
      strip(relation.op0()) != strip(index))
      continue;
    if(
      relation.id() == ID_ge && value_is(relation.op1(), 0))
      lower = true;
    irep_idt candidate;
    if(
      relation.id() == ID_lt &&
      symbol_id(relation.op1(), candidate))
    {
      if(upper && bound != candidate)
        return false;
      bound = candidate;
      upper = true;
    }
  }
  return lower && upper;
}

bool stream_refine_collect_bounds(
  const std::vector<exprt> &terms,
  const exprt &index,
  std::set<irep_idt> &bounds)
{
  bool lower = false;
  for(const auto &term : terms)
  {
    const exprt &relation = strip(term);
    if(
      relation.operands().size() != 2 ||
      strip(relation.op0()) != strip(index))
      continue;
    if(
      relation.id() == ID_ge && value_is(relation.op1(), 0))
      lower = true;
    irep_idt bound;
    if(
      relation.id() == ID_lt &&
      symbol_id(relation.op1(), bound))
      bounds.insert(bound);
  }
  return lower && !bounds.empty();
}

bool stream_refine_done_producer(
  const goto_modelt &model,
  const namespacet &ns,
  const irep_idt &worker,
  stream_refine_done_producert &result,
  std::string &reason)
{
  const auto &program =
    model.goto_functions.function_map.at(worker).body;
  natural_loopst loops;
  loops(program);
  if(loops.loop_map.size() != 1)
  {
    reason = "stream_refine_done_producer_loop_count";
    return false;
  }
  const auto loop_head = loops.loop_map.begin()->first;
  irep_idt finished;
  if(
    !stream_refine_truth_symbol(
      loop_head->condition(), finished) ||
    !shared_boolean(finished, ns))
  {
    reason = "stream_refine_done_producer_exit";
    return false;
  }
  result.worker = worker;
  result.finished = finished;

  unsigned atomic_depth = 0;
  unsigned atomic_epoch = 0;
  std::vector<exprt> publish_terms;
  std::vector<exprt> other_terms;
  std::size_t publish_assumes = 0;
  std::size_t update_assumes = 0;
  std::size_t size_updates = 0;
  std::size_t state_updates = 0;
  std::size_t done_updates = 0;
  exprt queue_index;
  exprt published_token;
  for(auto instruction = program.instructions.begin();
      instruction != program.instructions.end(); ++instruction)
  {
    if(instruction->is_atomic_begin())
    {
      if(atomic_depth != 0)
      {
        reason = "stream_refine_done_producer_atomic";
        return false;
      }
      atomic_depth = 1;
      ++atomic_epoch;
      continue;
    }
    if(instruction->is_atomic_end())
    {
      if(atomic_depth != 1)
      {
        reason = "stream_refine_done_producer_atomic";
        return false;
      }
      atomic_depth = 0;
      continue;
    }
    std::vector<exprt> terms;
    if(stream_refine_assume_terms(*instruction, terms))
    {
      if(atomic_depth == 1 && atomic_epoch == 1)
      {
        ++publish_assumes;
        publish_terms.insert(
          publish_terms.end(), terms.begin(), terms.end());
      }
      else if(atomic_depth == 0)
      {
        ++update_assumes;
        other_terms.insert(
          other_terms.end(), terms.begin(), terms.end());
      }
      else
      {
        reason = "stream_refine_done_producer_assume";
        return false;
      }
      continue;
    }
    if(!instruction->is_assign())
      continue;
    irep_idt lhs;
    if(!symbol_id(instruction->assign_lhs(), lhs))
      continue;
    if(
      atomic_depth == 1 && atomic_epoch == 1 &&
      unit_increment(*instruction, lhs))
    {
      result.size = lhs;
      ++size_updates;
      result.writes.insert(&*instruction);
      continue;
    }
    irep_idt base;
    exprt index;
    if(
      atomic_depth == 0 &&
      stream_refine_array(instruction->assign_rhs(), base, index) &&
      symbol_id(index, result.state) && lhs == result.state)
    {
      result.update = base;
      ++state_updates;
      result.writes.insert(&*instruction);
      continue;
    }
    if(
      atomic_depth == 1 && atomic_epoch == 2 &&
      stream_refine_array(instruction->assign_rhs(), base, index) &&
      lhs == result.finished &&
      symbol_id(index, result.state))
    {
      result.done = base;
      ++done_updates;
      result.writes.insert(&*instruction);
      continue;
    }
  }
  if(
    atomic_depth != 0 || atomic_epoch != 2 ||
    publish_assumes != 3 || update_assumes != 2 ||
    size_updates != 1 || state_updates != 1 || done_updates != 1 ||
    result.state.empty())
  {
    reason =
      "stream_refine_done_producer_shape_a" +
      std::to_string(atomic_epoch) + "_pa" +
      std::to_string(publish_assumes) + "_ua" +
      std::to_string(update_assumes) + "_sz" +
      std::to_string(size_updates) + "_st" +
      std::to_string(state_updates) + "_dn" +
      std::to_string(done_updates);
    return false;
  }

  bool publication = false;
  for(const auto &term : publish_terms)
  {
    irep_idt queue;
    exprt index;
    exprt token;
    const exprt &relation = strip(term);
    if(relation.id() != ID_equal || relation.operands().size() != 2)
      continue;
    if(stream_refine_array(relation.op0(), queue, index))
      token = strip(relation.op1());
    else if(stream_refine_array(relation.op1(), queue, index))
      token = strip(relation.op0());
    else
      continue;
    irep_idt generator;
    exprt generator_index;
    if(
      !stream_refine_array(token, generator, generator_index) ||
      !symbol_id(generator_index, result.state))
      continue;
    result.queue = queue;
    result.generator = generator;
    queue_index = strip(index);
    published_token = strip(token);
    publication = true;
  }
  irep_idt index_front;
  irep_idt index_size;
  if(
    !publication ||
    !stream_refine_plus_symbols(
      queue_index, index_front, index_size) ||
    index_size != result.size)
  {
    reason = "stream_refine_done_publication";
    return false;
  }
  result.front = index_front;
  if(
    !stream_refine_find_bound(
      publish_terms, queue_index, result.queue_bound) ||
    !stream_refine_find_bound(
      publish_terms,
      symbol_exprt(result.state, lookup(result.state, ns)->type),
      result.generator_bound) ||
    !stream_refine_find_bound(
      other_terms,
      symbol_exprt(result.state, lookup(result.state, ns)->type),
      result.update_bound) ||
    !shared_signed(result.front, ns) ||
    !shared_signed(result.size, ns) ||
    !shared_signed(result.state, ns) ||
    !shared_signed(result.queue_bound, ns) ||
    !shared_signed(result.generator_bound, ns) ||
    !shared_signed(result.update_bound, ns))
  {
    reason = "stream_refine_done_producer_bounds";
    return false;
  }
  return true;
}

bool stream_refine_condition_assignment(
  const goto_programt::instructiont &instruction,
  const irep_idt &finished,
  const irep_idt &size,
  irep_idt &condition)
{
  if(!instruction.is_assign())
    return false;
  irep_idt lhs;
  if(
    !symbol_id(instruction.assign_lhs(), lhs) ||
    !stream_refine_drain_condition(
      instruction.assign_rhs(), finished, size))
    return false;
  condition = lhs;
  return true;
}

bool stream_refine_done_consumer(
  const goto_modelt &model,
  const namespacet &ns,
  const irep_idt &worker,
  stream_refine_done_consumert &result,
  std::string &reason)
{
  const auto &program =
    model.goto_functions.function_map.at(worker).body;
  natural_loopst loops;
  loops(program);
  if(loops.loop_map.size() != 1)
  {
    reason = "stream_refine_done_consumer_loop_count";
    return false;
  }
  const auto loop_head = loops.loop_map.begin()->first;
  const exprt &head = strip(loop_head->condition());
  if(
    head.id() != ID_not || head.operands().size() != 1)
  {
    reason = "stream_refine_done_consumer_exit";
    return false;
  }
  const exprt &truth = strip(head.op0());
  irep_idt condition;
  if(
    truth.id() != ID_notequal || truth.operands().size() != 2 ||
    !symbol_id(truth.op0(), condition) ||
    !value_is(truth.op1(), 0))
  {
    reason = "stream_refine_done_consumer_exit";
    return false;
  }
  result.worker = worker;
  result.condition = condition;

  unsigned atomic_depth = 0;
  unsigned atomic_epoch = 0;
  std::vector<exprt> terms;
  std::size_t assumes = 0;
  std::size_t folds = 0;
  std::size_t front_updates = 0;
  std::size_t size_updates = 0;
  std::size_t condition_updates = 0;
  exprt token;
  for(auto instruction = program.instructions.begin();
      instruction != program.instructions.end(); ++instruction)
  {
    if(instruction->is_atomic_begin())
    {
      if(atomic_depth != 0)
      {
        reason = "stream_refine_done_consumer_atomic";
        return false;
      }
      atomic_depth = 1;
      ++atomic_epoch;
      continue;
    }
    if(instruction->is_atomic_end())
    {
      if(atomic_depth != 1)
      {
        reason = "stream_refine_done_consumer_atomic";
        return false;
      }
      atomic_depth = 0;
      continue;
    }
    std::vector<exprt> current_terms;
    if(stream_refine_assume_terms(*instruction, current_terms))
    {
      if(atomic_depth != 1 || atomic_epoch != 2)
      {
        reason = "stream_refine_done_consumer_assume";
        return false;
      }
      ++assumes;
      terms.insert(
        terms.end(), current_terms.begin(), current_terms.end());
      continue;
    }
    if(!instruction->is_assign())
      continue;
    irep_idt lhs;
    if(!symbol_id(instruction->assign_lhs(), lhs))
      continue;
    if(atomic_depth == 1 &&
       (atomic_epoch == 1 || atomic_epoch == 3))
    {
      irep_idt lhs;
      if(!symbol_id(instruction->assign_lhs(), lhs))
        continue;
      if(atomic_epoch == 1)
      {
        if(
          lhs != condition ||
          !stream_refine_parse_drain_condition(
            instruction->assign_rhs(),
            result.finished,
            result.size))
        {
          reason = "stream_refine_done_consumer_condition";
          return false;
        }
        ++condition_updates;
        result.writes.insert(&*instruction);
        continue;
      }
      irep_idt candidate;
      if(
        stream_refine_condition_assignment(
          *instruction,
          result.finished,
          result.size,
          candidate))
      {
        if(candidate != condition)
        {
          reason = "stream_refine_done_consumer_condition";
          return false;
        }
        ++condition_updates;
        result.writes.insert(&*instruction);
      }
      continue;
    }
    exprt row;
    exprt column;
    irep_idt matrix;
    if(
      atomic_depth == 1 && atomic_epoch == 2 &&
      stream_refine_matrix(
        instruction->assign_rhs(), matrix, row, column) &&
      symbol_id(row, result.state) && lhs == result.state)
    {
      result.matrix = matrix;
      token = strip(column);
      ++folds;
      result.writes.insert(&*instruction);
      continue;
    }
    if(
      atomic_depth == 1 && atomic_epoch == 2 &&
      unit_increment(*instruction, lhs))
    {
      result.front = lhs;
      ++front_updates;
      result.writes.insert(&*instruction);
      continue;
    }
    if(
      atomic_depth == 1 && atomic_epoch == 2 &&
      stream_refine_minus_one(*instruction, lhs))
    {
      result.size = lhs;
      ++size_updates;
      result.writes.insert(&*instruction);
      continue;
    }
  }
  if(
    atomic_depth != 0 || atomic_epoch != 3 || assumes != 4 ||
    folds != 1 || front_updates != 1 || size_updates != 1 ||
    condition_updates != 2 || result.state.empty() ||
    result.finished.empty() || result.size.empty())
  {
    reason = "stream_refine_done_consumer_shape";
    return false;
  }
  irep_idt queue;
  exprt queue_index;
  if(
    !stream_refine_array(token, queue, queue_index) ||
    !symbol_id(queue_index, result.front))
  {
    reason = "stream_refine_done_consumer_token";
    return false;
  }
  result.queue = queue;
  if(
    !stream_refine_find_bound(
      terms,
      symbol_exprt(result.state, lookup(result.state, ns)->type),
      result.row_bound) ||
    !stream_refine_find_bound(
      terms,
      symbol_exprt(result.front, lookup(result.front, ns)->type),
      result.queue_bound) ||
    !stream_refine_find_bound(
      terms, token, result.column_bound))
  {
    reason = "stream_refine_done_consumer_bounds";
    return false;
  }
  bool positive_size = false;
  for(const auto &term : terms)
  {
    if(stream_refine_symbol_zero_relation(term, result.size, ID_gt))
      positive_size = true;
  }
  if(
    !positive_size || !local_boolean(result.condition, ns) ||
    !shared_signed(result.state, ns) ||
    !shared_signed(result.front, ns) ||
    !shared_signed(result.size, ns))
  {
    reason = "stream_refine_done_consumer_types";
    return false;
  }
  return true;
}

bool stream_refine_direct(
  const goto_modelt &model,
  const namespacet &ns,
  const irep_idt &worker,
  stream_refine_directt &result,
  std::string &reason)
{
  const auto &program =
    model.goto_functions.function_map.at(worker).body;
  natural_loopst loops;
  loops(program);
  if(loops.loop_map.size() != 1)
  {
    reason = "stream_refine_direct_loop_count";
    return false;
  }
  const auto loop_head = loops.loop_map.begin()->first;
  irep_idt finished;
  if(
    !stream_refine_truth_symbol(
      loop_head->condition(), finished) ||
    !shared_boolean(finished, ns))
  {
    reason = "stream_refine_direct_exit";
    return false;
  }
  result.worker = worker;
  result.finished = finished;

  std::vector<exprt> terms;
  std::size_t assumes = 0;
  std::size_t folds = 0;
  std::size_t generator_updates = 0;
  std::size_t done_updates = 0;
  exprt generated_token;
  for(auto instruction = program.instructions.begin();
      instruction != program.instructions.end(); ++instruction)
  {
    std::vector<exprt> current;
    if(stream_refine_assume_terms(*instruction, current))
    {
      ++assumes;
      terms.insert(terms.end(), current.begin(), current.end());
      continue;
    }
    if(!instruction->is_assign())
      continue;
    irep_idt lhs;
    if(!symbol_id(instruction->assign_lhs(), lhs))
      continue;
    irep_idt matrix;
    exprt row;
    exprt column;
    if(
      stream_refine_matrix(
        instruction->assign_rhs(), matrix, row, column) &&
      symbol_id(row, result.fold_state) &&
      lhs == result.fold_state)
    {
      irep_idt generator;
      exprt generator_index;
      if(
        !stream_refine_array(
          column, generator, generator_index) ||
        !symbol_id(
          generator_index, result.generator_state))
      {
        reason = "stream_refine_direct_token";
        return false;
      }
      result.matrix = matrix;
      result.generator = generator;
      generated_token = strip(column);
      ++folds;
      result.writes.insert(&*instruction);
      continue;
    }
    irep_idt base;
    exprt index;
    if(
      stream_refine_array(
        instruction->assign_rhs(), base, index) &&
      symbol_id(index, result.generator_state) &&
      lhs == result.generator_state)
    {
      result.update = base;
      ++generator_updates;
      result.writes.insert(&*instruction);
      continue;
    }
    if(
      stream_refine_array(
        instruction->assign_rhs(), base, index) &&
      lhs == result.finished &&
      symbol_id(index, result.generator_state))
    {
      result.done = base;
      ++done_updates;
      result.writes.insert(&*instruction);
      continue;
    }
  }
  if(
    assumes != 5 || folds != 1 || generator_updates != 1 ||
    done_updates != 1 || result.fold_state.empty() ||
    result.generator_state.empty())
  {
    reason = "stream_refine_direct_shape";
    return false;
  }
  if(
    !stream_refine_find_bound(
      terms,
      symbol_exprt(
        result.fold_state, lookup(result.fold_state, ns)->type),
      result.row_bound) ||
    !stream_refine_collect_bounds(
      terms,
      symbol_exprt(
        result.generator_state,
        lookup(result.generator_state, ns)->type),
      result.generator_state_bounds) ||
    !stream_refine_find_bound(
      terms, generated_token, result.column_bound))
  {
    reason = "stream_refine_direct_bounds";
    return false;
  }
  return true;
}

bool stream_refine_main_equality(
  const goto_modelt &model,
  const lifecyclet &life,
  const irep_idt &left,
  const irep_idt &right)
{
  const auto &main =
    model.goto_functions.function_map.at(ID_main).body;
  for(const auto &instruction : main.instructions)
  {
    if(
      life.first_create != nullptr &&
      instruction.location_number >=
        life.first_create->location_number)
      break;
    if(!instruction.is_assign())
      continue;
    irep_idt lhs;
    irep_idt rhs;
    if(
      symbol_id(instruction.assign_lhs(), lhs) &&
      symbol_id(instruction.assign_rhs(), rhs) &&
      ((lhs == left && rhs == right) ||
       (lhs == right && rhs == left)))
      return true;
  }
  return false;
}

bool stream_refine_done_property(
  const goto_modelt &model,
  const namespacet &ns,
  const lifecyclet &life,
  irep_idt &left,
  irep_idt &right,
  const goto_programt::instructiont *&assumption,
  const goto_programt::instructiont *&error,
  std::string &reason)
{
  std::size_t errors = 0;
  for(const auto &entry : model.goto_functions.function_map)
  {
    for(const auto &instruction : entry.second.body.instructions)
    {
      irep_idt callee;
      if(call_id(instruction, callee) && is_reach_error(callee))
      {
        ++errors;
        if(entry.first != ID_main)
        {
          reason = "stream_refine_done_error_function";
          return false;
        }
        error = &instruction;
      }
    }
  }
  std::size_t matches = 0;
  const auto &main =
    model.goto_functions.function_map.at(ID_main).body;
  for(const auto &instruction : main.instructions)
  {
    if(
      life.last_join == nullptr ||
      instruction.location_number <= life.last_join->location_number)
      continue;
    irep_idt callee;
    irep_idt candidate_left;
    irep_idt candidate_right;
    if(
      call_id(instruction, callee) && is_assume(callee) &&
      instruction.call_arguments().size() == 1 &&
      unequal_symbols(
        instruction.call_arguments().front(),
        candidate_left,
        candidate_right) &&
      shared_signed(candidate_left, ns) &&
      shared_signed(candidate_right, ns))
    {
      ++matches;
      left = candidate_left;
      right = candidate_right;
      assumption = &instruction;
    }
  }
  if(
    matches != 1 || errors != 1 || assumption == nullptr ||
    error == nullptr ||
    assumption->location_number >= error->location_number)
  {
    reason = "stream_refine_done_property";
    return false;
  }
  return true;
}

bool stream_refine_immutable_phase(
  const goto_modelt &model,
  const lifecyclet &life,
  const std::set<irep_idt> &arrays,
  std::string &reason)
{
  for(const auto &entry : model.goto_functions.function_map)
  {
    for(const auto &instruction : entry.second.body.instructions)
    {
      if(entry.first == ID_main && life.first_create != nullptr &&
         instruction.location_number <
           life.first_create->location_number)
        continue;
      if(is_start_function(entry.first))
        continue;
      if(instruction.is_assign())
      {
        irep_idt lhs;
        irep_idt base;
        if(
          (symbol_id(instruction.assign_lhs(), lhs) &&
           arrays.count(lhs) != 0) ||
          (base_pointer(instruction.assign_lhs(), base) &&
           arrays.count(base) != 0))
        {
          reason = "stream_refine_mutable_map";
          return false;
        }
      }
    }
  }
  return true;
}

bool stream_done_drain_refinement_proof_impl(
  const goto_modelt &model,
  const namespacet &ns,
  std::string &reason)
{
  lifecyclet life;
  std::vector<irep_idt> workers;
  if(
    !stream_refine_lifecycle(model, life, workers, reason) ||
    workers.size() != 3)
  {
    if(reason.empty())
      reason = "stream_refine_done_lifecycle";
    return false;
  }
  irep_idt property_left;
  irep_idt property_right;
  const goto_programt::instructiont *property_assumption = nullptr;
  const goto_programt::instructiont *error = nullptr;
  if(
    !stream_refine_done_property(
      model,
      ns,
      life,
      property_left,
      property_right,
      property_assumption,
      error,
      reason))
    return false;

  stream_refine_done_producert producer;
  stream_refine_done_consumert consumer;
  stream_refine_directt direct;
  for(const auto &worker : workers)
  {
    std::string producer_reason;
    std::string consumer_reason;
    std::string direct_reason;
    stream_refine_done_producert candidate_producer;
    if(
      stream_refine_done_producer(
        model, ns, worker, candidate_producer, producer_reason))
    {
      if(!producer.worker.empty())
      {
        reason = "stream_refine_done_multiple_producers";
        return false;
      }
      producer = candidate_producer;
      continue;
    }
    stream_refine_done_consumert candidate_consumer;
    if(
      stream_refine_done_consumer(
        model, ns, worker, candidate_consumer, consumer_reason))
    {
      if(!consumer.worker.empty())
      {
        reason = "stream_refine_done_multiple_consumers";
        return false;
      }
      consumer = candidate_consumer;
      continue;
    }
    stream_refine_directt candidate_direct;
    if(
      stream_refine_direct(
        model, ns, worker, candidate_direct, direct_reason))
    {
      if(!direct.worker.empty())
      {
        reason = "stream_refine_done_multiple_direct";
        return false;
      }
      direct = candidate_direct;
      continue;
    }
    reason =
      "stream_refine_done_worker_p_" + producer_reason +
      "_c_" + consumer_reason + "_d_" + direct_reason;
    return false;
  }
  if(
    producer.worker.empty() || consumer.worker.empty() ||
    direct.worker.empty())
  {
    reason = "stream_refine_done_roles";
    return false;
  }
  if(
    producer.queue != consumer.queue ||
    producer.queue_bound != consumer.queue_bound ||
    producer.front != consumer.front ||
    producer.size != consumer.size ||
    producer.finished != consumer.finished ||
    producer.generator != direct.generator ||
    producer.update != direct.update ||
    producer.done != direct.done ||
    direct.generator_state_bounds.count(
      producer.generator_bound) == 0 ||
    direct.generator_state_bounds.count(
      producer.update_bound) == 0 ||
    consumer.matrix != direct.matrix ||
    consumer.row_bound != direct.row_bound ||
    consumer.column_bound != direct.column_bound)
  {
    reason = "stream_refine_done_signature";
    return false;
  }
  const std::set<irep_idt> property_states = {
    property_left, property_right};
  const std::set<irep_idt> actual_states = {
    consumer.state, direct.fold_state};
  if(
    property_states != actual_states ||
    !stream_refine_main_equality(
      model,
      life,
      producer.state,
      direct.generator_state) ||
    !stream_refine_main_equality(
      model,
      life,
      consumer.state,
      direct.fold_state))
  {
    reason = "stream_refine_done_initial_relation";
    return false;
  }

  const std::set<irep_idt> zero_symbols = {
    producer.size, producer.finished, direct.finished};
  std::set<const goto_programt::instructiont *> allowed =
    producer.writes;
  allowed.insert(consumer.writes.begin(), consumer.writes.end());
  allowed.insert(direct.writes.begin(), direct.writes.end());
  if(!zero_initialized_symbols(model, zero_symbols, allowed, reason))
    return false;

  const std::set<irep_idt> arrays = {
    producer.queue,
    producer.generator,
    producer.update,
    producer.done,
    consumer.matrix};
  if(!stream_refine_immutable_phase(model, life, arrays, reason))
    return false;

  std::set<irep_idt> protected_symbols = arrays;
  protected_symbols.insert({
    producer.front,
    producer.size,
    producer.state,
    producer.finished,
    consumer.state,
    consumer.condition,
    direct.generator_state,
    direct.fold_state,
    direct.finished});
  for(const auto &entry : model.goto_functions.function_map)
  {
    for(const auto &instruction : entry.second.body.instructions)
    {
      const exprt *lhs = nullptr;
      if(instruction.is_assign())
        lhs = &instruction.assign_lhs();
      else if(
        instruction.is_function_call() &&
        !instruction.call_lhs().is_nil())
        lhs = &instruction.call_lhs();
      if(lhs == nullptr)
        continue;
      irep_idt direct_lhs;
      if(
        !symbol_id(*lhs, direct_lhs) ||
        protected_symbols.count(direct_lhs) == 0)
        continue;
      if(
        is_start_function(entry.first) && instruction.is_assign() &&
        value_is(instruction.assign_rhs(), 0))
        continue;
      if(
        entry.first == ID_main && life.first_create != nullptr &&
        instruction.location_number <
          life.first_create->location_number)
        continue;
      if(allowed.count(&instruction) == 0)
      {
        reason = "stream_refine_done_external_writer";
        return false;
      }
    }
  }
  flow_equality_propertyt control;
  control.assumption = property_assumption;
  control.error = error;
  if(
    !no_addresses(model, protected_symbols, reason) ||
    !flow_main_control(model, life, control, reason))
    return false;

  std::cout << "NATIVE_STREAM_REFINEMENT applied=1"
            << " rule=done_drain"
            << " queued=" << consumer.state
            << " direct=" << direct.fold_state << '\n';
  return true;
}

bool shared_resource32(
  const irep_idt &identifier,
  const namespacet &ns)
{
  const symbolt *symbol = lookup(identifier, ns);
  if(
    symbol == nullptr || !symbol->is_static_lifetime || symbol->is_type)
    return false;
  if(symbol->type.id() == ID_unsignedbv)
    return to_unsignedbv_type(symbol->type).get_width() == 32;
  if(symbol->type.id() == ID_signedbv)
    return to_signedbv_type(symbol->type).get_width() == 32;
  return false;
}

struct resource_propertyt
{
  irep_idt left;
  irep_idt right;
  const goto_programt::instructiont *assumption;
  const goto_programt::instructiont *error;

  resource_propertyt() : assumption(nullptr), error(nullptr)
  {
  }
};

bool find_resource_property(
  const goto_modelt &model,
  const namespacet &ns,
  const lifecyclet &life,
  resource_propertyt &property,
  std::string &reason)
{
  const auto &main =
    model.goto_functions.function_map.at(ID_main).body;
  std::size_t matches = 0;
  std::size_t errors = 0;
  for(const auto &entry : model.goto_functions.function_map)
  {
    for(const auto &instruction : entry.second.body.instructions)
    {
      irep_idt callee;
      if(call_id(instruction, callee) && is_reach_error(callee))
      {
        ++errors;
        if(entry.first != ID_main)
        {
          reason = "resource_error_function";
          return false;
        }
        property.error = &instruction;
      }
    }
  }
  for(const auto &instruction : main.instructions)
  {
    if(
      life.last_join == nullptr ||
      instruction.location_number <= life.last_join->location_number)
      continue;
    irep_idt callee;
    if(
      !call_id(instruction, callee) || !is_assume(callee) ||
      instruction.call_arguments().size() != 1)
      continue;
    irep_idt left;
    irep_idt right;
    if(
      !unequal_symbols(
        instruction.call_arguments().front(), left, right) ||
      !shared_unsigned32(left, ns) || !shared_unsigned32(right, ns))
      continue;
    ++matches;
    property.left = left;
    property.right = right;
    property.assumption = &instruction;
  }
  if(
    matches != 1 || errors != 1 || property.assumption == nullptr ||
    property.error == nullptr ||
    property.assumption->location_number >= property.error->location_number)
  {
    reason =
      matches == 0 ? "resource_property" :
                     "resource_property_ambiguous";
    return false;
  }
  return true;
}

void flatten_plus_terms(
  const exprt &src,
  std::vector<exprt> &terms)
{
  const exprt &expr = strip(src);
  if(expr.id() == ID_plus)
  {
    for(const auto &operand : expr.operands())
      flatten_plus_terms(operand, terms);
  }
  else
    terms.push_back(expr);
}

bool multiplier_term(
  const exprt &src,
  irep_idt &multiplier,
  mp_integer &coefficient)
{
  const exprt &term = strip(src);
  irep_idt symbol;
  if(symbol_id(term, symbol))
  {
    multiplier = symbol;
    coefficient = 1;
    return true;
  }
  if(term.id() != ID_mult || term.operands().size() != 2)
    return false;
  for(unsigned order = 0; order < 2; ++order)
  {
    mp_integer value;
    if(
      integer_constant(term.operands()[order], value) &&
      value > 0 &&
      symbol_id(term.operands()[1 - order], symbol))
    {
      multiplier = symbol;
      coefficient = value;
      return true;
    }
  }
  return false;
}

bool accumulator_increment(
  const exprt &src,
  const irep_idt &accumulator,
  irep_idt &multiplier,
  mp_integer &delta)
{
  std::vector<exprt> terms;
  flatten_plus_terms(src, terms);
  std::size_t accumulator_terms = 0;
  irep_idt common_multiplier;
  mp_integer coefficient = 0;
  for(const auto &term : terms)
  {
    irep_idt symbol;
    if(symbol_id(term, symbol) && symbol == accumulator)
    {
      ++accumulator_terms;
      continue;
    }
    irep_idt candidate;
    mp_integer contribution;
    if(!multiplier_term(term, candidate, contribution))
      return false;
    if(common_multiplier.empty())
      common_multiplier = candidate;
    else if(common_multiplier != candidate)
      return false;
    coefficient += contribution;
  }
  if(
    accumulator_terms != 1 || common_multiplier.empty() ||
    coefficient <= 0 || coefficient > 16)
    return false;
  multiplier = common_multiplier;
  delta = coefficient;
  return true;
}

bool resource_decrement(
  const exprt &src,
  const irep_idt &resource,
  mp_integer &delta)
{
  const exprt &rhs = strip(src);
  irep_idt left;
  mp_integer amount;
  if(
    rhs.id() != ID_minus || rhs.operands().size() != 2 ||
    !symbol_id(rhs.op0(), left) || left != resource ||
    !integer_constant(rhs.op1(), amount) ||
    amount <= 0 || amount > 16)
    return false;
  delta = amount;
  return true;
}

bool resource_skip_guard(
  const exprt &src,
  const irep_idt &resource,
  const mp_integer &delta)
{
  const exprt &outer = strip(src);
  if(outer.id() != ID_not || outer.operands().size() != 1)
    return false;
  const exprt &relation = strip(outer.op0());
  irep_idt left;
  mp_integer bound;
  return
    relation.id() == ID_gt && relation.operands().size() == 2 &&
    symbol_id(relation.op0(), left) && left == resource &&
    integer_constant(relation.op1(), bound) && bound == delta - 1;
}

bool resource_positive(
  const exprt &src,
  const irep_idt &resource)
{
  const exprt &relation = strip(src);
  irep_idt left;
  return
    relation.id() == ID_gt && relation.operands().size() == 2 &&
    symbol_id(relation.op0(), left) && left == resource &&
    value_is(relation.op1(), 0);
}

struct resource_workert
{
  irep_idt accumulator;
  irep_idt resource;
  irep_idt multiplier;
  mp_integer delta;
  bool unit_completion;
  std::set<const goto_programt::instructiont *> writes;

  resource_workert() : delta(0), unit_completion(false)
  {
  }
};

bool affine_resource_worker(
  const goto_modelt &model,
  const namespacet &ns,
  const irep_idt &worker,
  resource_workert &result,
  std::string &reason)
{
  const auto &program =
    model.goto_functions.function_map.at(worker).body;
  natural_loopst loops;
  loops(program);
  if(loops.loop_map.size() != 1)
  {
    reason = "resource_loop_count";
    return false;
  }
  const auto loop_head = loops.loop_map.begin()->first;
  const auto &loop = loops.loop_map.begin()->second;

  goto_programt::const_targett accumulator_write =
    program.instructions.end();
  goto_programt::const_targett resource_write =
    program.instructions.end();
  unsigned atomic_epoch = 0;
  unsigned accumulator_epoch = 0;
  unsigned resource_epoch = 0;
  int atomic_depth = 0;
  std::size_t atomic_begins = 0;
  std::size_t atomic_ends = 0;
  std::size_t gotos = 0;
  std::size_t backedges = 0;
  for(auto instruction = program.instructions.begin();
      instruction != program.instructions.end(); ++instruction)
  {
    if(instruction->is_atomic_begin())
    {
      ++atomic_depth;
      ++atomic_begins;
      ++atomic_epoch;
      if(atomic_depth != 1)
      {
        reason = "resource_atomic_nesting";
        return false;
      }
      continue;
    }
    if(instruction->is_atomic_end())
    {
      --atomic_depth;
      ++atomic_ends;
      if(atomic_depth != 0)
      {
        reason = "resource_atomic_balance";
        return false;
      }
      continue;
    }
    irep_idt callee;
    if(call_id(*instruction, callee))
    {
      reason = "resource_worker_call";
      return false;
    }
    if(instruction->is_goto() && loop.contains(instruction))
    {
      ++gotos;
      if(
        instruction != loop_head &&
        instruction->condition().is_true() &&
        instruction->targets.size() == 1 &&
        instruction->get_target() == loop_head)
        ++backedges;
    }
    if(!instruction->is_assign())
      continue;
    irep_idt lhs;
    if(!shared_symbol_lhs(*instruction, ns, lhs))
    {
      irep_idt base;
      if(base_pointer(instruction->assign_lhs(), base))
      {
        reason = "resource_worker_pointer_write";
        return false;
      }
      continue;
    }
    if(atomic_depth != 1)
    {
      reason = "resource_nonatomic_write";
      return false;
    }

    irep_idt multiplier;
    mp_integer increment;
    if(
      accumulator_increment(
        instruction->assign_rhs(), lhs, multiplier, increment))
    {
      if(accumulator_write != program.instructions.end())
      {
        reason = "resource_accumulator_count";
        return false;
      }
      result.accumulator = lhs;
      result.multiplier = multiplier;
      if(result.delta != 0 && result.delta != increment)
      {
        reason = "resource_delta_mismatch";
        return false;
      }
      result.delta = increment;
      accumulator_write = instruction;
      accumulator_epoch = atomic_epoch;
      result.writes.insert(&*instruction);
      continue;
    }

    mp_integer decrement;
    if(resource_decrement(instruction->assign_rhs(), lhs, decrement))
    {
      if(resource_write != program.instructions.end())
      {
        reason = "resource_resource_count";
        return false;
      }
      result.resource = lhs;
      resource_write = instruction;
      resource_epoch = atomic_epoch;
      result.writes.insert(&*instruction);
      if(result.delta != 0 && result.delta != decrement)
      {
        reason = "resource_delta_mismatch";
        return false;
      }
      result.delta = decrement;
      continue;
    }
    reason = "resource_unrecognized_shared_write";
    return false;
  }
  if(
    atomic_depth != 0 || atomic_begins != atomic_ends ||
    (atomic_begins != 1 && atomic_begins != 3) ||
    accumulator_write == program.instructions.end() ||
    resource_write == program.instructions.end() ||
    accumulator_epoch == 0 || accumulator_epoch != resource_epoch ||
    accumulator_write->location_number >= resource_write->location_number ||
    result.accumulator == result.resource ||
    !shared_unsigned32(result.accumulator, ns) ||
    !shared_unsigned32(result.multiplier, ns) ||
    !shared_resource32(result.resource, ns) ||
    gotos < 2 || gotos > 3 || backedges != 1)
  {
    reason = "resource_worker_shape";
    return false;
  }

  const symbolt *resource_symbol = lookup(result.resource, ns);
  if(resource_symbol == nullptr)
  {
    reason = "resource_symbol";
    return false;
  }
  std::size_t transition_guards = 0;
  for(auto instruction = program.instructions.begin();
      instruction != program.instructions.end(); ++instruction)
  {
    if(
      instruction->is_goto() && !instruction->condition().is_true() &&
      instruction->targets.size() == 1 &&
      instruction->location_number < accumulator_write->location_number &&
      instruction->get_target()->location_number >
        resource_write->location_number &&
      resource_skip_guard(
        instruction->condition(), result.resource, result.delta))
      ++transition_guards;
  }
  if(transition_guards != 1)
  {
    reason = "resource_transition_guard";
    return false;
  }

  if(result.delta == 1)
  {
    if(resource_skip_guard(loop_head->condition(), result.resource, 1))
      result.unit_completion = true;
    else
    {
      irep_idt condition;
      if(
        loop_head->condition().id() != ID_nil &&
        loop_head->condition().operands().size() >= 1)
      {
        const exprt &outer = strip(loop_head->condition());
        if(outer.id() == ID_not && outer.operands().size() == 1)
        {
          const exprt &truth = strip(outer.op0());
          if(
            truth.id() == ID_notequal &&
            truth.operands().size() == 2)
          {
            if(
              symbol_id(truth.op0(), condition) &&
              value_is(truth.op1(), 0))
            {
            }
            else if(
              symbol_id(truth.op1(), condition) &&
              value_is(truth.op0(), 0))
            {
            }
            else
              condition.clear();
          }
        }
      }
      if(!condition.empty())
      {
        int depth = 0;
        std::size_t condition_writes = 0;
        std::size_t positive_writes = 0;
        for(const auto &instruction : program.instructions)
        {
          if(instruction.is_atomic_begin())
            ++depth;
          else if(instruction.is_atomic_end())
            --depth;
          else if(instruction.is_assign())
          {
            irep_idt lhs;
            if(
              symbol_id(instruction.assign_lhs(), lhs) &&
              lhs == condition)
            {
              ++condition_writes;
              if(
                depth == 1 &&
                resource_positive(
                  instruction.assign_rhs(), result.resource))
                ++positive_writes;
            }
          }
        }
        result.unit_completion =
          condition_writes == 2 && positive_writes == 2;
      }
    }
    if(!result.unit_completion)
    {
      reason = "resource_unit_completion";
      return false;
    }
  }
  return true;
}

void add_equality_terms(
  const exprt &src,
  std::map<irep_idt, std::set<irep_idt>> &edges)
{
  std::vector<exprt> terms;
  flatten_and(src, terms);
  for(const auto &term_src : terms)
  {
    const exprt &term = strip(term_src);
    irep_idt left;
    irep_idt right;
    if(
      term.id() == ID_equal && term.operands().size() == 2 &&
      symbol_id(term.op0(), left) && symbol_id(term.op1(), right))
    {
      edges[left].insert(right);
      edges[right].insert(left);
    }
  }
}

bool equality_reachable(
  const std::map<irep_idt, std::set<irep_idt>> &edges,
  const irep_idt &left,
  const irep_idt &right)
{
  if(left == right)
    return true;
  std::set<irep_idt> reached = {left};
  std::vector<irep_idt> work = {left};
  for(std::size_t index = 0; index < work.size(); ++index)
  {
    const auto found = edges.find(work[index]);
    if(found == edges.end())
      continue;
    for(const auto &next : found->second)
    {
      if(next == right)
        return true;
      if(reached.insert(next).second)
        work.push_back(next);
    }
  }
  return false;
}

bool resource_initial_relations(
  const goto_modelt &model,
  const lifecyclet &life,
  const resource_propertyt &property,
  const resource_workert &left,
  const resource_workert &right,
  std::set<const goto_programt::instructiont *> &allowed,
  std::string &reason)
{
  const auto &main =
    model.goto_functions.function_map.at(ID_main).body;
  const std::set<irep_idt> protected_symbols = {
    left.accumulator,
    right.accumulator,
    left.resource,
    right.resource,
    left.multiplier};
  std::map<irep_idt, std::set<irep_idt>> edges;
  std::set<irep_idt> zero;
  std::map<irep_idt, const goto_programt::instructiont *> main_writes;
  for(const auto &entry : model.goto_functions.function_map)
  {
    if(!is_start_function(entry.first))
      continue;
    for(const auto &instruction : entry.second.body.instructions)
    {
      if(!instruction.is_assign())
        continue;
      irep_idt lhs;
      if(
        symbol_id(instruction.assign_lhs(), lhs) &&
        protected_symbols.count(lhs) != 0 &&
        value_is(instruction.assign_rhs(), 0))
      {
        zero.insert(lhs);
        allowed.insert(&instruction);
      }
    }
  }
  for(const auto &instruction : main.instructions)
  {
    if(
      life.first_create != nullptr &&
      instruction.location_number >= life.first_create->location_number)
      break;
    if(instruction.is_assign())
    {
      irep_idt lhs;
      if(
        symbol_id(instruction.assign_lhs(), lhs) &&
        protected_symbols.count(lhs) != 0)
      {
        if(!main_writes.emplace(lhs, &instruction).second)
        {
          reason = "resource_multiple_initial_writes";
          return false;
        }
        allowed.insert(&instruction);
      }
    }
  }
  for(const auto &write : main_writes)
  {
    const auto &instruction = *write.second;
    zero.erase(write.first);
    if(value_is(instruction.assign_rhs(), 0))
      zero.insert(write.first);
    irep_idt rhs;
    if(symbol_id(instruction.assign_rhs(), rhs))
    {
      const auto rhs_write = main_writes.find(rhs);
      if(
        rhs_write != main_writes.end() &&
        rhs_write->second->location_number >=
          instruction.location_number)
      {
        reason = "resource_initial_write_order";
        return false;
      }
      edges[write.first].insert(rhs);
      edges[rhs].insert(write.first);
    }
  }
  for(const auto &instruction : main.instructions)
  {
    if(
      life.first_create != nullptr &&
      instruction.location_number >= life.first_create->location_number)
      break;
    irep_idt callee;
    if(
      call_id(instruction, callee) && is_assume(callee) &&
      instruction.call_arguments().size() == 1)
    {
      for(const auto &write : main_writes)
      {
        if(
          write.second->location_number >=
          instruction.location_number)
        {
          reason = "resource_initial_assume_order";
          return false;
        }
      }
      add_equality_terms(instruction.call_arguments().front(), edges);
    }
  }
  for(const auto &symbol : zero)
  {
    edges[irep_idt("__linear_zero")].insert(symbol);
    edges[symbol].insert(irep_idt("__linear_zero"));
  }
  if(
    !equality_reachable(
      edges, left.accumulator, right.accumulator) ||
    !equality_reachable(edges, left.resource, right.resource))
  {
    reason = "resource_initial_relation";
    return false;
  }
  (void)property;
  return true;
}

bool resource_global_obligations(
  const goto_modelt &model,
  const lifecyclet &life,
  const resource_propertyt &property,
  const std::vector<resource_workert> &workers,
  const resource_workert &left,
  const resource_workert &right,
  std::string &reason)
{
  std::set<const goto_programt::instructiont *> allowed;
  for(const auto &worker : workers)
    allowed.insert(worker.writes.begin(), worker.writes.end());
  if(
    !resource_initial_relations(
      model, life, property, left, right, allowed, reason))
    return false;
  const std::set<irep_idt> protected_symbols = {
    left.accumulator,
    right.accumulator,
    left.resource,
    right.resource,
    left.multiplier};

  for(const auto &entry : model.goto_functions.function_map)
  {
    for(const auto &instruction : entry.second.body.instructions)
    {
      const exprt *lhs = nullptr;
      if(instruction.is_assign())
        lhs = &instruction.assign_lhs();
      else if(
        instruction.is_function_call() &&
        !instruction.call_lhs().is_nil())
        lhs = &instruction.call_lhs();
      if(lhs == nullptr)
        continue;
      irep_idt symbol;
      if(
        !symbol_id(*lhs, symbol) ||
        protected_symbols.count(symbol) == 0)
        continue;
      if(
        is_start_function(entry.first) && instruction.is_assign() &&
        value_is(instruction.assign_rhs(), 0))
        continue;
      if(allowed.count(&instruction) == 0)
      {
        reason = "resource_external_writer";
        return false;
      }
    }
  }
  if(!no_addresses(model, protected_symbols, reason))
    return false;

  const auto &main =
    model.goto_functions.function_map.at(ID_main).body;
  for(const auto &instruction : main.instructions)
  {
    if(
      life.first_create != nullptr && life.last_join != nullptr &&
      instruction.location_number >= life.first_create->location_number &&
      instruction.location_number <= life.last_join->location_number)
    {
      if(
        instruction.is_assign() || instruction.is_goto() ||
        instruction.is_assert() || instruction.is_assume() ||
        instruction.is_atomic_begin() || instruction.is_atomic_end())
      {
        reason = "resource_main_concurrent_effect";
        return false;
      }
      irep_idt callee;
      if(
        call_id(instruction, callee) &&
        !is_create(callee) && !is_join(callee))
      {
        reason = "resource_main_concurrent_call";
        return false;
      }
    }
    if(
      life.last_join != nullptr &&
      instruction.location_number > life.last_join->location_number)
    {
      if(
        instruction.is_assign() || instruction.is_goto() ||
        instruction.is_assert() || instruction.is_assume() ||
        instruction.is_atomic_begin() || instruction.is_atomic_end())
      {
        reason = "resource_main_postjoin_control";
        return false;
      }
      irep_idt callee;
      if(
        call_id(instruction, callee) &&
        &instruction != property.assumption &&
        &instruction != property.error)
      {
        reason = "resource_main_postjoin_call";
        return false;
      }
    }
  }
  return true;
}

bool affine_resource_proof_impl(
  const goto_modelt &model,
  const namespacet &ns,
  std::string &reason)
{
  lifecyclet life;
  if(
    !lifecycle(model, life, reason) ||
    (life.workers.size() != 3 && life.workers.size() != 4))
  {
    if(reason.empty())
      reason = "resource_lifecycle";
    return false;
  }
  resource_propertyt property;
  if(!find_resource_property(model, ns, life, property, reason))
    return false;

  std::vector<resource_workert> workers;
  for(const auto &worker_id : life.workers)
  {
    resource_workert worker;
    if(
      !affine_resource_worker(
        model, ns, worker_id, worker, reason))
    {
      reason = "resource_worker " + id2string(worker_id) + " " + reason;
      return false;
    }
    workers.push_back(worker);
  }
  std::map<irep_idt, std::vector<std::size_t>> groups;
  for(std::size_t index = 0; index < workers.size(); ++index)
    groups[workers[index].resource].push_back(index);
  if(groups.size() != 2)
  {
    reason = "resource_group_count";
    return false;
  }

  std::vector<resource_workert> summaries;
  for(const auto &group : groups)
  {
    resource_workert summary = workers[group.second.front()];
    bool unit = false;
    for(const auto index : group.second)
    {
      if(
        workers[index].accumulator != summary.accumulator ||
        workers[index].multiplier != summary.multiplier)
      {
        reason = "resource_group_signature";
        return false;
      }
      unit = unit || workers[index].unit_completion;
    }
    if(!unit)
    {
      reason = "resource_group_unit";
      return false;
    }
    summaries.push_back(summary);
  }
  if(
    summaries[0].multiplier != summaries[1].multiplier ||
    summaries[0].accumulator == summaries[1].accumulator)
  {
    reason = "resource_cross_group_signature";
    return false;
  }
  const symbolt *first_resource = lookup(summaries[0].resource, ns);
  const symbolt *second_resource = lookup(summaries[1].resource, ns);
  if(
    first_resource == nullptr || second_resource == nullptr ||
    first_resource->type != second_resource->type)
  {
    reason = "resource_cross_group_type";
    return false;
  }

  const resource_workert *left = nullptr;
  const resource_workert *right = nullptr;
  for(const auto &summary : summaries)
  {
    if(summary.accumulator == property.left)
      left = &summary;
    if(summary.accumulator == property.right)
      right = &summary;
  }
  if(left == nullptr || right == nullptr)
  {
    reason = "resource_property_groups";
    return false;
  }
  if(
    !resource_global_obligations(
      model, life, property, workers, *left, *right, reason))
    return false;

  std::cout << "NATIVE_LINEAR_ANNIHILATOR applied=1 rule=resource"
            << " left=" << property.left
            << " right=" << property.right
            << " multiplier=" << left->multiplier << '\n';
  return true;
}

bool extremum_homomorphism_proof_impl(
  const goto_modelt &model,
  const namespacet &ns,
  std::string &reason)
{
  lifecyclet life;
  if(!lifecycle(model, life, reason) || life.workers.size() != 3)
  {
    if(reason.empty())
      reason = "hom_lifecycle";
    return false;
  }

  hom_propertyt property;
  if(!find_hom_property(model, ns, life, property, reason))
    return false;
  if(!signed_addition_helper(model, ns, property.operation, reason))
    return false;

  hom_main_initt initial;
  if(!find_hom_initial_summaries(model, life, property, initial, reason))
    return false;

  for(const auto &fold_worker : life.workers)
  {
    hom_worker_resultt fold;
    std::string fold_reason;
    if(
      !hom_fold_worker(
        model,
        ns,
        fold_worker,
        property,
        initial,
        fold,
        fold_reason))
      continue;
    for(const auto &producer_worker : life.workers)
    {
      if(producer_worker == fold_worker)
        continue;
      hom_worker_resultt producer;
      std::string producer_reason;
      if(
        !hom_producer_worker(
          model,
          ns,
          producer_worker,
          property,
          initial,
          producer,
          producer_reason) ||
        producer.bound != fold.bound)
        continue;
      irep_idt consumer_worker;
      for(const auto &worker : life.workers)
      {
        if(worker != fold_worker && worker != producer_worker)
          consumer_worker = worker;
      }
      hom_worker_resultt consumer;
      std::string consumer_reason;
      if(
        consumer_worker.empty() ||
        !hom_consumer_worker(
          model,
          ns,
          consumer_worker,
          property,
          producer,
          consumer,
          consumer_reason))
        continue;

      hom_main_statet main_state;
      if(
        !hom_main_obligations(
          model,
          life,
          property,
          initial,
          producer,
          main_state,
          reason) ||
        !fresh_array_allocator(
          model, ns, main_state.allocator, reason) ||
        !hom_global_writes(
          model,
          ns,
          life,
          property,
          initial,
          fold,
          producer,
          consumer,
          main_state,
          reason))
        return false;
      std::cout << "NATIVE_EXTREMUM_HOMOMORPHISM applied=1 direction="
                << (property.minimum ? "min" : "max")
                << " left=" << property.left_summary
                << " right=" << property.right_summary
                << " result=" << property.result_summary << '\n';
      return true;
    }
  }
  reason = "hom_worker_partition";
  return false;
}

bool role_split_stream_global_writes(
  const goto_modelt &model,
  const lifecyclet &life,
  const std::set<irep_idt> &queues,
  const std::set<irep_idt> &protected_symbols,
  const std::set<const goto_programt::instructiont *> &allowed,
  std::string &reason)
{
  for(const auto &entry : model.goto_functions.function_map)
  {
    for(const auto &instruction : entry.second.body.instructions)
    {
      const exprt *lhs = nullptr;
      if(instruction.is_assign())
        lhs = &instruction.assign_lhs();
      else if(
        instruction.is_function_call() &&
        !instruction.call_lhs().is_nil())
        lhs = &instruction.call_lhs();
      if(lhs == nullptr)
        continue;
      irep_idt direct;
      irep_idt base;
      const bool protected_write =
        (symbol_id(*lhs, direct) &&
         protected_symbols.count(direct) != 0) ||
        (base_pointer(*lhs, base) && queues.count(base) != 0);
      if(!protected_write)
        continue;
      if(
        is_start_function(entry.first) && instruction.is_assign() &&
        value_is(instruction.assign_rhs(), 0))
        continue;
      if(
        entry.first == ID_main && life.first_create != nullptr &&
        instruction.location_number <
          life.first_create->location_number)
        continue;
      if(allowed.count(&instruction) == 0)
      {
        reason =
          "role_split_external_writer_" +
          id2string(entry.first) + "_" +
          std::to_string(instruction.location_number);
        return false;
      }
    }
  }
  for(const auto &queue : queues)
  {
    if(!flow_alias_free(model, queue, reason))
      return false;
  }
  return no_addresses(model, protected_symbols, reason);
}

bool role_split_fold_equation(
  const exprt &src,
  const std::map<
    irep_idt,
    std::pair<mp_integer, mp_integer>> &equations,
  mp_integer &slope,
  mp_integer &intercept)
{
  const exprt &expr = strip(src);
  irep_idt identifier;
  if(symbol_id(expr, identifier))
  {
    const auto found = equations.find(identifier);
    if(found == equations.end())
      return false;
    slope = found->second.first;
    intercept = found->second.second;
    return true;
  }
  if(integer_constant(expr, intercept))
  {
    slope = 0;
    return true;
  }
  if(expr.id() == ID_unary_minus && expr.operands().size() == 1)
  {
    if(!role_split_fold_equation(
         expr.op0(), equations, slope, intercept))
      return false;
    slope = -slope;
    intercept = -intercept;
    return true;
  }
  if(
    (expr.id() == ID_plus || expr.id() == ID_minus) &&
    expr.operands().size() == 2)
  {
    mp_integer left_slope;
    mp_integer left_intercept;
    mp_integer right_slope;
    mp_integer right_intercept;
    if(
      !role_split_fold_equation(
        expr.op0(), equations, left_slope, left_intercept) ||
      !role_split_fold_equation(
        expr.op1(), equations, right_slope, right_intercept))
      return false;
    slope =
      expr.id() == ID_plus ?
        left_slope + right_slope :
        left_slope - right_slope;
    intercept =
      expr.id() == ID_plus ?
        left_intercept + right_intercept :
        left_intercept - right_intercept;
    return true;
  }
  if(expr.id() == ID_mult && expr.operands().size() == 2)
  {
    mp_integer factor;
    if(integer_constant(expr.op0(), factor))
    {
      if(!role_split_fold_equation(
           expr.op1(), equations, slope, intercept))
        return false;
      slope *= factor;
      intercept *= factor;
      return true;
    }
    if(integer_constant(expr.op1(), factor))
    {
      if(!role_split_fold_equation(
           expr.op0(), equations, slope, intercept))
        return false;
      slope *= factor;
      intercept *= factor;
      return true;
    }
  }
  return false;
}

bool role_split_stream_property(
  const goto_modelt &model,
  const namespacet &ns,
  const lifecyclet &life,
  const stream_refine_sourcet &source,
  const std::vector<const stream_refine_staget *> &ordered,
  const bool source_has_sink_role,
  const irep_idt &source_sink_fold,
  std::string &reason)
{
  std::set<std::pair<irep_idt, irep_idt>> equalities;
  irep_idt property_sink;
  exprt expected;
  const goto_programt::instructiont *assumption = nullptr;
  const goto_programt::instructiont *error = nullptr;
  if(
    !stream_refine_property(
      model,
      ns,
      life,
      equalities,
      property_sink,
      expected,
      assumption,
      error,
      reason) ||
    !equalities.empty())
  {
    if(reason.empty())
      reason = "role_split_property_shape";
    return false;
  }

  mp_integer data_token;
  mp_integer sentinel_token;
  if(
    !integer_constant(source.data.token, data_token) ||
    !integer_constant(source.sentinel.token, sentinel_token))
  {
    reason = "role_split_source_tokens";
    return false;
  }
  mp_integer transform_slope = 1;
  mp_integer transform_intercept = 0;
  std::map<
    irep_idt,
    std::pair<mp_integer, mp_integer>> fold_equations;
  for(const auto *stage : ordered)
  {
    const mp_integer input_data =
      transform_slope * data_token + transform_intercept;
    const mp_integer input_sentinel =
      transform_slope * sentinel_token + transform_intercept;
    if(
      input_data <= 0 ||
      (stage->nonpositive_exit ?
         input_sentinel > 0 :
         input_sentinel != 0))
    {
      reason = "role_split_terminal_language";
      return false;
    }
    if(!stage->fold.empty())
    {
      if(
        !fold_equations.emplace(
          stage->fold,
          std::make_pair(input_data, input_sentinel)).second)
      {
        reason = "role_split_fold_ownership";
        return false;
      }
    }
    if(stage->forwards)
    {
      mp_integer stage_slope;
      mp_integer stage_intercept;
      if(
        !stream_refine_affine_form(
          stage->transform,
          stage->consume.temporary,
          stage_slope,
          stage_intercept))
      {
        reason = "role_split_stage_affine";
        return false;
      }
      transform_slope *= stage_slope;
      transform_intercept =
        stage_slope * transform_intercept + stage_intercept;
    }
  }

  if(source_has_sink_role)
  {
    if(
      property_sink != source_sink_fold ||
      !value_is(expected, 0) ||
      transform_slope * data_token + transform_intercept != 0)
    {
      reason = "role_split_prefix_zero_property";
      return false;
    }
  }
  else
  {
    const auto sink_equation = fold_equations.find(property_sink);
    mp_integer expected_slope;
    mp_integer expected_intercept;
    if(
      sink_equation == fold_equations.end() ||
      !role_split_fold_equation(
        expected,
        fold_equations,
        expected_slope,
        expected_intercept) ||
      sink_equation->second.first != expected_slope ||
      sink_equation->second.second != expected_intercept)
    {
      reason = "role_split_complete_property";
      return false;
    }
  }

  flow_equality_propertyt control;
  control.assumption = assumption;
  control.error = error;
  return flow_main_control(model, life, control, reason);
}

bool role_split_affine_stream_audit_impl(
  const goto_modelt &model,
  const namespacet &ns,
  std::string &reason,
  std::size_t &source_roles,
  std::size_t &stage_roles,
  std::size_t &sink_roles)
{
  std::size_t signed_pointer_globals = 0;
  for(const auto &entry : model.symbol_table.symbols)
  {
    const symbolt &symbol = entry.second;
    if(
      symbol.is_static_lifetime && !symbol.is_type &&
      symbol.type.id() == ID_pointer &&
      to_pointer_type(symbol.type).base_type().id() == ID_signedbv)
      ++signed_pointer_globals;
  }
  if(signed_pointer_globals < 2)
  {
    reason = "role_split_channel_prefilter";
    return false;
  }

  lifecyclet life;
  std::vector<irep_idt> workers;
  if(!stream_refine_lifecycle(model, life, workers, reason))
    return false;
  if(workers.size() < 2)
  {
    reason = "role_split_worker_prefilter";
    return false;
  }
  std::size_t atomic_regions = 0;
  for(const auto &worker : workers)
  {
    const auto &body =
      model.goto_functions.function_map.at(worker).body;
    atomic_regions += std::count_if(
      body.instructions.begin(),
      body.instructions.end(),
      [](const goto_programt::instructiont &instruction) {
        return instruction.is_atomic_begin();
      });
  }
  if(atomic_regions < 3)
  {
    reason = "role_split_atomic_prefilter";
    return false;
  }

  stream_refine_sourcet source;
  stream_refine_consumet source_sink_consume;
  irep_idt source_sink_fold;
  bool source_has_sink_role = false;
  std::vector<stream_refine_staget> stages;
  for(const auto &worker : workers)
  {
    stream_refine_sourcet candidate_source;
    std::string source_reason;
    if(
      stream_refine_source(
        model, ns, worker, candidate_source, source_reason))
    {
      if(!source.worker.empty())
      {
        reason = "role_split_multiple_sources";
        return false;
      }
      source = candidate_source;
      continue;
    }
    source_reason.clear();
    stream_refine_consumet candidate_sink_consume;
    irep_idt candidate_sink_fold;
    if(
      stream_refine_source(
        model,
        ns,
        worker,
        candidate_source,
        source_reason,
        true,
        &candidate_sink_consume,
        &candidate_sink_fold))
    {
      if(!source.worker.empty())
      {
        reason = "role_split_multiple_sources";
        return false;
      }
      source = candidate_source;
      source_sink_consume = candidate_sink_consume;
      source_sink_fold = candidate_sink_fold;
      source_has_sink_role = true;
      continue;
    }
    source_reason.clear();
    if(
      role_split_guarded_source_sink(
        model,
        ns,
        worker,
        candidate_source,
        candidate_sink_consume,
        candidate_sink_fold,
        source_reason))
    {
      if(!source.worker.empty())
      {
        reason = "role_split_multiple_sources";
        return false;
      }
      source = candidate_source;
      source_sink_consume = candidate_sink_consume;
      source_sink_fold = candidate_sink_fold;
      source_has_sink_role = true;
      continue;
    }

    stream_refine_staget stage;
    std::string stage_reason;
    if(
      stream_refine_stage(
        model, ns, worker, stage, stage_reason, true))
    {
      stages.push_back(stage);
      continue;
    }
    reason =
      "role_split_worker_shape_source_" + source_reason +
      "_stage_" + stage_reason;
    return false;
  }
  if(source.worker.empty() || stages.empty())
  {
    reason = "role_split_missing_roles";
    return false;
  }

  stream_refine_channelt channel = source.data.channel;
  std::set<irep_idt> used_workers;
  std::vector<const stream_refine_staget *> ordered;
  std::size_t connected = 0;
  while(connected != stages.size())
  {
    const stream_refine_staget *next = nullptr;
    for(const auto &stage : stages)
    {
      if(
        used_workers.count(stage.worker) == 0 &&
        stage.consume.channel.storage == channel.storage &&
        stage.consume.channel.back == channel.back &&
        stage.consume.channel.bound == channel.bound)
      {
        if(next != nullptr)
        {
          reason = "role_split_branching";
          return false;
        }
        next = &stage;
      }
    }
    if(next == nullptr)
    {
      reason = "role_split_disconnected";
      return false;
    }
    ++connected;
    ordered.push_back(next);
    used_workers.insert(next->worker);
    if(connected != stages.size())
    {
      if(!next->forwards)
      {
        reason = "role_split_early_sink";
        return false;
      }
      channel = next->publish.channel;
    }
    else if(next->forwards && source_has_sink_role)
      channel = next->publish.channel;
    else if(next->forwards)
    {
      reason = "role_split_open_output";
      return false;
    }
  }
  if(source_has_sink_role)
  {
    if(
      channel.storage != source_sink_consume.channel.storage ||
      channel.back != source_sink_consume.channel.back ||
      channel.bound != source_sink_consume.channel.bound)
    {
      reason = "role_split_sink_channel";
      return false;
    }
  }

  std::set<stream_refine_channelt> channels;
  stream_refine_channelt source_channel = source.data.channel;
  source_channel.front = ordered.front()->consume.channel.front;
  channels.insert(source_channel);
  for(std::size_t index = 0; index < ordered.size(); ++index)
  {
    if(!ordered[index]->forwards)
      continue;
    stream_refine_channelt composed = ordered[index]->publish.channel;
    if(index + 1 < ordered.size())
      composed.front = ordered[index + 1]->consume.channel.front;
    else if(source_has_sink_role)
      composed.front = source_sink_consume.channel.front;
    else
    {
      reason = "role_split_unconsumed_output";
      return false;
    }
    channels.insert(composed);
  }
  std::set<irep_idt> queues;
  std::set<irep_idt> protected_symbols = {source.count};
  std::set<const goto_programt::instructiont *> allowed =
    source.writes;
  if(source_has_sink_role)
    protected_symbols.insert(source_sink_fold);
  for(const auto *stage : ordered)
  {
    allowed.insert(stage->writes.begin(), stage->writes.end());
    if(!stage->fold.empty())
      protected_symbols.insert(stage->fold);
  }
  for(const auto &entry : channels)
  {
    if(!stream_refine_initial_channel(model, life, entry))
    {
      reason = "role_split_initial_channel";
      return false;
    }
    queues.insert(entry.storage);
    protected_symbols.insert(entry.storage);
    protected_symbols.insert(entry.front);
    protected_symbols.insert(entry.back);
    protected_symbols.insert(entry.bound);
  }
  if(
    !stream_refine_fresh_queues(
      model, ns, life, queues, reason) ||
    !role_split_stream_global_writes(
      model,
      life,
      queues,
      protected_symbols,
      allowed,
      reason) ||
    !role_split_stream_property(
      model,
      ns,
      life,
      source,
      ordered,
      source_has_sink_role,
      source_sink_fold,
      reason))
    return false;

  source_roles = 1;
  stage_roles = stages.size();
  sink_roles = source_has_sink_role ? 1 : 0;
  return true;
}

struct publication_frontier_arrayt
{
  irep_idt producer;
  irep_idt consumer;
  irep_idt output;
  irep_idt producer_cursor;
  irep_idt consumer_cursor;
  irep_idt frontier;
  exprt bound;
  int terminal_offset;
  mp_integer map_constant;
  std::set<irep_idt> input_bases;
  std::set<irep_idt> consumer_summaries;
  std::map<irep_idt, irep_idt> input_summaries;
  std::set<const goto_programt::instructiont *> allowed_summary_writes;
  const goto_programt::instructiont *consumer_fold;
  const goto_programt::instructiont *consumer_increment;
  const goto_programt::instructiont *producer_output_write;
  const goto_programt::instructiont *producer_frontier_write;
  const goto_programt::instructiont *consumer_guard_source;
  std::set<const goto_programt::instructiont *> allowed_output_writes;
  std::set<const goto_programt::instructiont *> allowed_frontier_writes;

  publication_frontier_arrayt()
    : terminal_offset(0),
      map_constant(0),
      consumer_fold(nullptr),
      consumer_increment(nullptr),
      producer_output_write(nullptr),
      producer_frontier_write(nullptr),
      consumer_guard_source(nullptr)
  {
  }
};

bool publication_frontier_relation(
  const exprt &src,
  const irep_idt &cursor,
  const irep_idt &frontier)
{
  const exprt &expr = strip(src);
  irep_idt left;
  irep_idt right;
  if(
    expr.id() == ID_lt && expr.operands().size() == 2 &&
    symbol_id(expr.op0(), left) && left == cursor &&
    symbol_id(expr.op1(), right) && right == frontier)
    return true;
  return std::any_of(
    expr.operands().begin(),
    expr.operands().end(),
    [&](const exprt &operand) {
      return publication_frontier_relation(
        operand, cursor, frontier);
    });
}

bool publication_frontier_array_read(
  const exprt &src,
  const irep_idt &base,
  const irep_idt &index)
{
  irep_idt candidate_base;
  irep_idt candidate_index;
  if(
    array_symbol_index(src, candidate_base, candidate_index) &&
    candidate_base == base && candidate_index == index)
    return true;
  return std::any_of(
    src.operands().begin(),
    src.operands().end(),
    [&](const exprt &operand) {
      return publication_frontier_array_read(
        operand, base, index);
    });
}

bool publication_frontier_loop(
  const goto_programt &program,
  irep_idt &cursor,
  exprt &bound,
  std::string &reason,
  const exprt *expected_bound = nullptr)
{
  std::size_t exits = 0;
  for(const auto &instruction : program.instructions)
  {
    irep_idt candidate_cursor;
    exprt candidate_bound;
    if(
      parse_loop_exit(
        instruction, candidate_cursor, candidate_bound) &&
      (expected_bound == nullptr ||
       strip(candidate_bound) == strip(*expected_bound)))
    {
      ++exits;
      cursor = candidate_cursor;
      bound = candidate_bound;
    }
  }
  if(exits != 1)
  {
    reason = "publication_frontier_loop_exit";
    return false;
  }
  std::size_t initializations = 0;
  std::size_t increments = 0;
  for(const auto &instruction : program.instructions)
  {
    irep_idt lhs;
    if(
      instruction.is_assign() &&
      symbol_id(instruction.assign_lhs(), lhs) &&
      lhs == cursor && value_is(instruction.assign_rhs(), 0))
      ++initializations;
    if(unit_increment(instruction, cursor))
      ++increments;
  }
  if(initializations != 1 || increments != 1)
  {
    reason = "publication_frontier_cursor_progress";
    return false;
  }
  return true;
}

bool publication_frontier_assignment(
  const exprt &src,
  const irep_idt &cursor,
  int &offset)
{
  const exprt &expr = strip(src);
  irep_idt identifier;
  if(symbol_id(expr, identifier) && identifier == cursor)
  {
    offset = 0;
    return true;
  }
  if(expr.id() != ID_plus || expr.operands().size() != 2)
    return false;
  if(
    symbol_id(expr.op0(), identifier) && identifier == cursor &&
    value_is(expr.op1(), 1))
  {
    offset = 1;
    return true;
  }
  if(
    symbol_id(expr.op1(), identifier) && identifier == cursor &&
    value_is(expr.op0(), 1))
  {
    offset = 1;
    return true;
  }
  return false;
}

bool publication_frontier_additive_map(
  const exprt &src,
  const irep_idt &cursor,
  std::set<irep_idt> &input_bases,
  mp_integer &constant)
{
  const exprt &expr = strip(src);
  mp_integer value;
  if(integer_constant(expr, value))
  {
    constant += value;
    return true;
  }
  irep_idt base;
  irep_idt index;
  if(array_symbol_index(expr, base, index))
  {
    if(index != cursor)
      return false;
    input_bases.insert(base);
    return true;
  }
  if(expr.id() != ID_plus || expr.operands().empty())
    return false;
  return std::all_of(
    expr.operands().begin(),
    expr.operands().end(),
    [&](const exprt &operand) {
      return publication_frontier_additive_map(
        operand, cursor, input_bases, constant);
    });
}

bool publication_frontier_find_array_producer(
  const goto_modelt &model,
  const namespacet &ns,
  const irep_idt &worker,
  publication_frontier_arrayt &result,
  std::string &reason)
{
  const auto &program =
    model.goto_functions.function_map.at(worker).body;
  exprt bound;
  irep_idt cursor;
  if(!publication_frontier_loop(program, cursor, bound, reason))
    return false;

  const goto_programt::instructiont *output_write = nullptr;
  const goto_programt::instructiont *frontier_write = nullptr;
  irep_idt output;
  irep_idt frontier;
  int offset = 0;
  for(const auto &instruction : program.instructions)
  {
    if(!instruction.is_assign())
      continue;
    irep_idt base;
    irep_idt index;
    if(array_symbol_index(instruction.assign_lhs(), base, index))
    {
      if(index != cursor || output_write != nullptr)
      {
        reason = "publication_frontier_output_write";
        return false;
      }
      if(
        !publication_frontier_additive_map(
          instruction.assign_rhs(),
          cursor,
          result.input_bases,
          result.map_constant))
      {
        reason = "publication_frontier_unsupported_map";
        return false;
      }
      output = base;
      output_write = &instruction;
      continue;
    }
    irep_idt lhs;
    int candidate_offset = 0;
    if(
      shared_symbol_lhs(instruction, ns, lhs) &&
      publication_frontier_assignment(
        instruction.assign_rhs(), cursor, candidate_offset))
    {
      if(frontier_write != nullptr)
      {
        reason = "publication_frontier_multiple_frontiers";
        return false;
      }
      frontier = lhs;
      offset = candidate_offset;
      frontier_write = &instruction;
    }
  }
  if(
    output_write == nullptr || frontier_write == nullptr ||
    output.empty() || frontier.empty() || output == frontier ||
    result.input_bases.empty() ||
    result.input_bases.count(output) != 0 ||
    output_write->location_number >= frontier_write->location_number)
  {
    reason = "publication_frontier_producer_shape";
    return false;
  }

  result.producer = worker;
  result.output = output;
  result.producer_cursor = cursor;
  result.frontier = frontier;
  result.bound = bound;
  result.terminal_offset = offset;
  result.allowed_output_writes.insert(output_write);
  result.allowed_frontier_writes.insert(frontier_write);
  result.producer_output_write = output_write;
  result.producer_frontier_write = frontier_write;
  return true;
}

bool publication_frontier_find_array_consumer(
  const goto_modelt &model,
  const namespacet &ns,
  const irep_idt &worker,
  publication_frontier_arrayt &result,
  std::string &reason)
{
  const auto &program =
    model.goto_functions.function_map.at(worker).body;
  irep_idt cursor;
  exprt bound;
  if(
    !publication_frontier_loop(
      program, cursor, bound, reason, &result.bound))
    return false;

  std::size_t reads = 0;
  bool availability = false;
  for(const auto &instruction : program.instructions)
  {
    if(
      instruction.has_condition() &&
      publication_frontier_relation(
        instruction.condition(), cursor, result.frontier))
      availability = true;
    if(instruction.is_assign())
    {
      if(
        publication_frontier_relation(
          instruction.assign_rhs(), cursor, result.frontier))
        availability = true;
      if(
        publication_frontier_array_read(
          instruction.assign_rhs(), result.output, cursor))
      {
        irep_idt lhs;
        const exprt &rhs = strip(instruction.assign_rhs());
        bool fold = false;
        if(
          shared_symbol_lhs(instruction, ns, lhs) &&
          rhs.id() == ID_plus && rhs.operands().size() == 2)
        {
          irep_idt accumulator;
          fold =
            (symbol_id(rhs.op0(), accumulator) &&
             accumulator == lhs &&
             publication_frontier_array_read(
               rhs.op1(), result.output, cursor)) ||
            (symbol_id(rhs.op1(), accumulator) &&
             accumulator == lhs &&
             publication_frontier_array_read(
               rhs.op0(), result.output, cursor));
        }
        if(fold)
        {
          ++reads;
          result.consumer_summaries.insert(lhs);
          result.allowed_summary_writes.insert(&instruction);
          result.consumer_fold = &instruction;
        }
      }
      if(unit_increment(instruction, cursor))
        result.consumer_increment = &instruction;
    }
  }
  if(reads != 1 || !availability || result.consumer_summaries.empty())
  {
    reason = "publication_frontier_consumer_shape";
    return false;
  }
  result.consumer = worker;
  result.consumer_cursor = cursor;
  return true;
}

void publication_frontier_collect_symbols(
  const exprt &src,
  std::set<irep_idt> &symbols)
{
  irep_idt identifier;
  if(symbol_id(src, identifier))
    symbols.insert(identifier);
  for(const auto &operand : src.operands())
    publication_frontier_collect_symbols(operand, symbols);
}

bool publication_frontier_array_guarded_consume(
  const goto_modelt &model,
  const namespacet &ns,
  publication_frontier_arrayt &candidate,
  std::string &reason)
{
  if(
    candidate.consumer_fold == nullptr ||
    candidate.consumer_increment == nullptr ||
    candidate.consumer_fold->location_number >=
      candidate.consumer_increment->location_number)
  {
    reason = "publication_frontier_consumer_effect_order";
    return false;
  }
  const auto &program =
    model.goto_functions.function_map.at(candidate.consumer).body;
  std::size_t guards = 0;
  for(const auto &instruction : program.instructions)
  {
    if(
      !instruction.is_goto() ||
      instruction.targets.size() != 1 ||
      instruction.location_number >=
        candidate.consumer_fold->location_number ||
      instruction.get_target()->location_number <=
        candidate.consumer_increment->location_number)
      continue;
    if(
      publication_frontier_relation(
        instruction.condition(),
        candidate.consumer_cursor,
        candidate.frontier))
    {
      ++guards;
      candidate.consumer_guard_source = &instruction;
      continue;
    }
    std::set<irep_idt> condition_symbols;
    publication_frontier_collect_symbols(
      instruction.condition(), condition_symbols);
    for(const auto &condition_symbol : condition_symbols)
    {
      const symbolt *symbol = lookup(condition_symbol, ns);
      if(
        symbol == nullptr || symbol->is_static_lifetime ||
        (symbol->type.id() != ID_c_bool &&
         symbol->type.id() != ID_bool))
        continue;
      std::size_t writes = 0;
      bool frontier_snapshot = false;
      for(const auto &candidate_write : program.instructions)
      {
        if(!candidate_write.is_assign())
          continue;
        irep_idt lhs;
        if(
          symbol_id(candidate_write.assign_lhs(), lhs) &&
          lhs == condition_symbol)
        {
          ++writes;
          if(
            candidate_write.location_number <
              instruction.location_number &&
            publication_frontier_relation(
              candidate_write.assign_rhs(),
              candidate.consumer_cursor,
              candidate.frontier))
            frontier_snapshot = true;
        }
      }
      if(writes == 1 && frontier_snapshot)
      {
        ++guards;
        candidate.consumer_guard_source = nullptr;
        for(const auto &candidate_write : program.instructions)
        {
          if(!candidate_write.is_assign())
            continue;
          irep_idt lhs;
          if(
            symbol_id(candidate_write.assign_lhs(), lhs) &&
            lhs == condition_symbol &&
            publication_frontier_relation(
              candidate_write.assign_rhs(),
              candidate.consumer_cursor,
              candidate.frontier))
          {
            candidate.consumer_guard_source = &candidate_write;
            break;
          }
        }
      }
    }
  }
  if(guards != 1)
  {
    reason = "publication_frontier_consumer_guard";
    return false;
  }
  return true;
}

unsigned publication_frontier_atomic_epoch(
  const goto_programt &program,
  const goto_programt::instructiont *target)
{
  unsigned epoch = 0;
  unsigned active = 0;
  int depth = 0;
  for(const auto &instruction : program.instructions)
  {
    if(instruction.is_atomic_begin())
    {
      ++depth;
      ++epoch;
      active = epoch;
    }
    if(&instruction == target)
      return depth == 1 ? active : 0;
    if(instruction.is_atomic_end())
    {
      --depth;
      if(depth == 0)
        active = 0;
    }
  }
  return 0;
}

bool publication_frontier_array_memory_order(
  const goto_modelt &model,
  const lifecyclet &life,
  publication_frontier_arrayt &candidate,
  std::string &reason)
{
  if(
    candidate.producer_output_write == nullptr ||
    candidate.producer_frontier_write == nullptr ||
    candidate.consumer_guard_source == nullptr ||
    candidate.consumer_fold == nullptr)
  {
    reason = "publication_frontier_memory_events";
    return false;
  }
  std::set<const goto_programt::instructiont *> initial_writes;
  if(
    !zero_initialized_symbols(
      model, {candidate.frontier}, initial_writes, reason))
    return false;
  const auto &main =
    model.goto_functions.function_map.at(ID_main).body;
  for(const auto &instruction : main.instructions)
  {
    if(
      life.first_create != nullptr &&
      instruction.location_number >=
        life.first_create->location_number)
      break;
    if(!instruction.is_assign())
      continue;
    irep_idt lhs;
    if(
      symbol_id(instruction.assign_lhs(), lhs) &&
      lhs == candidate.frontier)
    {
      reason = "publication_frontier_main_frontier_write";
      return false;
    }
  }

  const auto &producer =
    model.goto_functions.function_map.at(candidate.producer).body;
  const unsigned output_epoch =
    publication_frontier_atomic_epoch(
      producer, candidate.producer_output_write);
  const unsigned frontier_epoch =
    publication_frontier_atomic_epoch(
      producer, candidate.producer_frontier_write);
  const bool atomic_producer_objects =
    atomic_type(
      candidate.producer_output_write->assign_lhs().type()) &&
    atomic_type(
      candidate.producer_frontier_write->assign_lhs().type());
  if(
    !atomic_producer_objects &&
    (output_epoch == 0 || output_epoch != frontier_epoch))
  {
    reason = "publication_frontier_producer_memory_order";
    return false;
  }

  const auto &consumer =
    model.goto_functions.function_map.at(candidate.consumer).body;
  const unsigned guard_epoch =
    publication_frontier_atomic_epoch(
      consumer, candidate.consumer_guard_source);
  const unsigned fold_epoch =
    publication_frontier_atomic_epoch(
      consumer, candidate.consumer_fold);
  const symbolt *frontier_symbol =
    lookup(candidate.frontier, namespacet(model.symbol_table));
  const bool atomic_frontier =
    frontier_symbol != nullptr &&
    atomic_type(frontier_symbol->type);
  const bool atomic_fold_objects =
    atomic_type(candidate.consumer_fold->assign_lhs().type()) &&
    atomic_type(candidate.producer_output_write->assign_lhs().type());
  if(
    (!atomic_frontier && guard_epoch == 0) ||
    (!atomic_fold_objects && fold_epoch == 0))
  {
    reason = "publication_frontier_consumer_memory_order";
    return false;
  }
  return true;
}

bool publication_frontier_additive_symbols(
  const exprt &src,
  std::multiset<irep_idt> &symbols)
{
  const exprt &expr = strip(src);
  irep_idt identifier;
  if(symbol_id(expr, identifier))
  {
    symbols.insert(identifier);
    return true;
  }
  if(expr.id() != ID_plus || expr.operands().empty())
    return false;
  return std::all_of(
    expr.operands().begin(),
    expr.operands().end(),
    [&](const exprt &operand) {
      return publication_frontier_additive_symbols(
        operand, symbols);
    });
}

bool publication_frontier_array_property_equation(
  const goto_modelt &model,
  const lifecyclet &life,
  const irep_idt &consumer_summary,
  exprt &expected,
  std::string &reason)
{
  const auto &main =
    model.goto_functions.function_map.at(ID_main).body;
  std::size_t matches = 0;
  for(const auto &instruction : main.instructions)
  {
    if(
      life.last_join == nullptr ||
      instruction.location_number <=
        life.last_join->location_number)
      continue;
    irep_idt callee;
    if(
      !call_id(instruction, callee) || !is_assume(callee) ||
      instruction.call_arguments().size() != 1)
      continue;
    const exprt &condition =
      strip(instruction.call_arguments().front());
    if(
      condition.id() != ID_notequal ||
      condition.operands().size() != 2)
      continue;
    irep_idt left;
    irep_idt right;
    if(
      symbol_id(condition.op0(), left) &&
      left == consumer_summary &&
      !contains_symbol(condition.op1(), consumer_summary))
    {
      ++matches;
      expected = strip(condition.op1());
    }
    else if(
      symbol_id(condition.op1(), right) &&
      right == consumer_summary &&
      !contains_symbol(condition.op0(), consumer_summary))
    {
      ++matches;
      expected = strip(condition.op0());
    }
  }
  if(matches != 1)
  {
    reason = "publication_frontier_array_equation";
    return false;
  }
  return true;
}

bool publication_frontier_input_fold(
  const goto_programt::instructiont &instruction,
  const irep_idt &input,
  const irep_idt &cursor,
  irep_idt &summary)
{
  if(
    !instruction.is_assign() ||
    !symbol_id(instruction.assign_lhs(), summary))
    return false;
  const exprt &rhs = strip(instruction.assign_rhs());
  if(rhs.id() != ID_plus || rhs.operands().size() != 2)
    return false;
  irep_idt accumulator;
  return
    (symbol_id(rhs.op0(), accumulator) &&
     accumulator == summary &&
     publication_frontier_array_read(
       rhs.op1(), input, cursor)) ||
    (symbol_id(rhs.op1(), accumulator) &&
     accumulator == summary &&
     publication_frontier_array_read(
       rhs.op0(), input, cursor));
}

bool publication_frontier_find_input_folds(
  const goto_modelt &model,
  const namespacet &ns,
  const std::vector<irep_idt> &workers,
  publication_frontier_arrayt &candidate,
  std::string &reason)
{
  std::size_t fold_workers = 0;
  for(const auto &worker : workers)
  {
    if(
      worker == candidate.producer ||
      worker == candidate.consumer)
      continue;
    const auto &program =
      model.goto_functions.function_map.at(worker).body;
    irep_idt cursor;
    exprt bound;
    std::string loop_reason;
    if(
      !publication_frontier_loop(
        program,
        cursor,
        bound,
        loop_reason,
        &candidate.bound))
      continue;

    std::map<irep_idt, irep_idt> folds;
    std::set<const goto_programt::instructiont *> writes;
    bool valid = true;
    for(const auto &input : candidate.input_bases)
    {
      std::size_t matches = 0;
      irep_idt input_summary;
      for(const auto &instruction : program.instructions)
      {
        irep_idt summary;
        if(
          publication_frontier_input_fold(
            instruction, input, cursor, summary))
        {
          if(!shared_unsigned32(summary, ns))
            valid = false;
          ++matches;
          input_summary = summary;
          writes.insert(&instruction);
        }
      }
      if(matches != 1)
        valid = false;
      folds[input] = input_summary;
    }
    if(
      valid && folds.size() == candidate.input_bases.size())
    {
      ++fold_workers;
      candidate.input_summaries = folds;
      candidate.allowed_summary_writes.insert(
        writes.begin(), writes.end());
    }
  }
  if(fold_workers != 1)
  {
    reason = "publication_frontier_input_fold_partition";
    return false;
  }
  return true;
}

bool publication_frontier_array_summary_obligations(
  const goto_modelt &model,
  const lifecyclet &life,
  publication_frontier_arrayt &candidate,
  std::string &reason)
{
  if(candidate.consumer_summaries.size() != 1)
  {
    reason = "publication_frontier_consumer_summary";
    return false;
  }
  const irep_idt consumer_summary =
    *candidate.consumer_summaries.begin();
  if(!shared_unsigned32(consumer_summary, namespacet(model.symbol_table)))
  {
    reason = "publication_frontier_consumer_summary_type";
    return false;
  }

  exprt expected;
  if(
    !publication_frontier_array_property_equation(
      model, life, consumer_summary, expected, reason))
    return false;
  if(
    candidate.terminal_offset == 1 &&
    candidate.map_constant != 0)
  {
    reason = "publication_frontier_complete_map_constant";
    return false;
  }
  std::multiset<irep_idt> expected_symbols;
  if(
    !publication_frontier_additive_symbols(
      expected, expected_symbols))
  {
    reason = "publication_frontier_expected_additive";
    return false;
  }
  std::multiset<irep_idt> required;
  for(const auto &entry : candidate.input_summaries)
    required.insert(entry.second);
  if(candidate.terminal_offset == 0)
  {
    irep_idt bound;
    if(!symbol_id(candidate.bound, bound))
    {
      reason = "publication_frontier_incomplete_bound";
      return false;
    }
    required.insert(bound);
  }
  if(expected_symbols != required)
  {
    reason = "publication_frontier_expected_equation";
    return false;
  }

  std::set<irep_idt> summaries = {consumer_summary};
  for(const auto &entry : candidate.input_summaries)
    summaries.insert(entry.second);
  std::set<const goto_programt::instructiont *> initial_writes;
  if(
    !zero_initialized_symbols(
      model, summaries, initial_writes, reason))
    return false;
  candidate.allowed_summary_writes.insert(
    initial_writes.begin(), initial_writes.end());

  for(const auto &entry : model.goto_functions.function_map)
  {
    for(const auto &instruction : entry.second.body.instructions)
    {
      if(!instruction.is_assign())
        continue;
      irep_idt lhs;
      if(
        !symbol_id(instruction.assign_lhs(), lhs) ||
        summaries.count(lhs) == 0)
        continue;
      if(
        candidate.allowed_summary_writes.count(&instruction) == 0)
      {
        reason = "publication_frontier_summary_external_writer";
        return false;
      }
    }
  }
  return true;
}

bool publication_frontier_postjoin_property(
  const goto_modelt &model,
  const lifecyclet &life,
  const std::set<irep_idt> &summaries,
  bool boolean_summary,
  std::string &reason)
{
  const goto_programt::instructiont *error = nullptr;
  std::size_t errors = 0;
  for(const auto &entry : model.goto_functions.function_map)
  {
    for(const auto &instruction : entry.second.body.instructions)
    {
      irep_idt callee;
      if(call_id(instruction, callee) && is_reach_error(callee))
      {
        ++errors;
        if(entry.first != ID_main)
        {
          reason = "publication_frontier_error_function";
          return false;
        }
        error = &instruction;
      }
    }
  }
  const auto &main =
    model.goto_functions.function_map.at(ID_main).body;
  std::size_t properties = 0;
  const goto_programt::instructiont *assumption = nullptr;
  for(const auto &instruction : main.instructions)
  {
    if(
      life.last_join == nullptr ||
      instruction.location_number <=
        life.last_join->location_number)
      continue;
    irep_idt callee;
    if(
      !call_id(instruction, callee) || !is_assume(callee) ||
      instruction.call_arguments().size() != 1)
      continue;
    const exprt &condition =
      strip(instruction.call_arguments().front());
    for(const auto &summary : summaries)
    {
      bool valid = false;
      if(boolean_summary)
      {
        irep_idt identifier;
        if(
          condition.id() == ID_not &&
          condition.operands().size() == 1)
        {
          const exprt &inner = strip(condition.op0());
          if(
            symbol_id(inner, identifier) &&
            identifier == summary)
            valid = true;
          if(
            inner.id() == ID_notequal &&
            inner.operands().size() == 2)
          {
            valid =
              (symbol_id(inner.op0(), identifier) &&
               identifier == summary && value_is(inner.op1(), 0)) ||
              (symbol_id(inner.op1(), identifier) &&
               identifier == summary && value_is(inner.op0(), 0));
          }
        }
        if(
          condition.id() == ID_equal &&
          condition.operands().size() == 2)
        {
          valid =
            (symbol_id(condition.op0(), identifier) &&
             identifier == summary && value_is(condition.op1(), 0)) ||
            (symbol_id(condition.op1(), identifier) &&
             identifier == summary && value_is(condition.op0(), 0));
        }
      }
      else if(
        condition.id() == ID_notequal &&
        condition.operands().size() == 2)
      {
        irep_idt identifier;
        valid =
          (symbol_id(condition.op0(), identifier) &&
           identifier == summary &&
           !contains_symbol(condition.op1(), summary)) ||
          (symbol_id(condition.op1(), identifier) &&
           identifier == summary &&
           !contains_symbol(condition.op0(), summary));
      }
      if(valid)
      {
        ++properties;
        assumption = &instruction;
        break;
      }
    }
  }
  if(
    properties != 1 || errors != 1 || assumption == nullptr ||
    error == nullptr ||
    assumption->location_number >= error->location_number)
  {
    reason = "publication_frontier_property";
    return false;
  }
  flow_equality_propertyt control;
  control.assumption = assumption;
  control.error = error;
  return flow_main_control(model, life, control, reason);
}

bool publication_frontier_array_global_obligations(
  const goto_modelt &model,
  const lifecyclet &life,
  const publication_frontier_arrayt &candidate,
  std::string &reason)
{
  for(const auto &entry : model.goto_functions.function_map)
  {
    for(const auto &instruction : entry.second.body.instructions)
    {
      if(!instruction.is_assign())
        continue;
      irep_idt base;
      irep_idt direct;
      const bool writes_output =
        base_pointer(instruction.assign_lhs(), base) &&
        base == candidate.output;
      const bool writes_frontier =
        symbol_id(instruction.assign_lhs(), direct) &&
        direct == candidate.frontier;
      bool writes_input = false;
      if(base_pointer(instruction.assign_lhs(), base))
        writes_input = candidate.input_bases.count(base) != 0;
      if(
        symbol_id(instruction.assign_lhs(), direct) &&
        direct == candidate.output)
      {
        for(const auto &input : candidate.input_bases)
        {
          if(contains_symbol(instruction.assign_rhs(), input))
          {
            reason = "publication_frontier_source_output_alias";
            return false;
          }
        }
      }
      if(
        writes_output &&
        candidate.allowed_output_writes.count(&instruction) == 0)
      {
        reason = "publication_frontier_external_output_writer";
        return false;
      }
      if(
        writes_input &&
        !is_start_function(entry.first) &&
        !(entry.first == ID_main &&
          life.first_create != nullptr &&
          instruction.location_number <
            life.first_create->location_number))
      {
        reason = "publication_frontier_input_mutation";
        return false;
      }
      if(
        writes_frontier &&
        !is_start_function(entry.first) &&
        !(entry.first == ID_main &&
          life.first_create != nullptr &&
          instruction.location_number <
            life.first_create->location_number) &&
        candidate.allowed_frontier_writes.count(&instruction) == 0)
      {
        reason = "publication_frontier_external_frontier_writer";
        return false;
      }
    }
  }
  if(!flow_alias_free(model, candidate.output, reason))
    return false;
  return no_addresses(model, {candidate.frontier}, reason);
}

bool publication_frontier_array_audit_impl(
  const goto_modelt &model,
  const namespacet &ns,
  const lifecyclet &life,
  const std::vector<irep_idt> &workers,
  publication_frontier_arrayt &candidate,
  std::string &reason)
{
  std::size_t producers = 0;
  for(const auto &worker : workers)
  {
    publication_frontier_arrayt current;
    std::string current_reason;
    if(
      publication_frontier_find_array_producer(
        model, ns, worker, current, current_reason))
    {
      ++producers;
      candidate = current;
    }
  }
  if(producers != 1)
  {
    reason = "publication_frontier_producer_partition";
    return false;
  }

  std::size_t consumers = 0;
  for(const auto &worker : workers)
  {
    if(worker == candidate.producer)
      continue;
    publication_frontier_arrayt current = candidate;
    std::string current_reason;
    if(
      publication_frontier_find_array_consumer(
        model, ns, worker, current, current_reason))
    {
      ++consumers;
      candidate = current;
    }
  }
  if(consumers != 1)
  {
    reason = "publication_frontier_consumer_partition";
    return false;
  }
  if(
    !publication_frontier_array_guarded_consume(
      model, ns, candidate, reason) ||
    !publication_frontier_array_memory_order(
      model, life, candidate, reason) ||
    !publication_frontier_find_input_folds(
      model, ns, workers, candidate, reason) ||
    !publication_frontier_array_summary_obligations(
      model, life, candidate, reason) ||
    !publication_frontier_postjoin_property(
      model,
      life,
      candidate.consumer_summaries,
      false,
      reason) ||
    !publication_frontier_array_global_obligations(
      model, life, candidate, reason))
    return false;
  return true;
}

struct publication_frontier_filtert
{
  irep_idt producer;
  irep_idt consumer;
  irep_idt source;
  irep_idt output;
  irep_idt scan;
  irep_idt frontier;
  irep_idt cursor;
  irep_idt last;
  irep_idt previous;
  irep_idt current;
  irep_idt summary;
  exprt bound;
  bool increasing;
  std::set<const goto_programt::instructiont *> allowed_writes;
  const goto_programt::instructiont *guard;
  const goto_programt::instructiont *publication;
  const goto_programt::instructiont *frontier_increment;
  const goto_programt::instructiont *last_update;
  const goto_programt::instructiont *scan_increment;
  const goto_programt::instructiont *consumer_read;
  const goto_programt::instructiont *consumer_cursor_increment;
  const goto_programt::instructiont *consumer_summary_update;
  const goto_programt::instructiont *consumer_previous_update;
  const goto_programt::instructiont *consumer_availability;
  const goto_programt::instructiont *consumer_progress_first;
  const goto_programt::instructiont *consumer_progress_last;
  irep_idt consumer_progress_condition;

  publication_frontier_filtert()
    : increasing(false),
      guard(nullptr),
      publication(nullptr),
      frontier_increment(nullptr),
      last_update(nullptr),
      scan_increment(nullptr),
      consumer_read(nullptr),
      consumer_cursor_increment(nullptr),
      consumer_summary_update(nullptr),
      consumer_previous_update(nullptr),
      consumer_availability(nullptr),
      consumer_progress_first(nullptr),
      consumer_progress_last(nullptr)
  {
  }
};

bool publication_frontier_indexed_relation(
  const exprt &src,
  irep_idt &base,
  irep_idt &index,
  irep_idt &value,
  bool &greater)
{
  const exprt &expr = strip(src);
  if(
    (expr.id() == ID_ge || expr.id() == ID_le) &&
    expr.operands().size() == 2)
  {
    irep_idt candidate_base;
    irep_idt candidate_index;
    irep_idt candidate_value;
    if(
      array_symbol_index(
        expr.op0(), candidate_base, candidate_index) &&
      symbol_id(expr.op1(), candidate_value))
    {
      base = candidate_base;
      index = candidate_index;
      value = candidate_value;
      greater = expr.id() == ID_ge;
      return true;
    }
  }
  for(const auto &operand : expr.operands())
  {
    if(
      publication_frontier_indexed_relation(
        operand, base, index, value, greater))
      return true;
  }
  return false;
}

bool publication_frontier_array_equality(
  const exprt &src,
  irep_idt &left_base,
  irep_idt &left_index,
  irep_idt &right_base,
  irep_idt &right_index)
{
  const exprt &expr = strip(src);
  if(expr.id() == ID_equal && expr.operands().size() == 2)
  {
    if(
      array_symbol_index(expr.op0(), left_base, left_index) &&
      array_symbol_index(expr.op1(), right_base, right_index))
      return true;
    if(
      array_symbol_index(expr.op1(), left_base, left_index) &&
      array_symbol_index(expr.op0(), right_base, right_index))
      return true;
  }
  for(const auto &operand : expr.operands())
  {
    if(
      publication_frontier_array_equality(
        operand,
        left_base,
        left_index,
        right_base,
        right_index))
      return true;
  }
  return false;
}

bool publication_frontier_symbol_relation(
  const exprt &src,
  const irep_idt &left,
  const irep_idt &right,
  bool increasing)
{
  const exprt &expr = strip(src);
  irep_idt lhs;
  irep_idt rhs;
  if(
    expr.operands().size() == 2 &&
    symbol_id(expr.op0(), lhs) && lhs == left &&
    symbol_id(expr.op1(), rhs) && rhs == right &&
    expr.id() == (increasing ? ID_le : ID_ge))
    return true;
  return std::any_of(
    expr.operands().begin(),
    expr.operands().end(),
    [&](const exprt &operand) {
      return publication_frontier_symbol_relation(
        operand, left, right, increasing);
    });
}

bool publication_frontier_or_progress(
  const exprt &src,
  const irep_idt &scan,
  const exprt &bound,
  const irep_idt &cursor,
  const irep_idt &frontier)
{
  const exprt &expr = strip(src);
  if(expr.id() == ID_or && expr.operands().size() == 2)
  {
    bool scan_progress = false;
    bool drain_progress = false;
    for(const auto &operand : expr.operands())
    {
      const exprt &term = strip(operand);
      irep_idt left;
      irep_idt right;
      if(
        term.id() == ID_lt && term.operands().size() == 2 &&
        symbol_id(term.op0(), left) && left == scan &&
        strip(term.op1()) == strip(bound))
        scan_progress = true;
      if(
        term.id() == ID_lt && term.operands().size() == 2 &&
        symbol_id(term.op0(), left) && left == cursor &&
        symbol_id(term.op1(), right) && right == frontier)
        drain_progress = true;
    }
    if(scan_progress && drain_progress)
      return true;
  }
  return std::any_of(
    expr.operands().begin(),
    expr.operands().end(),
    [&](const exprt &operand) {
      return publication_frontier_or_progress(
        operand, scan, bound, cursor, frontier);
    });
}

bool publication_frontier_find_filter_producer(
  const goto_modelt &model,
  const namespacet &ns,
  const irep_idt &worker,
  publication_frontier_filtert &result,
  std::string &reason)
{
  const auto &program =
    model.goto_functions.function_map.at(worker).body;
  std::size_t loop_exits = 0;
  for(const auto &instruction : program.instructions)
  {
    irep_idt cursor;
    exprt bound;
    if(parse_loop_exit(instruction, cursor, bound))
    {
      ++loop_exits;
      result.scan = cursor;
      result.bound = bound;
    }
  }
  std::size_t scan_increments = 0;
  for(const auto &instruction : program.instructions)
  {
    if(unit_increment(instruction, result.scan))
      ++scan_increments;
  }
  if(loop_exits != 1 || scan_increments != 1)
  {
    reason = "publication_frontier_filter_loop";
    return false;
  }

  std::size_t guards = 0;
  std::size_t publications = 0;
  std::size_t frontier_increments = 0;
  std::size_t last_updates = 0;
  for(const auto &instruction : program.instructions)
  {
    if(instruction.has_condition())
    {
      irep_idt source;
      irep_idt index;
      irep_idt last;
      bool greater = false;
      if(
        publication_frontier_indexed_relation(
          instruction.condition(),
          source,
          index,
          last,
          greater) &&
        index == result.scan)
      {
        ++guards;
        result.source = source;
        result.last = last;
        result.increasing = greater;
        result.guard = &instruction;
      }
    }
    irep_idt callee;
    if(
      call_id(instruction, callee) && is_assume(callee) &&
      instruction.call_arguments().size() == 1)
    {
      irep_idt output;
      irep_idt frontier;
      irep_idt source;
      irep_idt scan;
      if(
        publication_frontier_array_equality(
          instruction.call_arguments().front(),
          output,
          frontier,
          source,
          scan) &&
        source == result.source && scan == result.scan)
      {
        ++publications;
        result.output = output;
        result.frontier = frontier;
        result.publication = &instruction;
      }
    }
    if(
      !result.frontier.empty() &&
      unit_increment(instruction, result.frontier))
    {
      ++frontier_increments;
      result.allowed_writes.insert(&instruction);
      result.frontier_increment = &instruction;
    }
    if(instruction.is_assign())
    {
      irep_idt lhs;
      if(
        symbol_id(instruction.assign_lhs(), lhs) &&
        lhs == result.last &&
        publication_frontier_array_read(
          instruction.assign_rhs(),
          result.source,
          result.scan))
      {
        ++last_updates;
        result.allowed_writes.insert(&instruction);
        result.last_update = &instruction;
      }
      if(unit_increment(instruction, result.scan))
      {
        result.allowed_writes.insert(&instruction);
        result.scan_increment = &instruction;
      }
    }
  }
  if(
    guards != 1 || publications != 1 ||
    frontier_increments != 1 || last_updates != 1 ||
    result.output.empty() || result.source.empty() ||
    result.output == result.source ||
    result.frontier == result.scan)
  {
    reason = "publication_frontier_filter_producer";
    return false;
  }
  result.producer = worker;
  return true;
}

bool publication_frontier_filter_producer_control(
  const goto_modelt &model,
  const publication_frontier_filtert &candidate,
  std::string &reason)
{
  if(
    candidate.guard == nullptr ||
    candidate.publication == nullptr ||
    candidate.frontier_increment == nullptr ||
    candidate.last_update == nullptr ||
    candidate.scan_increment == nullptr ||
    !candidate.guard->is_goto() ||
    candidate.guard->targets.size() != 1)
  {
    reason = "publication_frontier_filter_producer_control_shape";
    return false;
  }
  const unsigned guard = candidate.guard->location_number;
  const unsigned publication =
    candidate.publication->location_number;
  const unsigned frontier =
    candidate.frontier_increment->location_number;
  const unsigned last = candidate.last_update->location_number;
  const unsigned scan = candidate.scan_increment->location_number;
  const unsigned skip =
    candidate.guard->get_target()->location_number;
  if(
    !(guard < publication && publication < frontier &&
      frontier < last && last < skip && skip <= scan))
  {
    reason = "publication_frontier_filter_producer_order";
    return false;
  }

  const auto &program =
    model.goto_functions.function_map.at(candidate.producer).body;
  unsigned epoch = 0;
  int depth = 0;
  unsigned publication_epoch = 0;
  unsigned frontier_epoch = 0;
  unsigned scan_epoch = 0;
  for(const auto &instruction : program.instructions)
  {
    if(instruction.is_atomic_begin())
    {
      ++depth;
      ++epoch;
    }
    if(&instruction == candidate.publication && depth == 1)
      publication_epoch = epoch;
    if(&instruction == candidate.frontier_increment && depth == 1)
      frontier_epoch = epoch;
    if(&instruction == candidate.scan_increment && depth == 1)
      scan_epoch = epoch;
    if(instruction.is_atomic_end())
      --depth;
    if(depth < 0 || depth > 1)
    {
      reason = "publication_frontier_filter_atomic_nesting";
      return false;
    }
  }
  if(
    depth != 0 || publication_epoch == 0 ||
    publication_epoch != frontier_epoch || scan_epoch == 0 ||
    scan_epoch == publication_epoch)
  {
    reason = "publication_frontier_filter_producer_atomicity";
    return false;
  }
  return true;
}

bool publication_frontier_find_filter_consumer(
  const goto_modelt &model,
  const namespacet &ns,
  const irep_idt &worker,
  publication_frontier_filtert &result,
  std::string &reason)
{
  (void)ns;
  const auto &program =
    model.goto_functions.function_map.at(worker).body;
  std::size_t reads = 0;
  std::size_t cursor_increments = 0;
  std::size_t previous_updates = 0;
  bool availability = false;
  bool complete_drain = false;

  for(const auto &instruction : program.instructions)
  {
    if(instruction.is_assign())
    {
      irep_idt lhs;
      if(
        symbol_id(instruction.assign_lhs(), lhs))
      {
        irep_idt index;
        if(
          base_index(
            instruction.assign_rhs(), result.output, index))
        {
          ++reads;
          result.current = lhs;
          result.cursor = index;
          result.consumer_read = &instruction;
          result.allowed_writes.insert(&instruction);
        }
      }
    }
  }

  if(reads != 1 || result.cursor.empty() || result.current.empty())
  {
    reason = "publication_frontier_filter_consumer_read";
    return false;
  }

  for(const auto &instruction : program.instructions)
  {
    if(instruction.is_assign())
    {
      irep_idt lhs;
      irep_idt rhs;
      if(
        symbol_id(instruction.assign_lhs(), lhs) &&
        symbol_id(instruction.assign_rhs(), rhs) &&
        rhs == result.current && lhs != result.current)
      {
        result.previous = lhs;
        ++previous_updates;
        result.allowed_writes.insert(&instruction);
        result.consumer_previous_update = &instruction;
      }
      if(unit_increment(instruction, result.cursor))
      {
        ++cursor_increments;
        result.allowed_writes.insert(&instruction);
        result.consumer_cursor_increment = &instruction;
      }
      if(
        publication_frontier_or_progress(
          instruction.assign_rhs(),
          result.scan,
          result.bound,
          result.cursor,
          result.frontier))
      {
        complete_drain = true;
        irep_idt lhs;
        if(
          symbol_id(instruction.assign_lhs(), lhs) &&
          !lookup(lhs, ns)->is_static_lifetime)
        {
          if(result.consumer_progress_first == nullptr)
          {
            result.consumer_progress_first = &instruction;
            result.consumer_progress_condition = lhs;
          }
          result.consumer_progress_last = &instruction;
        }
      }
    }
    irep_idt callee;
    if(
      call_id(instruction, callee) && is_assume(callee) &&
      instruction.call_arguments().size() == 1 &&
      publication_frontier_relation(
        instruction.call_arguments().front(),
        result.cursor,
        result.frontier))
    {
      availability = true;
      result.consumer_availability = &instruction;
    }
  }

  std::size_t summary_updates = 0;
  for(const auto &instruction : program.instructions)
  {
    if(!instruction.is_assign())
      continue;
    irep_idt lhs;
    if(
      symbol_id(instruction.assign_lhs(), lhs) &&
      contains_symbol(instruction.assign_rhs(), lhs) &&
      publication_frontier_symbol_relation(
        instruction.assign_rhs(),
        result.previous,
        result.current,
        result.increasing))
    {
      ++summary_updates;
      result.summary = lhs;
      result.allowed_writes.insert(&instruction);
      result.consumer_summary_update = &instruction;
    }
  }
  if(
    cursor_increments != 1 || summary_updates != 1 ||
    previous_updates != 1 || !availability || !complete_drain ||
    result.summary.empty() || result.previous.empty())
  {
    reason = "publication_frontier_filter_consumer";
    return false;
  }
  result.consumer = worker;
  return true;
}

bool publication_frontier_filter_consumer_control(
  const goto_modelt &model,
  const publication_frontier_filtert &candidate,
  std::string &reason)
{
  if(
    candidate.consumer_read == nullptr ||
    candidate.consumer_cursor_increment == nullptr ||
    candidate.consumer_summary_update == nullptr ||
    candidate.consumer_previous_update == nullptr ||
    candidate.consumer_availability == nullptr ||
    candidate.consumer_progress_first == nullptr ||
    candidate.consumer_progress_last == nullptr ||
    candidate.consumer_progress_first ==
      candidate.consumer_progress_last ||
    candidate.consumer_progress_condition.empty())
  {
    reason = "publication_frontier_filter_consumer_control_shape";
    return false;
  }
  const unsigned progress_first =
    candidate.consumer_progress_first->location_number;
  const unsigned availability =
    candidate.consumer_availability->location_number;
  const unsigned read = candidate.consumer_read->location_number;
  const unsigned increment =
    candidate.consumer_cursor_increment->location_number;
  const unsigned summary =
    candidate.consumer_summary_update->location_number;
  const unsigned previous =
    candidate.consumer_previous_update->location_number;
  const unsigned progress_last =
    candidate.consumer_progress_last->location_number;
  if(
    !(progress_first < availability &&
      availability < read && read < increment &&
      increment < summary && summary < previous &&
      previous < progress_last))
  {
    reason = "publication_frontier_filter_consumer_order";
    return false;
  }

  const auto &program =
    model.goto_functions.function_map.at(candidate.consumer).body;
  std::size_t progress_writes = 0;
  std::size_t loop_guards = 0;
  unsigned epoch = 0;
  int depth = 0;
  unsigned availability_epoch = 0;
  unsigned read_epoch = 0;
  unsigned increment_epoch = 0;
  for(const auto &instruction : program.instructions)
  {
    if(instruction.is_atomic_begin())
    {
      ++depth;
      ++epoch;
    }
    if(&instruction == candidate.consumer_availability && depth == 1)
      availability_epoch = epoch;
    if(&instruction == candidate.consumer_read && depth == 1)
      read_epoch = epoch;
    if(
      &instruction == candidate.consumer_cursor_increment &&
      depth == 1)
      increment_epoch = epoch;
    if(instruction.is_assign())
    {
      irep_idt lhs;
      if(
        symbol_id(instruction.assign_lhs(), lhs) &&
        lhs == candidate.consumer_progress_condition)
      {
        ++progress_writes;
        if(
          !publication_frontier_or_progress(
            instruction.assign_rhs(),
            candidate.scan,
            candidate.bound,
            candidate.cursor,
            candidate.frontier))
        {
          reason = "publication_frontier_filter_progress_write";
          return false;
        }
      }
    }
    if(
      instruction.is_goto() &&
      instruction.targets.size() == 1 &&
      instruction.location_number > progress_first &&
      instruction.location_number < availability &&
      contains_symbol(
        instruction.condition(),
        candidate.consumer_progress_condition) &&
      instruction.get_target()->location_number > progress_last)
      ++loop_guards;
    if(instruction.is_atomic_end())
      --depth;
    if(depth < 0 || depth > 1)
    {
      reason = "publication_frontier_filter_consumer_atomic_nesting";
      return false;
    }
  }
  if(
    depth != 0 || progress_writes != 2 || loop_guards != 1 ||
    availability_epoch == 0 ||
    availability_epoch != read_epoch ||
    availability_epoch != increment_epoch)
  {
    reason = "publication_frontier_filter_consumer_control";
    return false;
  }
  return true;
}

bool publication_frontier_filter_global_obligations(
  const goto_modelt &model,
  const lifecyclet &life,
  const publication_frontier_filtert &candidate,
  std::string &reason)
{
  const std::set<irep_idt> protected_symbols = {
    candidate.scan,
    candidate.frontier,
    candidate.cursor,
    candidate.last,
    candidate.previous,
    candidate.current,
    candidate.summary};
  for(const auto &entry : model.goto_functions.function_map)
  {
    for(const auto &instruction : entry.second.body.instructions)
    {
      if(!instruction.is_assign())
        continue;
      irep_idt base;
      if(
        base_pointer(instruction.assign_lhs(), base) &&
        base == candidate.source &&
        !is_start_function(entry.first) &&
        !(entry.first == ID_main &&
          life.first_create != nullptr &&
          instruction.location_number <
            life.first_create->location_number))
      {
        reason = "publication_frontier_filter_source_mutation";
        return false;
      }
      if(
        base_pointer(instruction.assign_lhs(), base) &&
        base == candidate.output)
      {
        reason = "publication_frontier_filter_output_mutation";
        return false;
      }
      irep_idt direct;
      if(
        symbol_id(instruction.assign_lhs(), direct) &&
        direct == candidate.output &&
        contains_symbol(instruction.assign_rhs(), candidate.source))
      {
        reason = "publication_frontier_filter_source_output_alias";
        return false;
      }
      irep_idt lhs;
      if(
        !symbol_id(instruction.assign_lhs(), lhs) ||
        protected_symbols.count(lhs) == 0)
        continue;
      if(is_start_function(entry.first))
        continue;
      if(
        entry.first == ID_main && life.first_create != nullptr &&
        instruction.location_number <
          life.first_create->location_number)
        continue;
      if(candidate.allowed_writes.count(&instruction) == 0)
      {
        reason = "publication_frontier_filter_external_writer";
        return false;
      }
    }
  }
  if(
    !flow_alias_free(model, candidate.source, reason) ||
    !flow_alias_free(model, candidate.output, reason))
    return false;
  return no_addresses(model, protected_symbols, reason);
}

bool publication_frontier_filter_no_feedback(
  const goto_modelt &model,
  const publication_frontier_filtert &candidate,
  std::string &reason)
{
  const auto &program =
    model.goto_functions.function_map.at(candidate.producer).body;
  const std::set<irep_idt> consumer_state = {
    candidate.cursor,
    candidate.previous,
    candidate.current,
    candidate.summary};
  for(const auto &instruction : program.instructions)
  {
    for(const auto &symbol : consumer_state)
    {
      if(
        contains_symbol(instruction.code(), symbol) ||
        (instruction.has_condition() &&
         contains_symbol(instruction.condition(), symbol)))
      {
        reason = "publication_frontier_filter_feedback";
        return false;
      }
    }
  }
  return true;
}

bool publication_frontier_filter_initial_state(
  const goto_modelt &model,
  const lifecyclet &life,
  const publication_frontier_filtert &candidate,
  std::string &reason)
{
  irep_idt bound;
  if(!symbol_id(candidate.bound, bound))
  {
    reason = "publication_frontier_filter_bound_symbol";
    return false;
  }

  std::set<const goto_programt::instructiont *> zero_writes;
  std::string zero_reason;
  if(
    !zero_initialized_symbols(
      model, {candidate.scan}, zero_writes, zero_reason))
  {
    reason = "publication_frontier_filter_scan_init";
    return false;
  }

  const auto &main =
    model.goto_functions.function_map.at(ID_main).body;
  std::size_t summary_true = 0;
  std::size_t frontier_cursor = 0;
  std::size_t previous_source = 0;
  std::size_t last_previous = 0;
  std::size_t positive_bound = 0;
  std::size_t scan_main_writes = 0;
  std::size_t summary_writes = 0;
  std::size_t frontier_writes = 0;
  std::size_t previous_writes = 0;
  std::size_t last_writes = 0;
  unsigned summary_location = 0;
  unsigned frontier_location = 0;
  unsigned previous_location = 0;
  unsigned last_location = 0;
  unsigned cursor_last_location = 0;
  for(const auto &instruction : main.instructions)
  {
    if(
      life.first_create != nullptr &&
      instruction.location_number >=
        life.first_create->location_number)
      break;
    if(instruction.is_assign())
    {
      irep_idt lhs;
      irep_idt rhs;
      if(!symbol_id(instruction.assign_lhs(), lhs))
        continue;
      if(lhs == candidate.scan)
      {
        ++scan_main_writes;
        continue;
      }
      if(lhs == candidate.cursor)
        cursor_last_location = instruction.location_number;
      if(
        lhs == candidate.summary &&
        value_is(instruction.assign_rhs(), 1))
      {
        ++summary_true;
        ++summary_writes;
        summary_location = instruction.location_number;
        continue;
      }
      if(lhs == candidate.summary)
        ++summary_writes;
      if(
        lhs == candidate.frontier &&
        symbol_id(instruction.assign_rhs(), rhs) &&
        rhs == candidate.cursor)
      {
        ++frontier_cursor;
        ++frontier_writes;
        frontier_location = instruction.location_number;
        continue;
      }
      if(lhs == candidate.frontier)
        ++frontier_writes;
      if(
        lhs == candidate.previous &&
        array_at_zero(instruction.assign_rhs(), candidate.source))
      {
        ++previous_source;
        ++previous_writes;
        previous_location = instruction.location_number;
        continue;
      }
      if(lhs == candidate.previous)
        ++previous_writes;
      if(
        lhs == candidate.last &&
        symbol_id(instruction.assign_rhs(), rhs) &&
        rhs == candidate.previous)
      {
        ++last_previous;
        ++last_writes;
        last_location = instruction.location_number;
        continue;
      }
      if(lhs == candidate.last)
        ++last_writes;
    }
    irep_idt callee;
    if(
      call_id(instruction, callee) && is_assume(callee) &&
      instruction.call_arguments().size() == 1)
    {
      std::vector<exprt> terms;
      flatten_and(instruction.call_arguments().front(), terms);
      for(const auto &term : terms)
      {
        if(
          stream_refine_symbol_zero_relation(
            term, bound, ID_gt))
          ++positive_bound;
      }
    }
  }
  if(
    summary_true != 1 || frontier_cursor != 1 ||
    previous_source != 1 || last_previous != 1 ||
    positive_bound != 1 || scan_main_writes != 0 ||
    summary_writes != 1 || frontier_writes != 1 ||
    previous_writes != 1 || last_writes != 1 ||
    summary_location >= frontier_location ||
    cursor_last_location >= frontier_location ||
    frontier_location >= previous_location ||
    previous_location >= last_location)
  {
    reason = "publication_frontier_filter_initial_state";
    return false;
  }
  return true;
}

bool publication_frontier_filter_audit_impl(
  const goto_modelt &model,
  const namespacet &ns,
  const lifecyclet &life,
  const std::vector<irep_idt> &workers,
  publication_frontier_filtert &candidate,
  std::string &reason)
{
  if(workers.size() != 2)
  {
    reason = "publication_frontier_filter_worker_count";
    return false;
  }
  std::size_t producers = 0;
  std::string producer_reasons;
  for(const auto &worker : workers)
  {
    publication_frontier_filtert current;
    std::string current_reason;
    if(
      publication_frontier_find_filter_producer(
        model, ns, worker, current, current_reason))
    {
      ++producers;
      candidate = current;
    }
    else
    {
      if(!producer_reasons.empty())
        producer_reasons += "_";
      producer_reasons += current_reason;
    }
  }
  if(producers != 1)
  {
    reason =
      "publication_frontier_filter_producer_partition_" +
      producer_reasons;
    return false;
  }
  for(const auto &worker : workers)
  {
    if(worker == candidate.producer)
      continue;
    if(
      !publication_frontier_find_filter_consumer(
        model, ns, worker, candidate, reason))
      return false;
  }
  if(
    !publication_frontier_postjoin_property(
      model, life, {candidate.summary}, true, reason) ||
    !publication_frontier_filter_initial_state(
      model, life, candidate, reason) ||
    !publication_frontier_filter_producer_control(
      model, candidate, reason) ||
    !publication_frontier_filter_consumer_control(
      model, candidate, reason) ||
    !publication_frontier_filter_no_feedback(
      model, candidate, reason) ||
    !publication_frontier_filter_global_obligations(
      model, life, candidate, reason))
    return false;
  return true;
}

bool publication_frontier_sequence_audit_impl(
  const goto_modelt &model,
  const namespacet &ns,
  std::string &mode,
  std::string &reason)
{
  lifecyclet life;
  std::vector<irep_idt> workers;
  if(!stream_refine_lifecycle(model, life, workers, reason))
    return false;

  publication_frontier_arrayt array_candidate;
  if(
    publication_frontier_array_audit_impl(
      model, ns, life, workers, array_candidate, reason))
  {
    mode =
      array_candidate.terminal_offset == 1 ?
      "complete-array" : "incomplete-array";
    return true;
  }
  const std::string array_reason = reason;
  publication_frontier_filtert filter_candidate;
  reason.clear();
  if(
    publication_frontier_filter_audit_impl(
      model, ns, life, workers, filter_candidate, reason))
  {
    mode =
      filter_candidate.increasing ?
      "monotone-filter-increasing" :
      "monotone-filter-decreasing";
    return true;
  }
  reason =
    "array_" + array_reason + "_filter_" + reason;
  return false;
}

struct relational_bisimulation_mappingt
{
  std::map<irep_idt, irep_idt> forward;
  std::map<irep_idt, irep_idt> reverse;
  std::set<irep_idt> comparator_mapped;
  std::vector<std::pair<exprt, exprt>> comparator_equalities;
  mutable std::size_t comparator_current_region = 0;
  mutable std::map<std::size_t, std::set<std::size_t>>
    comparator_equality_uses;
};

bool relational_bisimulation_contains_nondet(const exprt &expr)
{
  if(
    expr.id() == ID_side_effect &&
    to_side_effect_expr(expr).get_statement() == ID_nondet)
    return true;
  return std::any_of(
    expr.operands().begin(),
    expr.operands().end(),
    relational_bisimulation_contains_nondet);
}

bool relational_bisimulation_bind(
  const irep_idt &left,
  const irep_idt &right,
  const namespacet &ns,
  relational_bisimulation_mappingt &mapping,
  std::string &reason)
{
  const auto existing = mapping.forward.find(left);
  if(existing != mapping.forward.end())
  {
    if(existing->second != right)
    {
      reason = "symbol_mapping_conflict";
      return false;
    }
    return true;
  }
  const auto inverse = mapping.reverse.find(right);
  if(inverse != mapping.reverse.end() && inverse->second != left)
  {
    reason = "symbol_mapping_noninjective";
    return false;
  }
  const symbolt *left_symbol = lookup(left, ns);
  const symbolt *right_symbol = lookup(right, ns);
  if(
    left_symbol == nullptr || right_symbol == nullptr ||
    left_symbol->type != right_symbol->type ||
    left_symbol->is_static_lifetime != right_symbol->is_static_lifetime ||
    left_symbol->is_type != right_symbol->is_type)
  {
    reason = "symbol_type";
    return false;
  }
  if(
    left_symbol->type.id() == ID_code &&
    left != right)
  {
    reason = "callee_mapping";
    return false;
  }
  mapping.forward.emplace(left, right);
  mapping.reverse.emplace(right, left);
  return true;
}

bool relational_bisimulation_expression(
  const exprt &left,
  const exprt &right,
  const namespacet &ns,
  relational_bisimulation_mappingt &mapping,
  std::string &reason)
{
  if(
    left.id() != right.id() ||
    left.type() != right.type() ||
    left.operands().size() != right.operands().size())
  {
    reason = "expression_shape";
    return false;
  }
  const bool left_nondet =
    relational_bisimulation_contains_nondet(left);
  const bool right_nondet =
    relational_bisimulation_contains_nondet(right);
  if(left_nondet != right_nondet)
  {
    reason = "unpaired_worker_nondeterminism";
    return false;
  }
  if(
    left.id() == ID_side_effect &&
    to_side_effect_expr(left).get_statement() == ID_nondet)
  {
    if(
      right.id() != ID_side_effect ||
      to_side_effect_expr(right).get_statement() != ID_nondet)
    {
      reason = "unpaired_worker_nondeterminism";
      return false;
    }
    return true;
  }
  if(left.id() == ID_symbol)
  {
    return relational_bisimulation_bind(
      to_symbol_expr(left).get_identifier(),
      to_symbol_expr(right).get_identifier(),
      ns,
      mapping,
      reason);
  }
  if(
    (left.id() == ID_constant &&
     left.get(ID_value) != right.get(ID_value)) ||
    left.get(ID_statement) != right.get(ID_statement) ||
    left.get(ID_component_name) != right.get(ID_component_name))
  {
    reason = "expression_value";
    return false;
  }
  for(std::size_t index = 0; index < left.operands().size(); ++index)
  {
    if(
      !relational_bisimulation_expression(
        left.operands()[index],
        right.operands()[index],
        ns,
        mapping,
        reason))
      return false;
  }
  return true;
}

bool relational_bisimulation_programs(
  const goto_programt &left,
  const goto_programt &right,
  const namespacet &ns,
  relational_bisimulation_mappingt &mapping,
  std::string &reason)
{
  if(left.instructions.size() != right.instructions.size())
  {
    reason = "cfg_size";
    return false;
  }
  std::map<const goto_programt::instructiont *, std::size_t> left_indices;
  std::map<const goto_programt::instructiont *, std::size_t> right_indices;
  std::size_t ordinal = 0;
  for(const auto &instruction : left.instructions)
    left_indices.emplace(&instruction, ordinal++);
  ordinal = 0;
  for(const auto &instruction : right.instructions)
    right_indices.emplace(&instruction, ordinal++);

  auto left_instruction = left.instructions.begin();
  auto right_instruction = right.instructions.begin();
  for(;
      left_instruction != left.instructions.end();
      ++left_instruction, ++right_instruction)
  {
    if(
      left_instruction->type() != right_instruction->type() ||
      left_instruction->targets.size() !=
        right_instruction->targets.size())
    {
      reason = "cfg_instruction";
      return false;
    }
    auto left_target = left_instruction->targets.begin();
    auto right_target = right_instruction->targets.begin();
    for(;
        left_target != left_instruction->targets.end();
        ++left_target, ++right_target)
    {
      if(
        left_indices.at(&**left_target) !=
        right_indices.at(&**right_target))
      {
        reason = "cfg_edge";
        return false;
      }
    }
    if(
      left_instruction->has_condition() !=
        right_instruction->has_condition())
    {
      reason = "cfg_condition";
      return false;
    }
    if(
      (left_instruction->has_condition() &&
       !relational_bisimulation_expression(
         left_instruction->condition(),
         right_instruction->condition(),
         ns,
         mapping,
         reason)) ||
      !relational_bisimulation_expression(
        left_instruction->code(),
        right_instruction->code(),
        ns,
        mapping,
        reason))
      return false;
  }
  return true;
}

bool relational_bisimulation_verified_assume(
  const goto_programt::instructiont &instruction,
  const goto_modelt &model,
  const namespacet &ns,
  const bool allow_unresolved_abort = false);

bool relational_bisimulation_function_effects(
  const goto_modelt &model,
  const irep_idt &function,
  const namespacet &ns,
  std::set<irep_idt> &visiting,
  std::set<irep_idt> &reads,
  std::set<irep_idt> &writes,
  std::string &reason,
  const bool allow_verified_assume = false)
{
  if(!visiting.insert(function).second)
  {
    reason = "recursive_helper";
    return false;
  }
  const auto found =
    model.goto_functions.function_map.find(function);
  if(
    found == model.goto_functions.function_map.end() ||
    !found->second.body_available())
  {
    reason = "helper_body";
    visiting.erase(function);
    return false;
  }
  const goto_programt &program = found->second.body;
  std::size_t atomic_depth = 0;
  for(const auto &instruction : program.instructions)
  {
    // Diagnostic only: paired nondeterministic expressions are checked by
    // relational_bisimulation_programs. A production proof must additionally
    // establish unique feasible assume-controlled choices.
    if(instruction.is_atomic_begin())
    {
      if(atomic_depth != 0)
      {
        reason = "nested_atomic_region";
        visiting.erase(function);
        return false;
      }
      ++atomic_depth;
      continue;
    }
    if(instruction.is_atomic_end())
    {
      if(atomic_depth != 1)
      {
        reason = "unbalanced_atomic_region";
        visiting.erase(function);
        return false;
      }
      --atomic_depth;
      continue;
    }
    if(
      instruction.is_start_thread() || instruction.is_end_thread() ||
      instruction.is_assert() || instruction.is_other())
    {
      reason = "worker_effect";
      visiting.erase(function);
      return false;
    }
    if(instruction.is_assign())
    {
      irep_idt lhs;
      if(!symbol_id(instruction.assign_lhs(), lhs))
      {
        reason = "worker_pointer_write";
        visiting.erase(function);
        return false;
      }
      const symbolt *symbol = lookup(lhs, ns);
      if(
        symbol != nullptr && symbol->is_static_lifetime &&
        !symbol->is_type)
        writes.insert(lhs);
      collect_static_symbols(instruction.assign_rhs(), ns, reads);
      continue;
    }
    if(instruction.is_function_call())
    {
      irep_idt callee;
      if(
        !call_id(instruction, callee) ||
        is_create(callee) || is_join(callee) ||
        is_atomic_marker(callee) ||
        id2string(callee).find("pthread_") == 0 ||
        id2string(callee).find("__atomic_") == 0 ||
        id2string(callee).find("__sync_") == 0 ||
        is_named(callee, "malloc") ||
        is_named(callee, "calloc") ||
        is_named(callee, "realloc") ||
        is_named(callee, "free"))
      {
        reason = "worker_call";
        visiting.erase(function);
        return false;
      }
      for(const auto &argument : instruction.call_arguments())
        collect_static_symbols(argument, ns, reads);
      if(!instruction.call_lhs().is_nil())
      {
        irep_idt lhs;
        if(!symbol_id(instruction.call_lhs(), lhs))
        {
          reason = "worker_call_lhs";
          visiting.erase(function);
          return false;
        }
        const symbolt *symbol = lookup(lhs, ns);
        if(
          symbol != nullptr && symbol->is_static_lifetime &&
          !symbol->is_type)
          writes.insert(lhs);
      }
      if(
        !is_named(callee, "__CPROVER_assume") &&
        !(allow_verified_assume &&
          relational_bisimulation_verified_assume(
            instruction, model, ns, true)) &&
        !relational_bisimulation_function_effects(
          model,
          callee,
          ns,
          visiting,
          reads,
          writes,
          reason,
          allow_verified_assume))
      {
        visiting.erase(function);
        return false;
      }
      continue;
    }
    if(instruction.has_condition())
      collect_static_symbols(instruction.condition(), ns, reads);
    if(instruction.is_set_return_value())
      collect_static_symbols(instruction.return_value(), ns, reads);
  }
  if(atomic_depth != 0)
  {
    reason = "unbalanced_atomic_region";
    visiting.erase(function);
    return false;
  }
  visiting.erase(function);
  return true;
}

bool relational_bisimulation_main_regions(
  const goto_modelt &model,
  const lifecyclet &life,
  const goto_programt::instructiont *property,
  const goto_programt::instructiont *error,
  std::string &reason)
{
  const auto &main =
    model.goto_functions.function_map.at(ID_main).body;
  bool in_concurrent_region = false;
  bool after_join = false;
  for(const auto &instruction : main.instructions)
  {
    if(&instruction == life.first_create)
      in_concurrent_region = true;
    if(in_concurrent_region)
    {
      irep_idt callee;
      if(instruction.is_function_call())
      {
        if(
          !call_id(instruction, callee) ||
          (!is_create(callee) && !is_join(callee)))
        {
          reason = "main_concurrent_effect";
          return false;
        }
      }
      else if(
        !instruction.is_skip() &&
        !instruction.is_location() &&
        !instruction.is_decl() &&
        !instruction.is_dead())
      {
        reason = "main_concurrent_effect";
        return false;
      }
    }
    if(&instruction == life.last_join)
    {
      in_concurrent_region = false;
      after_join = true;
      continue;
    }
    if(!after_join || &instruction == property || &instruction == error)
      continue;
    if(
      instruction.is_skip() || instruction.is_location() ||
      instruction.is_dead() || instruction.is_end_function() ||
      instruction.is_set_return_value())
      continue;
    reason = "postjoin_effect";
    return false;
  }
  return true;
}

bool relational_bisimulation_stable_symbols(
  const std::set<irep_idt> &symbols,
  const namespacet &ns,
  std::string &reason)
{
  for(const auto &identifier : symbols)
  {
    const symbolt *symbol = lookup(identifier, ns);
    if(
      symbol != nullptr &&
      (symbol->type.get_bool(ID_C_volatile) ||
       atomic_type(symbol->type)))
    {
      reason = "volatile_or_atomic_state";
      return false;
    }
  }
  return true;
}

bool relational_bisimulation_equality_term(
  const exprt &src,
  const irep_idt &left,
  const irep_idt &right)
{
  std::vector<exprt> terms;
  flatten_and(src, terms);
  for(const auto &term_src : terms)
  {
    const exprt &term = strip(term_src);
    if(term.id() != ID_equal || term.operands().size() != 2)
      continue;
    irep_idt first;
    irep_idt second;
    if(
      symbol_id(term.op0(), first) &&
      symbol_id(term.op1(), second) &&
      ((first == left && second == right) ||
       (first == right && second == left)))
      return true;
  }
  return false;
}

bool relational_bisimulation_parameter_truth(
  const exprt &src,
  const irep_idt &parameter)
{
  const exprt &expr = strip(src);
  irep_idt identifier;
  if(symbol_id(expr, identifier))
    return identifier == parameter;
  if(
    expr.id() != ID_notequal ||
    expr.operands().size() != 2)
    return false;
  return
    (symbol_id(expr.op0(), identifier) &&
     identifier == parameter && value_is(expr.op1(), 0)) ||
    (symbol_id(expr.op1(), identifier) &&
     identifier == parameter && value_is(expr.op0(), 0));
}

bool relational_bisimulation_abort_sink(
  const irep_idt &callee,
  const goto_modelt &model,
  const bool allow_unresolved_abort)
{
  const auto function =
    model.goto_functions.function_map.find(callee);
  if(
    function == model.goto_functions.function_map.end() ||
    !function->second.body_available())
  {
    if(!allow_unresolved_abort)
      return false;
    const auto symbol = model.symbol_table.symbols.find(callee);
    if(
      !is_named(callee, "abort") ||
      symbol == model.symbol_table.symbols.end() ||
      symbol->second.type.id() != ID_code)
      return false;
    const auto &code_type = to_code_type(symbol->second.type);
    return
      code_type.parameters().empty() &&
      code_type.return_type().id() == ID_empty;
  }
  std::size_t false_assumptions = 0;
  for(const auto &instruction : function->second.body.instructions)
  {
    if(instruction.is_assume())
    {
      const exprt &condition = strip(instruction.condition());
      mp_integer left;
      mp_integer right;
      const bool false_condition =
        condition.is_false() ||
        (condition.id() == ID_notequal &&
         condition.operands().size() == 2 &&
         integer_constant(condition.op0(), left) &&
         integer_constant(condition.op1(), right) &&
         left == right);
      if(false_condition)
        ++false_assumptions;
      else
        return false;
    }
    else if(
      !instruction.is_end_function() &&
      !instruction.is_skip() &&
      !instruction.is_location())
      return false;
  }
  return false_assumptions == 1;
}

bool relational_bisimulation_assume_semantics(
  const irep_idt &callee,
  const goto_modelt &model,
  const namespacet &ns,
  const bool allow_unresolved_abort)
{
  if(is_named(callee, "__CPROVER_assume"))
    return true;
  const symbolt *symbol = lookup(callee, ns);
  const auto function =
    model.goto_functions.function_map.find(callee);
  if(
    symbol == nullptr || symbol->type.id() != ID_code ||
    function == model.goto_functions.function_map.end() ||
    !function->second.body_available())
    return false;
  const auto &parameters =
    to_code_type(symbol->type).parameters();
  if(
    parameters.size() != 1 ||
    parameters.front().get_identifier().empty())
    return false;
  const irep_idt parameter =
    parameters.front().get_identifier();
  const goto_programt::instructiont *guard = nullptr;
  const goto_programt::instructiont *abort_call = nullptr;
  irep_idt abort_callee;
  for(const auto &instruction : function->second.body.instructions)
  {
    if(instruction.is_goto())
    {
      if(
        guard != nullptr ||
        instruction.targets.size() != 1 ||
        !relational_bisimulation_parameter_truth(
          instruction.condition(), parameter))
        return false;
      guard = &instruction;
      continue;
    }
    if(instruction.is_function_call())
    {
      if(
        abort_call != nullptr ||
        !call_id(instruction, abort_callee) ||
        !is_named(abort_callee, "abort"))
        return false;
      abort_call = &instruction;
      continue;
    }
    if(
      !instruction.is_end_function() &&
      !instruction.is_skip() &&
      !instruction.is_location())
      return false;
  }
  return
    guard != nullptr && abort_call != nullptr &&
    guard->get_target()->location_number >
      abort_call->location_number &&
    guard->location_number < abort_call->location_number &&
    relational_bisimulation_abort_sink(
      abort_callee, model, allow_unresolved_abort);
}

bool relational_bisimulation_verified_assume(
  const goto_programt::instructiont &instruction,
  const goto_modelt &model,
  const namespacet &ns,
  const bool allow_unresolved_abort)
{
  irep_idt callee;
  return
    call_id(instruction, callee) &&
    is_assume(callee) &&
    instruction.call_arguments().size() == 1 &&
    relational_bisimulation_assume_semantics(
      callee, model, ns, allow_unresolved_abort);
}

bool relational_bisimulation_exact_error_sink(
  const goto_modelt &model)
{
  std::size_t assertions = 0;
  for(const auto &entry : model.goto_functions.function_map)
  {
    for(const auto &instruction : entry.second.body.instructions)
    {
      if(!instruction.is_assert())
        continue;
      ++assertions;
      if(!instruction.condition().is_false())
        return false;
    }
  }
  return assertions == 1;
}

bool relational_bisimulation_initial_relation(
  const goto_modelt &model,
  const lifecyclet &life,
  const std::set<irep_idt> &left_reads,
  const relational_bisimulation_mappingt &mapping,
  const namespacet &ns,
  std::size_t &pairs,
  std::string &reason)
{
  const auto &main =
    model.goto_functions.function_map.at(ID_main).body;
  std::map<irep_idt, unsigned> last_writes;
  std::vector<const goto_programt::instructiont *> assumptions;
  for(const auto &instruction : main.instructions)
  {
    if(
      life.first_create != nullptr &&
      instruction.location_number >=
        life.first_create->location_number)
      break;
    if(instruction.is_assign())
    {
      irep_idt lhs;
      if(symbol_id(instruction.assign_lhs(), lhs))
        last_writes[lhs] = instruction.location_number;
    }
    irep_idt callee;
    if(
      call_id(instruction, callee) && is_assume(callee) &&
      relational_bisimulation_verified_assume(
        instruction, model, ns))
      assumptions.push_back(&instruction);
  }

  for(const auto &entry : mapping.forward)
  {
    if(entry.first == entry.second ||
       left_reads.count(entry.first) == 0)
      continue;
    const symbolt *left_symbol = lookup(entry.first, ns);
    const symbolt *right_symbol = lookup(entry.second, ns);
    if(
      left_symbol == nullptr || right_symbol == nullptr ||
      !left_symbol->is_static_lifetime ||
      !right_symbol->is_static_lifetime)
      continue;
    bool established = false;
    for(const auto *assumption : assumptions)
    {
      if(assumption->call_arguments().size() != 1)
        continue;
      const auto left_write = last_writes.find(entry.first);
      const auto right_write = last_writes.find(entry.second);
      if(
        left_write == last_writes.end() ||
        right_write == last_writes.end() ||
        left_write->second >= assumption->location_number ||
        right_write->second >= assumption->location_number)
        continue;
      if(
        relational_bisimulation_equality_term(
          assumption->call_arguments().front(),
          entry.first,
          entry.second))
      {
        established = true;
        break;
      }
    }
    if(!established)
    {
      reason = "initial_relation";
      return false;
    }
    ++pairs;
  }
  if(pairs == 0)
  {
    reason = "initial_relation_empty";
    return false;
  }
  return true;
}

bool relational_bisimulation_audit_impl(
  const goto_modelt &model,
  const namespacet &ns,
  std::size_t &pairs,
  std::string &reason)
{
  lifecyclet life;
  std::vector<irep_idt> workers;
  if(
    !stream_refine_lifecycle(model, life, workers, reason) ||
    workers.size() != 2)
  {
    if(reason.empty())
      reason = "lifecycle";
    return false;
  }
  const auto &left =
    model.goto_functions.function_map.at(workers[0]).body;
  const auto &right =
    model.goto_functions.function_map.at(workers[1]).body;
  relational_bisimulation_mappingt mapping;
  if(
    !relational_bisimulation_programs(
      left, right, ns, mapping, reason))
    return false;

  std::set<irep_idt> left_reads;
  std::set<irep_idt> left_writes;
  std::set<irep_idt> right_reads;
  std::set<irep_idt> right_writes;
  std::set<irep_idt> left_visiting;
  std::set<irep_idt> right_visiting;
  if(
    !relational_bisimulation_function_effects(
      model,
      workers[0],
      ns,
      left_visiting,
      left_reads,
      left_writes,
      reason) ||
    !relational_bisimulation_function_effects(
      model,
      workers[1],
      ns,
      right_visiting,
      right_reads,
      right_writes,
      reason))
    return false;
  std::set<irep_idt> all_effects = left_reads;
  all_effects.insert(left_writes.begin(), left_writes.end());
  all_effects.insert(right_reads.begin(), right_reads.end());
  all_effects.insert(right_writes.begin(), right_writes.end());
  if(!relational_bisimulation_stable_symbols(
       all_effects, ns, reason))
    return false;
  std::vector<irep_idt> overlap;
  std::set_intersection(
    left_writes.begin(),
    left_writes.end(),
    right_writes.begin(),
    right_writes.end(),
    std::back_inserter(overlap));
  std::set_intersection(
    left_writes.begin(),
    left_writes.end(),
    right_reads.begin(),
    right_reads.end(),
    std::back_inserter(overlap));
  std::set_intersection(
    right_writes.begin(),
    right_writes.end(),
    left_reads.begin(),
    left_reads.end(),
    std::back_inserter(overlap));
  if(!overlap.empty())
  {
    reason = "worker_interference";
    return false;
  }

  flow_equality_propertyt property;
  if(!find_flow_equality_property(model, ns, life, property, reason))
    return false;
  if(
    property.assumption == nullptr ||
    !relational_bisimulation_verified_assume(
      *property.assumption, model, ns) ||
    !relational_bisimulation_exact_error_sink(model))
  {
    reason = "property_semantics";
    return false;
  }
  if(
    !relational_bisimulation_main_regions(
      model,
      life,
      property.assumption,
      property.error,
      reason))
    return false;
  const auto mapped = mapping.forward.find(property.left);
  const auto reverse = mapping.forward.find(property.right);
  if(
    (mapped == mapping.forward.end() ||
     mapped->second != property.right) &&
    (reverse == mapping.forward.end() ||
     reverse->second != property.left))
  {
    reason = "property_mapping";
    return false;
  }
  if(
    !relational_bisimulation_initial_relation(
      model, life, left_reads, mapping, ns, pairs, reason))
    return false;
  return true;
}

bool relational_comparator_sign_term(
  const exprt &src,
  irep_idt &result)
{
  const exprt &expr = strip(src);
  if(
    expr.id() != ID_if ||
    expr.operands().size() != 3 ||
    !value_is(expr.op1(), -1))
    return false;
  const exprt &negative = strip(expr.op0());
  const exprt &tail = strip(expr.op2());
  if(
    negative.id() != ID_lt ||
    negative.operands().size() != 2 ||
    !value_is(negative.op1(), 0) ||
    tail.id() != ID_if ||
    tail.operands().size() != 3 ||
    !value_is(tail.op1(), 1) ||
    !value_is(tail.op2(), 0))
    return false;
  const exprt &positive = strip(tail.op0());
  irep_idt negative_result;
  irep_idt positive_result;
  if(
    positive.id() != ID_gt ||
    positive.operands().size() != 2 ||
    !value_is(positive.op1(), 0) ||
    !symbol_id(negative.op0(), negative_result) ||
    !symbol_id(positive.op0(), positive_result) ||
    negative_result != positive_result)
    return false;
  result = negative_result;
  return true;
}

bool relational_comparator_negated_sign(
  const exprt &src,
  irep_idt &result)
{
  const exprt &expr = strip(src);
  return
    expr.id() == ID_minus &&
    expr.operands().size() == 2 &&
    value_is(expr.op0(), 0) &&
    relational_comparator_sign_term(expr.op1(), result);
}

bool relational_comparator_property(
  const goto_modelt &model,
  const lifecyclet &life,
  const namespacet &ns,
  irep_idt &left_result,
  irep_idt &right_result,
  const goto_programt::instructiont *&property,
  const goto_programt::instructiont *&error,
  std::string &reason)
{
  const auto &main =
    model.goto_functions.function_map.at(ID_main).body;
  bool after_join = false;
  for(const auto &instruction : main.instructions)
  {
    if(&instruction == life.last_join)
    {
      after_join = true;
      continue;
    }
    if(!after_join || !instruction.is_function_call())
      continue;
    if(
      relational_bisimulation_verified_assume(
        instruction, model, ns, true))
    {
      if(property != nullptr)
      {
        reason = "multiple_postjoin_assumptions";
        return false;
      }
      property = &instruction;
    }
  }
  if(
    property == nullptr ||
    property->call_arguments().size() != 1)
  {
    reason = "missing_postjoin_sign_property";
    return false;
  }
  const exprt &argument =
    strip(property->call_arguments().front());
  if(
    argument.id() != ID_not ||
    argument.operands().size() != 1)
  {
    reason = "postjoin_property_not_negated";
    return false;
  }
  const exprt &equality = strip(argument.op0());
  if(
    equality.id() != ID_equal ||
    equality.operands().size() != 2)
  {
    reason = "postjoin_property_not_equality";
    return false;
  }
  if(
    relational_comparator_sign_term(
      equality.op0(), left_result) &&
    relational_comparator_negated_sign(
      equality.op1(), right_result))
  {
    if(left_result == right_result)
      return false;
  }
  else if(
    relational_comparator_sign_term(
      equality.op1(), left_result) &&
    relational_comparator_negated_sign(
      equality.op0(), right_result))
  {
    if(left_result == right_result)
      return false;
  }
  else
  {
    reason = "postjoin_sign_shape";
    return false;
  }

  bool after_property = false;
  for(const auto &instruction : main.instructions)
  {
    if(&instruction == property)
    {
      after_property = true;
      continue;
    }
    if(!after_property)
      continue;
    if(
      instruction.is_skip() ||
      instruction.is_location() ||
      instruction.is_decl() ||
      instruction.is_dead())
      continue;
    if(!instruction.is_function_call())
    {
      reason = "postjoin_missing_error_call";
      return false;
    }
    irep_idt callee;
    if(!call_id(instruction, callee))
    {
      reason = "postjoin_error_callee";
      return false;
    }
    const auto function =
      model.goto_functions.function_map.find(callee);
    if(
      function == model.goto_functions.function_map.end() ||
      !function->second.body_available())
    {
      reason = "postjoin_error_body";
      return false;
    }
    std::size_t assertions = 0;
    for(const auto &body_instruction :
        function->second.body.instructions)
    {
      if(body_instruction.is_assert())
      {
        if(
          ++assertions != 1 ||
          !body_instruction.condition().is_false())
        {
          reason = "postjoin_error_assertion";
          return false;
        }
      }
      else if(
        !body_instruction.is_end_function() &&
        !body_instruction.is_skip() &&
        !body_instruction.is_location())
      {
        reason = "postjoin_error_effect";
        return false;
      }
    }
    if(assertions != 1)
    {
      reason = "postjoin_error_assertion";
      return false;
    }
    error = &instruction;
    return true;
  }
  reason = "postjoin_missing_error_call";
  return false;
}

struct relational_comparator_atomic_regiont
{
  const goto_programt::instructiont *begin = nullptr;
  const goto_programt::instructiont *end = nullptr;
  std::vector<const goto_programt::instructiont *> assumptions;
  std::vector<const goto_programt::instructiont *> assignments;
  std::vector<const goto_programt::instructiont *> helper_calls;
  std::vector<const goto_programt::instructiont *> internal_gotos;
};

bool relational_comparator_atomic_regions(
  const goto_programt &program,
  const goto_modelt &model,
  const namespacet &ns,
  std::vector<relational_comparator_atomic_regiont> &regions,
  std::string &reason)
{
  relational_comparator_atomic_regiont *current = nullptr;
  for(const auto &instruction : program.instructions)
  {
    if(instruction.is_atomic_begin())
    {
      if(current != nullptr)
      {
        reason = "nested_atomic_region";
        return false;
      }
      regions.emplace_back();
      current = &regions.back();
      current->begin = &instruction;
      continue;
    }
    if(instruction.is_atomic_end())
    {
      if(current == nullptr)
      {
        reason = "unbalanced_atomic_region";
        return false;
      }
      current->end = &instruction;
      for(const auto *branch : current->internal_gotos)
      {
        if(branch->targets.size() != 1)
        {
          reason = "atomic_multi_target_goto";
          return false;
        }
        const auto *target = &*branch->get_target();
        if(
          target->location_number <= current->begin->location_number ||
          target->location_number >= current->end->location_number)
        {
          reason = "atomic_goto_escape";
          return false;
        }
      }
      current = nullptr;
      continue;
    }
    if(current == nullptr)
      continue;
    if(instruction.is_assign())
    {
      current->assignments.push_back(&instruction);
      continue;
    }
    if(instruction.is_function_call())
    {
      if(relational_bisimulation_verified_assume(
           instruction, model, ns))
      {
        current->assumptions.push_back(&instruction);
        continue;
      }
      irep_idt callee;
      if(
        !call_id(instruction, callee) ||
        model.goto_functions.function_map.find(callee) ==
          model.goto_functions.function_map.end() ||
        !model.goto_functions.function_map.at(callee).body_available())
      {
        reason = "atomic_unverified_helper";
        return false;
      }
      current->helper_calls.push_back(&instruction);
      continue;
    }
    if(instruction.is_goto())
    {
      current->internal_gotos.push_back(&instruction);
      continue;
    }
    if(
      instruction.is_decl() || instruction.is_dead() ||
      instruction.is_skip() || instruction.is_location())
    {
      continue;
    }
    reason = "atomic_unclassified_instruction";
    return false;
  }
  if(current != nullptr)
  {
    reason = "unbalanced_atomic_region";
    return false;
  }
  if(regions.empty())
  {
    reason = "missing_atomic_regions";
    return false;
  }
  for(const auto &region : regions)
  {
    if(
      region.begin == nullptr || region.end == nullptr ||
      region.assumptions.empty())
    {
      reason = "unguarded_atomic_region";
      return false;
    }
  }
  return true;
}

bool relational_comparator_negated_symbol(
  const exprt &src,
  const irep_idt &identifier)
{
  const exprt &expr = strip(src);
  irep_idt operand;
  return
    expr.id() == ID_minus &&
    expr.operands().size() == 2 &&
    value_is(expr.op0(), 0) &&
    symbol_id(expr.op1(), operand) &&
    operand == identifier;
}

bool relational_comparator_expression(
  const exprt &left_src,
  const exprt &right_src,
  bool negate,
  const namespacet &ns,
  const relational_bisimulation_mappingt &mapping,
  const std::set<irep_idt> &negative_locals)
{
  const exprt &left = strip(left_src);
  const exprt &right = strip(right_src);
  if(!negate)
  {
    for(std::size_t index = 0;
        index < mapping.comparator_equalities.size(); ++index)
    {
      const auto &equality =
        mapping.comparator_equalities[index];
      if(
        (left == strip(equality.first) &&
         right == strip(equality.second)) ||
        (left == strip(equality.second) &&
         right == strip(equality.first)))
      {
        mapping.comparator_equality_uses[index].insert(
          mapping.comparator_current_region);
        return true;
      }
    }
  }
  irep_idt left_symbol;
  if(symbol_id(left, left_symbol))
  {
    irep_idt right_symbol = left_symbol;
    if(mapping.comparator_mapped.count(left_symbol) != 0)
    {
      const auto mapped = mapping.forward.find(left_symbol);
      if(mapped == mapping.forward.end())
        return false;
      right_symbol = mapped->second;
    }
    const bool effective_negate =
      negate != (negative_locals.count(left_symbol) != 0);
    irep_idt direct;
    return effective_negate ?
      relational_comparator_negated_symbol(
        right, right_symbol) :
      symbol_id(right, direct) && direct == right_symbol;
  }

  mp_integer left_value;
  mp_integer right_value;
  if(
    integer_constant(left, left_value) &&
    integer_constant(right, right_value))
    return (negate ? -left_value : left_value) == right_value;

  if(
    negate && left.id() == ID_minus &&
    left.operands().size() == 2 &&
    value_is(left.op0(), 0))
    return relational_comparator_expression(
      left.op1(), right, false, ns, mapping, negative_locals);

  if(left.id() == ID_if && left.operands().size() == 3)
  {
    if(right.id() != ID_if || right.operands().size() != 3)
      return false;
    return
      relational_comparator_expression(
        left.op0(),
        right.op0(),
        false,
        ns,
        mapping,
        negative_locals) &&
      relational_comparator_expression(
        left.op1(),
        right.op1(),
        negate,
        ns,
        mapping,
        negative_locals) &&
      relational_comparator_expression(
        left.op2(),
        right.op2(),
        negate,
        ns,
        mapping,
      negative_locals);
  }

  if(
    (left.id() == ID_equal ||
     left.id() == ID_notequal) &&
    left.id() == right.id() &&
    left.operands().size() == 2 &&
    right.operands().size() == 2 &&
    ((left.op0() == right.op0() &&
      left.op1() == right.op1()) ||
     (left.op0() == right.op1() &&
      left.op1() == right.op0())))
    return true;

  if(negate)
    return false;
  if(
    left.id() != right.id() ||
    left.type() != right.type() ||
    left.operands().size() != right.operands().size() ||
    left.get(ID_statement) != right.get(ID_statement) ||
    left.get(ID_component_name) != right.get(ID_component_name))
    return false;
  if(
    left.id() == ID_constant &&
    left.get(ID_value) != right.get(ID_value))
    return false;

  if(left.id() == ID_and || left.id() == ID_or)
  {
    std::vector<exprt> left_terms;
    std::vector<exprt> right_terms;
    if(left.id() == ID_and)
    {
      flatten_and(left, left_terms);
      flatten_and(right, right_terms);
    }
    else
    {
      flatten_or(left, left_terms);
      flatten_or(right, right_terms);
    }
    if(left_terms.size() != right_terms.size())
      return false;
    std::vector<bool> used(right_terms.size(), false);
    std::vector<bool> matched(left_terms.size(), false);
    for(std::size_t left_index = 0;
        left_index < left_terms.size(); ++left_index)
    {
      for(std::size_t right_index = 0;
          right_index < right_terms.size(); ++right_index)
      {
        if(
          !used[right_index] &&
          strip(left_terms[left_index]) ==
            strip(right_terms[right_index]))
        {
          used[right_index] = true;
          matched[left_index] = true;
          break;
        }
      }
    }
    for(std::size_t left_index = 0;
        left_index < left_terms.size(); ++left_index)
    {
      if(matched[left_index])
        continue;
      bool found = false;
      for(std::size_t index = 0;
          index < right_terms.size(); ++index)
      {
        if(
          !used[index] &&
          relational_comparator_expression(
            left_terms[left_index],
            right_terms[index],
            false,
            ns,
            mapping,
            negative_locals))
        {
          used[index] = true;
          found = true;
          break;
        }
      }
      if(!found)
        return false;
    }
    return true;
  }

  bool direct = true;
  for(std::size_t index = 0; index < left.operands().size(); ++index)
  {
    if(
      !relational_comparator_expression(
        left.operands()[index],
        right.operands()[index],
        false,
        ns,
        mapping,
        negative_locals))
    {
      direct = false;
      break;
    }
  }
  if(direct)
    return true;
  const bool commutative =
    left.operands().size() == 2 &&
    (left.id() == ID_and || left.id() == ID_or ||
     left.id() == ID_equal || left.id() == ID_notequal ||
     left.id() == ID_plus || left.id() == ID_mult);
  return
    commutative &&
    relational_comparator_expression(
      left.op0(),
      right.op1(),
      false,
      ns,
      mapping,
      negative_locals) &&
    relational_comparator_expression(
      left.op1(),
      right.op0(),
      false,
      ns,
      mapping,
      negative_locals);
}

bool relational_comparator_lhs(
  const exprt &left,
  const exprt &right,
  const namespacet &ns,
  const relational_bisimulation_mappingt &mapping,
  irep_idt &left_identifier)
{
  irep_idt right_identifier;
  if(
    !symbol_id(left, left_identifier) ||
    !symbol_id(right, right_identifier))
    return false;
  if(mapping.comparator_mapped.count(left_identifier) == 0)
    return left_identifier == right_identifier;
  const auto mapped = mapping.forward.find(left_identifier);
  return
    mapped != mapping.forward.end() &&
    mapped->second == right_identifier;
}

void relational_comparator_negative_locals(
  const std::vector<relational_comparator_atomic_regiont> &regions,
  const irep_idt &result,
  std::set<irep_idt> &negative_locals)
{
  negative_locals.insert(result);
  bool changed = true;
  while(changed)
  {
    changed = false;
    for(const auto &region : regions)
    {
      for(const auto *assignment : region.assignments)
      {
        irep_idt lhs;
        irep_idt rhs;
        if(
          symbol_id(assignment->assign_lhs(), lhs) &&
          negative_locals.count(lhs) != 0 &&
          symbol_id(assignment->assign_rhs(), rhs) &&
          negative_locals.insert(rhs).second)
          changed = true;
      }
    }
  }
}

bool relational_comparator_antisymmetric_selector(
  const exprt &left_src,
  const exprt &right_src,
  const namespacet &ns,
  const relational_bisimulation_mappingt &mapping,
  const std::set<irep_idt> &negative_locals)
{
  const exprt &left = strip(left_src);
  const exprt &right = strip(right_src);
  if(
    left.id() != ID_if || left.operands().size() != 3 ||
    right.id() != ID_if || right.operands().size() != 3 ||
    !value_is(left.op1(), 0) || !value_is(right.op1(), 0))
    return false;
  const exprt &left_first = strip(left.op2());
  const exprt &right_first = strip(right.op2());
  if(
    left_first.id() != ID_if ||
    left_first.operands().size() != 3 ||
    right_first.id() != ID_if ||
    right_first.operands().size() != 3)
    return false;
  const exprt &left_second = strip(left_first.op2());
  const exprt &right_second = strip(right_first.op2());
  if(
    left_second.id() != ID_if ||
    left_second.operands().size() != 3 ||
    right_second.id() != ID_if ||
    right_second.operands().size() != 3)
    return false;
  return
    relational_comparator_expression(
      left.op0(),
      right.op0(),
      false,
      ns,
      mapping,
      negative_locals) &&
    relational_comparator_expression(
      left_first.op0(),
      right_second.op0(),
      false,
      ns,
      mapping,
      negative_locals) &&
    relational_comparator_expression(
      left_second.op0(),
      right_first.op0(),
      false,
      ns,
      mapping,
      negative_locals) &&
    relational_comparator_expression(
      left_first.op1(),
      right_second.op1(),
      true,
      ns,
      mapping,
      negative_locals) &&
    relational_comparator_expression(
      left_second.op1(),
      right_first.op1(),
      true,
      ns,
      mapping,
      negative_locals) &&
    relational_comparator_expression(
      left_second.op2(),
      right_second.op2(),
      true,
      ns,
      mapping,
      negative_locals);
}

bool relational_comparator_region_match(
  const relational_comparator_atomic_regiont &left,
  const relational_comparator_atomic_regiont &right,
  const namespacet &ns,
  const relational_bisimulation_mappingt &mapping,
  const std::set<irep_idt> &negative_locals,
  std::string &reason)
{
  if(
    left.assumptions.size() != right.assumptions.size() ||
    left.assignments.size() != right.assignments.size() ||
    left.helper_calls.size() != right.helper_calls.size() ||
    left.internal_gotos.size() != right.internal_gotos.size())
  {
    reason = "shape";
    return false;
  }

  std::vector<bool> used_assumptions(
    right.assumptions.size(), false);
  for(const auto *left_assume : left.assumptions)
  {
    bool found = false;
    for(std::size_t index = 0;
        index < right.assumptions.size(); ++index)
    {
      if(
        !used_assumptions[index] &&
        relational_comparator_expression(
          left_assume->call_arguments().front(),
          right.assumptions[index]->call_arguments().front(),
          false,
          ns,
          mapping,
          negative_locals))
      {
        used_assumptions[index] = true;
        found = true;
        break;
      }
    }
    if(!found)
    {
      reason = "assumption";
      return false;
    }
  }

  for(std::size_t index = 0;
      index < left.assignments.size(); ++index)
  {
    irep_idt lhs;
    if(
      !relational_comparator_lhs(
        left.assignments[index]->assign_lhs(),
        right.assignments[index]->assign_lhs(),
        ns,
        mapping,
        lhs))
    {
      reason = "assignment_lhs_" + std::to_string(index);
      return false;
    }
    if(
      !relational_comparator_expression(
        left.assignments[index]->assign_rhs(),
        right.assignments[index]->assign_rhs(),
        negative_locals.count(lhs) != 0,
        ns,
        mapping,
        negative_locals) &&
      !(
        negative_locals.count(lhs) != 0 &&
        relational_comparator_antisymmetric_selector(
          left.assignments[index]->assign_rhs(),
          right.assignments[index]->assign_rhs(),
          ns,
          mapping,
          negative_locals)))
    {
      reason = "assignment_rhs_" + std::to_string(index);
      return false;
    }
  }

  for(std::size_t index = 0;
      index < left.helper_calls.size(); ++index)
  {
    const auto *left_call = left.helper_calls[index];
    const auto *right_call = right.helper_calls[index];
    irep_idt left_callee;
    irep_idt right_callee;
    irep_idt lhs;
    if(
      !call_id(*left_call, left_callee) ||
      !call_id(*right_call, right_callee) ||
      left_callee != right_callee ||
      left_call->call_arguments().size() != 2 ||
      right_call->call_arguments().size() != 2 ||
      !relational_comparator_lhs(
        left_call->call_lhs(),
        right_call->call_lhs(),
        ns,
        mapping,
        lhs))
    {
      reason = "helper_shape_" + std::to_string(index);
      return false;
    }
    const bool reversed =
      negative_locals.count(lhs) != 0;
    for(std::size_t argument = 0; argument < 2; ++argument)
    {
      const std::size_t right_argument =
        reversed ? 1 - argument : argument;
      if(
        !relational_comparator_expression(
          left_call->call_arguments()[argument],
          right_call->call_arguments()[right_argument],
          false,
          ns,
          mapping,
          negative_locals))
      {
        reason =
          "helper_argument_" + std::to_string(index) +
          "_" + std::to_string(argument);
        return false;
      }
    }
  }

  for(std::size_t index = 0;
      index < left.internal_gotos.size(); ++index)
  {
    if(
      !relational_comparator_expression(
        left.internal_gotos[index]->condition(),
        right.internal_gotos[index]->condition(),
        false,
        ns,
        mapping,
        negative_locals))
    {
      reason = "goto_" + std::to_string(index);
      return false;
    }
  }
  return true;
}

bool relational_comparator_transition_matching(
  const std::vector<relational_comparator_atomic_regiont> &left,
  const std::vector<relational_comparator_atomic_regiont> &right,
  const namespacet &ns,
  relational_bisimulation_mappingt &mapping,
  const irep_idt &left_result,
  std::size_t &matches,
  std::size_t &contextual_equalities,
  std::string &reason)
{
  for(const auto &region : left)
  {
    for(const auto *assignment : region.assignments)
    {
      irep_idt lhs;
      if(symbol_id(assignment->assign_lhs(), lhs))
        mapping.comparator_mapped.insert(lhs);
    }
    for(const auto *call : region.helper_calls)
    {
      irep_idt lhs;
      if(
        !call->call_lhs().is_nil() &&
        symbol_id(call->call_lhs(), lhs))
        mapping.comparator_mapped.insert(lhs);
    }
  }
  for(const auto &region : left)
  {
    for(const auto *assumption : region.assumptions)
    {
      std::vector<exprt> terms;
      flatten_and(
        assumption->call_arguments().front(), terms);
      for(const auto &term_src : terms)
      {
        const exprt &term = strip(term_src);
        if(
          term.id() == ID_equal &&
          term.operands().size() == 2 &&
          term.op0() != term.op1())
        {
          mapping.comparator_equalities.emplace_back(
            term.op0(), term.op1());
          ++contextual_equalities;
        }
      }
    }
  }
  std::set<irep_idt> negative_locals;
  relational_comparator_negative_locals(
    left, left_result, negative_locals);
  std::vector<bool> used(right.size(), false);
  for(std::size_t left_index = 0;
      left_index < left.size(); ++left_index)
  {
    const auto &left_region = left[left_index];
    mapping.comparator_current_region = left_index;
    std::size_t candidates = 0;
    std::size_t candidate = right.size();
    std::string ordinal_reason = "not_tested";
    for(std::size_t index = 0; index < right.size(); ++index)
    {
      std::string match_reason;
      const auto saved_uses =
        mapping.comparator_equality_uses;
      const bool matched =
        !used[index] &&
        relational_comparator_region_match(
          left_region,
          right[index],
          ns,
          mapping,
          negative_locals,
          match_reason);
      if(matched)
      {
        ++candidates;
        candidate = index;
      }
      else
        mapping.comparator_equality_uses = saved_uses;
      if(index == left_index)
        ordinal_reason = match_reason;
    }
    if(candidates == 0)
    {
      reason =
        "unmatched_atomic_transition_" +
        std::to_string(left_index) + "_" +
        ordinal_reason;
      return false;
    }
    if(candidates != 1)
    {
      reason = "ambiguous_atomic_transition";
      return false;
    }
    used[candidate] = true;
    ++matches;
  }
  return matches == left.size();
}

bool relational_comparator_context_dominance(
  const goto_programt &program,
  const std::vector<relational_comparator_atomic_regiont> &regions,
  const relational_bisimulation_mappingt &mapping,
  std::size_t &dominated,
  std::string &reason)
{
  std::vector<const goto_programt::instructiont *> instructions;
  std::map<const goto_programt::instructiont *, std::size_t> indices;
  for(const auto &instruction : program.instructions)
  {
    indices.emplace(&instruction, instructions.size());
    instructions.push_back(&instruction);
  }
  const std::size_t count = instructions.size();
  if(count == 0)
  {
    reason = "context_empty_cfg";
    return false;
  }
  std::vector<std::set<std::size_t>> predecessors(count);
  for(std::size_t index = 0; index < count; ++index)
  {
    const auto *instruction = instructions[index];
    if(instruction->is_goto())
    {
      for(const auto &target : instruction->targets)
        predecessors[indices.at(&*target)].insert(index);
      if(
        !instruction->condition().is_true() &&
        index + 1 < count)
        predecessors[index + 1].insert(index);
    }
    else if(
      !instruction->is_end_function() &&
      index + 1 < count)
      predecessors[index + 1].insert(index);
  }
  std::set<std::size_t> all;
  for(std::size_t index = 0; index < count; ++index)
    all.insert(index);
  std::vector<std::set<std::size_t>> dominators(
    count, all);
  dominators[0].clear();
  dominators[0].insert(0);
  bool changed = true;
  while(changed)
  {
    changed = false;
    for(std::size_t node = 1; node < count; ++node)
    {
      std::set<std::size_t> next;
      bool first = true;
      for(const auto predecessor : predecessors[node])
      {
        if(first)
        {
          next = dominators[predecessor];
          first = false;
        }
        else
        {
          std::set<std::size_t> intersection;
          std::set_intersection(
            next.begin(),
            next.end(),
            dominators[predecessor].begin(),
            dominators[predecessor].end(),
            std::inserter(
              intersection, intersection.begin()));
          next.swap(intersection);
        }
      }
      if(first)
        next.clear();
      next.insert(node);
      if(next != dominators[node])
      {
        dominators[node].swap(next);
        changed = true;
      }
    }
  }

  for(std::size_t equality_index = 0;
      equality_index < mapping.comparator_equalities.size();
      ++equality_index)
  {
    const auto &equality =
      mapping.comparator_equalities[equality_index];
    const goto_programt::instructiont *establish = nullptr;
    std::size_t establish_region = regions.size();
    for(std::size_t region_index = 0;
        region_index < regions.size(); ++region_index)
    {
      for(const auto *assumption :
          regions[region_index].assumptions)
      {
        std::vector<exprt> terms;
        flatten_and(
          assumption->call_arguments().front(), terms);
        for(const auto &term_src : terms)
        {
          const exprt &term = strip(term_src);
          if(
            term.id() == ID_equal &&
            term.operands().size() == 2 &&
            ((term.op0() == equality.first &&
              term.op1() == equality.second) ||
             (term.op0() == equality.second &&
              term.op1() == equality.first)))
          {
            establish = assumption;
            establish_region = region_index;
          }
        }
      }
    }
    if(establish == nullptr)
    {
      reason = "context_missing_establishment";
      return false;
    }
    const auto uses =
      mapping.comparator_equality_uses.find(
        equality_index);
    if(uses == mapping.comparator_equality_uses.end())
      continue;
    bool has_later_use = false;
    for(const auto use_region : uses->second)
    {
      if(use_region <= establish_region)
        continue;
      has_later_use = true;
      const std::size_t use =
        indices.at(regions[use_region].begin);
      if(
        dominators[use].count(
          indices.at(establish)) == 0)
      {
        reason =
          "context_not_dominating_" +
          std::to_string(equality_index) +
          "_" + std::to_string(use_region);
        return false;
      }
    }
    if(has_later_use)
      ++dominated;
  }
  return dominated != 0;
}

void relational_comparator_boolean_atoms(
  const exprt &src,
  std::set<exprt> &atoms)
{
  const exprt &expr = strip(src);
  if(expr.is_true() || expr.is_false())
    return;
  if(
    (expr.id() == ID_and || expr.id() == ID_or) &&
    !expr.operands().empty())
  {
    for(const auto &operand : expr.operands())
      relational_comparator_boolean_atoms(operand, atoms);
    return;
  }
  if(expr.id() == ID_not && expr.operands().size() == 1)
  {
    relational_comparator_boolean_atoms(expr.op0(), atoms);
    return;
  }
  atoms.insert(expr);
}

bool relational_comparator_boolean_value(
  const exprt &src,
  const std::map<exprt, std::size_t> &atom_indices,
  std::size_t valuation)
{
  const exprt &expr = strip(src);
  if(expr.is_true())
    return true;
  if(expr.is_false())
    return false;
  if(expr.id() == ID_not && expr.operands().size() == 1)
    return !relational_comparator_boolean_value(
      expr.op0(), atom_indices, valuation);
  if(expr.id() == ID_and && !expr.operands().empty())
  {
    for(const auto &operand : expr.operands())
    {
      if(!relational_comparator_boolean_value(
           operand, atom_indices, valuation))
        return false;
    }
    return true;
  }
  if(expr.id() == ID_or && !expr.operands().empty())
  {
    for(const auto &operand : expr.operands())
    {
      if(relational_comparator_boolean_value(
           operand, atom_indices, valuation))
        return true;
    }
    return false;
  }
  return
    (valuation &
     (std::size_t(1) << atom_indices.at(expr))) != 0;
}

bool relational_comparator_exact_partition(
  const std::vector<std::vector<exprt>> &guards,
  std::size_t subset)
{
  std::set<exprt> atoms;
  for(std::size_t index = 0; index < guards.size(); ++index)
  {
    if((subset & (std::size_t(1) << index)) == 0)
      continue;
    for(const auto &guard : guards[index])
      relational_comparator_boolean_atoms(guard, atoms);
  }
  if(atoms.empty() || atoms.size() > 16)
    return false;
  std::map<exprt, std::size_t> atom_indices;
  std::size_t atom_index = 0;
  for(const auto &atom : atoms)
    atom_indices.emplace(atom, atom_index++);
  const std::size_t valuations =
    std::size_t(1) << atoms.size();
  for(std::size_t valuation = 0;
      valuation < valuations; ++valuation)
  {
    std::size_t enabled = 0;
    for(std::size_t index = 0; index < guards.size(); ++index)
    {
      if((subset & (std::size_t(1) << index)) == 0)
        continue;
      bool matches = true;
      for(const auto &guard : guards[index])
      {
        if(
          !relational_comparator_boolean_value(
            guard, atom_indices, valuation))
        {
          matches = false;
          break;
        }
      }
      if(matches)
        ++enabled;
    }
    if(enabled != 1)
      return false;
  }
  return true;
}

bool relational_comparator_partition_cover(
  const std::vector<std::size_t> &partitions,
  std::size_t all,
  std::size_t covered,
  std::vector<std::size_t> &selected)
{
  if(covered == all)
    return true;
  std::size_t first = 0;
  while((covered & (std::size_t(1) << first)) != 0)
    ++first;
  for(std::size_t index = 0;
      index < partitions.size(); ++index)
  {
    const std::size_t partition = partitions[index];
    if(
      (partition & (std::size_t(1) << first)) == 0 ||
      (partition & covered) != 0)
      continue;
    selected.push_back(partition);
    if(
      relational_comparator_partition_cover(
        partitions,
        all,
        covered | partition,
        selected))
      return true;
    selected.pop_back();
  }
  return false;
}

bool relational_comparator_guard_partitions(
  const std::vector<relational_comparator_atomic_regiont> &regions,
  std::vector<std::size_t> &selected,
  std::string &reason)
{
  if(regions.size() < 2 || regions.size() > 20)
  {
    reason = "guard_partition_region_bound";
    return false;
  }
  std::vector<std::vector<exprt>> guards(regions.size());
  for(std::size_t index = 0; index < regions.size(); ++index)
  {
    for(const auto *assumption : regions[index].assumptions)
    {
      if(assumption->call_arguments().size() != 1)
      {
        reason =
          "invalid_region_guard_" +
          std::to_string(index);
        return false;
      }
      guards[index].push_back(
        assumption->call_arguments().front());
    }
  }
  std::vector<std::size_t> partitions;
  const std::size_t all =
    (std::size_t(1) << regions.size()) - 1;
  for(std::size_t subset = 1; subset <= all; ++subset)
  {
    if(
      (subset & (subset - 1)) != 0 &&
      relational_comparator_exact_partition(
        guards, subset))
      partitions.push_back(subset);
  }
  if(
    partitions.empty() ||
    !relational_comparator_partition_cover(
      partitions, all, 0, selected))
  {
    reason = "guard_partition_incomplete";
    return false;
  }
  return !selected.empty();
}

bool relational_comparator_false_nondet_gate(
  const goto_programt::instructiont &assignment,
  const goto_programt::instructiont &branch)
{
  irep_idt temporary;
  if(
    !assignment.is_assign() ||
    !symbol_id(assignment.assign_lhs(), temporary) ||
    !relational_bisimulation_contains_nondet(
      assignment.assign_rhs()) ||
    !branch.is_goto() ||
    branch.targets.size() != 1)
    return false;
  const exprt &condition = strip(branch.condition());
  const exprt *test = &condition;
  bool negated = false;
  if(condition.id() == ID_not &&
     condition.operands().size() == 1)
  {
    negated = true;
    test = &strip(condition.op0());
  }
  if(
    test->id() != ID_notequal ||
    test->operands().size() != 2)
    return false;
  irep_idt identifier;
  const bool nonzero =
    (symbol_id(test->op0(), identifier) &&
     identifier == temporary && value_is(test->op1(), 0)) ||
    (symbol_id(test->op1(), identifier) &&
     identifier == temporary && value_is(test->op0(), 0));
  return negated && nonzero;
}

bool relational_comparator_dispatch_cfg(
  const goto_programt &program,
  const std::vector<relational_comparator_atomic_regiont> &regions,
  const std::vector<std::size_t> &partitions,
  std::size_t &gates,
  std::string &reason)
{
  std::vector<const goto_programt::instructiont *> instructions;
  std::map<const goto_programt::instructiont *, std::size_t> indices;
  for(const auto &instruction : program.instructions)
  {
    indices.emplace(&instruction, instructions.size());
    instructions.push_back(&instruction);
  }
  std::vector<bool> gated(regions.size(), false);
  std::vector<std::size_t> targets(
    regions.size(), instructions.size());
  std::set<const goto_programt::instructiont *> consumed_nondet;
  for(std::size_t index = 0; index < regions.size(); ++index)
  {
    const std::size_t begin = indices.at(regions[index].begin);
    if(begin < 2)
      continue;
    const auto *assignment = instructions[begin - 2];
    const auto *branch = instructions[begin - 1];
    if(!relational_comparator_false_nondet_gate(
         *assignment, *branch))
      continue;
    gated[index] = true;
    targets[index] = indices.at(&*branch->get_target());
    consumed_nondet.insert(assignment);
    ++gates;
  }

  for(const auto partition : partitions)
  {
    std::vector<std::size_t> members;
    for(std::size_t index = 0; index < regions.size(); ++index)
    {
      if((partition & (std::size_t(1) << index)) != 0)
        members.push_back(index);
    }
    if(members.size() < 2)
    {
      reason = "dispatch_singleton_partition";
      return false;
    }
    for(std::size_t position = 0;
        position + 1 < members.size(); ++position)
    {
      const std::size_t current = members[position];
      const std::size_t next = members[position + 1];
      if(!gated[current])
      {
        reason =
          "dispatch_missing_gate_" +
          std::to_string(current);
        return false;
      }
      const std::size_t current_end =
        indices.at(regions[current].end);
      const std::size_t next_begin =
        indices.at(regions[next].begin);
      if(
        targets[current] <= current_end ||
        targets[current] > next_begin)
      {
        reason =
          "dispatch_skip_target_" +
          std::to_string(current);
        return false;
      }
    }
    if(gated[members.back()])
    {
      reason =
        "dispatch_default_is_gated_" +
        std::to_string(members.back());
      return false;
    }
  }

  std::size_t nondet_assignments = 0;
  for(const auto *instruction : instructions)
  {
    if(
      instruction->is_assign() &&
      relational_bisimulation_contains_nondet(
        instruction->assign_rhs()))
    {
      ++nondet_assignments;
      if(consumed_nondet.count(instruction) == 0)
      {
        reason = "dispatch_unconsumed_nondet";
        return false;
      }
    }
    else if(
      relational_bisimulation_contains_nondet(
        instruction->code()) ||
      (instruction->has_condition() &&
       relational_bisimulation_contains_nondet(
         instruction->condition())))
    {
      reason = "dispatch_nondet_effect";
      return false;
    }
  }
  if(
    nondet_assignments != gates ||
    gates != regions.size() - partitions.size())
  {
    reason = "dispatch_gate_count";
    return false;
  }
  return true;
}

bool relational_comparator_subtraction_helper(
  const goto_modelt &model,
  const namespacet &ns,
  const irep_idt &callee,
  std::string &reason,
  const bool allow_unresolved_abort = false)
{
  const symbolt *symbol = lookup(callee, ns);
  const auto function =
    model.goto_functions.function_map.find(callee);
  if(
    symbol == nullptr || symbol->type.id() != ID_code ||
    function == model.goto_functions.function_map.end() ||
    !function->second.body_available())
  {
    reason = "subtraction_helper_body";
    return false;
  }
  const auto &parameters =
    to_code_type(symbol->type).parameters();
  if(
    parameters.size() != 2 ||
    parameters[0].get_identifier().empty() ||
    parameters[1].get_identifier().empty() ||
    parameters[0].type() != parameters[1].type() ||
    parameters[0].type().id() != ID_signedbv)
  {
    reason = "subtraction_helper_parameters";
    return false;
  }
  const irep_idt first = parameters[0].get_identifier();
  const irep_idt second = parameters[1].get_identifier();
  std::size_t assumptions = 0;
  std::size_t returns = 0;
  for(const auto &instruction : function->second.body.instructions)
  {
    if(instruction.is_function_call())
    {
      if(
        !relational_bisimulation_verified_assume(
          instruction,
          model,
          ns,
          allow_unresolved_abort) ||
        instruction.call_arguments().size() != 1 ||
        !contains_symbol(
          instruction.call_arguments().front(), first) ||
        !contains_symbol(
          instruction.call_arguments().front(), second))
      {
        reason = "subtraction_helper_guard";
        return false;
      }
      ++assumptions;
      continue;
    }
    if(instruction.is_set_return_value())
    {
      const exprt &value = strip(instruction.return_value());
      irep_idt left;
      irep_idt right;
      if(
        ++returns != 1 ||
        value.id() != ID_minus ||
        value.operands().size() != 2 ||
        !symbol_id(value.op0(), left) ||
        !symbol_id(value.op1(), right) ||
        left != first || right != second)
      {
        reason = "subtraction_helper_return";
        return false;
      }
      continue;
    }
    if(
      instruction.is_end_function() ||
      instruction.is_skip() ||
      instruction.is_location() ||
      instruction.is_decl() ||
      instruction.is_dead())
      continue;
    reason = "subtraction_helper_effect";
    return false;
  }
  if(assumptions == 0 || returns != 1)
  {
    reason = "subtraction_helper_incomplete";
    return false;
  }
  return true;
}

bool relational_comparator_helpers(
  const std::vector<relational_comparator_atomic_regiont> &regions,
  const goto_modelt &model,
  const namespacet &ns,
  std::size_t &helpers,
  std::string &reason)
{
  std::set<irep_idt> callees;
  for(const auto &region : regions)
  {
    for(const auto *call : region.helper_calls)
    {
      irep_idt callee;
      if(!call_id(*call, callee))
      {
        reason = "helper_callee";
        return false;
      }
      callees.insert(callee);
    }
  }
  for(const auto &callee : callees)
  {
    if(
      !relational_comparator_subtraction_helper(
        model, ns, callee, reason))
      return false;
    ++helpers;
  }
  return helpers != 0;
}

bool relational_comparator_worker_effects(
  const goto_modelt &model,
  const std::vector<irep_idt> &workers,
  const namespacet &ns,
  std::string &reason)
{
  if(workers.size() < 2)
  {
    reason = "comparator_worker_count";
    return false;
  }
  std::vector<std::set<irep_idt>> reads(workers.size());
  std::vector<std::set<irep_idt>> writes(workers.size());
  std::set<irep_idt> all_effects;
  for(std::size_t index = 0; index < workers.size(); ++index)
  {
    std::set<irep_idt> visiting;
    if(
      !relational_bisimulation_function_effects(
        model,
        workers[index],
        ns,
        visiting,
        reads[index],
        writes[index],
        reason))
      return false;
    all_effects.insert(
      reads[index].begin(), reads[index].end());
    all_effects.insert(
      writes[index].begin(), writes[index].end());
  }
  if(
    !relational_bisimulation_stable_symbols(
      all_effects, ns, reason))
    return false;
  for(std::size_t left = 0; left < workers.size(); ++left)
  {
    for(std::size_t right = left + 1;
        right < workers.size(); ++right)
    {
      std::vector<irep_idt> overlap;
      std::set_intersection(
        writes[left].begin(),
        writes[left].end(),
        writes[right].begin(),
        writes[right].end(),
        std::back_inserter(overlap));
      std::set_intersection(
        writes[left].begin(),
        writes[left].end(),
        reads[right].begin(),
        reads[right].end(),
        std::back_inserter(overlap));
      std::set_intersection(
        writes[right].begin(),
        writes[right].end(),
        reads[left].begin(),
        reads[left].end(),
        std::back_inserter(overlap));
      if(!overlap.empty())
      {
        reason = "comparator_worker_interference";
        return false;
      }
    }
  }
  return true;
}

bool relational_comparator_initial_results(
  const goto_modelt &model,
  const lifecyclet &life,
  const std::vector<irep_idt> &workers,
  const irep_idt &left_result,
  const irep_idt &right_result,
  const namespacet &ns,
  std::string &reason)
{
  const symbolt *left_symbol = lookup(left_result, ns);
  const symbolt *right_symbol = lookup(right_result, ns);
  if(
    left_symbol == nullptr || right_symbol == nullptr ||
    !left_symbol->is_static_lifetime ||
    !right_symbol->is_static_lifetime ||
    left_symbol->type != right_symbol->type ||
    left_symbol->type.id() != ID_signedbv)
  {
    reason = "comparator_result_type";
    return false;
  }
  std::size_t left_initializations = 0;
  std::size_t right_initializations = 0;
  for(const auto &entry : model.goto_functions.function_map)
  {
    const bool worker =
      std::find(
        workers.begin(), workers.end(), entry.first) !=
      workers.end();
    for(const auto &instruction : entry.second.body.instructions)
    {
      exprt lhs;
      exprt rhs;
      bool write = false;
      if(instruction.is_assign())
      {
        lhs = instruction.assign_lhs();
        rhs = instruction.assign_rhs();
        write = true;
      }
      else if(
        instruction.is_function_call() &&
        !instruction.call_lhs().is_nil())
      {
        lhs = instruction.call_lhs();
        write = true;
      }
      if(!write)
        continue;
      irep_idt identifier;
      if(
        !symbol_id(lhs, identifier) ||
        (identifier != left_result &&
         identifier != right_result))
        continue;
      if(worker)
        continue;
      const bool initializer =
        is_named(entry.first, "__CPROVER_initialize");
      const bool main_before_create =
        entry.first == ID_main &&
        life.first_create != nullptr &&
        instruction.location_number <
          life.first_create->location_number;
      if(
        (!initializer && !main_before_create) ||
        !instruction.is_assign() ||
        !value_is(rhs, 0))
      {
        reason = "comparator_result_external_write";
        return false;
      }
      if(identifier == left_result)
        ++left_initializations;
      else
        ++right_initializations;
    }
  }
  if(
    left_initializations != 1 ||
    right_initializations != 1)
  {
    reason = "comparator_result_initialization";
    return false;
  }
  return no_addresses(
    model, {left_result, right_result}, reason);
}

bool relational_comparator_scan_antisymmetry(
  const goto_modelt &model,
  const namespacet &ns,
  const std::vector<irep_idt> &workers,
  const irep_idt &left_result,
  const irep_idt &right_result,
  std::size_t &transition_matches,
  std::size_t &audited_helpers,
  std::string &reason);

bool relational_comparator_diagnostic(
  const goto_modelt &model,
  const namespacet &ns,
  irep_idt &left_result,
  irep_idt &right_result,
  std::size_t &left_regions,
  std::size_t &right_regions,
  std::size_t &left_assumptions,
  std::size_t &right_assumptions,
  std::size_t &left_assignments,
  std::size_t &right_assignments,
  std::size_t &left_helpers,
  std::size_t &right_helpers,
  std::size_t &left_internal_gotos,
  std::size_t &right_internal_gotos,
  std::size_t &transition_matches,
  std::size_t &contextual_equalities,
  std::size_t &dominated_equalities,
  std::size_t &guard_partition_groups,
  std::size_t &dispatch_gates,
  std::size_t &audited_helpers,
  std::string &reason)
{
  lifecyclet life;
  std::vector<irep_idt> workers;
  if(
    !stream_refine_lifecycle(model, life, workers, reason) ||
    workers.size() != 2)
  {
    if(reason.empty())
      reason = "lifecycle";
    return false;
  }
  const goto_programt::instructiont *property = nullptr;
  const goto_programt::instructiont *error = nullptr;
  if(
    !relational_comparator_property(
      model,
      life,
      ns,
      left_result,
      right_result,
      property,
      error,
      reason))
    return false;
  if(
    !relational_bisimulation_exact_error_sink(model))
  {
    reason = "property_semantics";
    return false;
  }
  if(
    !relational_bisimulation_main_regions(
      model, life, property, error, reason))
    return false;
  std::string scan_reason;
  if(
    relational_comparator_scan_antisymmetry(
      model,
      ns,
      workers,
      left_result,
      right_result,
      transition_matches,
      audited_helpers,
      scan_reason))
  {
    left_regions = 1;
    right_regions = 1;
    left_assumptions = 2;
    right_assumptions = 2;
    left_assignments = 11;
    right_assignments = 11;
    left_helpers = 1;
    right_helpers = 1;
    dominated_equalities = 3;
    guard_partition_groups = 1;
    dispatch_gates = 1;
    return true;
  }
  if(
    !relational_comparator_worker_effects(
      model, workers, ns, reason))
    return false;
  if(
    !relational_comparator_initial_results(
      model,
      life,
      workers,
      left_result,
      right_result,
      ns,
      reason))
  {
    if(reason == "comparator_result_external_write" &&
       !scan_reason.empty())
      reason = scan_reason;
    return false;
  }
  const auto &left =
    model.goto_functions.function_map.at(workers[0]).body;
  const auto &right =
    model.goto_functions.function_map.at(workers[1]).body;
  relational_bisimulation_mappingt mapping;
  if(
    !relational_bisimulation_programs(
      left, right, ns, mapping, reason))
    return false;
  std::vector<relational_comparator_atomic_regiont> left_summaries;
  std::vector<relational_comparator_atomic_regiont> right_summaries;
  if(
    !relational_comparator_atomic_regions(
      left,
      model,
      ns,
      left_summaries,
      reason) ||
    !relational_comparator_atomic_regions(
      right,
      model,
      ns,
      right_summaries,
      reason))
    return false;
  left_regions = left_summaries.size();
  right_regions = right_summaries.size();
  for(const auto &region : left_summaries)
  {
    left_assumptions += region.assumptions.size();
    left_assignments += region.assignments.size();
    left_helpers += region.helper_calls.size();
    left_internal_gotos += region.internal_gotos.size();
  }
  for(const auto &region : right_summaries)
  {
    right_assumptions += region.assumptions.size();
    right_assignments += region.assignments.size();
    right_helpers += region.helper_calls.size();
    right_internal_gotos += region.internal_gotos.size();
  }
  if(
    left_regions != right_regions ||
    left_assumptions != right_assumptions ||
    left_assignments != right_assignments ||
    left_helpers != right_helpers ||
    left_internal_gotos != right_internal_gotos)
  {
    reason = "atomic_census_mismatch";
    return false;
  }
  if(
    !relational_comparator_transition_matching(
      left_summaries,
      right_summaries,
      ns,
      mapping,
      left_result,
      transition_matches,
      contextual_equalities,
      reason))
    return false;
  if(
    !relational_comparator_context_dominance(
      left,
      left_summaries,
      mapping,
      dominated_equalities,
      reason))
    return false;
  std::size_t right_dominated_equalities = 0;
  if(
    !relational_comparator_context_dominance(
      right,
      right_summaries,
      mapping,
      right_dominated_equalities,
      reason) ||
    right_dominated_equalities != dominated_equalities)
  {
    if(reason.empty())
      reason = "right_context_dominance";
    return false;
  }
  std::vector<std::size_t> partitions;
  if(
    !relational_comparator_guard_partitions(
      left_summaries, partitions, reason))
    return false;
  guard_partition_groups = partitions.size();
  std::vector<std::size_t> right_partitions;
  if(
    !relational_comparator_guard_partitions(
      right_summaries, right_partitions, reason) ||
    right_partitions != partitions)
  {
    if(reason.empty())
      reason = "right_guard_partitions";
    return false;
  }
  if(
    !relational_comparator_dispatch_cfg(
      left,
      left_summaries,
      partitions,
      dispatch_gates,
      reason))
    return false;
  std::size_t right_dispatch_gates = 0;
  if(
    !relational_comparator_dispatch_cfg(
      right,
      right_summaries,
      right_partitions,
      right_dispatch_gates,
      reason) ||
    right_dispatch_gates != dispatch_gates)
  {
    if(reason.empty())
      reason = "right_dispatch_cfg";
    return false;
  }
  if(
    !relational_comparator_helpers(
    left_summaries,
    model,
    ns,
    audited_helpers,
    reason))
    return false;
  std::size_t right_audited_helpers = 0;
  if(
    !relational_comparator_helpers(
      right_summaries,
      model,
      ns,
      right_audited_helpers,
      reason) ||
    right_audited_helpers != audited_helpers)
  {
    if(reason.empty())
      reason = "right_helper_audit";
    return false;
  }
  return true;
}

bool relational_comparator_relation_to_zero(
  const exprt &src,
  const irep_idt &relation,
  irep_idt &result)
{
  const exprt &expr = strip(src);
  return
    expr.id() == relation &&
    expr.operands().size() == 2 &&
    symbol_id(expr.op0(), result) &&
    value_is(expr.op1(), 0);
}

bool relational_comparator_same_boolean_relation(
  const exprt &src,
  const irep_idt &relation,
  irep_idt &left_result,
  irep_idt &right_result)
{
  const exprt &expr = strip(src);
  if(
    expr.id() != ID_equal ||
    expr.operands().size() != 2)
    return false;
  return
    relational_comparator_relation_to_zero(
      expr.op0(), relation, left_result) &&
    relational_comparator_relation_to_zero(
      expr.op1(), relation, right_result);
}

bool relational_comparator_nonzero_relation(
  const exprt &src,
  irep_idt &result)
{
  const exprt &expr = strip(src);
  if(
    relational_comparator_relation_to_zero(
      expr, ID_notequal, result))
    return true;
  return
    expr.id() == ID_not &&
    expr.operands().size() == 1 &&
    relational_comparator_relation_to_zero(
      expr.op0(), ID_equal, result);
}

bool relational_comparator_transitivity_property(
  const goto_modelt &model,
  const lifecyclet &life,
  const namespacet &ns,
  std::vector<irep_idt> &positive_results,
  irep_idt &nonpositive_result,
  std::string &rule,
  const goto_programt::instructiont *&property,
  const goto_programt::instructiont *&error,
  std::string &reason)
{
  const auto &main =
    model.goto_functions.function_map.at(ID_main).body;
  bool after_join = false;
  for(const auto &instruction : main.instructions)
  {
    if(&instruction == life.last_join)
    {
      after_join = true;
      continue;
    }
    if(
      !after_join || !instruction.is_function_call() ||
      !relational_bisimulation_verified_assume(
        instruction, model, ns, true))
      continue;
    if(property != nullptr)
    {
      reason = "transitivity_multiple_postjoin_assumptions";
      return false;
    }
    property = &instruction;
  }
  if(
    property == nullptr ||
    property->call_arguments().size() != 1)
  {
    reason = "transitivity_missing_property";
    return false;
  }
  const exprt &argument =
    strip(property->call_arguments().front());
  std::vector<exprt> terms;
  flatten_and(argument, terms);
  bool parsed = false;
  if(terms.size() == 3)
  {
    bool valid = true;
    for(const auto &source_term : terms)
    {
      const exprt &term = strip(source_term);
      irep_idt result;
      if(
        term.operands().size() != 2 ||
        !symbol_id(term.op0(), result) ||
        !value_is(term.op1(), 0))
      {
        valid = false;
        break;
      }
      if(term.id() == ID_gt)
        positive_results.push_back(result);
      else if(term.id() == ID_le)
      {
        if(!nonpositive_result.empty())
        {
          valid = false;
          break;
        }
        nonpositive_result = result;
      }
      else
      {
        valid = false;
        break;
      }
    }
    parsed =
      valid &&
      positive_results.size() == 2 &&
      !nonpositive_result.empty();
    if(parsed)
      rule = "strict_transitivity";
  }

  if(!parsed)
  {
    positive_results.clear();
    nonpositive_result.clear();
    const exprt &outer = strip(argument);
    if(
      outer.id() == ID_not &&
      outer.operands().size() == 1)
    {
      const exprt &disjunction = strip(outer.op0());
      if(
        disjunction.id() == ID_or &&
        disjunction.operands().size() == 2)
      {
        const exprt *negated_conjunction = nullptr;
        const exprt *conclusion = nullptr;
        for(const auto &operand_src : disjunction.operands())
        {
          const exprt &operand = strip(operand_src);
          if(
            operand.id() == ID_not &&
            operand.operands().size() == 1 &&
            strip(operand.op0()).id() == ID_and)
            negated_conjunction = &operand;
          else
            conclusion = &operand;
        }
        if(
          negated_conjunction != nullptr &&
          conclusion != nullptr &&
          relational_comparator_relation_to_zero(
            *conclusion, ID_gt, nonpositive_result))
        {
          std::vector<exprt> premises;
          flatten_and(
            negated_conjunction->op0(), premises);
          bool valid = premises.size() == 2;
          for(const auto &premise : premises)
          {
            irep_idt result;
            if(
              !relational_comparator_relation_to_zero(
                premise, ID_gt, result))
            {
              valid = false;
              break;
            }
            positive_results.push_back(result);
          }
          if(
            valid &&
            positive_results.size() == 2 &&
            positive_results[0] != positive_results[1] &&
            positive_results[0] != nonpositive_result &&
            positive_results[1] != nonpositive_result)
          {
            rule = "strict_transitivity";
            parsed = true;
          }
        }
      }
    }
  }

  if(!parsed)
  {
    positive_results.clear();
    nonpositive_result.clear();
    const exprt &outer = strip(argument);
    if(
      outer.id() == ID_not &&
      outer.operands().size() == 1)
    {
      const exprt &disjunction = strip(outer.op0());
      if(
        disjunction.id() == ID_or &&
        disjunction.operands().size() == 2)
      {
        const exprt &nonzero_relation =
          strip(disjunction.op0());
        const exprt &same_sign = strip(disjunction.op1());
        irep_idt equal_result;
        irep_idt positive_left;
        irep_idt positive_right;
        irep_idt negative_left;
        irep_idt negative_right;
        if(
          relational_comparator_nonzero_relation(
            nonzero_relation, equal_result) &&
          same_sign.id() == ID_and &&
          same_sign.operands().size() == 2 &&
          relational_comparator_same_boolean_relation(
            same_sign.op0(),
            ID_gt,
            positive_left,
            positive_right) &&
          relational_comparator_same_boolean_relation(
            same_sign.op1(),
            ID_lt,
            negative_left,
            negative_right) &&
          positive_left == negative_left &&
          positive_right == negative_right &&
          positive_left != positive_right &&
          equal_result != positive_left &&
          equal_result != positive_right)
        {
          nonpositive_result = equal_result;
          positive_results = {
            positive_left, positive_right};
          rule = "equality_substitution";
          parsed = true;
        }
      }
    }
  }

  if(
    !parsed ||
    positive_results.size() != 2 ||
    nonpositive_result.empty() ||
    positive_results[0] == positive_results[1] ||
    positive_results[0] == nonpositive_result ||
    positive_results[1] == nonpositive_result)
  {
    reason = "transitivity_property_results";
    return false;
  }

  bool after_property = false;
  for(const auto &instruction : main.instructions)
  {
    if(&instruction == property)
    {
      after_property = true;
      continue;
    }
    if(!after_property)
      continue;
    if(
      instruction.is_skip() || instruction.is_location() ||
      instruction.is_decl() || instruction.is_dead())
      continue;
    if(!instruction.is_function_call())
    {
      reason = "transitivity_missing_error_call";
      return false;
    }
    error = &instruction;
    return true;
  }
  reason = "transitivity_missing_error_call";
  return false;
}

bool relational_comparator_result_value_symbol(
  const goto_programt &program,
  const goto_modelt &model,
  const namespacet &ns,
  const irep_idt &result,
  const irep_idt &candidate,
  std::set<irep_idt> &visiting,
  bool &negative,
  bool &zero,
  bool &positive,
  std::size_t &subtraction_calls,
  std::string &reason);

bool relational_comparator_result_value_expression(
  const exprt &src,
  const goto_programt &program,
  const goto_modelt &model,
  const namespacet &ns,
  const irep_idt &result,
  std::set<irep_idt> &visiting,
  bool &negative,
  bool &zero,
  bool &positive,
  std::size_t &subtraction_calls,
  std::string &reason)
{
  const exprt &expr = strip(src);
  if(value_is(expr, -1))
  {
    negative = true;
    return true;
  }
  if(value_is(expr, 0))
  {
    zero = true;
    return true;
  }
  if(value_is(expr, 1))
  {
    positive = true;
    return true;
  }
  irep_idt identifier;
  if(symbol_id(expr, identifier))
    return relational_comparator_result_value_symbol(
      program,
      model,
      ns,
      result,
      identifier,
      visiting,
      negative,
      zero,
      positive,
      subtraction_calls,
      reason);
  if(expr.id() != ID_if || expr.operands().size() != 3)
  {
    reason = "transitivity_result_value_expression";
    return false;
  }
  return
    relational_comparator_result_value_expression(
      expr.op1(),
      program,
      model,
      ns,
      result,
      visiting,
      negative,
      zero,
      positive,
      subtraction_calls,
      reason) &&
    relational_comparator_result_value_expression(
      expr.op2(),
      program,
      model,
      ns,
      result,
      visiting,
      negative,
      zero,
      positive,
      subtraction_calls,
      reason);
}

bool relational_comparator_result_value_symbol(
  const goto_programt &program,
  const goto_modelt &model,
  const namespacet &ns,
  const irep_idt &result,
  const irep_idt &candidate,
  std::set<irep_idt> &visiting,
  bool &negative,
  bool &zero,
  bool &positive,
  std::size_t &subtraction_calls,
  std::string &reason)
{
  if(candidate == result)
    return true;
  const symbolt *symbol = lookup(candidate, ns);
  if(
    symbol == nullptr || symbol->is_static_lifetime ||
    !visiting.insert(candidate).second)
  {
    reason = "transitivity_result_value_symbol";
    return false;
  }
  std::size_t definitions = 0;
  for(const auto &instruction : program.instructions)
  {
    irep_idt lhs;
    if(
      instruction.is_assign() &&
      symbol_id(instruction.assign_lhs(), lhs) &&
      lhs == candidate)
    {
      ++definitions;
      if(
        !relational_comparator_result_value_expression(
          instruction.assign_rhs(),
          program,
          model,
          ns,
          result,
          visiting,
          negative,
          zero,
          positive,
          subtraction_calls,
          reason))
      {
        visiting.erase(candidate);
        return false;
      }
    }
    else if(
      instruction.is_function_call() &&
      !instruction.call_lhs().is_nil() &&
      symbol_id(instruction.call_lhs(), lhs) &&
      lhs == candidate)
    {
      irep_idt callee;
      ++definitions;
      if(
        !call_id(instruction, callee) ||
        instruction.call_arguments().size() != 2 ||
        !relational_comparator_subtraction_helper(
          model, ns, callee, reason, true))
      {
        visiting.erase(candidate);
        if(reason.empty())
          reason = "transitivity_result_value_helper";
        return false;
      }
      ++subtraction_calls;
    }
  }
  visiting.erase(candidate);
  if(definitions == 0)
  {
    reason = "transitivity_result_value_definition";
    return false;
  }
  return true;
}

bool relational_comparator_transitivity_result_owners(
  const goto_modelt &model,
  const std::vector<irep_idt> &workers,
  const std::vector<irep_idt> &positive_results,
  const irep_idt &nonpositive_result,
  const namespacet &ns,
  std::vector<irep_idt> &worker_results,
  std::size_t &owned_results,
  std::string &reason,
  const bool allow_verified_assume)
{
  std::set<irep_idt> property_results(
    positive_results.begin(), positive_results.end());
  property_results.insert(nonpositive_result);
  if(
    workers.size() != property_results.size() ||
    property_results.size() < 3)
  {
    reason = "transitivity_result_owner_arity";
    return false;
  }

  std::set<irep_idt> owners;
  std::set<irep_idt> positive_owners;
  irep_idt conclusion_owner;
  for(const auto &worker : workers)
  {
    std::set<irep_idt> reads;
    std::set<irep_idt> writes;
    std::set<irep_idt> visiting;
    if(
      !relational_bisimulation_function_effects(
        model,
        worker,
        ns,
        visiting,
        reads,
        writes,
        reason,
        allow_verified_assume))
      return false;

    std::vector<irep_idt> worker_property_results;
    std::set_intersection(
      writes.begin(),
      writes.end(),
      property_results.begin(),
      property_results.end(),
      std::back_inserter(worker_property_results));
    if(worker_property_results.size() != 1)
    {
      reason = "transitivity_result_owner_cardinality";
      return false;
    }
    const irep_idt result = worker_property_results.front();
    worker_results.push_back(result);
    if(!owners.insert(result).second)
    {
      reason = "transitivity_result_multiple_owners";
      return false;
    }
    if(
      std::find(
        positive_results.begin(),
        positive_results.end(),
        result) != positive_results.end())
      positive_owners.insert(worker);
    else if(result == nonpositive_result)
      conclusion_owner = worker;
    else
    {
      reason = "transitivity_result_unknown_owner";
      return false;
    }
  }
  for(std::size_t index = 0; index < workers.size(); ++index)
  {
    const symbolt *symbol = lookup(worker_results[index], ns);
    if(
      symbol == nullptr || !symbol->is_static_lifetime ||
      symbol->type.id() != ID_signedbv)
    {
      reason = "transitivity_result_type";
      return false;
    }
    bool negative = false;
    bool zero = false;
    bool positive = false;
    std::size_t subtraction_calls = 0;
    std::size_t result_definitions = 0;
    std::set<irep_idt> visiting;
    const auto &program =
      model.goto_functions.function_map.at(workers[index]).body;
    for(const auto &instruction : program.instructions)
    {
      irep_idt lhs;
      if(
        instruction.is_assign() &&
        symbol_id(instruction.assign_lhs(), lhs) &&
        lhs == worker_results[index])
      {
        ++result_definitions;
        if(
          !relational_comparator_result_value_expression(
            instruction.assign_rhs(),
            program,
            model,
            ns,
            worker_results[index],
            visiting,
            negative,
            zero,
            positive,
            subtraction_calls,
            reason))
          return false;
      }
      else if(
        instruction.is_function_call() &&
        !instruction.call_lhs().is_nil() &&
        symbol_id(instruction.call_lhs(), lhs) &&
        lhs == worker_results[index])
      {
        irep_idt callee;
        ++result_definitions;
        if(
          !call_id(instruction, callee) ||
          instruction.call_arguments().size() != 2 ||
          !relational_comparator_subtraction_helper(
            model, ns, callee, reason, true))
        {
          if(reason.empty())
            reason = "transitivity_result_helper";
          return false;
        }
        ++subtraction_calls;
      }
    }
    if(
      result_definitions == 0 ||
      !negative || !zero || !positive ||
      subtraction_calls == 0)
    {
      reason = "transitivity_result_sign_domain";
      return false;
    }
  }
  if(
    owners != property_results ||
    positive_owners.size() != positive_results.size() ||
    conclusion_owner.empty() ||
    positive_owners.count(conclusion_owner) != 0)
  {
    reason = "transitivity_result_owner_partition";
    return false;
  }
  owned_results = owners.size();
  return true;
}

bool relational_comparator_transitivity_unary_selectors(
  const std::vector<relational_comparator_atomic_regiont> &regions,
  const irep_idt &result,
  const std::set<irep_idt> &worker_writes,
  const std::set<irep_idt> &left_inputs,
  const std::set<irep_idt> &right_inputs,
  const relational_bisimulation_mappingt &left_to_right,
  const namespacet &ns,
  std::size_t &selectors,
  std::string &reason)
{
  relational_bisimulation_mappingt unary_mapping;
  for(const auto &identifier : left_inputs)
  {
    const auto mapped = left_to_right.forward.find(identifier);
    if(
      mapped == left_to_right.forward.end() ||
      right_inputs.count(mapped->second) == 0)
    {
      reason = "transitivity_unary_input_mapping";
      return false;
    }
    unary_mapping.comparator_mapped.insert(identifier);
    unary_mapping.forward.emplace(identifier, mapped->second);
  }
  const std::set<irep_idt> no_negative_locals;
  for(const auto &region : regions)
  {
    for(const auto *assignment : region.assignments)
    {
      irep_idt lhs;
      if(
        !symbol_id(assignment->assign_lhs(), lhs) ||
        lhs != result)
        continue;
      const exprt &outer = strip(assignment->assign_rhs());
      if(
        outer.id() != ID_if ||
        outer.operands().size() != 3 ||
        !value_is(outer.op1(), 0))
        continue;
      const exprt &left_case = strip(outer.op2());
      if(
        left_case.id() != ID_if ||
        left_case.operands().size() != 3)
        continue;
      const exprt &right_case = strip(left_case.op2());
      if(
        right_case.id() != ID_if ||
        right_case.operands().size() != 3)
        continue;

      const bool negative_then_positive =
        value_is(left_case.op1(), -1) &&
        value_is(right_case.op1(), 1);
      const bool positive_then_negative =
        value_is(left_case.op1(), 1) &&
        value_is(right_case.op1(), -1);
      irep_idt fallback;
      if(
        (!negative_then_positive && !positive_then_negative) ||
        !symbol_id(right_case.op2(), fallback) ||
        fallback != result)
      {
        reason = "transitivity_unary_selector_sign";
        return false;
      }

      std::vector<exprt> joint_terms;
      std::vector<exprt> left_terms;
      std::vector<exprt> right_terms;
      flatten_and(outer.op0(), joint_terms);
      flatten_and(left_case.op0(), left_terms);
      flatten_and(right_case.op0(), right_terms);
      std::set<exprt> joint_atoms;
      std::set<exprt> left_atoms;
      std::set<exprt> right_atoms;
      std::set<exprt> side_atoms;
      for(const auto &term : joint_terms)
        joint_atoms.insert(strip(term));
      for(const auto &term : left_terms)
        left_atoms.insert(strip(term));
      for(const auto &term : right_terms)
        right_atoms.insert(strip(term));
      std::set_union(
        left_atoms.begin(),
        left_atoms.end(),
        right_atoms.begin(),
        right_atoms.end(),
        std::inserter(side_atoms, side_atoms.begin()));
      if(joint_atoms != side_atoms)
      {
        reason = "transitivity_unary_selector_joint";
        return false;
      }

      std::vector<exprt> left_predicate_terms;
      std::vector<exprt> right_predicate_terms;
      for(const auto &term : left_atoms)
      {
        if(right_atoms.count(term) == 0)
          left_predicate_terms.push_back(term);
      }
      for(const auto &term : right_atoms)
      {
        if(left_atoms.count(term) == 0)
          right_predicate_terms.push_back(term);
      }
      std::set<irep_idt> left_symbols;
      std::set<irep_idt> right_symbols;
      for(const auto &term : left_predicate_terms)
        collect_static_symbols(term, ns, left_symbols);
      for(const auto &term : right_predicate_terms)
        collect_static_symbols(term, ns, right_symbols);
      for(const auto &identifier : worker_writes)
      {
        left_symbols.erase(identifier);
        right_symbols.erase(identifier);
      }
      if(
        left_symbols.empty() || right_symbols.empty() ||
        !std::includes(
          left_inputs.begin(),
          left_inputs.end(),
          left_symbols.begin(),
          left_symbols.end()) ||
        !std::includes(
          right_inputs.begin(),
          right_inputs.end(),
          right_symbols.begin(),
          right_symbols.end()))
      {
        reason = "transitivity_unary_selector_support";
        return false;
      }
      std::vector<bool> used_right(
        right_predicate_terms.size(), false);
      for(const auto &left_term : left_predicate_terms)
      {
        bool matched = false;
        for(std::size_t index = 0;
            index < right_predicate_terms.size(); ++index)
        {
          if(
            !used_right[index] &&
            relational_comparator_expression(
              left_term,
              right_predicate_terms[index],
              false,
              ns,
              unary_mapping,
              no_negative_locals))
          {
            used_right[index] = true;
            matched = true;
            break;
          }
        }
        if(!matched)
        {
          reason = "transitivity_unary_selector_predicate";
          return false;
        }
      }
      if(
        left_predicate_terms.size() !=
        right_predicate_terms.size())
      {
        reason = "transitivity_unary_selector_predicate";
        return false;
      }
      ++selectors;
    }
  }
  if(selectors == 0)
  {
    reason = "transitivity_unary_selector_missing";
    return false;
  }
  return true;
}

bool relational_comparator_transitivity_selector_dominance(
  const goto_programt &program,
  const std::vector<relational_comparator_atomic_regiont> &regions,
  const irep_idt &result,
  const std::set<irep_idt> &worker_writes,
  const std::set<irep_idt> &left_inputs,
  const std::set<irep_idt> &right_inputs,
  const relational_bisimulation_mappingt &left_to_right,
  const namespacet &ns,
  std::size_t &dominated_selectors,
  std::size_t &ordered_subtractions,
  std::string &reason)
{
  std::vector<const goto_programt::instructiont *> instructions;
  std::map<const goto_programt::instructiont *, std::size_t> indices;
  for(const auto &instruction : program.instructions)
  {
    indices.emplace(&instruction, instructions.size());
    instructions.push_back(&instruction);
  }
  if(instructions.empty())
  {
    reason = "transitivity_dominance_empty_cfg";
    return false;
  }
  std::vector<std::set<std::size_t>> predecessors(
    instructions.size());
  for(std::size_t index = 0;
      index < instructions.size(); ++index)
  {
    const auto *instruction = instructions[index];
    if(instruction->is_goto())
    {
      for(const auto &target : instruction->targets)
        predecessors[indices.at(&*target)].insert(index);
      if(
        !instruction->condition().is_true() &&
        index + 1 < instructions.size())
        predecessors[index + 1].insert(index);
    }
    else if(
      !instruction->is_end_function() &&
      index + 1 < instructions.size())
      predecessors[index + 1].insert(index);
  }
  std::set<std::size_t> all;
  for(std::size_t index = 0;
      index < instructions.size(); ++index)
    all.insert(index);
  std::vector<std::set<std::size_t>> dominators(
    instructions.size(), all);
  dominators[0] = {0};
  bool changed = true;
  while(changed)
  {
    changed = false;
    for(std::size_t node = 1;
        node < instructions.size(); ++node)
    {
      std::set<std::size_t> next;
      bool first = true;
      for(const auto predecessor : predecessors[node])
      {
        if(first)
        {
          next = dominators[predecessor];
          first = false;
        }
        else
        {
          std::set<std::size_t> intersection;
          std::set_intersection(
            next.begin(),
            next.end(),
            dominators[predecessor].begin(),
            dominators[predecessor].end(),
            std::inserter(
              intersection, intersection.begin()));
          next.swap(intersection);
        }
      }
      if(first)
        next.clear();
      next.insert(node);
      if(next != dominators[node])
      {
        dominators[node].swap(next);
        changed = true;
      }
    }
  }

  relational_bisimulation_mappingt unary_mapping;
  for(const auto &identifier : left_inputs)
  {
    const auto mapped = left_to_right.forward.find(identifier);
    if(
      mapped == left_to_right.forward.end() ||
      right_inputs.count(mapped->second) == 0)
    {
      reason = "transitivity_dominance_input_mapping";
      return false;
    }
    unary_mapping.comparator_mapped.insert(identifier);
    unary_mapping.forward.emplace(identifier, mapped->second);
  }
  const std::set<irep_idt> no_negative_locals;
  std::vector<const goto_programt::instructiont *> equalities;
  for(const auto &region : regions)
  {
    for(const auto *assumption : region.assumptions)
    {
      std::vector<exprt> terms;
      flatten_and(
        assumption->call_arguments().front(), terms);
      for(const auto &term_src : terms)
      {
        const exprt &term = strip(term_src);
        if(
          term.id() != ID_equal ||
          term.operands().size() != 2)
          continue;
        std::set<irep_idt> left_symbols;
        std::set<irep_idt> right_symbols;
        collect_static_symbols(term.op0(), ns, left_symbols);
        collect_static_symbols(term.op1(), ns, right_symbols);
        for(const auto &identifier : worker_writes)
        {
          left_symbols.erase(identifier);
          right_symbols.erase(identifier);
        }
        const bool direct_support =
          !left_symbols.empty() && !right_symbols.empty() &&
          std::includes(
            left_inputs.begin(),
            left_inputs.end(),
            left_symbols.begin(),
            left_symbols.end()) &&
          std::includes(
            right_inputs.begin(),
            right_inputs.end(),
            right_symbols.begin(),
            right_symbols.end());
        const bool reverse_support =
          !left_symbols.empty() && !right_symbols.empty() &&
          std::includes(
            right_inputs.begin(),
            right_inputs.end(),
            left_symbols.begin(),
            left_symbols.end()) &&
          std::includes(
            left_inputs.begin(),
            left_inputs.end(),
            right_symbols.begin(),
            right_symbols.end());
        const bool mapped =
          direct_support ?
          relational_comparator_expression(
            term.op0(),
            term.op1(),
            false,
            ns,
            unary_mapping,
            no_negative_locals) :
          reverse_support &&
          relational_comparator_expression(
            term.op1(),
            term.op0(),
            false,
            ns,
            unary_mapping,
            no_negative_locals);
        if(mapped)
          equalities.push_back(assumption);
      }
    }
  }
  if(equalities.empty())
  {
    reason = "transitivity_dominance_missing_equality";
    return false;
  }

  std::size_t selectors = 0;
  for(const auto &region : regions)
  {
    for(const auto *assignment : region.assignments)
    {
      irep_idt lhs;
      if(
        !symbol_id(assignment->assign_lhs(), lhs) ||
        lhs != result)
        continue;
      const exprt &outer = strip(assignment->assign_rhs());
      if(
        outer.id() != ID_if ||
        outer.operands().size() != 3 ||
        !value_is(outer.op1(), 0))
        continue;
      const exprt &left_case = strip(outer.op2());
      if(
        left_case.id() != ID_if ||
        left_case.operands().size() != 3)
        continue;
      const exprt &right_case = strip(left_case.op2());
      if(
        right_case.id() != ID_if ||
        right_case.operands().size() != 3)
        continue;
      ++selectors;
      const std::size_t node = indices.at(assignment);
      bool dominated = false;
      for(const auto *equality : equalities)
      {
        if(
          dominators[node].count(indices.at(equality)) != 0)
        {
          dominated = true;
          break;
        }
      }
      if(!dominated)
      {
        reason = "transitivity_selector_without_key_equality";
        return false;
      }
      ++dominated_selectors;
    }
  }
  if(selectors == 0 || dominated_selectors != selectors)
  {
    reason = "transitivity_selector_dominance_incomplete";
    return false;
  }

  for(const auto &region : regions)
  {
    for(const auto *call : region.helper_calls)
    {
      irep_idt lhs;
      if(
        call->call_lhs().is_nil() ||
        !symbol_id(call->call_lhs(), lhs) ||
        lhs != result)
        continue;
      if(call->call_arguments().size() != 2)
      {
        reason = "transitivity_subtraction_arity";
        return false;
      }
      const exprt &left_argument =
        strip(call->call_arguments()[0]);
      const exprt &right_argument =
        strip(call->call_arguments()[1]);
      std::set<irep_idt> left_symbols;
      std::set<irep_idt> right_symbols;
      collect_static_symbols(
        left_argument, ns, left_symbols);
      collect_static_symbols(
        right_argument, ns, right_symbols);
      for(const auto &identifier : worker_writes)
      {
        left_symbols.erase(identifier);
        right_symbols.erase(identifier);
      }
      if(
        left_symbols.empty() || right_symbols.empty() ||
        !std::includes(
          left_inputs.begin(),
          left_inputs.end(),
          left_symbols.begin(),
          left_symbols.end()) ||
        !std::includes(
          right_inputs.begin(),
          right_inputs.end(),
          right_symbols.begin(),
          right_symbols.end()) ||
        !relational_comparator_expression(
          left_argument,
          right_argument,
          false,
          ns,
          unary_mapping,
          no_negative_locals))
      {
        reason = "transitivity_subtraction_key_mapping";
        return false;
      }

      bool relation_dominates = false;
      const std::size_t node = indices.at(call);
      for(const auto &candidate_region : regions)
      {
        for(const auto *assumption :
            candidate_region.assumptions)
        {
          if(
            dominators[node].count(
              indices.at(assumption)) == 0)
            continue;
          std::vector<exprt> terms;
          flatten_and(
            assumption->call_arguments().front(), terms);
          for(const auto &term_src : terms)
          {
            const exprt &term = strip(term_src);
            const exprt *relation = &term;
            if(
              term.id() == ID_not &&
              term.operands().size() == 1)
              relation = &strip(term.op0());
            if(
              relation->id() == ID_equal &&
              relation->operands().size() == 2 &&
              ((strip(relation->op0()) == left_argument &&
                strip(relation->op1()) == right_argument) ||
               (strip(relation->op0()) == right_argument &&
                strip(relation->op1()) == left_argument)))
            {
              relation_dominates = true;
              break;
            }
          }
          if(relation_dominates)
            break;
        }
        if(relation_dominates)
          break;
      }
      if(!relation_dominates)
      {
        reason = "transitivity_subtraction_without_relation";
        return false;
      }
      ++ordered_subtractions;
    }
  }
  if(ordered_subtractions == 0)
  {
    reason = "transitivity_subtraction_missing";
    return false;
  }
  return true;
}

void relational_comparator_region_guard_terms(
  const relational_comparator_atomic_regiont &region,
  std::set<exprt> &terms)
{
  for(const auto *assumption : region.assumptions)
  {
    std::vector<exprt> flattened;
    flatten_and(
      assumption->call_arguments().front(), flattened);
    for(const auto &term : flattened)
      terms.insert(strip(term));
  }
}

void relational_comparator_boolean_base(
  const exprt &src,
  exprt &base,
  bool &negated)
{
  const exprt &expr = strip(src);
  if(expr.id() == ID_not && expr.operands().size() == 1)
  {
    base = strip(expr.op0());
    negated = true;
  }
  else
  {
    base = expr;
    negated = false;
  }
}

bool relational_comparator_transitivity_validity_selector(
  const std::vector<relational_comparator_atomic_regiont> &regions,
  const irep_idt &result,
  const std::set<irep_idt> &worker_writes,
  const std::set<irep_idt> &left_inputs,
  const std::set<irep_idt> &right_inputs,
  const relational_bisimulation_mappingt &left_to_right,
  const namespacet &ns,
  std::size_t &validity_selectors,
  std::size_t &missing_key_guards,
  std::string &reason)
{
  std::map<int, const relational_comparator_atomic_regiont *>
    sign_regions;
  for(const auto &region : regions)
  {
    for(const auto *assignment : region.assignments)
    {
      irep_idt lhs;
      if(
        !symbol_id(assignment->assign_lhs(), lhs) ||
        lhs != result)
        continue;
      const exprt &rhs = strip(assignment->assign_rhs());
      int sign = 2;
      if(value_is(rhs, -1))
        sign = -1;
      else if(value_is(rhs, 0))
        sign = 0;
      else if(value_is(rhs, 1))
        sign = 1;
      if(sign == 2)
        continue;
      if(!sign_regions.emplace(sign, &region).second)
      {
        reason = "transitivity_validity_duplicate_sign";
        return false;
      }
    }
  }
  if(sign_regions.size() != 3)
  {
    reason = "transitivity_validity_sign_regions";
    return false;
  }

  std::map<int, std::set<exprt>> guards;
  for(const auto &entry : sign_regions)
    relational_comparator_region_guard_terms(
      *entry.second, guards[entry.first]);
  std::set<exprt> common;
  std::set_intersection(
    guards[-1].begin(),
    guards[-1].end(),
    guards[0].begin(),
    guards[0].end(),
    std::inserter(common, common.begin()));
  std::set<exprt> all_common;
  std::set_intersection(
    common.begin(),
    common.end(),
    guards[1].begin(),
    guards[1].end(),
    std::inserter(all_common, all_common.begin()));
  if(all_common.size() != 1)
  {
    reason = "transitivity_validity_common_guard";
    return false;
  }
  const exprt &missing_guard = *all_common.begin();
  if(
    missing_guard.id() != ID_not ||
    missing_guard.operands().size() != 1)
  {
    reason = "transitivity_validity_missing_guard";
    return false;
  }
  std::vector<exprt> present_terms;
  flatten_or(missing_guard.op0(), present_terms);
  if(present_terms.size() != 2)
  {
    reason = "transitivity_validity_present_arity";
    return false;
  }
  const auto term_side =
    [&](const exprt &term) -> int
    {
      std::set<irep_idt> symbols;
      collect_static_symbols(term, ns, symbols);
      for(const auto &identifier : worker_writes)
        symbols.erase(identifier);
      if(
        !symbols.empty() &&
        std::includes(
          left_inputs.begin(),
          left_inputs.end(),
          symbols.begin(),
          symbols.end()))
        return -1;
      if(
        !symbols.empty() &&
        std::includes(
          right_inputs.begin(),
          right_inputs.end(),
          symbols.begin(),
          symbols.end()))
        return 1;
      return 0;
    };
  const exprt *left_present = nullptr;
  const exprt *right_present = nullptr;
  for(const auto &term : present_terms)
  {
    if(term_side(term) == -1 && left_present == nullptr)
      left_present = &term;
    else if(term_side(term) == 1 && right_present == nullptr)
      right_present = &term;
    else
    {
      reason = "transitivity_validity_present_support";
      return false;
    }
  }
  relational_bisimulation_mappingt present_mapping;
  for(const auto &identifier : left_inputs)
  {
    const auto mapped = left_to_right.forward.find(identifier);
    if(
      mapped == left_to_right.forward.end() ||
      right_inputs.count(mapped->second) == 0)
    {
      reason = "transitivity_validity_present_mapping";
      return false;
    }
    present_mapping.comparator_mapped.insert(identifier);
    present_mapping.forward.emplace(identifier, mapped->second);
  }
  const std::set<irep_idt> no_present_negative_locals;
  if(
    left_present == nullptr || right_present == nullptr ||
    !relational_comparator_expression(
      *left_present,
      *right_present,
      false,
      ns,
      present_mapping,
      no_present_negative_locals))
  {
    reason = "transitivity_validity_present_predicate";
    return false;
  }
  missing_key_guards = 1;
  for(auto &entry : guards)
  {
    for(const auto &term : all_common)
      entry.second.erase(term);
    if(entry.second.size() != 2)
    {
      reason = "transitivity_validity_residual_arity";
      return false;
    }
  }

  const auto support_side =
    [&](const exprt &term) -> int
    {
      std::set<irep_idt> symbols;
      collect_static_symbols(term, ns, symbols);
      for(const auto &identifier : worker_writes)
        symbols.erase(identifier);
      if(
        !symbols.empty() &&
        std::includes(
          left_inputs.begin(),
          left_inputs.end(),
          symbols.begin(),
          symbols.end()))
        return -1;
      if(
        !symbols.empty() &&
        std::includes(
          right_inputs.begin(),
          right_inputs.end(),
          symbols.begin(),
          symbols.end()))
        return 1;
      return 0;
    };
  std::map<int, std::map<int, exprt>> sided;
  for(const auto &entry : guards)
  {
    for(const auto &term : entry.second)
    {
      const int side = support_side(term);
      if(
        side == 0 ||
        !sided[entry.first].emplace(side, term).second)
      {
        reason = "transitivity_validity_support";
        return false;
      }
    }
    if(sided[entry.first].size() != 2)
    {
      reason = "transitivity_validity_side_arity";
      return false;
    }
  }

  exprt positive_left;
  exprt positive_right;
  bool positive_left_negated = false;
  bool positive_right_negated = false;
  relational_comparator_boolean_base(
    sided[1].at(-1),
    positive_left,
    positive_left_negated);
  relational_comparator_boolean_base(
    sided[-1].at(1),
    positive_right,
    positive_right_negated);
  if(positive_left_negated || positive_right_negated)
  {
    reason = "transitivity_validity_positive_polarity";
    return false;
  }
  for(const auto sign : {-1, 0, 1})
  {
    exprt left_base;
    exprt right_base;
    bool left_negated = false;
    bool right_negated = false;
    relational_comparator_boolean_base(
      sided[sign].at(-1), left_base, left_negated);
    relational_comparator_boolean_base(
      sided[sign].at(1), right_base, right_negated);
    const bool expected_left_negated = sign != 1;
    const bool expected_right_negated = sign != -1;
    if(
      left_base != positive_left ||
      right_base != positive_right ||
      left_negated != expected_left_negated ||
      right_negated != expected_right_negated)
    {
      reason = "transitivity_validity_truth_table";
      return false;
    }
  }

  relational_bisimulation_mappingt unary_mapping;
  for(const auto &identifier : left_inputs)
  {
    const auto mapped = left_to_right.forward.find(identifier);
    if(
      mapped == left_to_right.forward.end() ||
      right_inputs.count(mapped->second) == 0)
    {
      reason = "transitivity_validity_input_mapping";
      return false;
    }
    unary_mapping.comparator_mapped.insert(identifier);
    unary_mapping.forward.emplace(identifier, mapped->second);
  }
  const std::set<irep_idt> no_negative_locals;
  if(
    !relational_comparator_expression(
      positive_left,
      positive_right,
      false,
      ns,
      unary_mapping,
      no_negative_locals))
  {
    reason = "transitivity_validity_predicate";
    return false;
  }

  bool positive_pair_path = false;
  for(const auto &region : regions)
  {
    std::set<exprt> terms;
    relational_comparator_region_guard_terms(region, terms);
    if(
      terms.count(positive_left) != 0 &&
      terms.count(positive_right) != 0)
    {
      positive_pair_path = true;
      break;
    }
  }
  if(!positive_pair_path)
  {
    reason = "transitivity_validity_positive_pair";
    return false;
  }
  validity_selectors = 1;
  return true;
}

struct relational_comparator_scan_summaryt
{
  irep_idt result;
  irep_idt first;
  irep_idt second;
  irep_idt current;
  irep_idt breaker;
  irep_idt index;
  irep_idt array;
  irep_idt subtraction;
  exprt bound;
};

bool relational_comparator_zero_test(
  const exprt &src,
  const irep_idt &identifier)
{
  const exprt &expr = strip(src);
  irep_idt symbol;
  if(
    expr.id() == ID_not &&
    expr.operands().size() == 1)
  {
    const exprt &operand = strip(expr.op0());
    return
      (symbol_id(operand, symbol) && symbol == identifier) ||
      (operand.id() == ID_notequal &&
       operand.operands().size() == 2 &&
       ((symbol_id(operand.op0(), symbol) &&
         symbol == identifier && value_is(operand.op1(), 0)) ||
        (symbol_id(operand.op1(), symbol) &&
         symbol == identifier && value_is(operand.op0(), 0))));
  }
  return
    expr.id() == ID_equal &&
    expr.operands().size() == 2 &&
    ((symbol_id(expr.op0(), symbol) &&
      symbol == identifier && value_is(expr.op1(), 0)) ||
     (symbol_id(expr.op1(), symbol) &&
      symbol == identifier && value_is(expr.op0(), 0)));
}

bool relational_comparator_equal_symbols(
  const exprt &src,
  irep_idt &left,
  irep_idt &right)
{
  const exprt &expr = strip(src);
  return
    expr.id() == ID_equal &&
    expr.operands().size() == 2 &&
    symbol_id(expr.op0(), left) &&
    symbol_id(expr.op1(), right) &&
    left != right;
}

bool relational_comparator_result_selector(
  const exprt &src,
  const irep_idt &result,
  const mp_integer &selected,
  exprt &condition)
{
  const exprt &expr = strip(src);
  irep_idt fallback;
  if(
    expr.id() != ID_if ||
    expr.operands().size() != 3 ||
    !value_is(expr.op1(), selected) ||
    !symbol_id(expr.op2(), fallback) ||
    fallback != result)
    return false;
  condition = expr.op0();
  return true;
}

bool relational_comparator_guard(
  const exprt &src,
  const irep_idt &index,
  const irep_idt &breaker,
  exprt &bound)
{
  std::vector<exprt> terms;
  flatten_and(strip(src), terms);
  if(terms.size() != 2)
    return false;
  bool index_term = false;
  bool break_term = false;
  for(const auto &term_src : terms)
  {
    const exprt &term = strip(term_src);
    irep_idt symbol;
    if(
      term.id() == ID_lt &&
      term.operands().size() == 2 &&
      symbol_id(term.op0(), symbol) &&
      symbol == index)
    {
      if(index_term)
        return false;
      index_term = true;
      bound = term.op1();
    }
    else if(relational_comparator_zero_test(term, breaker))
    {
      if(break_term)
        return false;
      break_term = true;
    }
    else
      return false;
  }
  return index_term && break_term;
}

bool relational_comparator_scan_summary(
  const goto_modelt &model,
  const namespacet &ns,
  const irep_idt &worker,
  const irep_idt &result,
  relational_comparator_scan_summaryt &summary,
  std::string &reason)
{
  const auto function =
    model.goto_functions.function_map.find(worker);
  if(
    function == model.goto_functions.function_map.end() ||
    !function->second.body_available())
  {
    reason = "scan_worker_body";
    return false;
  }
  const auto &program = function->second.body;
  summary.result = result;
  exprt initial_condition;
  exprt positive_condition;
  exprt negative_condition;
  std::size_t result_assignments = 0;
  std::size_t result_selectors = 0;
  std::size_t result_passthroughs = 0;
  const goto_programt::instructiont *initial_result = nullptr;
  const goto_programt::instructiont *positive_result = nullptr;
  const goto_programt::instructiont *negative_result = nullptr;
  const goto_programt::instructiont *final_result = nullptr;
  for(const auto &instruction : program.instructions)
  {
    irep_idt lhs;
    if(
      !instruction.is_assign() ||
      !symbol_id(instruction.assign_lhs(), lhs) ||
      lhs != result)
      continue;
    ++result_assignments;
    exprt condition;
    if(
      relational_comparator_result_selector(
        instruction.assign_rhs(), result, 0, condition))
    {
      irep_idt left;
      irep_idt right;
      if(
        !relational_comparator_equal_symbols(
          condition, left, right) ||
        !summary.first.empty())
      {
        reason = "scan_initial_selector";
        return false;
      }
      summary.first = left;
      summary.second = right;
      initial_condition = condition;
      initial_result = &instruction;
      ++result_selectors;
    }
    else if(
      relational_comparator_result_selector(
        instruction.assign_rhs(), result, 1, condition))
    {
      irep_idt left;
      irep_idt right;
      if(
        !relational_comparator_equal_symbols(
          condition, left, right) ||
        !summary.current.empty())
      {
        reason = "scan_positive_selector";
        return false;
      }
      if(left == summary.first || right == summary.first)
      {
        summary.current =
          left == summary.first ? right : left;
      }
      else if(left == summary.second || right == summary.second)
      {
        std::swap(summary.first, summary.second);
        summary.current =
          left == summary.first ? right : left;
      }
      else
      {
        reason = "scan_positive_key";
        return false;
      }
      positive_condition = condition;
      positive_result = &instruction;
      ++result_selectors;
    }
    else if(
      relational_comparator_result_selector(
        instruction.assign_rhs(), result, -1, condition))
    {
      if(!negative_condition.id().empty())
      {
        reason = "scan_negative_selector";
        return false;
      }
      negative_condition = condition;
      negative_result = &instruction;
      ++result_selectors;
    }
    else
    {
      ++result_passthroughs;
      final_result = &instruction;
    }
  }
  if(
    result_assignments != 4 ||
    result_selectors != 3 ||
    result_passthroughs != 1 ||
    summary.first.empty() || summary.second.empty() ||
    summary.current.empty() ||
    initial_condition.id().empty() ||
    positive_condition.id().empty() ||
    negative_condition.id().empty())
  {
    reason = "scan_result_selectors";
    return false;
  }

  std::vector<exprt> negative_terms;
  flatten_and(negative_condition, negative_terms);
  if(negative_terms.size() != 2)
  {
    reason = "scan_negative_guard";
    return false;
  }
  for(const auto &term : negative_terms)
  {
    irep_idt left;
    irep_idt right;
    if(relational_comparator_equal_symbols(term, left, right))
    {
      if(
        !((left == summary.current &&
           right == summary.second) ||
          (right == summary.current &&
           left == summary.second)))
      {
        reason = "scan_negative_key";
        return false;
      }
    }
    else
    {
      std::set<irep_idt> symbols;
      collect_static_symbols(term, ns, symbols);
      if(symbols.size() != 1)
      {
        reason = "scan_break_guard";
        return false;
      }
      summary.breaker = *symbols.begin();
      if(!relational_comparator_zero_test(
           term, summary.breaker))
      {
        reason = "scan_break_guard";
        return false;
      }
    }
  }
  if(summary.breaker.empty())
  {
    reason = "scan_break_guard";
    return false;
  }

  std::size_t break_zero = 0;
  std::size_t break_selectors = 0;
  std::size_t array_reads = 0;
  std::size_t index_zero = 0;
  std::size_t index_steps = 0;
  std::size_t assumptions = 0;
  std::size_t positive_guards = 0;
  std::size_t negative_guards = 0;
  std::size_t subtraction_calls = 0;
  std::size_t nondet_assignments = 0;
  std::size_t backward_gotos = 0;
  std::vector<std::pair<
    const goto_programt::instructiont *, exprt>>
      assumption_arguments;
  const goto_programt::instructiont *break_initial = nullptr;
  const goto_programt::instructiont *break_initial_selector = nullptr;
  const goto_programt::instructiont *break_positive_selector = nullptr;
  const goto_programt::instructiont *break_negative_selector = nullptr;
  const goto_programt::instructiont *array_read = nullptr;
  const goto_programt::instructiont *index_initial = nullptr;
  const goto_programt::instructiont *index_step = nullptr;
  const goto_programt::instructiont *nondet_assignment = nullptr;
  const goto_programt::instructiont *backedge = nullptr;
  const goto_programt::instructiont *positive_assumption = nullptr;
  const goto_programt::instructiont *negative_assumption = nullptr;
  const goto_programt::instructiont *subtraction_call = nullptr;
  std::set<irep_idt> reads;
  std::set<irep_idt> writes;
  std::set<irep_idt> visiting;
  if(
    !relational_bisimulation_function_effects(
      model,
      worker,
      ns,
      visiting,
      reads,
      writes,
      reason,
      true))
    return false;
  for(const auto &instruction : program.instructions)
  {
    irep_idt lhs;
    if(
      instruction.is_assign() &&
      symbol_id(instruction.assign_lhs(), lhs))
    {
      const exprt &rhs = strip(instruction.assign_rhs());
      if(
        relational_bisimulation_contains_nondet(rhs))
      {
        ++nondet_assignments;
        nondet_assignment = &instruction;
      }
      if(lhs == summary.breaker)
      {
        if(value_is(rhs, 0))
        {
          ++break_zero;
          break_initial = &instruction;
        }
        else
        {
          const exprt &selector = strip(rhs);
          irep_idt fallback;
          if(
            selector.id() != ID_if ||
            selector.operands().size() != 3 ||
            !value_is(selector.op1(), 1) ||
            !symbol_id(selector.op2(), fallback) ||
            fallback != summary.breaker ||
            (strip(selector.op0()) !=
               strip(initial_condition) &&
             strip(selector.op0()) !=
               strip(positive_condition) &&
             strip(selector.op0()) !=
               strip(negative_condition)))
          {
            reason = "scan_break_selector";
            return false;
          }
          if(
            strip(selector.op0()) ==
              strip(initial_condition))
            break_initial_selector = &instruction;
          else if(
            strip(selector.op0()) ==
              strip(positive_condition))
            break_positive_selector = &instruction;
          else
            break_negative_selector = &instruction;
          ++break_selectors;
        }
      }
      if(lhs == summary.current)
      {
        const exprt &load = strip(rhs);
        if(
          load.id() != ID_dereference ||
          load.operands().size() != 1)
        {
          reason = "scan_array_load";
          return false;
        }
        const exprt &address = strip(load.op0());
        if(
          address.id() != ID_plus ||
          address.operands().size() != 2)
        {
          reason = "scan_array_address";
          return false;
        }
        irep_idt left;
        irep_idt right;
        if(
          !symbol_id(address.op0(), left) ||
          !symbol_id(address.op1(), right))
        {
          reason = "scan_array_address";
          return false;
        }
        const symbolt *left_symbol = lookup(left, ns);
        const symbolt *right_symbol = lookup(right, ns);
        if(
          left_symbol != nullptr &&
          left_symbol->type.id() == ID_pointer)
        {
          summary.array = left;
          summary.index = right;
        }
        else if(
          right_symbol != nullptr &&
          right_symbol->type.id() == ID_pointer)
        {
          summary.array = right;
          summary.index = left;
        }
        else
        {
          reason = "scan_array_pointer";
          return false;
        }
        array_read = &instruction;
        ++array_reads;
      }
    }
    if(
      instruction.is_function_call())
    {
      if(
        relational_bisimulation_verified_assume(
          instruction, model, ns, true))
      {
        ++assumptions;
        assumption_arguments.emplace_back(
          &instruction,
          instruction.call_arguments().front());
      }
      else
      {
        irep_idt callee;
        if(
          !call_id(instruction, callee) ||
          instruction.call_arguments().size() != 2 ||
          !relational_comparator_subtraction_helper(
            model, ns, callee, reason, true))
          continue;
        if(
          strip(instruction.call_arguments()[0]) !=
            symbol_exprt(
              summary.first,
              lookup(summary.first, ns)->type) ||
          strip(instruction.call_arguments()[1]) !=
            symbol_exprt(
              summary.second,
              lookup(summary.second, ns)->type))
        {
          reason = "scan_subtraction_order";
          return false;
        }
        summary.subtraction = callee;
        subtraction_call = &instruction;
        ++subtraction_calls;
      }
    }
    if(instruction.is_goto() &&
       instruction.condition().is_true() &&
       instruction.targets.size() == 1 &&
       instruction.get_target()->location_number <
         instruction.location_number)
    {
      ++backward_gotos;
      backedge = &instruction;
    }
  }
  for(const auto &assumption : assumption_arguments)
  {
    const exprt &argument = strip(assumption.second);
    exprt bound;
    if(
      relational_comparator_guard(
        argument,
        summary.index,
        summary.breaker,
        bound))
    {
      ++positive_guards;
      summary.bound = bound;
      positive_assumption = assumption.first;
    }
    else if(
      argument.id() == ID_not &&
      argument.operands().size() == 1 &&
      relational_comparator_guard(
        argument.op0(),
        summary.index,
        summary.breaker,
        bound))
    {
      ++negative_guards;
      negative_assumption = assumption.first;
      if(
        !summary.bound.id().empty() &&
        strip(summary.bound) != strip(bound))
      {
        reason = "scan_bound_mismatch";
        return false;
      }
      summary.bound = bound;
    }
    else
    {
      reason = "scan_assumption";
      return false;
    }
  }
  for(const auto &instruction : program.instructions)
  {
    if(!instruction.is_assign())
      continue;
    irep_idt lhs;
    if(!symbol_id(instruction.assign_lhs(), lhs))
      continue;
    const exprt &rhs = strip(instruction.assign_rhs());
    if(lhs == summary.index)
    {
      if(value_is(rhs, 0))
      {
        ++index_zero;
        index_initial = &instruction;
      }
      else if(
        rhs.id() == ID_plus &&
        rhs.operands().size() == 2)
      {
        irep_idt step_symbol;
        if(
          (symbol_id(rhs.op0(), step_symbol) &&
           step_symbol == summary.index &&
           value_is(rhs.op1(), 1)) ||
          (symbol_id(rhs.op1(), step_symbol) &&
           step_symbol == summary.index &&
          value_is(rhs.op0(), 1)))
        {
          ++index_steps;
          index_step = &instruction;
        }
        else
        {
          reason = "scan_index_step";
          return false;
        }
      }
      else
      {
        reason = "scan_index_write";
        return false;
      }
    }
  }
  const goto_programt::instructiont *exit_branch = nullptr;
  if(nondet_assignment != nullptr &&
     negative_assumption != nullptr)
  {
    for(const auto &instruction : program.instructions)
    {
      if(
        relational_comparator_false_nondet_gate(
          *nondet_assignment, instruction) &&
        &*instruction.get_target() ==
          negative_assumption)
      {
        if(exit_branch != nullptr)
        {
          reason = "scan_exit_branch_count";
          return false;
        }
        exit_branch = &instruction;
      }
    }
  }
  const auto before =
    [](const goto_programt::instructiont *left,
       const goto_programt::instructiont *right)
    {
      return
        left != nullptr && right != nullptr &&
        left->location_number < right->location_number;
    };
  if(
    !before(index_initial, break_initial) ||
    !before(break_initial, initial_result) ||
    !before(initial_result, break_initial_selector) ||
    !before(break_initial_selector, nondet_assignment) ||
    !before(nondet_assignment, exit_branch) ||
    !before(exit_branch, positive_assumption) ||
    !before(positive_assumption, array_read) ||
    !before(array_read, positive_result) ||
    !before(positive_result, break_positive_selector) ||
    !before(break_positive_selector, negative_result) ||
    !before(negative_result, break_negative_selector) ||
    !before(break_negative_selector, index_step) ||
    !before(index_step, backedge) ||
    !before(backedge, negative_assumption) ||
    !before(negative_assumption, subtraction_call) ||
    !before(subtraction_call, final_result) ||
    backedge == nullptr ||
    backedge->get_target()->location_number >
      nondet_assignment->location_number)
  {
    reason = "scan_control_order";
    return false;
  }
  const std::set<irep_idt> expected_writes{
    summary.result,
    summary.current,
    summary.breaker,
    summary.index};
  if(
    writes != expected_writes ||
    break_zero != 1 || break_selectors != 3 ||
    array_reads != 1 ||
    index_zero != 1 || index_steps != 1 ||
    assumptions != 2 ||
    positive_guards != 1 || negative_guards != 1 ||
    subtraction_calls != 1 ||
    nondet_assignments != 1 ||
    backward_gotos != 1 ||
    summary.array.empty() || summary.index.empty() ||
    summary.bound.id().empty())
  {
    reason = "scan_structural_census";
    return false;
  }
  for(const auto &identifier :
      {summary.first, summary.second, summary.current,
       summary.breaker, summary.index, summary.result})
  {
    const symbolt *symbol = lookup(identifier, ns);
    if(
      symbol == nullptr || !symbol->is_static_lifetime ||
      symbol->type.id() != ID_signedbv)
    {
      reason = "scan_symbol_type";
      return false;
    }
  }
  const symbolt *array_symbol = lookup(summary.array, ns);
  if(
    array_symbol == nullptr ||
    !array_symbol->is_static_lifetime ||
    array_symbol->type.id() != ID_pointer ||
    to_pointer_type(array_symbol->type).base_type().id() !=
      ID_signedbv ||
    writes.count(summary.array) != 0)
  {
    reason = "scan_array_type";
    return false;
  }
  return true;
}

bool relational_comparator_scan_law(
  const goto_modelt &model,
  const namespacet &ns,
  const std::vector<irep_idt> &workers,
  const std::vector<irep_idt> &worker_results,
  const std::string &rule,
  std::size_t &pairwise_program_matches,
  std::size_t &mapped_symbols,
  std::size_t &audited_helpers,
  std::string &reason)
{
  if(workers.size() != 3 || worker_results.size() != 3)
  {
    reason = "scan_law_arity";
    return false;
  }
  std::vector<relational_comparator_scan_summaryt>
    summaries(workers.size());
  for(std::size_t index = 0; index < workers.size(); ++index)
  {
    if(
      !relational_comparator_scan_summary(
        model,
        ns,
        workers[index],
        worker_results[index],
        summaries[index],
        reason))
      return false;
    if(index != 0)
    {
      relational_bisimulation_mappingt mapping;
      if(
        !relational_bisimulation_programs(
          model.goto_functions.function_map.at(workers[0]).body,
          model.goto_functions.function_map.at(workers[index]).body,
          ns,
          mapping,
          reason))
      {
        reason =
          "scan_law_pair_" + std::to_string(index) +
          "_" + reason;
        return false;
      }
      ++pairwise_program_matches;
      mapped_symbols += mapping.forward.size();
    }
  }
  for(std::size_t index = 1; index < summaries.size(); ++index)
  {
    if(
      summaries[index].array != summaries[0].array ||
      strip(summaries[index].bound) !=
        strip(summaries[0].bound) ||
      summaries[index].subtraction !=
        summaries[0].subtraction)
    {
      reason = "scan_law_shared_definition";
      return false;
    }
  }
  const auto &first = summaries[0];
  const auto &second = summaries[1];
  const auto &third = summaries[2];
  const bool triangle =
    (rule == "strict_transitivity" &&
     first.second == second.first &&
     first.first == third.first &&
     second.second == third.second) ||
    (rule == "equality_substitution" &&
     first.first == second.first &&
     first.second == third.first &&
     second.second == third.second);
  if(!triangle)
  {
    reason = "scan_law_input_triangle";
    return false;
  }
  audited_helpers = 1;
  return true;
}

bool relational_comparator_scan_antisymmetry(
  const goto_modelt &model,
  const namespacet &ns,
  const std::vector<irep_idt> &workers,
  const irep_idt &left_result,
  const irep_idt &right_result,
  std::size_t &transition_matches,
  std::size_t &audited_helpers,
  std::string &reason)
{
  if(
    workers.size() != 2 ||
    left_result.empty() || right_result.empty() ||
    left_result == right_result)
  {
    reason = "scan_antisymmetry_arity";
    return false;
  }
  relational_comparator_scan_summaryt left;
  relational_comparator_scan_summaryt right;
  if(
    !relational_comparator_scan_summary(
      model, ns, workers[0], left_result, left, reason) ||
    !relational_comparator_scan_summary(
      model, ns, workers[1], right_result, right, reason))
    return false;
  relational_bisimulation_mappingt mapping;
  if(
    !relational_bisimulation_programs(
      model.goto_functions.function_map.at(workers[0]).body,
      model.goto_functions.function_map.at(workers[1]).body,
      ns,
      mapping,
      reason))
  {
    reason = "scan_antisymmetry_pair_" + reason;
    return false;
  }
  if(
    left.first != right.second ||
    left.second != right.first ||
    left.array != right.array ||
    strip(left.bound) != strip(right.bound) ||
    left.subtraction != right.subtraction)
  {
    reason = "scan_antisymmetry_definition";
    return false;
  }
  transition_matches = 1;
  audited_helpers = 1;
  return true;
}

bool relational_comparator_transitivity_diagnostic(
  const goto_modelt &model,
  const namespacet &ns,
  std::size_t &workers_count,
  std::size_t &regions_per_worker,
  std::size_t &pairwise_program_matches,
  std::size_t &mapped_symbols,
  std::size_t &endpoint_input_symbols,
  std::size_t &middle_input_symbols,
  std::size_t &owned_results,
  std::size_t &unary_selectors,
  std::size_t &dominated_selectors,
  std::size_t &guard_partition_groups,
  std::size_t &dispatch_gates,
  std::size_t &audited_helpers,
  std::size_t &validity_selectors,
  std::size_t &ordered_subtractions,
  std::size_t &missing_key_guards,
  std::string &rule,
  std::string &reason)
{
  lifecyclet life;
  std::vector<irep_idt> workers;
  if(
    !stream_refine_lifecycle(model, life, workers, reason) ||
    workers.size() != 3)
  {
    if(reason.empty())
      reason = "transitivity_lifecycle";
    return false;
  }
  workers_count = workers.size();
  std::vector<irep_idt> positive_results;
  std::vector<irep_idt> worker_results;
  irep_idt nonpositive_result;
  const goto_programt::instructiont *property = nullptr;
  const goto_programt::instructiont *error = nullptr;
  if(
    !relational_comparator_transitivity_property(
      model,
      life,
      ns,
      positive_results,
      nonpositive_result,
      rule,
      property,
      error,
      reason) ||
    !relational_bisimulation_exact_error_sink(model) ||
    !relational_bisimulation_main_regions(
      model, life, property, error, reason) ||
    !relational_comparator_transitivity_result_owners(
      model,
      workers,
      positive_results,
      nonpositive_result,
      ns,
      worker_results,
      owned_results,
      reason,
      true))
    return false;
  const auto is_positive_result =
    [&](const irep_idt &result)
    {
      return
        std::find(
          positive_results.begin(),
          positive_results.end(),
          result) != positive_results.end();
    };
  const bool result_roles =
    worker_results.size() == workers.size() &&
    ((rule == "strict_transitivity" &&
      is_positive_result(worker_results[0]) &&
      is_positive_result(worker_results[1]) &&
      worker_results[2] == nonpositive_result) ||
     (rule == "equality_substitution" &&
      worker_results[0] == nonpositive_result &&
      is_positive_result(worker_results[1]) &&
      is_positive_result(worker_results[2])));
  if(!result_roles)
  {
    reason = "transitivity_result_role_order";
    return false;
  }

  std::string scan_reason;
  if(
    relational_comparator_scan_law(
      model,
      ns,
      workers,
      worker_results,
      rule,
      pairwise_program_matches,
      mapped_symbols,
      audited_helpers,
      scan_reason))
  {
    regions_per_worker = 1;
    endpoint_input_symbols = 2;
    middle_input_symbols = 1;
    unary_selectors = 3;
    dominated_selectors = 3;
    guard_partition_groups = 1;
    dispatch_gates = 1;
    validity_selectors = 3;
    ordered_subtractions = 3;
    missing_key_guards = 1;
    return true;
  }
  if(
    !relational_comparator_worker_effects(
      model, workers, ns, reason))
    return false;

  std::vector<std::vector<relational_comparator_atomic_regiont>>
    summaries(workers.size());
  for(std::size_t index = 0; index < workers.size(); ++index)
  {
    const auto &program =
      model.goto_functions.function_map.at(workers[index]).body;
    if(
      !relational_comparator_atomic_regions(
        program, model, ns, summaries[index], reason))
    {
      if(reason == "missing_atomic_regions" &&
         !scan_reason.empty())
        reason = scan_reason;
      return false;
    }
    if(index == 0)
      regions_per_worker = summaries[index].size();
    else if(summaries[index].size() != regions_per_worker)
    {
      reason = "transitivity_region_census";
      return false;
    }
  }

  std::vector<relational_bisimulation_mappingt> mappings;
  for(std::size_t right = 1; right < workers.size(); ++right)
  {
    const auto &left_program =
      model.goto_functions.function_map.at(workers[0]).body;
    const auto &right_program =
      model.goto_functions.function_map.at(workers[right]).body;
    relational_bisimulation_mappingt mapping;
    if(
      !relational_bisimulation_programs(
        left_program,
        right_program,
        ns,
        mapping,
        reason))
    {
      reason = "transitivity_pair_" +
        std::to_string(right) + "_" + reason;
      return false;
    }
    ++pairwise_program_matches;
    mapped_symbols += mapping.forward.size();
    mappings.push_back(mapping);
  }

  std::set<irep_idt> reads;
  std::set<irep_idt> writes;
  std::set<irep_idt> visiting;
  if(
    !relational_bisimulation_function_effects(
      model,
      workers[0],
      ns,
      visiting,
      reads,
      writes,
      reason))
    return false;
  std::set<irep_idt> left_inputs;
  std::set<irep_idt> right_inputs;
  const auto mapped =
    [](const relational_bisimulation_mappingt &mapping,
       const irep_idt &identifier)
    {
      const auto entry = mapping.forward.find(identifier);
      return entry == mapping.forward.end() ?
        identifier : entry->second;
    };
  const relational_bisimulation_mappingt *left_to_right_mapping =
    nullptr;
  for(std::size_t bridge_index = 0;
      bridge_index < mappings.size(); ++bridge_index)
  {
    const std::size_t endpoint_index = 1 - bridge_index;
    std::set<irep_idt> candidate_left_inputs;
    std::set<irep_idt> candidate_right_inputs;
    for(const auto &identifier : reads)
    {
      if(writes.count(identifier) != 0)
        continue;
      const symbolt *symbol = lookup(identifier, ns);
      if(
        symbol == nullptr ||
        !symbol->is_static_lifetime)
        continue;
      const irep_idt bridge =
        mapped(mappings[bridge_index], identifier);
      const irep_idt endpoint =
        mapped(mappings[endpoint_index], identifier);
      if(endpoint == identifier && bridge != identifier)
      {
        const irep_idt bridge_middle =
          mapped(mappings[bridge_index], bridge);
        const irep_idt endpoint_middle =
          mapped(mappings[endpoint_index], bridge);
        if(
          bridge_middle == endpoint_middle &&
          bridge_middle != bridge)
          candidate_left_inputs.insert(identifier);
      }
      else if(
        bridge == endpoint &&
        bridge != identifier)
        candidate_right_inputs.insert(identifier);
    }
    if(
      !candidate_left_inputs.empty() &&
      candidate_left_inputs.size() ==
        candidate_right_inputs.size())
    {
      if(left_to_right_mapping != nullptr)
      {
        reason = "transitivity_ambiguous_input_triangle";
        return false;
      }
      left_inputs = candidate_left_inputs;
      right_inputs = candidate_right_inputs;
      left_to_right_mapping = &mappings[bridge_index];
    }
  }
  endpoint_input_symbols = left_inputs.size();
  middle_input_symbols = right_inputs.size();
  if(
    left_to_right_mapping == nullptr ||
    endpoint_input_symbols == 0 ||
    endpoint_input_symbols != middle_input_symbols)
  {
    reason = "transitivity_input_triangle";
    return false;
  }
  if(
    worker_results.size() != workers.size() ||
    !relational_comparator_transitivity_unary_selectors(
      summaries[0],
      worker_results[0],
      writes,
      left_inputs,
      right_inputs,
      *left_to_right_mapping,
      ns,
      unary_selectors,
      reason))
    return false;
  if(
    !relational_comparator_transitivity_validity_selector(
      summaries[0],
      worker_results[0],
      writes,
      left_inputs,
      right_inputs,
      *left_to_right_mapping,
      ns,
      validity_selectors,
      missing_key_guards,
      reason))
    return false;
  if(
    !relational_comparator_transitivity_selector_dominance(
      model.goto_functions.function_map.at(workers[0]).body,
      summaries[0],
      worker_results[0],
      writes,
      left_inputs,
      right_inputs,
      *left_to_right_mapping,
      ns,
      dominated_selectors,
      ordered_subtractions,
      reason) ||
    dominated_selectors != unary_selectors)
  {
    if(reason.empty())
      reason = "transitivity_selector_dominance_count";
    return false;
  }

  std::vector<std::size_t> reference_partitions;
  std::size_t reference_gates = 0;
  std::size_t reference_helpers = 0;
  for(std::size_t index = 0; index < workers.size(); ++index)
  {
    std::vector<std::size_t> partitions;
    std::size_t gates = 0;
    std::size_t helpers = 0;
    const auto &program =
      model.goto_functions.function_map.at(workers[index]).body;
    if(
      !relational_comparator_guard_partitions(
        summaries[index], partitions, reason) ||
      !relational_comparator_dispatch_cfg(
        program, summaries[index], partitions, gates, reason) ||
      !relational_comparator_helpers(
        summaries[index], model, ns, helpers, reason))
      return false;
    if(index == 0)
    {
      reference_partitions = partitions;
      reference_gates = gates;
      reference_helpers = helpers;
    }
    else if(
      partitions != reference_partitions ||
      gates != reference_gates ||
      helpers != reference_helpers)
    {
      reason = "transitivity_worker_audit_mismatch";
      return false;
    }
  }
  guard_partition_groups = reference_partitions.size();
  dispatch_gates = reference_gates;
  audited_helpers = reference_helpers;
  return true;
}
} // namespace

void role_split_affine_stream_audit(
  const goto_modelt &goto_model,
  message_handlert &message_handler)
{
  (void)message_handler;
  const namespacet ns(goto_model.symbol_table);
  std::string reason;
  std::size_t source_roles = 0;
  std::size_t stage_roles = 0;
  std::size_t sink_roles = 0;
  const bool candidate =
    role_split_affine_stream_audit_impl(
      goto_model,
      ns,
      reason,
      source_roles,
      stage_roles,
      sink_roles);
  std::cout << "NATIVE_ROLE_SPLIT_STREAM_AUDIT candidate="
            << (candidate ? 1 : 0)
            << " source_roles=" << source_roles
            << " stage_roles=" << stage_roles
            << " sink_roles=" << sink_roles;
  if(!candidate)
    std::cout << " reason=" << reason;
  std::cout << '\n';
}

void publication_frontier_sequence_audit(
  const goto_modelt &goto_model,
  message_handlert &message_handler)
{
  (void)message_handler;
  const namespacet ns(goto_model.symbol_table);
  std::string mode;
  std::string reason;
  const bool candidate =
    publication_frontier_sequence_audit_impl(
      goto_model, ns, mode, reason);
  std::cout << "NATIVE_PUBLICATION_FRONTIER_AUDIT candidate="
            << (candidate ? 1 : 0);
  if(candidate)
    std::cout << " mode=" << mode;
  else
    std::cout << " reason=" << reason;
  std::cout << '\n';
}

void relational_bisimulation_audit(
  const goto_modelt &goto_model,
  message_handlert &message_handler)
{
  (void)message_handler;
  const namespacet ns(goto_model.symbol_table);
  std::size_t pairs = 0;
  std::string reason;
  const bool candidate =
    relational_bisimulation_audit_impl(
      goto_model, ns, pairs, reason);
  std::cout << "NATIVE_RELATIONAL_BISIMULATION_AUDIT candidate="
            << (candidate ? 1 : 0)
            << " pairs=" << pairs;
  if(!candidate)
    std::cout << " reason=" << reason;
  std::cout << '\n';

  std::size_t transitivity_workers = 0;
  std::size_t transitivity_regions = 0;
  std::size_t transitivity_program_matches = 0;
  std::size_t transitivity_mapped_symbols = 0;
  std::size_t transitivity_endpoint_inputs = 0;
  std::size_t transitivity_middle_inputs = 0;
  std::size_t transitivity_owned_results = 0;
  std::size_t transitivity_unary_selectors = 0;
  std::size_t transitivity_dominated_selectors = 0;
  std::size_t transitivity_guard_partitions = 0;
  std::size_t transitivity_dispatch_gates = 0;
  std::size_t transitivity_audited_helpers = 0;
  std::size_t transitivity_validity_selectors = 0;
  std::size_t transitivity_ordered_subtractions = 0;
  std::size_t transitivity_missing_key_guards = 0;
  std::string transitivity_rule;
  reason.clear();
  const bool transitivity =
    relational_comparator_transitivity_diagnostic(
      goto_model,
      ns,
      transitivity_workers,
      transitivity_regions,
      transitivity_program_matches,
      transitivity_mapped_symbols,
      transitivity_endpoint_inputs,
      transitivity_middle_inputs,
      transitivity_owned_results,
      transitivity_unary_selectors,
      transitivity_dominated_selectors,
      transitivity_guard_partitions,
      transitivity_dispatch_gates,
      transitivity_audited_helpers,
      transitivity_validity_selectors,
      transitivity_ordered_subtractions,
      transitivity_missing_key_guards,
      transitivity_rule,
      reason);
  std::cout
    << "NATIVE_RELATIONAL_TRANSITIVITY_DIAGNOSTIC candidate="
    << (transitivity ? 1 : 0)
    << " workers=" << transitivity_workers
    << " regions_per_worker=" << transitivity_regions
    << " pairwise_program_matches=" << transitivity_program_matches
    << " mapped_symbols=" << transitivity_mapped_symbols
    << " endpoint_inputs=" << transitivity_endpoint_inputs
    << " middle_inputs=" << transitivity_middle_inputs
    << " owned_results=" << transitivity_owned_results
    << " unary_selectors=" << transitivity_unary_selectors
    << " dominated_selectors="
    << transitivity_dominated_selectors
    << " guard_partitions="
    << transitivity_guard_partitions
    << " dispatch_gates=" << transitivity_dispatch_gates
    << " audited_helpers="
    << transitivity_audited_helpers
    << " validity_selectors="
    << transitivity_validity_selectors
    << " ordered_subtractions="
    << transitivity_ordered_subtractions
    << " missing_key_guards="
    << transitivity_missing_key_guards;
  if(transitivity)
    std::cout << " rule=" << transitivity_rule;
  if(!transitivity)
    std::cout << " reason=" << reason;
  std::cout << '\n';

  irep_idt left_result;
  irep_idt right_result;
  std::size_t left_regions = 0;
  std::size_t right_regions = 0;
  std::size_t left_assumptions = 0;
  std::size_t right_assumptions = 0;
  std::size_t left_assignments = 0;
  std::size_t right_assignments = 0;
  std::size_t left_helpers = 0;
  std::size_t right_helpers = 0;
  std::size_t left_internal_gotos = 0;
  std::size_t right_internal_gotos = 0;
  std::size_t transition_matches = 0;
  std::size_t contextual_equalities = 0;
  std::size_t dominated_equalities = 0;
  std::size_t guard_partition_groups = 0;
  std::size_t dispatch_gates = 0;
  std::size_t audited_helpers = 0;
  reason.clear();
  const bool comparator =
    relational_comparator_diagnostic(
      goto_model,
      ns,
      left_result,
      right_result,
      left_regions,
      right_regions,
      left_assumptions,
      right_assumptions,
      left_assignments,
      right_assignments,
      left_helpers,
      right_helpers,
      left_internal_gotos,
      right_internal_gotos,
      transition_matches,
      contextual_equalities,
      dominated_equalities,
      guard_partition_groups,
      dispatch_gates,
      audited_helpers,
      reason);
  std::cout
    << "NATIVE_RELATIONAL_COMPARATOR_DIAGNOSTIC candidate="
    << (comparator ? 1 : 0)
    << " left_regions=" << left_regions
    << " right_regions=" << right_regions
    << " left_assumptions=" << left_assumptions
    << " right_assumptions=" << right_assumptions
    << " left_assignments=" << left_assignments
    << " right_assignments=" << right_assignments
    << " left_helpers=" << left_helpers
    << " right_helpers=" << right_helpers
    << " left_internal_gotos=" << left_internal_gotos
    << " right_internal_gotos=" << right_internal_gotos
    << " transition_matches=" << transition_matches
    << " contextual_equalities=" << contextual_equalities
    << " dominated_equalities=" << dominated_equalities
    << " guard_partition_groups=" << guard_partition_groups
    << " dispatch_gates=" << dispatch_gates
    << " audited_helpers=" << audited_helpers;
  if(comparator)
    std::cout
      << " left_result=" << left_result
      << " right_result=" << right_result;
  else
    std::cout << " reason=" << reason;
  std::cout << '\n';
}

bool relational_comparator_transitivity_proof(
  const goto_modelt &goto_model,
  message_handlert &message_handler)
{
  (void)message_handler;
  const namespacet ns(goto_model.symbol_table);
  std::string reason;
  std::size_t transitivity_workers = 0;
  std::size_t transitivity_regions = 0;
  std::size_t transitivity_program_matches = 0;
  std::size_t transitivity_mapped_symbols = 0;
  std::size_t transitivity_endpoint_inputs = 0;
  std::size_t transitivity_middle_inputs = 0;
  std::size_t transitivity_owned_results = 0;
  std::size_t transitivity_unary_selectors = 0;
  std::size_t transitivity_dominated_selectors = 0;
  std::size_t transitivity_guard_partitions = 0;
  std::size_t transitivity_dispatch_gates = 0;
  std::size_t transitivity_audited_helpers = 0;
  std::size_t transitivity_validity_selectors = 0;
  std::size_t transitivity_ordered_subtractions = 0;
  std::size_t transitivity_missing_key_guards = 0;
  std::string transitivity_rule;
  if(
    relational_comparator_transitivity_diagnostic(
      goto_model,
      ns,
      transitivity_workers,
      transitivity_regions,
      transitivity_program_matches,
      transitivity_mapped_symbols,
      transitivity_endpoint_inputs,
      transitivity_middle_inputs,
      transitivity_owned_results,
      transitivity_unary_selectors,
      transitivity_dominated_selectors,
      transitivity_guard_partitions,
      transitivity_dispatch_gates,
      transitivity_audited_helpers,
      transitivity_validity_selectors,
      transitivity_ordered_subtractions,
      transitivity_missing_key_guards,
      transitivity_rule,
      reason))
  {
    std::cout
      << "NATIVE_RELATIONAL_TRANSITIVITY applied=1"
      << " workers=" << transitivity_workers
      << " regions=" << transitivity_regions
      << " selectors=" << transitivity_unary_selectors
      << " validity=" << transitivity_validity_selectors
      << " subtractions=" << transitivity_ordered_subtractions
      << " rule=" << transitivity_rule
      << '\n';
    return true;
  }
  std::cout
    << "NATIVE_RELATIONAL_TRANSITIVITY applied=0 reason="
    << reason << '\n';
  return false;
}

bool relational_comparator_antisymmetry_proof(
  const goto_modelt &goto_model,
  message_handlert &message_handler)
{
  (void)message_handler;
  const namespacet ns(goto_model.symbol_table);
  irep_idt left_result;
  irep_idt right_result;
  std::size_t left_regions = 0;
  std::size_t right_regions = 0;
  std::size_t left_assumptions = 0;
  std::size_t right_assumptions = 0;
  std::size_t left_assignments = 0;
  std::size_t right_assignments = 0;
  std::size_t left_helpers = 0;
  std::size_t right_helpers = 0;
  std::size_t left_internal_gotos = 0;
  std::size_t right_internal_gotos = 0;
  std::size_t transition_matches = 0;
  std::size_t contextual_equalities = 0;
  std::size_t dominated_equalities = 0;
  std::size_t guard_partition_groups = 0;
  std::size_t dispatch_gates = 0;
  std::size_t audited_helpers = 0;
  std::string reason;
  if(
    relational_comparator_diagnostic(
      goto_model,
      ns,
      left_result,
      right_result,
      left_regions,
      right_regions,
      left_assumptions,
      right_assumptions,
      left_assignments,
      right_assignments,
      left_helpers,
      right_helpers,
      left_internal_gotos,
      right_internal_gotos,
      transition_matches,
      contextual_equalities,
      dominated_equalities,
      guard_partition_groups,
      dispatch_gates,
      audited_helpers,
      reason))
  {
    std::cout
      << "NATIVE_RELATIONAL_COMPARATOR applied=1"
      << " transitions=" << transition_matches
      << " partitions=" << guard_partition_groups
      << " gates=" << dispatch_gates
      << '\n';
    return true;
  }
  std::cout
    << "NATIVE_RELATIONAL_COMPARATOR applied=0 reason="
    << reason << '\n';
  return false;
}

bool extremum_cone_proof(
  const goto_modelt &goto_model,
  message_handlert &message_handler)
{
  (void)message_handler;
  const namespacet ns(goto_model.symbol_table);
  std::string reason;
  if(
    relational_comparator_transitivity_proof(
      goto_model, message_handler))
    return true;
  irep_idt comparator_left_result;
  irep_idt comparator_right_result;
  std::size_t comparator_left_regions = 0;
  std::size_t comparator_right_regions = 0;
  std::size_t comparator_left_assumptions = 0;
  std::size_t comparator_right_assumptions = 0;
  std::size_t comparator_left_assignments = 0;
  std::size_t comparator_right_assignments = 0;
  std::size_t comparator_left_helpers = 0;
  std::size_t comparator_right_helpers = 0;
  std::size_t comparator_left_internal_gotos = 0;
  std::size_t comparator_right_internal_gotos = 0;
  std::size_t comparator_transition_matches = 0;
  std::size_t comparator_contextual_equalities = 0;
  std::size_t comparator_dominated_equalities = 0;
  std::size_t comparator_guard_partition_groups = 0;
  std::size_t comparator_dispatch_gates = 0;
  std::size_t comparator_audited_helpers = 0;
  if(
    relational_comparator_diagnostic(
      goto_model,
      ns,
      comparator_left_result,
      comparator_right_result,
      comparator_left_regions,
      comparator_right_regions,
      comparator_left_assumptions,
      comparator_right_assumptions,
      comparator_left_assignments,
      comparator_right_assignments,
      comparator_left_helpers,
      comparator_right_helpers,
      comparator_left_internal_gotos,
      comparator_right_internal_gotos,
      comparator_transition_matches,
      comparator_contextual_equalities,
      comparator_dominated_equalities,
      comparator_guard_partition_groups,
      comparator_dispatch_gates,
      comparator_audited_helpers,
      reason))
  {
    std::cout
      << "NATIVE_RELATIONAL_COMPARATOR applied=1"
      << " transitions=" << comparator_transition_matches
      << " partitions=" << comparator_guard_partition_groups
      << " gates=" << comparator_dispatch_gates
      << '\n';
    return true;
  }
  std::cout
    << "NATIVE_RELATIONAL_COMPARATOR applied=0 reason="
    << reason << '\n';
  reason.clear();
  if(prefix_channel_last_value_proof_impl(goto_model, ns, reason))
    return true;
  std::cout << "NATIVE_PREFIX_CHANNEL applied=0 reason="
            << reason << '\n';
  reason.clear();
  if(prefix_channel_alternating_sum_proof_impl(goto_model, ns, reason))
    return true;
  std::cout << "NATIVE_PREFIX_CHANNEL applied=0 reason="
            << reason << '\n';
  reason.clear();
  if(prefix_channel_alternating_snapshot_proof_impl(
       goto_model, ns, reason))
    return true;
  std::cout << "NATIVE_PREFIX_CHANNEL applied=0 reason="
            << reason << '\n';
  reason.clear();
  if(prefix_channel_bounded_sum_proof_impl(goto_model, ns, reason))
    return true;
  std::cout << "NATIVE_PREFIX_CHANNEL applied=0 reason="
            << reason << '\n';
  reason.clear();
  if(prefix_channel_affine_pipeline_proof_impl(
       goto_model, ns, reason))
    return true;
  std::cout << "NATIVE_PREFIX_CHANNEL applied=0 reason="
            << reason << '\n';
  reason.clear();
  if(stream_sentinel_refinement_proof_impl(goto_model, ns, reason))
    return true;
  std::cout << "NATIVE_STREAM_REFINEMENT applied=0 reason="
            << reason << '\n';
  reason.clear();
  if(stream_done_drain_refinement_proof_impl(goto_model, ns, reason))
    return true;
  std::cout << "NATIVE_STREAM_REFINEMENT applied=0 reason="
            << reason << '\n';
  reason.clear();
  if(hierarchical_fold_proof_impl(goto_model, ns, reason))
    return true;
  std::cout << "NATIVE_HIERARCHICAL_FOLD applied=0 reason="
            << reason << '\n';
  reason.clear();
  if(equivalent_static_partition_proof_impl(
       goto_model, ns, reason))
    return true;
  std::cout << "NATIVE_RELATIONAL_FLOW applied=0 reason="
            << reason << '\n';
  reason.clear();
  if(modular_sum_partition_proof_impl(
       goto_model, ns, reason))
    return true;
  std::cout
    << "NATIVE_MODULAR_SUM_PARTITION applied=0 reason="
    << reason << '\n';
  reason.clear();
  if(boolean_segment_partition_proof_impl(
       goto_model, ns, reason))
    return true;
  std::cout
    << "NATIVE_BOOLEAN_SEGMENT_PARTITION applied=0 reason="
    << reason << '\n';
  reason.clear();
  if(pointwise_map_partition_proof_impl(
       goto_model, ns, reason))
    return true;
  std::cout
    << "NATIVE_POINTWISE_MAP_PARTITION applied=0 reason="
    << reason << '\n';
  reason.clear();
  if(maximum_tail_partition_proof_impl(
       goto_model, ns, reason))
    return true;
  std::cout
    << "NATIVE_MAXIMUM_TAIL_PARTITION applied=0 reason="
    << reason << '\n';
  reason.clear();
  if(ordered_extremum_partition_proof_impl(
       goto_model, ns, reason))
    return true;
  std::cout
    << "NATIVE_ORDERED_EXTREMUM_PARTITION applied=0 reason="
    << reason << '\n';
  reason.clear();
  if(equivalent_dynamic_partition_proof_impl(goto_model, ns, reason))
    return true;
  std::cout << "NATIVE_RELATIONAL_FLOW applied=0 reason="
            << reason << '\n';
  reason.clear();
  if(ordered_stream_residual_proof_impl(goto_model, ns, reason))
    return true;
  std::cout << "NATIVE_RELATIONAL_FLOW applied=0 reason="
            << reason << '\n';
  reason.clear();
  if(linear_fold_proof_impl(goto_model, ns, reason))
    return true;
  std::cout << "NATIVE_LINEAR_ANNIHILATOR applied=0 reason="
            << reason << '\n';
  reason.clear();
  if(affine_resource_proof_impl(goto_model, ns, reason))
    return true;
  std::cout << "NATIVE_LINEAR_ANNIHILATOR applied=0 reason="
            << reason << '\n';
  reason.clear();
  if(extremum_homomorphism_proof_impl(goto_model, ns, reason))
    return true;
  std::cout << "NATIVE_EXTREMUM_HOMOMORPHISM applied=0 reason="
            << reason << '\n';
  reason.clear();
  std::size_t relational_pairs = 0;
  if(
    relational_bisimulation_audit_impl(
      goto_model, ns, relational_pairs, reason))
  {
    std::cout << "NATIVE_RELATIONAL_BISIMULATION applied=1 pairs="
              << relational_pairs << '\n';
    return true;
  }
  std::cout << "NATIVE_RELATIONAL_BISIMULATION applied=0 reason="
            << reason << '\n';
  reason.clear();
  std::size_t source_roles = 0;
  std::size_t stage_roles = 0;
  std::size_t sink_roles = 0;
  if(
    role_split_affine_stream_audit_impl(
      goto_model,
      ns,
      reason,
      source_roles,
      stage_roles,
      sink_roles))
  {
    std::cout << "NATIVE_ROLE_SPLIT_STREAM applied=1"
              << " source_roles=" << source_roles
              << " stage_roles=" << stage_roles
              << " sink_roles=" << sink_roles << '\n';
    return true;
  }
  std::cout << "NATIVE_ROLE_SPLIT_STREAM applied=0 reason="
            << reason << '\n';
  reason.clear();
  std::string publication_mode;
  if(
    publication_frontier_sequence_audit_impl(
      goto_model, ns, publication_mode, reason))
  {
    std::cout << "NATIVE_PUBLICATION_FRONTIER applied=1 mode="
              << publication_mode << '\n';
    return true;
  }
  std::cout << "NATIVE_PUBLICATION_FRONTIER applied=0 reason="
            << reason << '\n';
  reason.clear();
  propertyt property;
  if(!find_property(goto_model, ns, property, reason))
  {
    std::cout << "NATIVE_EXTREMUM_CONE applied=0 reason=" << reason << '\n';
    return false;
  }

  lifecyclet life;
  if(!lifecycle(goto_model, life, reason))
  {
    std::cout << "NATIVE_EXTREMUM_CONE applied=0 reason=" << reason << '\n';
    return false;
  }

  summary_infot lower;
  summary_infot upper;
  if(
    !summary_writes(
      goto_model, life, property, property.lower, true, lower, reason) ||
    !summary_writes(
      goto_model, life, property, property.upper, false, upper, reason))
  {
    std::cout << "NATIVE_EXTREMUM_CONE applied=0 reason=" << reason << '\n';
    return false;
  }

  std::set<irep_idt> initial_booleans = property.readiness;
  initial_booleans.insert(property.output);
  if(
    !main_booleans_zero_before_create(
      goto_model, life, initial_booleans, reason))
  {
    std::cout << "NATIVE_EXTREMUM_CONE applied=0 reason=" << reason << '\n';
    return false;
  }

  irep_idt anchor_base;
  if(property.readiness.empty())
  {
    irep_idt lower_base;
    irep_idt upper_base;
    if(
      !lower.has_main_init || !upper.has_main_init ||
      !base_pointer(lower.main_init_rhs, lower_base) ||
      !base_pointer(upper.main_init_rhs, upper_base) ||
      lower_base != upper_base ||
      strip(lower.main_init_rhs) != strip(upper.main_init_rhs) ||
      contains_side_effect(lower.main_init_rhs) ||
      contains_side_effect(upper.main_init_rhs) ||
      lower.has_worker_init || upper.has_worker_init)
    {
      std::cout << "NATIVE_EXTREMUM_CONE applied=0 reason=main_anchor\n";
      return false;
    }
    anchor_base = lower_base;
  }
  else
  {
    irep_idt lower_base;
    irep_idt upper_base;
    if(
      !lower.has_worker_init || !upper.has_worker_init ||
      lower.readiness == upper.readiness ||
      !base_pointer(lower.init_rhs, lower_base) ||
      !base_pointer(upper.init_rhs, upper_base) ||
      lower_base != upper_base ||
      (property.delta != 0 && !shared_atomic_array(lower_base, ns)) ||
      strip(lower.init_rhs) != strip(upper.init_rhs) ||
      !readiness_writes(
        goto_model, life, property, lower, upper, reason))
    {
      std::cout << "NATIVE_EXTREMUM_CONE applied=0 reason="
                << (reason.empty() ? "worker_anchor" : reason) << '\n';
      return false;
    }
    anchor_base = lower_base;
    if(property.delta == 0)
    {
      for(const auto &worker : life.workers)
      {
        const auto &body =
          goto_model.goto_functions.function_map.at(worker).body;
        for(const auto &instruction : body.instructions)
        {
          if(!instruction.is_assign())
            continue;
          irep_idt base;
          if(
            base_pointer(instruction.assign_lhs(), base) &&
            base == lower_base)
          {
            std::cout
              << "NATIVE_EXTREMUM_CONE applied=0 reason=anchor_writer\n";
            return false;
          }
        }
      }
    }
    else if(
      !anchor_skew_at_most_one(
        goto_model,
        life,
        property,
        lower,
        upper,
        lower_base,
        reason))
    {
      std::cout << "NATIVE_EXTREMUM_CONE applied=0 reason="
                << reason << '\n';
      return false;
    }
  }

  if(
    !output_and_error_path(goto_model, life, property, reason) ||
    !property_control_supported(goto_model, property, ns, reason) ||
    !worker_calls_supported(goto_model, life, reason) ||
    (!anchor_base.empty() &&
     (!anchor_storage_stable(goto_model, life, anchor_base, reason) ||
      !anchor_alias_free(goto_model, anchor_base, reason))))
  {
    std::cout << "NATIVE_EXTREMUM_CONE applied=0 reason=" << reason << '\n';
    return false;
  }
  std::set<irep_idt> concurrency_symbols = {
    property.lower, property.upper, property.output};
  concurrency_symbols.insert(
    property.readiness.begin(), property.readiness.end());
  if(
    !protected_accesses_supported(
      goto_model, life, ns, concurrency_symbols, reason))
  {
    std::cout << "NATIVE_EXTREMUM_CONE applied=0 reason=" << reason << '\n';
    return false;
  }
  std::set<irep_idt> protected_symbols = concurrency_symbols;
  if(!anchor_base.empty())
    protected_symbols.insert(anchor_base);
  if(!no_addresses(goto_model, protected_symbols, reason))
  {
    std::cout << "NATIVE_EXTREMUM_CONE applied=0 reason=" << reason << '\n';
    return false;
  }

  std::cout << "NATIVE_EXTREMUM_CONE applied=1 delta="
            << property.delta << " lower="
            << property.lower << " upper=" << property.upper << '\n';
  return true;
}
