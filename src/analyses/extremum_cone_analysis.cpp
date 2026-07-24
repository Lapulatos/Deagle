/*******************************************************************\

Module: Relational Extremum-Cone Invariant

\*******************************************************************/

#include "extremum_cone_analysis.h"

#include "natural_loops.h"

#include <goto-programs/goto_model.h>

#include <util/arith_tools.h>
#include <util/expr_util.h>
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
} // namespace

bool extremum_cone_proof(
  const goto_modelt &goto_model,
  message_handlert &message_handler)
{
  (void)message_handler;
  const namespacet ns(goto_model.symbol_table);
  std::string reason;
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
