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
      if(
        instruction->call_lhs().is_nil() ||
        instruction->call_arguments().size() != 2 ||
        !symbol_id(instruction->call_lhs(), accumulator) ||
        !symbol_id(instruction->call_arguments()[0], first) ||
        accumulator != first || !shared_signed(accumulator, ns) ||
        atomic_depth != 1 || fold_call != program.instructions.end())
      {
        reason = "flow_worker_call";
        return false;
      }
      result.accumulator = accumulator;
      result.operation = callee;
      result.contribution = strip(instruction->call_arguments()[1]);
      result.writes.insert(&*instruction);
      fold_call = instruction;
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
    fold_call == program.instructions.end())
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
  bool strict_bound = false;
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
      strict_bound =
        strict_bound ||
        relation_symbols(term, ID_gt, bound, split) ||
        relation_symbols(term, ID_lt, split, bound);
    }
  }
  return nonnegative && strict_bound;
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
      condition.id() != ID_le || condition.operands().size() != 2 ||
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
      assume_calls != 1 || role.queue.empty() || role.back.empty() ||
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
  return
    strict_residual && negative_nonnegative &&
    element_positive && defined_negation;
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
    if(symbol_id(producer->element, candidate))
    {
      positive = producer;
      element = candidate;
    }
    const exprt &value = strip(producer->element);
    if(
      value.id() == ID_unary_minus && value.operands().size() == 1 &&
      symbol_id(value.op0(), candidate))
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
  if(
    positive == nullptr || negative == nullptr ||
    positive == negative || element.empty() ||
    !shared_signed(element, ns) ||
    !stream_positive_preconditions(
      model,
      life,
      positive->bound,
      negative->bound,
      element,
      roles))
  {
    reason = "stream_residual_precondition";
    return false;
  }

  std::set<irep_idt> queues = {
    producers[0]->queue, producers[1]->queue};
  if(!stream_main_allocations(model, life, queues, ns, reason))
    return false;
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
        (base_pointer(*lhs, base) && queues.count(base) != 0);
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
  for(const auto &queue : queues)
  {
    if(!flow_alias_free(model, queue, reason))
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
} // namespace

bool extremum_cone_proof(
  const goto_modelt &goto_model,
  message_handlert &message_handler)
{
  (void)message_handler;
  const namespacet ns(goto_model.symbol_table);
  std::string reason;
  if(hierarchical_fold_proof_impl(goto_model, ns, reason))
    return true;
  std::cout << "NATIVE_HIERARCHICAL_FOLD applied=0 reason="
            << reason << '\n';
  reason.clear();
  if(equivalent_static_partition_proof_impl(goto_model, ns, reason))
    return true;
  std::cout << "NATIVE_RELATIONAL_FLOW applied=0 reason="
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
