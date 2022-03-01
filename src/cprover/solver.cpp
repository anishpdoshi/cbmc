/*******************************************************************\

Module: Solver

Author:

\*******************************************************************/

/// \file
/// Solver

#include "solver.h"

#include <util/cout_message.h>
#include <util/format_expr.h>
#include <util/mathematical_expr.h>
#include <util/pointer_expr.h>
#include <util/simplify_expr.h>
#include <util/std_expr.h>

#include <solvers/flattening/bv_pointers.h>
#include <solvers/sat/satcheck.h>

#include "console.h"
#include "free_symbols.h"
#include "state.h"

#include <iomanip>
#include <iostream>
#include <map>
#include <set>

class statet
{
public:
  explicit statet(symbol_exprt _symbol) : symbol(std::move(_symbol))
  {
  }

  symbol_exprt symbol;

  // our current hypothesis invariant
  std::vector<exprt> invariants;

  // formulas where this state is on the rhs of ⇒
  std::vector<implies_exprt> implications;

  bool add_invariant(exprt);
};

class propertyt
{
public:
  propertyt(
    source_locationt __source_location,
    symbol_exprt __state_symbol,
    exprt __condition)
    : source_location(std::move(__source_location)),
      state_symbol(std::move(__state_symbol)),
      condition(std::move(__condition))
  {
  }

  // formulas where this state is on the lhs of ⇒
  source_locationt source_location;
  symbol_exprt state_symbol;
  exprt condition;

  using statust = enum { UNKNOWN, PASS, REFUTED, ERROR };
  statust status = UNKNOWN;
};

bool statet::add_invariant(exprt invariant)
{
  if(invariant.is_true())
    return false; // implied

  for(auto &i : invariants)
    if(i == invariant)
      return false; // already there

  invariants.push_back(std::move(invariant));

  return true;
}

std::vector<statet> find_states(const std::vector<exprt> &constraints)
{
  std::set<symbol_exprt> states_set;
  std::vector<statet> states_vector;

  for(auto &c : constraints)
  {
    free_symbols(c, [&states_set, &states_vector](const symbol_exprt &s) {
      auto insert_result = states_set.insert(s);
      if(insert_result.second)
        states_vector.emplace_back(s);
    });
  }

  return states_vector;
}

void find_implications(
  const std::vector<exprt> &constraints,
  std::vector<statet> &states)
{
  std::map<symbol_exprt, std::size_t> states_map;

  for(std::size_t i = 0; i < states.size(); i++)
    states_map[states[i].symbol] = i;

  for(const auto &c : constraints)
  {
    // look for ∀ ς : state . Sxx(ς) ⇒ Syy(...)
    //      and ∀ ς : state . Sxx(ς) ⇒ ...
    if(c.id() == ID_forall && to_forall_expr(c).where().id() == ID_implies)
    {
      auto &implication = to_implies_expr(to_forall_expr(c).where());

      if(
        implication.rhs().id() == ID_function_application &&
        to_function_application_expr(implication.rhs()).function().id() ==
          ID_symbol)
      {
        auto &rhs_symbol = to_symbol_expr(
          to_function_application_expr(implication.rhs()).function());
        auto s_it = states_map.find(rhs_symbol);
        if(s_it != states_map.end())
        {
          states[s_it->second].implications.emplace_back(implication);
        }
      }
    }
  }
}

std::vector<propertyt> find_properties(const std::vector<exprt> &constraints)
{
  std::vector<propertyt> properties;

  for(const auto &c : constraints)
  {
    // look for ∀ ς : state . Sxx(ς) ⇒ ...
    if(c.id() == ID_forall && to_forall_expr(c).where().id() == ID_implies)
    {
      auto &implication = to_implies_expr(to_forall_expr(c).where());

      if(
        implication.rhs().id() != ID_function_application &&
        implication.lhs().id() == ID_function_application &&
        to_function_application_expr(implication.lhs()).function().id() ==
          ID_symbol)
      {
        auto &lhs_symbol = to_symbol_expr(
          to_function_application_expr(implication.lhs()).function());
        properties.emplace_back(
          c.source_location(), lhs_symbol, implication.rhs());
      }
    }
  }

  return properties;
}

struct implicationt
{
  implicationt(
    optionalt<symbol_exprt> __source_state,
    optionalt<exprt> __guard,
    exprt __update)
    : source_state(std::move(__source_state)),
      guard(std::move(__guard)),
      update(std::move(__update))
  {
  }

  optionalt<symbol_exprt> source_state;
  optionalt<exprt> guard;
  exprt update;
};

#if 0
implicationt parse_implication(const implies_exprt &src)
{
  PRECONDITION(src.rhs().id() == ID_function_application);
  PRECONDITION(src.lhs().is_true() || src.lhs().id() == ID_function_application);

  auto &function_application = to_function_application_expr(src.rhs());
  PRECONDITION(function_application.arguments().size() == 1);

  if(src.lhs().id() == ID_function_application)
  {
    return implicationt(
      to_symbol_expr(to_function_application_expr(src.lhs()).function()),
      {},
      function_application.arguments().front());
  }
  else
  {
    return implicationt(
      {},
      {},
      function_application.arguments().front());
  }
}
#endif

exprt property_predicate(const implies_exprt &src)
{
  // Sxx(ς) ⇒ p(ς)
  return src.rhs();
}

void dump(const std::vector<statet> &states, bool values, bool implications)
{
  for(const auto &s : states)
  {
    std::cout << "STATE: " << format(s.symbol) << '\n';

    if(values)
    {
      for(auto &i : s.invariants)
        std::cout << "  invariant: " << format(i) << '\n';
    }

    if(implications)
    {
      for(auto &c : s.implications)
      {
        std::cout << "  implication: ";
        std::cout << format(c);
        std::cout << '\n';
      }
    }
  }
}

exprt simplify_evaluate_update(exprt src)
{
  if(src.id() == ID_evaluate)
  {
    auto &evaluate_expr = to_binary_expr(src);
    if(evaluate_expr.op0().id() == ID_update_state)
    {
      const auto &update_state_expr = to_ternary_expr(evaluate_expr.op0());
      if(evaluate_expr.op1() == update_state_expr.op1())
      {
        // (ς[A:=V])(A) -> V
        return update_state_expr.op2();
      }
      else if(
        evaluate_expr.op1().id() == ID_object_address &&
        update_state_expr.op1().id() == ID_object_address)
      {
        // Different object
        // (ς[❝x❞:=V])(❝y❞) -> ς(❝y❞)
        auto new_evaluate_expr = evaluate_expr;
        new_evaluate_expr.op0() = update_state_expr.op0();
        return std::move(new_evaluate_expr);
      }
      else
      {
      }
    }
  }

  for(auto &op : src.operands())
    op = simplify_evaluate_update(op);
  return src;
}

exprt replace_evaluate(exprt src)
{
  if(src.id() == ID_evaluate)
  {
    auto &evaluate_expr = to_binary_expr(src);
    if(evaluate_expr.op1().id() == ID_object_address)
    {
      const auto &object_address = to_object_address_expr(evaluate_expr.op1());
      auto id = object_address.object_identifier();
      return symbol_exprt(
        "evaluate-" + id2string(id), object_address.object_type());
    }
  }

  for(auto &op : src.operands())
    op = replace_evaluate(op);

  return src;
}

enum class propagate_resultt
{
  SATURATED,
  PROPAGATED,
  CONFLICT,
  ERROR
};

propagate_resultt propagate(
  std::vector<statet> &states,
  const namespacet &ns,
  const std::function<void(const symbol_exprt &, exprt)> &propagator)
{
  bool propagated = false, conflict = false, error = false;

  for(auto &s : states)
  {
    for(const auto &inv : s.invariants)
    {
      for(const auto &implication : s.implications)
      {
        if(
          implication.rhs().id() == ID_function_application &&
          to_function_application_expr(implication.rhs()).function() ==
            s.symbol)
        {
          auto &next_state =
            to_function_application_expr(implication.rhs()).arguments().front();
          auto lambda_expr = lambda_exprt({state_expr()}, inv);
          auto instance = lambda_expr.instantiate({next_state});
          auto simplified1 = simplify_evaluate_update(instance);
          auto simplified2 = simplify_expr(simplified1, ns);

          if(implication.lhs().id() == ID_function_application)
          {
            // Sxx(ς) ⇒ Syy(ς[update])
            auto &state = to_symbol_expr(
              to_function_application_expr(implication.lhs()).function());
            propagator(state, simplified2);
          }
          else if(
            implication.lhs().id() == ID_and &&
            to_and_expr(implication.lhs()).op0().id() ==
              ID_function_application)
          {
            // Sxx(ς) ∧ ς(COND) ⇒ Syy(ς)
            auto &function_application = to_function_application_expr(
              to_and_expr(implication.lhs()).op0());
            auto &state = to_symbol_expr(function_application.function());
            auto cond = to_and_expr(implication.lhs()).op1();
            propagator(state, implies_exprt(cond, simplified2));
          }
          else
          {
            // these are preconditions, e.g., true ⇒ SInitial(ς)
            auto cond = implies_exprt(implication.lhs(), simplified2);
            std::cout << "PREa: " << format(cond) << "\n";
            auto cond_replaced = replace_evaluate(cond);
            std::cout << "PREb: " << format(cond_replaced) << "\n";

            // ask the solver
            cout_message_handlert message_handler;
            satcheckt satcheck(message_handler);
            bv_pointerst solver(ns, satcheck, message_handler);
            solver.set_to_false(cond_replaced);
            switch(solver())
            {
            case decision_proceduret::resultt::D_SATISFIABLE:
              conflict = true;
              break;
            case decision_proceduret::resultt::D_UNSATISFIABLE:
              break;
            case decision_proceduret::resultt::D_ERROR:
              error = true;
              break;
            }
          }
        }
      }
    }
  }

  return error ? propagate_resultt::ERROR
               : conflict ? propagate_resultt::CONFLICT
                          : propagated ? propagate_resultt::PROPAGATED
                                       : propagate_resultt::SATURATED;
}

statet &find_state(
  std::vector<statet> &states,
  const std::unordered_map<symbol_exprt, std::size_t, irep_hash> &state_map,
  const symbol_exprt &state_symbol)
{
  auto entry = state_map.find(state_symbol);

  if(entry == state_map.end())
    PRECONDITION(false);

  return states[entry->second];
}

void solver(
  std::vector<statet> &states,
  const namespacet &ns,
  propertyt &property)
{
  std::cout << "Doing " << format(property.condition) << '\n';

  std::unordered_map<symbol_exprt, std::size_t, irep_hash> state_map;

  for(std::size_t i = 0; i < states.size(); i++)
    state_map[states[i].symbol] = i;

  // we start with I = P
  for(auto &state : states)
    state.invariants.clear();

  find_state(states, state_map, property.state_symbol)
    .add_invariant(property.condition);

  bool propagated = false;

  auto propagator = [&states,
                     &propagated](const symbol_exprt &symbol, exprt invariant) {
    for(auto &s : states)
    {
      if(s.symbol == symbol)
      {
        std::cout << "S: " << format(symbol) << " <- " << format(invariant)
                  << '\n';
        if(s.add_invariant(std::move(invariant)))
          propagated = true;
      }
    }
  };

  while(true)
  {
    dump(states, true, true);
    std::cout << '\n';
    propagated = false;

    switch(propagate(states, ns, propagator))
    {
    case propagate_resultt::CONFLICT:
      property.status = propertyt::REFUTED;
      return;

    case propagate_resultt::ERROR:
      property.status = propertyt::ERROR;
      return;

    case propagate_resultt::SATURATED:
    case propagate_resultt::PROPAGATED:
      break;
    }

    if(!propagated)
      break;
  }

  property.status = propertyt::PASS;
}

void report_properties(const std::vector<propertyt> &properties)
{
  irep_idt current_file, current_function;

  for(auto &property : properties)
  {
    const auto &l = property.source_location;

    if(l.get_function() != current_function)
    {
      if(!current_function.empty())
        consolet::out() << '\n';
      current_function = l.get_function();
      if(!current_function.empty())
      {
        current_file = l.get_file();
        if(!current_file.empty())
          consolet::out() << current_file << ' ';
        if(!l.get_function().empty())
          consolet::out() << "function " << l.get_function();
        consolet::out() << '\n';
      }
    }

    auto property_id = l.get_property_id();
    consolet::out() << consolet::faint << '[';
    if(property_id.empty())
      consolet::out() << '?';
    else
      consolet::out() << property_id;
    consolet::out() << ']' << consolet::reset;

    if(l.get_file() != current_file)
      consolet::out() << ' ' << l.get_file();

    if(!l.get_line().empty())
      consolet::out() << " line " << l.get_line();

    auto comment = l.get_comment();
    if(!comment.empty())
      consolet::out() << ' ' << comment;

    consolet::out() << ": ";

    switch(property.status)
    {
    case propertyt::PASS:
      consolet::out() << consolet::green << "SUCCESS" << consolet::reset;
      break;

    case propertyt::REFUTED:
      consolet::out() << consolet::red << "REFUTED" << consolet::reset;
      break;

    case propertyt::ERROR:
      consolet::out() << consolet::red << consolet::bold << "ERROR"
                      << consolet::reset;
      break;

    case propertyt::UNKNOWN:
      consolet::out() << consolet::yellow << "UNKNOWN" << consolet::reset;
      break;
    }

    consolet::out() << '\n';
  }
}

solver_resultt
solver(const std::vector<exprt> &constraints, const namespacet &ns)
{
  auto states = find_states(constraints);

  find_implications(constraints, states);

  auto properties = find_properties(constraints);

  // solve each property separately
  for(auto &property : properties)
    solver(states, ns, property);

  // reporting
  report_properties(properties);

  // overall outcome
  auto result = solver_resultt::ALL_PASS;

  for(auto &property : properties)
    if(property.status == propertyt::ERROR)
      result = solver_resultt::ERROR;
    else if(property.status == propertyt::REFUTED)
      result = solver_resultt::SOME_FAIL;

  return result;
}
