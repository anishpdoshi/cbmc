/*******************************************************************\

Module: State Encoding

Author:

\*******************************************************************/

#include "state_encoding.h"

#include <util/c_types.h>
#include <util/format_expr.h>
#include <util/mathematical_expr.h>
#include <util/pointer_expr.h>
#include <util/prefix.h>
#include <util/std_code.h>

#include <goto-programs/goto_model.h>

#include "equality_propagation.h"
#include "solver.h"
#include "state.h"
#include "state_encoding_targets.h"

#include <iostream>

class state_encodingt
{
public:
  void operator()(
    const goto_functionst &,
    const goto_functiont &,
    encoding_targett &);

protected:
  using loct = goto_programt::const_targett;

  symbol_exprt out_state_expr(loct) const;
  symbol_exprt state_expr_with_suffix(loct, const std::string &suffix) const;
  symbol_exprt out_state_expr(loct, bool taken) const;
  symbol_exprt in_state_expr(loct) const;
  std::vector<irep_idt> incoming_symbols(loct loc) const;
  exprt evaluate_expr(loct, const exprt &, const exprt &) const;
  exprt evaluate_expr_rec(
    loct,
    const exprt &,
    const exprt &,
    const std::unordered_set<symbol_exprt, irep_hash> &) const;
  exprt evaluate_expr(loct, const exprt &) const;
  exprt address_rec(loct, const exprt &, exprt) const;
  static exprt state_lambda_expr(exprt);
  exprt forall_states_expr(loct, exprt) const;
  exprt forall_states_expr(loct, exprt, exprt) const;
  void setup_incoming(const goto_functiont &);
  exprt assignment_constraint(loct, exprt lhs, exprt rhs) const;

  loct first_loc;
  using incomingt = std::map<loct, std::vector<loct>>;
  incomingt incoming;
};

symbol_exprt state_encodingt::out_state_expr(loct loc) const
{
  return state_expr_with_suffix(loc, "");
}

symbol_exprt state_encodingt::state_expr_with_suffix(
  loct loc,
  const std::string &suffix) const
{
  irep_idt identifier =
    std::string("S") + std::to_string(loc->location_number) + suffix;
  return symbol_exprt(identifier, state_predicate_type());
}

symbol_exprt state_encodingt::out_state_expr(loct loc, bool taken) const
{
  return state_expr_with_suffix(loc, taken ? "T" : "");
}

std::vector<irep_idt> state_encodingt::incoming_symbols(loct loc) const
{
  auto incoming_it = incoming.find(loc);

  DATA_INVARIANT(incoming_it != incoming.end(), "incoming is complete");

  std::vector<irep_idt> symbols;
  symbols.reserve(incoming_it->second.size());

  for(auto &loc_in : incoming_it->second)
  {
    std::string suffix;

    // conditional jump from loc_in to loc?
    if(
      loc_in->is_goto() && !loc_in->condition().is_true() &&
      loc != std::next(loc_in))
    {
      suffix = "T";
    }

    symbols.push_back("S" + std::to_string(loc_in->location_number) + suffix);
  }

  return symbols;
}

symbol_exprt state_encodingt::in_state_expr(loct loc) const
{
  if(loc == first_loc)
    return symbol_exprt("SInitial", state_predicate_type());

  auto incoming_symbols = this->incoming_symbols(loc);

  if(incoming_symbols.size() == 1)
    return symbol_exprt(incoming_symbols.front(), state_predicate_type());

  return symbol_exprt(
    "S" + std::to_string(loc->location_number) + "in", state_predicate_type());
}

exprt state_encodingt::evaluate_expr(
  loct loc,
  const exprt &state,
  const exprt &what) const
{
  return evaluate_expr_rec(loc, state, what, {});
}

exprt state_encodingt::evaluate_expr_rec(
  loct loc,
  const exprt &state,
  const exprt &what,
  const std::unordered_set<symbol_exprt, irep_hash> &bound_symbols) const
{
  PRECONDITION(state.type().id() == ID_state);

  if(what.id() == ID_symbol)
  {
    const auto &symbol_expr = to_symbol_expr(what);

    if(bound_symbols.find(symbol_expr) == bound_symbols.end())
    {
      return evaluate_exprt(state, address_rec(loc, state, what), what.type());
    }
    else
      return what; // leave as is
  }
  else if(
    what.id() == ID_dereference || what.id() == ID_member ||
    what.id() == ID_index)
  {
    return evaluate_exprt(state, address_rec(loc, state, what), what.type());
  }
  else if(what.id() == ID_side_effect)
  {
    auto &side_effect = to_side_effect_expr(what);
    auto statement = side_effect.get_statement();
    if(statement == ID_nondet)
    {
      irep_idt identifier = "nondet" + std::to_string(loc->location_number);
      return symbol_exprt(identifier, side_effect.type());
    }
    else
      return what;
  }
  else if(what.id() == ID_forall || what.id() == ID_exists)
  {
    auto new_quantifier_expr = to_quantifier_expr(what); // copy
    auto new_bound_symbols = bound_symbols;              // copy

    for(const auto &v : new_quantifier_expr.variables())
      new_bound_symbols.insert(v);

    new_quantifier_expr.where() = evaluate_expr_rec(
      loc, state, new_quantifier_expr.where(), new_bound_symbols);

    return std::move(new_quantifier_expr);
  }
  else if(what.id() == ID_address_of)
  {
    const auto &object = to_address_of_expr(what).object();
    return address_rec(loc, state, object);
  }
  else
  {
    exprt tmp = what;
    for(auto &op : tmp.operands())
      op = evaluate_expr_rec(loc, state, op, bound_symbols);
    return tmp;
  }
}

exprt state_encodingt::evaluate_expr(loct loc, const exprt &what) const
{
  return evaluate_expr(loc, in_state_expr(loc), what);
}

exprt state_encodingt::state_lambda_expr(exprt what)
{
  return lambda_exprt({state_expr()}, std::move(what));
}

exprt state_encodingt::forall_states_expr(loct loc, exprt what) const
{
  return forall_exprt(
    {state_expr()},
    implies_exprt(
      function_application_exprt(in_state_expr(loc), {state_expr()}),
      std::move(what)));
}

exprt state_encodingt::forall_states_expr(loct loc, exprt condition, exprt what)
  const
{
  return forall_exprt(
    {state_expr()},
    implies_exprt(
      and_exprt(
        function_application_exprt(in_state_expr(loc), {state_expr()}),
        std::move(condition)),
      std::move(what)));
}

exprt state_encodingt::address_rec(loct loc, const exprt &state, exprt expr)
  const
{
  if(expr.id() == ID_symbol)
  {
    if(expr.type().id() == ID_array)
    {
      const auto &element_type = to_array_type(expr.type()).element_type();
      return object_address_exprt(
        to_symbol_expr(expr), pointer_type(element_type));
    }
    else
      return object_address_exprt(to_symbol_expr(expr));
  }
  else if(expr.id() == ID_member)
  {
    auto compound = to_member_expr(expr).struct_op();
    auto compound_address = address_rec(loc, state, std::move(compound));
    auto component_name = to_member_expr(expr).get_component_name();

    if(expr.type().id() == ID_array)
    {
      const auto &element_type = to_array_type(expr.type()).element_type();
      return field_address_exprt(
        std::move(compound_address),
        component_name,
        pointer_type(element_type));
    }
    else
    {
      return field_address_exprt(
        std::move(compound_address), component_name, pointer_type(expr.type()));
    }
  }
  else if(expr.id() == ID_index)
  {
    auto array = to_index_expr(expr).array();
    auto index_evaluated =
      evaluate_expr(loc, state, to_index_expr(expr).index());
    auto array_address = address_rec(loc, state, std::move(array));
    return element_address_exprt(
      std::move(array_address), std::move(index_evaluated));
  }
  else if(expr.id() == ID_dereference)
    return evaluate_expr(loc, state, to_dereference_expr(expr).pointer());
  else if(expr.id() == ID_string_constant)
  {
    // TBD.
    throw incorrect_goto_program_exceptiont(
      "can't do string literals", expr.source_location());
  }
  else if(expr.id() == ID_array)
  {
    // TBD.
    throw incorrect_goto_program_exceptiont(
      "can't do array literals", expr.source_location());
  }
  else if(expr.id() == ID_union)
  {
    // TBD.
    throw incorrect_goto_program_exceptiont(
      "can't do union literals", expr.source_location());
  }
  else
    return nil_exprt();
}

exprt state_encodingt::assignment_constraint(loct loc, exprt lhs, exprt rhs)
  const
{
  auto s = state_expr();
  auto address = address_rec(loc, s, lhs);
  exprt new_value = evaluate_expr(loc, s, rhs);
  auto new_state = update_state_exprt(s, address, new_value);
  return forall_states_expr(
    loc, function_application_exprt(out_state_expr(loc), {new_state}));
}

void state_encodingt::setup_incoming(const goto_functiont &goto_function)
{
  forall_goto_program_instructions(it, goto_function.body)
    incoming[it];

  forall_goto_program_instructions(it, goto_function.body)
  {
    if(it->is_goto())
      incoming[it->get_target()].push_back(it);
  }

  forall_goto_program_instructions(it, goto_function.body)
  {
    auto next = std::next(it);
    if(it->is_goto() && it->condition().is_true())
    {
    }
    else if(next != goto_function.body.instructions.end())
    {
      incoming[next].push_back(it);
    }
  }
}

static exprt simplifying_not(exprt src)
{
  if(src.id() == ID_not)
    return to_not_expr(src).op();
  else
    return not_exprt(src);
}

void state_encodingt::operator()(
  const goto_functionst &goto_functions,
  const goto_functiont &goto_function,
  encoding_targett &dest)
{
  if(goto_function.body.instructions.empty())
    return;

  first_loc = goto_function.body.instructions.begin();

  setup_incoming(goto_function);

  // initial state
  dest << forall_exprt(
    {state_expr()},
    implies_exprt(
      true_exprt(),
      function_application_exprt(in_state_expr(first_loc), {state_expr()})));

  // constraints for each instruction
  forall_goto_program_instructions(loc, goto_function.body)
  {
    // pass on the source code location
    dest.source_location(loc->source_location());

    // constraints on the incoming state
    {
      auto incoming_symbols = this->incoming_symbols(loc);

      if(incoming_symbols.size() >= 2)
      {
        auto s = state_expr();
        for(auto incoming_symbol : incoming_symbols)
        {
          auto incoming_state =
            symbol_exprt(incoming_symbol, state_predicate_type());

          dest << forall_exprt(
            {s},
            implies_exprt(
              function_application_exprt(std::move(incoming_state), {s}),
              function_application_exprt(in_state_expr(loc), {s})));
        }
      }
    }

    if(loc->is_assign())
    {
      auto lhs = loc->assign_lhs();
      auto rhs = loc->assign_rhs();
      if(lhs.type().id() == ID_array)
      {
        // skip
        dest << equal_exprt(out_state_expr(loc), in_state_expr(loc));
      }
      else if(lhs.type().id() == ID_struct_tag)
      {
        // skip
        dest << equal_exprt(out_state_expr(loc), in_state_expr(loc));
      }
      else if(
        lhs.id() == ID_symbol &&
        has_prefix(
          id2string(to_symbol_expr(lhs).get_identifier()), CPROVER_PREFIX) &&
        to_symbol_expr(lhs).get_identifier() != CPROVER_PREFIX "rounding_mode")
      {
        // skip for now
        dest << equal_exprt(out_state_expr(loc), in_state_expr(loc));
      }
      else
        dest << assignment_constraint(loc, std::move(lhs), std::move(rhs));
    }
    else if(loc->is_assume())
    {
      // we produce ∅ when the assumption is false
      auto state = state_expr();
      auto condition_evaluated = evaluate_expr(loc, state, loc->condition());

      dest << forall_states_expr(
        loc,
        condition_evaluated,
        function_application_exprt(out_state_expr(loc), {state}));
    }
    else if(loc->is_goto())
    {
      // We produce ∅ when the 'other' branch is taken. Get the condition.
      const auto &condition = loc->condition();

      if(condition.is_true())
      {
        dest << equal_exprt(out_state_expr(loc), in_state_expr(loc));
      }
      else
      {
        auto state = state_expr();
        auto condition_evaluated = evaluate_expr(loc, state, condition);

        dest << forall_states_expr(
          loc,
          condition_evaluated,
          function_application_exprt(out_state_expr(loc, true), {state}));

        dest << forall_states_expr(
          loc,
          simplifying_not(condition_evaluated),
          function_application_exprt(out_state_expr(loc, false), {state}));
      }

      // annotated invariants -- these are stuck to the condition
      // of the (backwards) goto
      if(loc->is_backwards_goto())
      {
        const auto &invariant = static_cast<const exprt &>(
          loc->condition().find(ID_C_spec_loop_invariant));
        if(invariant.is_not_nil())
        {
#if 0
          // We stick these onto the loop head.
          auto loop_head = loc->get_target();
          auto invariant_source_location = invariant.source_location();
//          invariant_source_location 
          auto new_invariant = invariant;
          new_invariant.add_source_location() = std::move(invariant_source_location);            
          dest << forall_states_expr(
            loop_head, evaluate_expr(loop_head, state_expr(), new_invariant));
#endif
        }
      }
    }
    else if(loc->is_assert())
    {
      // all assertions need to hold
      dest << forall_states_expr(
        loc, evaluate_expr(loc, state_expr(), loc->condition()));

      dest << equal_exprt(out_state_expr(loc), in_state_expr(loc));
    }
    else if(
      loc->is_skip() || loc->is_assert() || loc->is_location() ||
      loc->is_end_function() || loc->is_other())
    {
      dest << equal_exprt(out_state_expr(loc), in_state_expr(loc));
    }
    else if(loc->is_decl() || loc->is_dead())
    {
      // may wish to havoc the symbol
      dest << equal_exprt(out_state_expr(loc), in_state_expr(loc));
    }
    else if(loc->is_function_call())
    {
      // Function pointer?
      const auto &function = loc->call_function();
      if(function.id() == ID_dereference)
      {
        // TBD.
        throw incorrect_goto_program_exceptiont(
          "can't do function pointers", loc->source_location());
      }
      else if(function.id() == ID_symbol)
      {
        // Do we have a function body?
        auto identifier = to_symbol_expr(function).get_identifier();
        auto f = goto_functions.function_map.find(identifier);
        if(f == goto_functions.function_map.end())
          DATA_INVARIANT(false, "failed find function in function_map");
        if(f->second.body_available())
        {
          // Evaluate the arguments of the call in the 'in state'
          multi_ary_exprt arguments_evaluated(ID_tuple, {}, typet(ID_tuple));
          arguments_evaluated.reserve_operands(loc->call_arguments().size());

          const auto in_state = in_state_expr(loc);

          for(auto &argument : loc->call_arguments())
            arguments_evaluated.add_to_operands(
              evaluate_expr(loc, in_state, argument));

          auto function_entry_state = state_expr_with_suffix(loc, "Entry");

          dest << forall_states_expr(
            loc,
            function_application_exprt(function_entry_state, {state_expr()}));

          // Function return state (suffix PostReturn).
          // This is the state after exiting the function but prior to
          // assigning the LHS of the function call.
          auto return_state = state_expr_with_suffix(loc, "PostReturn");

          /*
          constraints.push_back(
            multi_ary_exprt(
              ID_goto_contract,
              {loc->call_function(), in_state, return_state, arguments_evaluated},
              bool_typet()));
          */

          // assign the return value, if any
          if(loc->call_lhs().is_not_nil())
          {
            exprt equality_rhs = return_state;

            /*
            auto &return_type = loc->call_lhs().type();
            auto rhs_evaluated =
              evaluate_expr(
                loc,
                return_state,
                symbol_exprt("return_value", return_type));

            multi_ary_exprt designator(ID_designator, { loc->call_lhs() }, typet());

            auto lhs = out_state_expr(source);

            auto rhs = update_exprt(
              return_state,
              designator,
              rhs_evaluated);

            // 'out state' equality
            constraints.push_back(equal_exprt(lhs, rhs));
    */
          }
          else
          {
            // 'out state' equality
            dest << equal_exprt(out_state_expr(loc), return_state);
          }
        }
        else
        {
          // no function body -- do LHS assignment nondeterministically, if any
          if(loc->call_lhs().is_not_nil())
          {
            auto rhs = side_effect_expr_nondett(
              loc->call_lhs().type(), loc->source_location());
            dest << assignment_constraint(loc, loc->call_lhs(), std::move(rhs));
          }
          else
          {
            // This is a SKIP.
            dest << equal_exprt(out_state_expr(loc), in_state_expr(loc));
          }
        }
      }
      else
      {
        DATA_INVARIANT(
          false, "got function that's neither a symbol nor a function pointer");
      }
    }
    else if(loc->is_set_return_value())
    {
      // treat these as assignments to a special symbol named 'return_value'
      auto rhs = loc->return_value();
      auto lhs = symbol_exprt("return_value", rhs.type());
      dest << assignment_constraint(loc, std::move(lhs), std::move(rhs));
    }
  }
}

void state_encoding(
  const goto_modelt &goto_model,
  bool program_is_inlined,
  encoding_targett &dest)
{
  if(program_is_inlined)
  {
    auto f_entry = goto_model.goto_functions.function_map.find(
      goto_functionst::entry_point());

    if(f_entry == goto_model.goto_functions.function_map.end())
    {
      std::cerr << "The program has no entry point\n";
      return;
    }

    state_encodingt{}(goto_model.goto_functions, f_entry->second, dest);
  }
  else
  {
    // output alphabetically
    const auto sorted = goto_model.goto_functions.sorted();

    for(const auto &f : sorted)
    {
      if(f->second.body_available())
      {
        dest.annotation("function " + id2string(f->first));
        state_encodingt{}(goto_model.goto_functions, f->second, dest);
      }
    }
  }
}

static void format_hooks()
{
  add_format_hook(
    ID_object_address,
    [](std::ostream &os, const exprt &expr) -> std::ostream & {
      const auto &object_address_expr = to_object_address_expr(expr);
      os << u8"\u275d" << object_address_expr.object_identifier() << u8"\u275e";
      return os;
    });

  add_format_hook(
    ID_field_address,
    [](std::ostream &os, const exprt &expr) -> std::ostream & {
      const auto &field_address_expr = to_field_address_expr(expr);
      os << format(field_address_expr.base()) << u8".\u275d"
         << field_address_expr.component_name() << u8"\u275e";
      return os;
    });

  add_format_hook(
    ID_evaluate, [](std::ostream &os, const exprt &expr) -> std::ostream & {
      const auto &evaluate_expr = to_evaluate_expr(expr);
      if(evaluate_expr.op0().id() == ID_symbol)
        os << format(evaluate_expr.op0());
      else
        os << '(' << format(evaluate_expr.op0()) << ')';
      os << '(' << format(evaluate_expr.op1()) << ')';
      return os;
    });

  add_format_hook(
    ID_update_state, [](std::ostream &os, const exprt &expr) -> std::ostream & {
      const auto &update_state_expr = to_update_state_expr(expr);
      os << format(update_state_expr.state()) << '['
         << format(update_state_expr.address())
         << ":=" << format(update_state_expr.new_value()) << ']';
      return os;
    });
}

void state_encoding(
  const goto_modelt &goto_model,
  state_encoding_formatt state_encoding_format,
  bool program_is_inlined,
  std::ostream &out)
{
  switch(state_encoding_format)
  {
  case state_encoding_formatt::ASCII:
  {
    format_hooks();
    ascii_encoding_targett dest(out);
    state_encoding(goto_model, program_is_inlined, dest);
  }
  break;

  case state_encoding_formatt::SMT2:
  {
    const namespacet ns(goto_model.symbol_table);
    smt2_encoding_targett dest(ns, out);
    state_encoding(goto_model, program_is_inlined, dest);
  }
  break;
  }
}

solver_resultt
state_encoding_solver(const goto_modelt &goto_model, bool program_is_inlined)
{
  const namespacet ns(goto_model.symbol_table);

  format_hooks();

  container_encoding_targett container;
  state_encoding(goto_model, program_is_inlined, container);

  equality_propagation(container.constraints);

  ascii_encoding_targett dest(std::cout);
  dest << container;

  return solver(container.constraints, ns);
}
