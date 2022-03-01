/*******************************************************************\

Module: State Encoding

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#ifndef CPROVER_CPROVER_STATE_H
#define CPROVER_CPROVER_STATE_H

#include <util/mathematical_expr.h>

class state_typet : public typet
{
public:
  state_typet() : typet(ID_state)
  {
  }
};

static inline mathematical_function_typet state_predicate_type()
{
  return mathematical_function_typet({state_typet()}, bool_typet());
}

static inline symbol_exprt state_expr()
{
  return symbol_exprt(u8"\u03c2", state_typet());
}

class evaluate_exprt : public binary_exprt
{
public:
  evaluate_exprt(exprt state, exprt address, typet type)
    : binary_exprt(
        std::move(state),
        ID_evaluate,
        std::move(address),
        std::move(type))
  {
    PRECONDITION(this->state().type().id() == ID_state);
    PRECONDITION(this->address().type().id() == ID_pointer);
  }

  const exprt &state() const
  {
    return op0();
  }

  const exprt &address() const
  {
    return op1();
  }
};

/// \brief Cast an exprt to a \ref evaluate_exprt
///
/// \a expr must be known to be \ref evaluate_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref evaluate_exprt
inline const evaluate_exprt &to_evaluate_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_evaluate);
  const evaluate_exprt &ret = static_cast<const evaluate_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \copydoc to_evaluate_expr(const exprt &)
inline evaluate_exprt &to_evaluate_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_evaluate);
  evaluate_exprt &ret = static_cast<evaluate_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

class update_state_exprt : public ternary_exprt
{
public:
  update_state_exprt(exprt state, exprt address, exprt new_value)
    : ternary_exprt(
        ID_update_state,
        std::move(state),
        std::move(address),
        std::move(new_value),
        state_typet())
  {
    // PRECONDITION(this->state().id() == ID_state);
    PRECONDITION(this->address().type().id() == ID_pointer);
  }

  const exprt &state() const
  {
    return op0();
  }

  const exprt &address() const
  {
    return op1();
  }

  const exprt &new_value() const
  {
    return op2();
  }
};

/// \brief Cast an exprt to a \ref update_state_exprt
///
/// \a expr must be known to be \ref update_state_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref update_state_exprt
inline const update_state_exprt &to_update_state_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_update_state);
  const update_state_exprt &ret = static_cast<const update_state_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \copydoc to_update_state_expr(const exprt &)
inline update_state_exprt &to_update_state_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_update_state);
  update_state_exprt &ret = static_cast<update_state_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

#endif // CPROVER_CPROVER_STATE_H