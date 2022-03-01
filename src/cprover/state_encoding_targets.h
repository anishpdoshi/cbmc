/*******************************************************************\

Module: State Encoding Targets

Author:

\*******************************************************************/

#ifndef CPROVER_CPROVER_STATE_ENCODING_TARGETS_H
#define CPROVER_CPROVER_STATE_ENCODING_TARGETS_H

#include <solvers/smt2/smt2_conv.h>

#include <iosfwd>

class encoding_targett
{
public:
  virtual void annotation(const std::string &)
  {
  }
  virtual void source_location(source_locationt)
  {
  }
  virtual void set_to_true(exprt) = 0;
  virtual ~encoding_targett() = default;
};

static inline void operator<<(encoding_targett &target, exprt constraint)
{
  target.set_to_true(std::move(constraint));
}

class container_encoding_targett : public encoding_targett
{
public:
  container_encoding_targett() = default;

  using constraintst = std::vector<exprt>;
  constraintst constraints;

  void source_location(source_locationt source_location) override
  {
    last_source_location = std::move(source_location);
  }

  void set_to_true(exprt expr) override
  {
    if(last_source_location.is_not_nil())
      expr.add_source_location() = last_source_location;

    constraints.emplace_back(std::move(expr));
  }

protected:
  source_locationt last_source_location = source_locationt::nil();
};

static inline void
operator<<(encoding_targett &target, const container_encoding_targett &src)
{
  for(const auto &constraint : src.constraints)
    target << constraint;
}

class smt2_encoding_targett : public encoding_targett
{
public:
  smt2_encoding_targett(const namespacet &ns, std::ostream &_out)
    : out(_out),
      smt2_conv(ns, "", "cprover", "", smt2_convt::solvert::GENERIC, _out)
  {
    smt2_conv.use_array_of_bool = true;
    smt2_conv.use_as_const = true;
  }

  ~smt2_encoding_targett()
  {
    // finish the conversion to SMT-LIB2
    smt2_conv();
  }

  void set_to_true(exprt expr) override
  {
    smt2_conv.set_to_true(std::move(expr));
  }

  void annotation(const std::string &text) override
  {
    out << ';' << ' ' << text << '\n';
  }

protected:
  std::ostream &out;
  smt2_convt smt2_conv;
};

class ascii_encoding_targett : public encoding_targett
{
public:
  explicit ascii_encoding_targett(std::ostream &_out) : out(_out)
  {
  }

  void set_to_true(exprt expr) override;

  void annotation(const std::string &text) override
  {
    out << '\n' << text << '\n';
  }

protected:
  std::ostream &out;
  std::size_t counter = 0;
};

#endif // CPROVER_CPROVER_STATE_ENCODING_TARGETS_H
