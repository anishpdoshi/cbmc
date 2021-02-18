/*******************************************************************\

 Module: analyses variable-sensitivity

 Author: Jez Higgins, jez@jezuk.co.uk

\*******************************************************************/

#include <analyses/variable-sensitivity/abstract_value_object.h>
#include <util/make_unique.h>

class empty_index_ranget : public index_range_implementationt
{
public:
  const exprt &current() const override
  {
    return nil;
  }
  bool advance_to_next() override
  {
    return false;
  }
  index_range_implementation_ptrt reset() const override
  {
    return make_empty_index_range();
  }

private:
  exprt nil = nil_exprt();
};

class indeterminate_index_ranget : public single_value_index_ranget
{
public:
  indeterminate_index_ranget() : single_value_index_ranget(nil_exprt())
  {
  }

  index_range_implementation_ptrt reset() const override
  {
    return make_indeterminate_index_range();
  }
};

single_value_index_ranget::single_value_index_ranget(const exprt &val)
  : value(val), available(true)
{
}

const exprt &single_value_index_ranget::current() const
{
  return value;
}

bool single_value_index_ranget::advance_to_next()
{
  bool a = available;
  available = false;
  return a;
}

index_range_implementation_ptrt make_empty_index_range()
{
  return util_make_unique<empty_index_ranget>();
}

index_range_implementation_ptrt make_indeterminate_index_range()
{
  return util_make_unique<indeterminate_index_ranget>();
}

class single_value_value_ranget : public value_range_implementationt
{
public:
  explicit single_value_value_ranget(const abstract_object_pointert &val)
    : value(val), available(true)
  {
  }

  const abstract_object_pointert &current() const override
  {
    return value;
  }
  bool advance_to_next() override
  {
    bool a = available;
    available = false;
    return a;
  }
  value_range_implementation_ptrt reset() const override
  {
    return make_single_value_range(value);
  }

private:
  const abstract_object_pointert value;
  bool available;
};

value_range_implementation_ptrt
make_single_value_range(const abstract_object_pointert &value)
{
  return util_make_unique<single_value_value_ranget>(value);
}
