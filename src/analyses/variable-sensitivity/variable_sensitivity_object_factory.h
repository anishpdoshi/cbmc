/*******************************************************************\

 Module: analyses variable-sensitivity

 Author: Owen Jones owen.jones@diffblue.com

\*******************************************************************/

/// \file
/// Tracks the user-supplied configuration for VSD and build the
/// correct type of abstract object when needed.  Note this is a factory
/// within the domain and so is lower-level than the abstract domain
/// factory that is part of the ai_baset interface.

#ifndef CPROVER_ANALYSES_VARIABLE_SENSITIVITY_VARIABLE_SENSITIVITY_OBJECT_FACTORY_H
#define CPROVER_ANALYSES_VARIABLE_SENSITIVITY_VARIABLE_SENSITIVITY_OBJECT_FACTORY_H

#include <analyses/variable-sensitivity/array_abstract_object.h>
#include <analyses/variable-sensitivity/constant_abstract_value.h>
#include <analyses/variable-sensitivity/constant_array_abstract_object.h>
#include <analyses/variable-sensitivity/constant_pointer_abstract_object.h>
#include <analyses/variable-sensitivity/context_abstract_object.h>
#include <analyses/variable-sensitivity/data_dependency_context.h>
#include <analyses/variable-sensitivity/full_struct_abstract_object.h>
#include <analyses/variable-sensitivity/interval_abstract_value.h>
#include <analyses/variable-sensitivity/pointer_abstract_object.h>
#include <analyses/variable-sensitivity/struct_abstract_object.h>
#include <analyses/variable-sensitivity/union_abstract_object.h>
#include <analyses/variable-sensitivity/value_set_abstract_object.h>
#include <analyses/variable-sensitivity/write_location_context.h>
#include <util/namespace.h>
#include <util/options.h>

enum ABSTRACT_OBJECT_TYPET
{
  TWO_VALUE,
  CONSTANT,
  INTERVAL,
  ARRAY_SENSITIVE,
  ARRAY_INSENSITIVE,
  POINTER_SENSITIVE,
  POINTER_INSENSITIVE,
  STRUCT_SENSITIVE,
  STRUCT_INSENSITIVE,
  // TODO: plug in UNION_SENSITIVE HERE
  UNION_INSENSITIVE,
  VALUE_SET
};

struct vsd_configt
{
  ABSTRACT_OBJECT_TYPET value_abstract_type;
  ABSTRACT_OBJECT_TYPET pointer_abstract_type;
  ABSTRACT_OBJECT_TYPET struct_abstract_type;
  ABSTRACT_OBJECT_TYPET array_abstract_type;

  struct
  {
    bool data_dependency_context;
    bool last_write_context;
  } context_tracking;

  struct
  {
    bool new_value_set;
  } advanced_sensitivities;

  static vsd_configt from_options(const optionst &options)
  {
    vsd_configt config{};

    if(
      options.get_bool_option("value-set") &&
      options.get_bool_option("data-dependencies"))
    {
      throw invalid_command_line_argument_exceptiont{
        "Value set is not currently supported with data dependency analysis",
        "--value-set --data-dependencies",
        "--data-dependencies"};
    }

    config.value_abstract_type = option_to_abstract_type(
      options,
      "values",
      value_option_mappings,
      CONSTANT
    );

    config.pointer_abstract_type = option_to_abstract_type(
      options,
      "pointers",
      pointer_option_mappings,
      POINTER_INSENSITIVE
    );

    config.struct_abstract_type = option_to_abstract_type(
      options,
      "structs",
      struct_option_mappings,
      STRUCT_INSENSITIVE
    );

    config.array_abstract_type = option_to_abstract_type(
      options,
      "arrays",
      array_option_mappings,
      ARRAY_INSENSITIVE
    );

    // This should always be on (for efficeny with 3-way merge)
    // Does not work with value set
    config.context_tracking.last_write_context =
      (config.value_abstract_type != VALUE_SET) &&
      (config.pointer_abstract_type != VALUE_SET);
    config.context_tracking.data_dependency_context =
      options.get_bool_option("data-dependencies");
    config.advanced_sensitivities.new_value_set =
      options.get_bool_option("new-value-set");

    return config;
  }

  static vsd_configt constant_domain()
  {
    vsd_configt config{};
    config.context_tracking.last_write_context = true;
    config.value_abstract_type = CONSTANT;
    config.pointer_abstract_type = POINTER_SENSITIVE;
    config.struct_abstract_type = STRUCT_SENSITIVE;
    config.array_abstract_type = ARRAY_SENSITIVE;
    return config;
  }

  static vsd_configt value_set()
  {
    vsd_configt config{};
    config.value_abstract_type = VALUE_SET;
    config.pointer_abstract_type = VALUE_SET;
    config.struct_abstract_type = STRUCT_SENSITIVE;
    config.array_abstract_type = ARRAY_SENSITIVE;
    return config;
  }

  static vsd_configt intervals()
  {
    vsd_configt config{};
    config.context_tracking.last_write_context = true;
    config.value_abstract_type = INTERVAL;
    config.pointer_abstract_type = POINTER_SENSITIVE;
    config.struct_abstract_type = STRUCT_SENSITIVE;
    config.array_abstract_type = ARRAY_SENSITIVE;
    return config;
  }

private:
  using option_mappingt = std::map<std::string, ABSTRACT_OBJECT_TYPET>;

  static ABSTRACT_OBJECT_TYPET option_to_abstract_type(
    const optionst& options,
    const std::string& option_name,
    const option_mappingt& mapping,
    ABSTRACT_OBJECT_TYPET default_type
  );

  static invalid_command_line_argument_exceptiont invalid_argument(
    const std::string& option_name,
    const std::string& bad_argument,
    const option_mappingt& mapping
  );

  static const option_mappingt value_option_mappings;
  static const option_mappingt pointer_option_mappings;
  static const option_mappingt struct_option_mappings;
  static const option_mappingt array_option_mappings;
};

class variable_sensitivity_object_factoryt;
using variable_sensitivity_object_factory_ptrt =
  std::shared_ptr<variable_sensitivity_object_factoryt>;

class variable_sensitivity_object_factoryt
{
public:
  static variable_sensitivity_object_factory_ptrt
  configured_with(const vsd_configt &options)
  {
    return std::make_shared<variable_sensitivity_object_factoryt>(options);
  }

  explicit variable_sensitivity_object_factoryt(const vsd_configt &options)
    : configuration(options), initialized(true)
  {
  }

  /// Get the appropriate abstract object for the variable under
  /// consideration.
  ///
  /// \param type: the type of the variable
  /// \param top: whether the abstract object should be top in the
  ///             two-value domain
  /// \param bottom: whether the abstract object should be bottom in the
  ///                two-value domain
  /// \param e: if top and bottom are false this expression is used as the
  ///           starting pointer for the abstract object
  /// \param environment: the current abstract environment
  /// \param ns: namespace, used when following the input type
  ///
  /// \return An abstract object of the appropriate type.
  abstract_object_pointert get_abstract_object(
    const typet type,
    bool top,
    bool bottom,
    const exprt &e,
    const abstract_environmentt &environment,
    const namespacet &ns);

private:
  variable_sensitivity_object_factoryt() : initialized(false)
  {
  }

  /// Decide which abstract object type to use for the variable in question.
  ///
  /// \param type: the type of the variable the abstract object is
  ///              meant to represent
  ///
  /// \return An enum indicating the abstract object type to use.
  ABSTRACT_OBJECT_TYPET get_abstract_object_type(const typet type);
  template <class abstract_object_class>
  abstract_object_pointert initialize_abstract_object(
    const typet type,
    bool top,
    bool bottom,
    const exprt &e,
    const abstract_environmentt &enviroment,
    const namespacet &ns);
  template <class abstract_object_class, class context_classt>
  abstract_object_pointert initialize_context_abstract_object(
    const typet type,
    bool top,
    bool bottom,
    const exprt &e,
    const abstract_environmentt &enviroment,
    const namespacet &ns);
  vsd_configt configuration;
  bool initialized;
};

/// Function: variable_sensitivity_object_factoryt::initialize_abstract_object
/// Initialize the abstract object class and return it.
///
/// \param type: the type of the variable
/// \param top: whether the abstract object should be top in the
///             two-value domain
/// \param bottom: whether the abstract object should be bottom in the
///                two-value domain
/// \param e: if top and bottom are false this expression is used as the
///           starting pointer for the abstract object
/// \param environment: the current abstract environment
/// \param ns: namespace, used when following the input type
///
/// \return An abstract object of the appropriate type.
///
template <class abstract_object_classt>
abstract_object_pointert
variable_sensitivity_object_factoryt::initialize_abstract_object(
  const typet type,
  bool top,
  bool bottom,
  const exprt &e,
  const abstract_environmentt &environment,
  const namespacet &ns)
{
  if(configuration.context_tracking.data_dependency_context)
    return initialize_context_abstract_object<
      abstract_object_classt,
      data_dependency_contextt>(type, top, bottom, e, environment, ns);
  if(configuration.context_tracking.last_write_context)
    return initialize_context_abstract_object<
      abstract_object_classt,
      write_location_contextt>(type, top, bottom, e, environment, ns);
  else
  {
    if(top || bottom)
    {
      return abstract_object_pointert(
        new abstract_object_classt(type, top, bottom));
    }
    else
    {
      PRECONDITION(type == ns.follow(e.type()));
      return abstract_object_pointert(
        new abstract_object_classt(e, environment, ns));
    }
  }
}

template <class abstract_object_classt, class context_classt>
abstract_object_pointert
variable_sensitivity_object_factoryt::initialize_context_abstract_object(
  const typet type,
  bool top,
  bool bottom,
  const exprt &e,
  const abstract_environmentt &environment,
  const namespacet &ns)
{
  if(top || bottom)
  {
    return abstract_object_pointert(new context_classt(
      abstract_object_pointert(new abstract_object_classt(type, top, bottom)),
      type,
      top,
      bottom));
  }
  else
  {
    PRECONDITION(type == ns.follow(e.type()));
    return abstract_object_pointert(new context_classt(
      abstract_object_pointert(new abstract_object_classt(e, environment, ns)),
      e,
      environment,
      ns));
  }
}

#endif // CPROVER_ANALYSES_VARIABLE_SENSITIVITY_VARIABLE_SENSITIVITY_OBJECT_FACTORY_H // NOLINT(*)
