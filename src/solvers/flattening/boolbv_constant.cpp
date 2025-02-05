/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/arith_tools.h>

#include "boolbv.h"

bvt boolbvt::convert_constant(const constant_exprt &expr)
{
  std::size_t width=boolbv_width(expr.type());

  if(width==0)
    return conversion_failed(expr);

  bvt bv;
  bv.resize(width);

  const typet &expr_type=expr.type();

  if(expr_type.id() == ID_string)
  {
    // we use the numbering for strings
    std::size_t number = string_numbering.number(expr.get_value());
    return bv_utils.build_constant(number, bv.size());
  }
  else if(expr_type.id()==ID_range)
  {
    mp_integer from=to_range_type(expr_type).get_from();
    mp_integer value=string2integer(id2string(expr.get_value()));
    mp_integer v=value-from;

    std::string binary=integer2binary(v, width);

    for(std::size_t i=0; i<width; i++)
    {
      bool bit=(binary[binary.size()-i-1]=='1');
      bv[i]=const_literal(bit);
    }

    return bv;
  }
  else if(
    expr_type.id() == ID_unsignedbv || expr_type.id() == ID_signedbv ||
    expr_type.id() == ID_bv || expr_type.id() == ID_fixedbv ||
    expr_type.id() == ID_floatbv || expr_type.id() == ID_c_enum ||
    expr_type.id() == ID_c_enum_tag || expr_type.id() == ID_c_bool ||
    expr_type.id() == ID_c_bit_field)
  {
    const auto &value = expr.get_value();

    for(std::size_t i=0; i<width; i++)
    {
      const bool bit = get_bvrep_bit(value, width, i);
      bv[i]=const_literal(bit);
    }

    return bv;
  }
  else if(expr_type.id()==ID_enumeration)
  {
    const irept::subt &elements=to_enumeration_type(expr_type).elements();
    const irep_idt &value=expr.get_value();

    for(std::size_t i=0; i<elements.size(); i++)
      if(elements[i].id()==value)
        return bv_utils.build_constant(i, width);
  }
  else if(expr_type.id()==ID_verilog_signedbv ||
          expr_type.id()==ID_verilog_unsignedbv)
  {
    const std::string &binary=id2string(expr.get_value());

    DATA_INVARIANT_WITH_DIAGNOSTICS(
      binary.size() * 2 == width,
      "wrong value length in constant",
      irep_pretty_diagnosticst{expr});

    for(std::size_t i=0; i<binary.size(); i++)
    {
      char bit=binary[binary.size()-i-1];

      switch(bit)
      {
      case '0':
        bv[i*2]=const_literal(false);
        bv[i*2+1]=const_literal(false);
        break;

      case '1':
        bv[i*2]=const_literal(true);
        bv[i*2+1]=const_literal(false);
        break;

      case 'x':
        bv[i*2]=const_literal(false);
        bv[i*2+1]=const_literal(true);
        break;

      case 'z':
      case '?':
        bv[i*2]=const_literal(true);
        bv[i*2+1]=const_literal(true);
        break;

      default:
        DATA_INVARIANT_WITH_DIAGNOSTICS(
          false,
          "unknown character in Verilog constant",
          irep_pretty_diagnosticst{expr});
      }
    }

    return bv;
  }

  return conversion_failed(expr);
}
