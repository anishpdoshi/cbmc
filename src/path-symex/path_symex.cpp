/*******************************************************************\

Module: Concrete Symbolic Transformer

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/simplify_expr.h>

#include "path_symex.h"

// #define DEBUG

class path_symext
{
public:
  explicit path_symext(
    const namespacet &_ns):
    ns(_ns)
  {
  }
  
  void operator()(
    path_symex_statet &state,
    std::list<path_symex_statet> &furter_states);

protected:
  const namespacet &ns;

  void do_goto(
    path_symex_statet &state,
    std::list<path_symex_statet> &further_states);

  void function_call(
    path_symex_statet &state,
    const code_function_callt &call)
  {
    function_call(state, call, call.function());
  }
    
  void function_call(
    path_symex_statet &state,
    const code_function_callt &function_call,
    const exprt &function);
    
  void return_from_function(
    path_symex_statet &state,
    const exprt &return_value);

  void symex_malloc(
    path_symex_statet &state,
    exprt::operandst &guard,
    const exprt &lhs,
    const side_effect_exprt &code,
    const std::string &suffix,
    const exprt &full_lhs);

  inline void assign(
    path_symex_statet &state,
    const exprt &lhs,
    const exprt &rhs)
  {
    exprt::operandst _guard; // start with empty guard
    assign_rec(state, _guard, lhs, rhs, std::string(), lhs);
  }

  inline void assign(
    path_symex_statet &state,
    const code_assignt &assignment)
  {
    assign(state, assignment.lhs(), assignment.rhs());
  }

  void assign_rec(
    path_symex_statet &state,
    exprt::operandst &guard,
    const exprt &lhs, // not instantiated, recursion here
    const exprt &rhs, // not instantiated
    const std::string &suffix,
    const exprt &full_lhs); // no recursion here

  static bool propagate(const exprt &src);
};

/*******************************************************************\

Function: path_symext::propagate

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

#include <iostream>

bool path_symext::propagate(const exprt &src)
{
  // propagate things that are 'simple enough'
  if(src.is_constant())
    return true;
  else if(src.id()==ID_member)
    return propagate(to_member_expr(src).struct_op());
  else if(src.id()==ID_index)
    return false;
  else if(src.id()==ID_typecast)
    return propagate(to_typecast_expr(src).op());
  else if(src.id()==ID_symbol)
    return true;
  else if(src.id()==ID_address_of)
    return true;
  else if(src.id()==ID_plus)
  {
    forall_operands(it, src)
      if(!propagate(*it)) return false;
    return true;
  }
  else
  {
    std::cout << "PROP: " << src.pretty() << std::endl;
    return false;
  }
}

/*******************************************************************\

Function: path_symext::symex_malloc

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

#if 0
inline static typet c_sizeof_type_rec(const exprt &expr)
{
  const irept &sizeof_type=expr.find(ID_C_c_sizeof_type);

  if(!sizeof_type.is_nil())
  {
    return static_cast<const typet &>(sizeof_type);
  }
  else if(expr.id()==ID_mult)
  {
    forall_operands(it, expr)
    {
      typet t=c_sizeof_type_rec(*it);
      if(t.is_not_nil()) return t;
    }
  }
  
  return nil_typet();
}
#endif

#if 0
void path_symext::symex_malloc(
  path_symex_statet &state,
  exprt::operandst &guard, // not instantiated
  const exprt &lhs,
  const side_effect_exprt &code,
  const std::string &suffix,
  const typet& lhs_suffix_type)
{
  if(code.operands().size()!=1)
    throw "malloc expected to have one operand";
    
  if(lhs.is_nil())
    return; // ignore

  // increment dynamic object counter
  unsigned dynamic_count=++state.var_map.dynamic_count;
  
  exprt size=code.op0();
  typet object_type=nil_typet();
  
  {
    exprt tmp_size=state.read(size); // to allow constant propagation
    
    // special treatment for sizeof(T)*x
    if(tmp_size.id()==ID_mult &&
       tmp_size.operands().size()==2 &&
       tmp_size.op0().find(ID_C_c_sizeof_type).is_not_nil())
    {
      object_type=array_typet(
        c_sizeof_type_rec(tmp_size.op0()),
        tmp_size.op1());      
    }
    else
    {
      typet tmp_type=c_sizeof_type_rec(tmp_size);
      
      if(tmp_type.is_not_nil())
      {
        // Did the size get multiplied?
        mp_integer elem_size=pointer_offset_size(ns, tmp_type);
        mp_integer alloc_size;
        if(elem_size<0 || to_integer(tmp_size, alloc_size))
        {
        }
        else
        {
          if(alloc_size==elem_size)
            object_type=tmp_type;
          else
          {
            mp_integer elements=alloc_size/elem_size;
            
            if(elements*elem_size==alloc_size)
              object_type=array_typet(tmp_type, from_integer(elements, tmp_size.type()));
          }
        }
      }
    }
    
    if(object_type.is_nil())
      object_type=array_typet(unsigned_char_type(), tmp_size);

    // we introduce a fresh symbol for the size
    // to prevent any issues of the size getting ever changed
    
    if(object_type.id()==ID_array &&
       !to_array_type(object_type).size().is_constant())
    {
      exprt &size=to_array_type(object_type).size();
    
      symbolt size_symbol;

      size_symbol.base_name="dynamic_object_size"+i2string(dynamic_count);
      size_symbol.name="symex::"+id2string(size_symbol.base_name);
      size_symbol.is_lvalue=true;
      size_symbol.type=tmp_size.type();
      size_symbol.mode=ID_C;

      state.var_map(size_symbol.name, suffix, size_symbol.type);

      assign_rec(state,
                 guard,
                 size_symbol.symbol_expr(), 
                 size,
                 suffix,
                 lhs_suffix_type);

      size=size_symbol.symbol_expr();
    }
  }
  
  // value
  symbolt value_symbol;

  value_symbol.base_name="dynamic_object"+i2string(state.var_map.dynamic_count);
  value_symbol.name="symex::"+id2string(value_symbol.base_name);
  value_symbol.is_lvalue=true;
  value_symbol.type=object_type;
  value_symbol.type.set("#dynamic", true);
  value_symbol.mode=ID_C;

  state.var_map(value_symbol.name, suffix, value_symbol.type);

  address_of_exprt rhs;
  
  if(object_type.id()==ID_array)
  {
    rhs.type()=pointer_typet(value_symbol.type.subtype());
    index_exprt index_expr(value_symbol.type.subtype());
    index_expr.array()=value_symbol.symbol_expr();
    index_expr.index()=gen_zero(index_type());
    rhs.op0()=index_expr;
  }
  else
  {
    rhs.op0()=value_symbol.symbol_expr();
    rhs.type()=pointer_typet(value_symbol.type);
  }
  
  if(rhs.type()!=lhs.type())
    rhs.make_typecast(lhs.type());

  assign_rec(state,
             guard,
             lhs,
             rhs,
             suffix,
             object_type);
}
#endif

/*******************************************************************\

Function: path_symext::assign_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

#include <iostream>

void path_symext::assign_rec(
  path_symex_statet &state,
  exprt::operandst &guard, 
  const exprt &lhs, 
  const exprt &rhs, 
  const std::string &suffix,
  const exprt &full_lhs) 
{
  if(ns.follow(full_lhs.type()).id()==ID_struct) // full_lhs is a struct
  {
    const struct_typet &struct_type=to_struct_type(ns.follow(full_lhs.type()));
    const struct_typet::componentst &components=struct_type.components();

    // split it up into components
    for(struct_typet::componentst::const_iterator
        it=components.begin();
        it!=components.end();
        it++)
    {
      const typet &subtype=it->type();  
      const irep_idt &component_name=it->get_name();

      exprt new_rhs=member_exprt(rhs, component_name, subtype);
      exprt new_full_lhs=member_exprt(full_lhs, component_name, subtype);
      exprt new_lhs=member_exprt(lhs, component_name, subtype);
      
      // struct constructor on rhs?
      if(rhs.id()==ID_struct)
        new_rhs=simplify_expr(new_rhs, ns);
      
      // recursive call
      assign_rec(state, guard, new_lhs, new_rhs, suffix, new_full_lhs);
    }

    return; // done
  } 

  #if 0
  else if(rhs.id()==ID_sideeffect) // catch side effects on rhs
  {
    const side_effect_exprt &side_effect_expr=to_side_effect_expr(rhs);
    const irep_idt &statement=side_effect_expr.get_statement();

    if(statement==ID_malloc)
    {
      symex_malloc(state, guard, lhs, side_effect_expr, suffix, lhs_suffix_type);
      return;
    }
  }
  #endif
  
  if(lhs.id()==ID_symbol)
  {
    // We might have SSA variables if this comes from dereferenced point.

    // TODO: Please, check!     
    //exprt original_lhs=state.original_name(lhs);
    //exprt original_rhs=state.original_name(rhs);

    // Deal with LHS.
    const symbol_exprt &symbol_expr=to_symbol_expr(lhs);
    const irep_idt &identifier=symbol_expr.get_identifier();
    
    var_mapt::var_infot &var_info=
      state.var_map(identifier, suffix, full_lhs.type());

    // increase SSA counter and produce symbol expression
    var_info.increment_ssa_counter();
 
    symbol_exprt ssa_lhs=
      symbol_exprt(var_info.ssa_identifier(), var_info.type);

    // setup final RHS: deal with arrays on LHS
    //exprt final_rhs=rhs;

    // now dereference, instantiate, propagate RHS
    //exprt rhs_deref=state.dereference(final_rhs);
    //exprt ssa_rhs_no_prop=state.read_no_propagate(rhs_deref);

    exprt ssa_rhs=state.read(rhs);
    
    // make sure that rhs and lhs have matching types

    /*
    if(ssa_rhs_no_prop.is_not_nil() && ssa_rhs_no_prop.type() != lhs_type)
    {

      std::cout << "different types " << std::endl;
      exprt rhs_typecasted=ssa_rhs_no_prop;
      rhs_typecasted.make_typecast(lhs_type);
      ssa_rhs_no_prop=rhs_typecasted;
    }
    */

    // record the step
    path_symex_stept &step=state.record_step();
    
    if(!guard.empty()) step.guard=conjunction(guard);
    step.full_lhs=full_lhs;
    step.ssa_lhs=ssa_lhs;
    step.ssa_rhs=ssa_rhs;
    //step.ssa_rhs_no_prop=ssa_rhs_no_prop;

    // record new state of lhs
    path_symex_statet::var_statet &var_state=state.get_var_state(var_info);
    var_state.ssa_symbol=ssa_lhs;

    // propagate the rhs?
    var_state.value=propagate(ssa_rhs)?ssa_rhs:nil_exprt();

    #ifdef DEBUG
    std::cout << "assign_rec ID_symbol " << identifier << suffix << std::endl;
    #endif
  }
  else if(lhs.id()==ID_member)
  {
    #ifdef DEBUG
    std::cout << "assign_rec ID_member" << std::endl;
    #endif

    const member_exprt &lhs_member_expr=to_member_expr(lhs);
  
    // add component name to the suffix
    const std::string new_suffix=
      "."+id2string(lhs_member_expr.get_component_name())+suffix;

    const exprt &struct_op=lhs_member_expr.struct_op();

    //typet lhs_type=state.var_map.ns.follow(lhs_suffix_type);

    assign_rec(state, guard, struct_op, rhs, new_suffix, full_lhs);
  }
  else if(lhs.id()==ID_index)
  {
    #ifdef DEBUG
    std::cout << "assign_rec ID_index" << std::endl;
    #endif

    const index_exprt &lhs_index_expr=to_index_expr(lhs);

    const exprt &lhs_array=lhs_index_expr.array();
    const exprt &lhs_index=lhs_index_expr.index();
    const typet &lhs_type=ns.follow(lhs_array.type());

    if(lhs_type.id()!=ID_array)
      throw "index must take array type operand, but got `"+
            lhs_type.id_string()+"'";
            
    std::string array_index=state.array_index_as_string(lhs_index);
    if(array_index=="") array_index="[*]";
    
    // add index to the suffix
    const std::string new_suffix=array_index+suffix;

    assign_rec(state, guard, lhs_array, rhs, new_suffix, full_lhs);
  }
  else if(lhs.id()==ID_dereference)
  {
    #ifdef DEBUG
    std::cout << "assign_rec ID_dereference" << std::endl;
    #endif

    const dereference_exprt &dereference_expr=to_dereference_expr(lhs);
    exprt address=state.read(dereference_expr.pointer());
    exprt tmp_lhs=state.dereference(address);

    assign_rec(state, guard, tmp_lhs, rhs, suffix, full_lhs);

    #ifdef DEBUG
    //std::cout << "assign_rec ID_dereference (done)" << std::endl;
    #endif
  }
  else if(lhs.id()==ID_if)
  {
    #ifdef DEBUG
    std::cout << "assign_rec ID_if" << std::endl;
    #endif

    const if_exprt &lhs_if_expr=to_if_expr(lhs);
    exprt cond=state.read(lhs_if_expr.cond());

    // true
    guard.push_back(cond);
    assign_rec(state, guard, lhs_if_expr.true_case(), rhs, suffix, full_lhs);
    guard.pop_back();
    
    // false
    guard.push_back(not_exprt(cond));
    assign_rec(state, guard, lhs_if_expr.false_case(), rhs, suffix, full_lhs);
    guard.pop_back();
  }
  
  #if 0
  else if(lhs.id()==ID_byte_extract_little_endian ||
          lhs.id()==ID_byte_extract_big_endian)
  {
    #ifdef DEBUG
    std::cout << "assign_rec ID_byte_extract" << std::endl;
    #endif

    const byte_extract_exprt &byte_extract_expr=
      to_byte_extract_expr(lhs);
  
    // assignment to byte_extract operators:
    // turn into byte_update operator
    
    // This requires a split over any struct fields, which
    // is todo.
    
    irep_idt new_id;
    
    if(lhs.id()==ID_byte_extract_little_endian)
      new_id=ID_byte_update_little_endian;
    else if(lhs.id()==ID_byte_extract_big_endian)
      new_id=ID_byte_update_big_endian;
    else
      assert(false);

    byte_update_exprt new_rhs(new_id);

    new_rhs.type()=byte_extract_expr.op().type();
    new_rhs.op()=byte_extract_expr.op();
    new_rhs.offset()=byte_extract_expr.offset();
    new_rhs.value()=rhs;

    assign_rec(state, guard, lhs.op0(), new_rhs, suffix, lhs_suffix_type);
  }
  else if(lhs.id()==ID_string_constant ||
          lhs.id()=="NULL-object" ||
          lhs.id()=="zero_string" ||
          lhs.id()=="is_zero_string" ||
          lhs.id()=="zero_string_length")
  {
    // ignore
  }
  else
  {
    // ignore
    //throw "path_symext::assign_rec(): unexpected lhs: ";
  }
  #endif
}

/*******************************************************************\

Function: path_symext::function_call

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void path_symext::function_call(
  path_symex_statet &state,
  const code_function_callt &call,
  const exprt &function)
{
  if(function.id()==ID_symbol)
  {
    const irep_idt &function_identifier=
      to_symbol_expr(function).get_identifier();

    // find the function
    locst::function_mapt::const_iterator f_it=
      state.locs.function_map.find(function_identifier);

    if(f_it==state.locs.function_map.end())
      throw "failed to find `"+id2string(function_identifier)+"' in function_map";
  
    const locst::function_entryt &function_entry=f_it->second;

    loc_reft function_entry_point=function_entry.first;
  
    // do we have a body?
    if(function_entry_point==loc_reft())
    {
      // no body, this is a skip
      if(call.lhs().is_not_nil())
        assign(state, call.lhs(), nil_exprt());

      state.next_pc();
      return;
    }
  
    // push a frame on the call stack
    path_symex_statet::threadt &thread=state.threads[state.get_current_thread()];
    thread.call_stack.push_back(path_symex_statet::framet());
    thread.call_stack.back().return_location=thread.pc.next_loc();
    thread.call_stack.back().return_lhs=call.lhs();
    thread.call_stack.back().saved_local_vars=thread.local_vars;

    const code_typet &code_type=
      to_code_type(ns.follow(function_entry.second));

    const code_typet::argumentst &function_arguments=code_type.arguments();

    const exprt::operandst &call_arguments=call.arguments();
  
    // now assign the argument values
    for(unsigned i=0; i<call_arguments.size(); i++)
    {
      if(i<function_arguments.size())
      {
        const code_typet::argumentt &function_argument=function_arguments[i];
        irep_idt identifier=function_argument.get_identifier();

        if(identifier==irep_idt())
          throw "function_call " + id2string(function_identifier) + " no identifier for function argument";

        symbol_exprt lhs(identifier, function_argument.type());
            
        // TODO: need to save+restore

        assign(state, lhs, call_arguments[i]);
      }
    }

    // set the new PC
    thread.pc=function_entry_point;
  }
  else
    throw "TODO: function_call "+function.id_string();
}

/*******************************************************************\

Function: path_symext::return_from_function

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void path_symext::return_from_function(
  path_symex_statet &state,
  const exprt &return_value)
{
  if(state.threads[state.get_current_thread()].call_stack.empty())
  {
    state.remove_current_thread();
  }
  else
  {
    path_symex_statet::threadt &thread=state.threads[state.get_current_thread()];
    thread.pc=thread.call_stack.back().return_location;

    // assign the return value
    if(return_value.is_not_nil() &&
       thread.call_stack.back().return_lhs.is_not_nil())
      assign(state, thread.call_stack.back().return_lhs, return_value);

    thread.call_stack.pop_back();
  }
}

/*******************************************************************\

Function: path_symext::do_goto

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void path_symext::do_goto(
  path_symex_statet &state,
  std::list<path_symex_statet> &further_states)
{
  const goto_programt::instructiont &instruction=
    *state.get_instruction();

  if(instruction.is_backwards_goto())
  {
    #if 0
    unsigned unwinding_steps=++state.unwind_map[state.pc().loc_number];

    if(unwinding_steps > max_unwind) {
      std::cout << "unwinding steps " << state.pc().loc_number << " : " << unwinding_steps << std::endl;
      state.threads[thread_nr].active=false;
      break;
    }
    #endif
  }

  const loct &loc=state.locs[state.pc()];

  exprt guard=state.read(instruction.guard);
  
  if(guard.is_true() && loc.targets.size()==1)
  {
    state.set_pc(loc.targets.front());
    return; // we are done
  }

  if(!guard.is_false())
  {
    // branch taken case
    for(loct::targetst::const_iterator
        t_it=loc.targets.begin();
        t_it!=loc.targets.end();
        t_it++)
    {
      // copy the state into 'furhter_states'
      further_states.push_back(state);
      further_states.back().set_pc(*t_it);
      further_states.back().history.steps.back().guard=guard;
    }
  }

  // branch not taken case
  exprt negated_guard=simplify_expr(not_exprt(guard), ns);
  state.next_pc();
  state.history.steps.back().guard=negated_guard;
}

/*******************************************************************\

Function: path_symext::operator()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void path_symext::operator()(
  path_symex_statet &state,
  std::list<path_symex_statet> &further_states)
{
  const goto_programt::instructiont &instruction=
    *state.get_instruction();

  switch(instruction.type)
  {
  case END_FUNCTION:
    // pop the call stack
    state.record_step();
    return_from_function(state, nil_exprt());
    break;
    
  case RETURN:
    // pop the call stack
    {
      state.record_step();
      exprt return_val=instruction.code.operands().size()==1?
                       instruction.code.op0():nil_exprt();
      return_from_function(state, return_val);
    }
    break;
    
  case START_THREAD:
    {
      const loct &loc=state.locs[state.pc()];
      assert(loc.targets.size()==1);
      
      state.record_step();
      state.next_pc();
      
      // ordering of the following matters due to vector instability
      path_symex_statet::threadt &new_thread=state.add_thread();
      path_symex_statet::threadt &old_thread=state.threads[state.get_current_thread()];
      new_thread.pc=loc.targets.front();
      new_thread.local_vars=old_thread.local_vars;
    }
    break;
    
  case END_THREAD:
    state.record_step();
    state.remove_current_thread();
    break;
    
  case GOTO:
    state.record_step();
    do_goto(state, further_states);
    break;
    
  case CATCH:
    // ignore for now
    state.record_step();
    state.next_pc();
    break;
    
  case THROW:
    state.record_step();
    throw "THROW not yet implemented";
    
  case ASSUME:
    state.record_step();
    if(instruction.guard.is_false())
      state.remove_current_thread();
    else
    {
      exprt guard=state.read(instruction.guard);
      //state.history.back().guard=guard;
      state.next_pc();
    }
    break;
    
  case ASSERT:
  case SKIP:
  case LOCATION:
  case DEAD:
    state.record_step();
    state.next_pc();
    break;

  case DECL:
    // assigning an RHS of NIL means 'nondet'
    assign(state, to_code_decl(instruction.code).symbol(), nil_exprt());
    state.next_pc();
    break;

  case ATOMIC_BEGIN:
    if(state.inside_atomic_section)
      throw "nested ATOMIC_BEGIN";

    state.record_step();
    state.next_pc();
    state.inside_atomic_section=true;
    break;

  case ATOMIC_END:
    if(state.inside_atomic_section)
      throw "ATOMIC_END unmatched";

    state.record_step();
    state.next_pc();
    state.inside_atomic_section=false;
    break;
    
  case ASSIGN:
    assign(state, to_code_assign(instruction.code));
    state.next_pc();
    break;
    
  case FUNCTION_CALL:
    state.record_step();
    function_call(state, to_code_function_call(instruction.code));
    break;
    
  case OTHER:
    state.record_step();

    {
      const codet &code=instruction.code;
      const irep_idt &statement=code.get_statement();

      if(statement==ID_expression)
      {
        // like SKIP
      }
      else if(statement==ID_printf)
      {
        // ignore for now (should record stuff printed)
      }
      else if(statement==ID_asm)
      {
        // ignore for now
      }
      else if(statement==ID_fence)
      {
        // ignore for SC
      }
      else
        throw "unexpected OTHER statement: "+id2string(statement);
    }

    state.next_pc();
    break;

  default:
    throw "path_symext: unexpected instruction";
  }
}

/*******************************************************************\

Function: path_symex

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void path_symex(
  path_symex_statet &state,
  std::list<path_symex_statet> &further_states,
  const namespacet &ns)
{
  path_symext path_symex(ns);  
  path_symex(state, further_states);
}

