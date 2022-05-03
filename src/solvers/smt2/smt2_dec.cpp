/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "smt2_dec.h"

#include <util/arith_tools.h>
#include <util/ieee_float.h>
#include <util/invariant.h>
#include <util/message.h>
#include <util/run.h>
#include <util/std_expr.h>
#include <util/std_types.h>
#include <util/tempfile.h>

#include "smt2irep.h"

std::string smt2_dect::decision_procedure_text() const
{
  // clang-format off
  return "SMT2 " + logic + (use_FPA_theory ? " (with FPA)" : "") + " using " +
    (solver==solvert::GENERIC?"Generic":
     solver==solvert::BOOLECTOR?"Boolector":
     solver==solvert::CPROVER_SMT2?"CPROVER SMT2":
     solver==solvert::CVC3?"CVC3":
     solver==solvert::CVC4?"CVC4":
     solver==solvert::MATHSAT?"MathSAT":
     solver==solvert::YICES?"Yices":
     solver==solvert::Z3?"Z3":
     "(unknown)");
  // clang-format on
}

#include <iostream>
void smt2_dect::substitute_oracles(std::unordered_map<std::string, std::string>& name2funcdefinition)
{
  problem_str = stringstream.str();
  /* std::cout << "====== Original problem =======\n" << problem_str; */
  for (const auto& entry : name2funcdefinition) {
    const std::string& binary_name = entry.first;
    const std::string& new_fun = entry.second;
    /* std::cout << "- Name: " << binary_name << '\n'; */
    /* std::cout << "---- " << new_fun << '\n'; */
    size_t start = problem_str.find(binary_name);
    assert(start != std::string::npos);
    size_t end_line = problem_str.find('\n', start);
    size_t start_line = problem_str.rfind('\n', start) + 1;
    assert(end_line != std::string::npos);
    assert(start_line != std::string::npos);
    problem_str.replace(start_line, end_line - start_line, new_fun);
  } 
  substituted_oracles = true;
}

void smt2_dect::push_assump_str(std::string& _assump_str)
{
  assump_str = _assump_str;
}

void smt2_dect::pop()
{
  assump_str.clear();
}

decision_proceduret::resultt smt2_dect::dec_solve()
{ 
  // has to substitute oracle before calling this function
  // TODO: set problem_str to stringstream.str() if problem_str_is_set is false 
  if (substituted_oracles!=true) {
    problem_str = stringstream.str();
    substituted_oracles = true;
  }
  assert(substituted_oracles);
  ++number_of_solver_calls;

  temporary_filet temp_file_problem("smt2_dec_problem_", ""),
    temp_file_stdout("smt2_dec_stdout_", ""),
    temp_file_stderr("smt2_dec_stderr_", "");

  {
    // we write the problem into a file
    std::ofstream problem_out(
      temp_file_problem(), std::ios_base::out | std::ios_base::trunc);
    /* problem_out << stringstream.str(); */
    problem_out << problem_str << assump_str;
    std::cout << "----------- Input -----------\n";
    std::cout << problem_str << assump_str << std::endl;
    std::cout << "-----------------------------\n";
    write_footer(problem_out);
    substituted_oracles = false;
  }

  std::vector<std::string> argv;
  std::string stdin_filename;

  switch(solver)
  {
  case solvert::BOOLECTOR:
    argv = {"boolector", "--smt2", temp_file_problem(), "-m"};
    break;

  case solvert::CPROVER_SMT2:
    argv = {"smt2_solver"};
    stdin_filename = temp_file_problem();
    break;

  case solvert::CVC3:
    argv = {"cvc3",
            "+model",
            "-lang",
            "smtlib",
            "-output-lang",
            "smtlib",
            temp_file_problem()};
    break;

  case solvert::CVC4:
    // The flags --bitblast=eager --bv-div-zero-const help but only
    // work for pure bit-vector formulas.
    argv = {"cvc4", "-L", "smt2", "--produce-models", "--nl-ext-tplanes", temp_file_problem()};
    break;

  case solvert::MATHSAT:
    // The options below were recommended by Alberto Griggio
    // on 10 July 2013

    argv = {"mathsat",
            "-input=smt2",
            "-preprocessor.toplevel_propagation=true",
            "-preprocessor.simplification=7",
            "-dpll.branching_random_frequency=0.01",
            "-dpll.branching_random_invalidate_phase_cache=true",
            "-dpll.restart_strategy=3",
            "-dpll.glucose_var_activity=true",
            "-dpll.glucose_learnt_minimization=true",
            "-theory.bv.eager=true",
            "-theory.bv.bit_blast_mode=1",
            "-theory.bv.delay_propagated_eqs=true",
            "-theory.fp.mode=1",
            "-theory.fp.bit_blast_mode=2",
            "-theory.arr.mode=1"};

    stdin_filename = temp_file_problem();
    break;

  case solvert::YICES:
    //    command = "yices -smt -e "   // Calling convention for older versions
    // Convention for 2.2.1
    argv = {"yices-smt2", temp_file_problem()};
    break;

  case solvert::Z3:
    argv = {"z3", "-smt2", temp_file_problem()};
    break;

  case solvert::GENERIC:
    UNREACHABLE;
  }

  int res =
    run(argv[0], argv, stdin_filename, temp_file_stdout(), temp_file_stderr());

  if(res<0)
  {
    messaget log{message_handler};
    log.error() << "error running SMT2 solver" << messaget::eom;
    return decision_proceduret::resultt::D_ERROR;
  }

  std::cout << "----------- Output ----------\n";
  std::ifstream debug_in(temp_file_stdout());
  std::cout << debug_in.rdbuf();
  debug_in.close();
  std::cout << "-----------------------------\n";

  std::ifstream in(temp_file_stdout());
  return read_result(in);
}

decision_proceduret::resultt smt2_dect::read_result(std::istream &in)
{
  std::string line;
  decision_proceduret::resultt res=resultt::D_ERROR;

  boolean_assignment.clear();
  boolean_assignment.resize(no_boolean_variables, false);

  typedef std::unordered_map<irep_idt, irept> valuest;
  valuest values;

  while(in)
  {
    auto parsed_opt = smt2irep(in, message_handler);

    if(!parsed_opt.has_value())
      break;

    const auto &parsed = parsed_opt.value();

    if(parsed.id()=="sat")
      res=resultt::D_SATISFIABLE;
    else if(parsed.id()=="unsat")
      res=resultt::D_UNSATISFIABLE;
    else if(
      parsed.id().empty() && parsed.get_sub().size() == 1 &&
      parsed.get_sub().front().get_sub().size() == 2)
    {
      const irept &s0=parsed.get_sub().front().get_sub()[0];
      const irept &s1=parsed.get_sub().front().get_sub()[1];

      // Examples:
      // ( (B0 true) )
      // ( (|__CPROVER_pipe_count#1| (_ bv0 32)) )
      // ( (|some_integer| 0) )
      // ( (|some_integer| (- 10)) )

      values[s0.id()]=s1;
    }
    else if(
      parsed.id().empty() && parsed.get_sub().size() == 2 &&
      parsed.get_sub().front().id() == "error")
    {
      // We ignore errors after UNSAT because get-value after check-sat
      // returns unsat will give an error.
      if(res!=resultt::D_UNSATISFIABLE)
      {
        messaget log{message_handler};
        log.error() << "SMT2 solver returned error message:\n"
                    << "\t\"" << parsed.get_sub()[1].id() << "\""
                    << messaget::eom;
        return decision_proceduret::resultt::D_ERROR;
      }
    }
  }

  for(auto &assignment : identifier_map)
  {
    std::string conv_id=convert_identifier(assignment.first);
    const irept &value=values[conv_id];
    assignment.second.value=parse_rec(value, assignment.second.type);
  }

  // Booleans
  for(unsigned v=0; v<no_boolean_variables; v++)
  {
    const irept &value=values["B"+std::to_string(v)];
    boolean_assignment[v]=(value.id()==ID_true);
  }

  return res;
}
