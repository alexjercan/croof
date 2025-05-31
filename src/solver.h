#ifndef SOLVER_H
#define SOLVER_H

#include "ds.h"
#include "parser.h"

ds_result solver_solve_program(program_t *program);
ds_result solver_solve_eval(ds_dynamic_array statements /* statement_t */,
                            expression_t *eval, expression_t *solution,
                            ds_dynamic_array *steps /* expression_t */);

#endif // SOLVER_H
