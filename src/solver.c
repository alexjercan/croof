#include <assert.h>
#include <limits.h>
#include "solver.h"
#include "parser.h"

// TODO: Maybe move this as a tuple data structure in ds.h
typedef struct pair_t {
    expression_t *key;
    expression_t *value;
} pair_t;

static boolean solver_find_pair(ds_dynamic_array mapping /* pair_t */, expression_t *key, expression_t *value) {
    // NOTE: Ideally this would be implemented using hashmap, but I am too lazy
    // to write the hashing function for the expression, so I just use a
    // dynamic array for now.

    for (unsigned int i = 0; i < mapping.count; i++) {
        pair_t *kv = NULL;
        DS_UNREACHABLE(ds_dynamic_array_get_ref(&mapping, i, (void **)&kv));

        if (expression_equal(kv->key, key)) {
            if (value != NULL) {
                *value = *kv->value;
            }
            return true;
        }
    }

    return false;
}

typedef struct parent_t {
    expression_t *expr; // The expression that was evaluated
    expression_t *prev; // The previous expression in the path
    int used;           // The index of the statement that was used to evaluate this expression
} parent_t;

static boolean solver_find_mapping_index(ds_dynamic_array mapping /* pair_t */, expression_t *key, int *index) {
    // NOTE: This function uses a "pair_t" like element to search
    // THE STRUCURE HAS TO START WITH THE KEY

    // NOTE: Ideally this would be implemented using hashmap, but I am too lazy
    // to write the hashing function for the expression, so I just use a
    // dynamic array for now.

    for (unsigned int i = 0; i < mapping.count; i++) {
        pair_t *kv = NULL;
        DS_UNREACHABLE(ds_dynamic_array_get_ref(&mapping, i, (void **)&kv));

        if (expression_equal(kv->key, key)) {
            if (index != NULL) {
                *index = i;
            }
            return true;
        }
    }

    return false;
}

static boolean solver_find_visited(ds_dynamic_array *visited /* expression_t */, expression_t *expr) {
    // NOTE: See the comment in solver_find_mapping for why I am not using a
    // hashmap here.

    for (unsigned int i = 0; i < visited->count; i++) {
        expression_t *item = NULL;
        DS_UNREACHABLE(ds_dynamic_array_get_ref(visited, i, (void **)&item));

        // TODO: implement something like equavalence instead,
        // so that we can compare expressions more efficiently
        if (expression_equal(expr, item)) {
            return true;
        }
    }

    return false;
}


static boolean solver_make_mapping(expression_t *reference, expression_t *expr, ds_dynamic_array *mapping /* pair_t */) {
    // This function checks if the expr can be directly substituted for the
    // reference expression, and builds a mapping if it can.

    // TODO: implement a more sophisticated mapping algorithm

    switch (reference->kind) {
    case EXPRESSION_KIND_SET: return false;
    case EXPRESSION_KIND_NAME: return false;
    case EXPRESSION_KIND_NUMBER:
        switch (expr->kind) {
        case EXPRESSION_KIND_SET:
            // Dead end: cannot substitute a set with a number
            return false;
        case EXPRESSION_KIND_NAME:
            // Dead end: cannot substitute a set name with a number
            return false;
        case EXPRESSION_KIND_NUMBER:
            // If the reference and the expression are both numbers, we can substitute if they are equal
            return ds_string_slice_equals(&reference->number.value, &expr->number.value);
        case EXPRESSION_KIND_FUNCTION:
            // Dead end: cannot substitute a function with a number
            return false;
        case EXPRESSION_KIND_OPERATOR:
            // Dead end: cannot substitute an operator with a number
            return false;
        case EXPRESSION_KIND_PAREN:
            // Dead end: cannot substitute a parenthesis with a number
            return false;
        }
    case EXPRESSION_KIND_FUNCTION:
        if (reference->function.args.count == 0) {
            // If the reference is a variable, we should be able to substitute the expression

            expression_t value = {0};
            boolean has_mapping = solver_find_pair(*mapping, reference, &value);
            boolean should_substitute = !has_mapping || expression_equal(&value, expr);

            if (!has_mapping) {
                // If we don't have a mapping for the reference, we can create one
                pair_t kv = CLITERAL(pair_t){reference, expr};
                DS_UNREACHABLE(ds_dynamic_array_append(mapping, &kv));
            }

            return should_substitute;
        }

        switch (expr->kind) {
        case EXPRESSION_KIND_SET:
            // Dead end: cannot substitute a set with a function
            return false;
        case EXPRESSION_KIND_NAME:
            // Dead end: cannot substitute a set name with a function
            return false;
        case EXPRESSION_KIND_NUMBER:
            // Dead end: cannot substitute a number with a function
            return false;
        case EXPRESSION_KIND_FUNCTION:
            // If we have a function try to match all the args
            if (ds_string_slice_equals(&reference->function.value, &expr->function.value)) {
                if (reference->function.args.count == expr->function.args.count) {
                    boolean can_substitute = true;
                    for (unsigned int i = 0; i < reference->function.args.count; i++) {
                        expression_t *ref_arg = NULL;
                        DS_UNREACHABLE(ds_dynamic_array_get_ref(&reference->function.args, i, (void **)&ref_arg));

                        expression_t *expr_arg = NULL;
                        DS_UNREACHABLE(ds_dynamic_array_get_ref(&expr->function.args, i, (void **)&expr_arg));

                        can_substitute = can_substitute && solver_make_mapping(ref_arg, expr_arg, mapping);
                    }

                    return can_substitute;
                }
            }

            return false;
        case EXPRESSION_KIND_OPERATOR:
            // Dead end: cannot substitute a function with another function or operator
            return false;
        case EXPRESSION_KIND_PAREN:
            // Dead end: cannot substitute a parenthesis with a function
            return false;
        }
    case EXPRESSION_KIND_OPERATOR:
        switch (expr->kind) {
        case EXPRESSION_KIND_SET:
            // Dead end: cannot substitute a set with an operator
            return false;
        case EXPRESSION_KIND_NAME:
            // Dead end: cannot substitute a set name with an operator
            return false;
        case EXPRESSION_KIND_NUMBER:
            // Dead end: cannot substitute a number with an operator
            return false;
        case EXPRESSION_KIND_FUNCTION:
            // Dead end: cannot substitute a function with an operator
            return false;
        case EXPRESSION_KIND_OPERATOR:
            // If the reference and the expression are both operators, we can substitute if they are equal
            if (ds_string_slice_equals(&reference->operator.value, &expr->operator.value)) {
                return solver_make_mapping(reference->operator.lhs, expr->operator.lhs, mapping)
                    && solver_make_mapping(reference->operator.rhs, expr->operator.rhs, mapping);
            }

            return false;
        case EXPRESSION_KIND_PAREN:
            // Dead end: cannot substitute a parenthesis with an operator
            return false;
        }
    case EXPRESSION_KIND_PAREN:
        switch (expr->kind) {
        case EXPRESSION_KIND_SET:
            // Dead end: cannot substitute a set with a parenthesis
            return false;
        case EXPRESSION_KIND_NAME:
            // Dead end: cannot substitute a set name with a parenthesis
            return false;
        case EXPRESSION_KIND_NUMBER:
            // Dead end: cannot substitute a number with a parenthesis
            return false;
        case EXPRESSION_KIND_FUNCTION:
            // Dead end: cannot substitute a function with a parenthesis
            return false;
        case EXPRESSION_KIND_OPERATOR:
            // Dead end: cannot substitute an operator with a parenthesis
            return false;
        case EXPRESSION_KIND_PAREN:
            // If the reference and the expression are both parenthesis, we can substitute if they are equal
            return solver_make_mapping(reference->paren.expr, expr->paren.expr, mapping);
        }
    }
}

static ds_result solver_apply_mapping(expression_t *expression, ds_dynamic_array mapping /* pair_t */, expression_t *target) {
    ds_result result = DS_OK;
    expression_t value = {0};

    switch (expression->kind) {
    case EXPRESSION_KIND_SET:
        target->kind = EXPRESSION_KIND_SET;
        ds_dynamic_array_init(&target->set.items, sizeof(expression_t));
        for (unsigned int i = 0; i < expression->set.items.count; i++) {
            expression_t *item_i = NULL;
            DS_UNREACHABLE(ds_dynamic_array_get_ref(&expression->set.items, i, (void **)&item_i));

            expression_t item = {0};
            TRY(solver_apply_mapping(item_i, mapping, &item));
            DS_UNREACHABLE(ds_dynamic_array_append(&target->set.items, &item));
        }
        break;
    case EXPRESSION_KIND_NAME:
        if (!solver_find_pair(mapping, expression, &value)) {
            DS_LOG_ERROR("Failed to find mapping for name %.*s",
                          (int)expression->name.value.len, expression->name.value.str);
            return_defer(DS_ERR);
        }
        *target = value;
        break;
    case EXPRESSION_KIND_NUMBER:
        *target = *expression;
        break;
    case EXPRESSION_KIND_FUNCTION:
        if (expression->function.args.count == 0) {
            if (!solver_find_pair(mapping, expression, &value)) {
                return_defer(DS_ERR);
            }

            *target = value;
        } else {
            target->kind = EXPRESSION_KIND_FUNCTION;
            target->function.value = expression->function.value;
            ds_dynamic_array_init(&target->function.args, sizeof(expression_t));

            for (unsigned int i = 0; i < expression->function.args.count; i++) {
                expression_t *arg_i = NULL;
                DS_UNREACHABLE(ds_dynamic_array_get_ref(&expression->function.args, i, (void **)&arg_i));

                expression_t item = {0};
                TRY(solver_apply_mapping(arg_i, mapping, &item));
                DS_UNREACHABLE(ds_dynamic_array_append(&target->function.args, &item));
            }
        }
        break;
    case EXPRESSION_KIND_OPERATOR:
        expression_clone(expression, target);
        TRY(solver_apply_mapping(expression->operator.lhs, mapping, target->operator.lhs));
        TRY(solver_apply_mapping(expression->operator.rhs, mapping, target->operator.rhs));
        break;
    case EXPRESSION_KIND_PAREN:
        expression_clone(expression, target);
        TRY(solver_apply_mapping(expression->paren.expr, mapping, target->paren.expr));
        break;
    }

defer:
    if (result != DS_OK) {
        expression_free(target);
    }

    return result;
}

static boolean solver_substitute(expression_t *expr, statement_t *statement,
                        expression_t *substitution, expression_t *iter,
                        ds_dynamic_array *substitutions /* expression_t */) {
    // substitutions will contain the list of substitutions that can be made
    // "we can change `expr` to `substitution:substitutions` if `statement` is applied"

    boolean result = false;

    if (statement->equality == NULL) {
        DS_PANIC("Statement has no equality");
    }

    expression_t reference = statement->equality->lhs;

    switch (reference.kind) {
    case EXPRESSION_KIND_SET: break;
    case EXPRESSION_KIND_NAME: break;
    case EXPRESSION_KIND_NUMBER:
        switch (expr->kind) {
        case EXPRESSION_KIND_SET:
            // If the reference is a number and the expression is a set, we can call substitute on each item
            DS_PANIC("This is not implemented yet");
            break;
        case EXPRESSION_KIND_NAME:
            // Dead end: cannot substitute a set name with a number
            break;
        case EXPRESSION_KIND_NUMBER:
            // If the reference and the expression are both numbers, we can substitute if they are equal
            if (ds_string_slice_equals(&reference.number.value, &expr->number.value)) {
                *iter = statement->equality->rhs;
                expression_t s = {0};
                expression_clone(substitution, &s);
                DS_UNREACHABLE(ds_dynamic_array_append(substitutions, &s));

                result = true;
            }
            break;
        case EXPRESSION_KIND_FUNCTION:
            // If the reference is a number and the expression is a function, we can call substitute on each argument
            for (unsigned int i = 0; i < expr->function.args.count; i++) {
                expression_clone(expr, iter);

                expression_t *expr_arg = NULL;
                DS_UNREACHABLE(ds_dynamic_array_get_ref(&expr->function.args, i, (void **)&expr_arg));

                expression_t *iter_arg = NULL;
                DS_UNREACHABLE(ds_dynamic_array_get_ref(&iter->function.args, i, (void **)&iter_arg));

                if (solver_substitute(expr_arg, statement, substitution, iter_arg, substitutions)) {
                    result = true;
                } else {
                    expression_free(iter);
                }
            }
            break;
        case EXPRESSION_KIND_OPERATOR:
            // If the reference is a number and the expression is an operator, we can call substitute on the rhs
            expression_clone(expr, iter);
            if (solver_substitute(expr->operator.rhs, statement, substitution, iter->operator.rhs, substitutions)) {
                result = true;
            } else {
                expression_free(iter);
            }

            break;
        case EXPRESSION_KIND_PAREN:
            // If the reference is a number and the expression is a parenthesis, we can substitute the inner expression
            expression_clone(expr, iter);
            if (solver_substitute(expr->paren.expr, statement, substitution, iter->paren.expr, substitutions)) {
                result = true;
            } else {
                expression_free(iter);
            }

            break;
        }
        break;
    case EXPRESSION_KIND_FUNCTION:
        if (reference.function.args.count == 0) {
            // If the reference is a variable, we should be able to substitute the expression with the rhs of the variable

            *iter = statement->equality->rhs;
            expression_t s = {0};
            expression_clone(substitution, &s);
            DS_UNREACHABLE(ds_dynamic_array_append(substitutions, &s));

            result = true;
        }

        switch (expr->kind) {
        case EXPRESSION_KIND_SET:
            // If the reference is a function and the expression is a set, we can call substitute on each item
            DS_PANIC("This is not implemented yet");
            break;
        case EXPRESSION_KIND_NAME:
            // Dead end: cannot substitute a set name with a function
            break;
        case EXPRESSION_KIND_NUMBER:
            // Dead end: cannot substitute a number with a function
            break;
        case EXPRESSION_KIND_FUNCTION:
            if (reference.function.args.count > 0) {
                // If the reference is a function and the expression is also a function,
                // - we can try to substitute the function call (when it matches)
                // - we can try to substitute the args of the function with the reference
                if (expression_equal(&reference, expr)) {
                    // If the reference and the expression are equal, we can substitute the expression with the rhs of the equality
                    *iter = statement->equality->rhs;
                    expression_t s = {0};
                    expression_clone(substitution, &s);
                    DS_UNREACHABLE(ds_dynamic_array_append(substitutions, &s));

                    result = true;
                }

                for (unsigned int i = 0; i < expr->function.args.count; i++) {
                    expression_clone(expr, iter);

                    expression_t *expr_arg = NULL;
                    DS_UNREACHABLE(ds_dynamic_array_get_ref(&expr->function.args, i, (void **)&expr_arg));

                    expression_t *iter_arg = NULL;
                    DS_UNREACHABLE(ds_dynamic_array_get_ref(&iter->function.args, i, (void **)&iter_arg));

                    if (solver_substitute(expr_arg, statement, substitution, iter_arg, substitutions)) {
                        result = true;
                    } else {
                        expression_free(iter);
                    }
                }
            }

            break;
        case EXPRESSION_KIND_OPERATOR:
            // We can also try to substitute the rhs of the operator with the reference
            expression_clone(expr, iter);
            if (solver_substitute(expr->operator.rhs, statement, substitution, iter->operator.rhs, substitutions)) {
                result = true;
            } else {
                expression_free(iter);
            }

            break;
        case EXPRESSION_KIND_PAREN:
            // If the reference is a function and the expression is a parenthesis, we can substitute the inner expression
            expression_clone(expr, iter);
            if (solver_substitute(expr->paren.expr, statement, substitution, iter->paren.expr, substitutions)) {
                result = true;
            } else {
                expression_free(iter);
            }

            break;
        }
        break;
    case EXPRESSION_KIND_OPERATOR:
        switch (expr->kind) {
        case EXPRESSION_KIND_SET:
            // If the reference is an operator and the expression is a set, we can call substitute on each item
            DS_PANIC("This is not implemented yet");
            break;
        case EXPRESSION_KIND_NAME:
            // Dead end: cannot substitute a set name with an operator
            break;
        case EXPRESSION_KIND_NUMBER:
            // Dead end: cannot substitute a number with an operator
            break;
        case EXPRESSION_KIND_FUNCTION:
            // If the reference is an operator and the expression is a function, we can call substitute on each argument
            for (unsigned int i = 0; i < expr->function.args.count; i++) {
                expression_clone(expr, iter);

                expression_t *expr_arg = NULL;
                DS_UNREACHABLE(ds_dynamic_array_get_ref(&expr->function.args, i, (void **)&expr_arg));

                expression_t *iter_arg = NULL;
                DS_UNREACHABLE(ds_dynamic_array_get_ref(&iter->function.args, i, (void **)&iter_arg));

                if (solver_substitute(expr_arg, statement, substitution, iter_arg, substitutions)) {
                    result = true;
                } else {
                    expression_free(iter);
                }
            }

            break;
        case EXPRESSION_KIND_OPERATOR:
            if (ds_string_slice_equals(&reference.operator.value, &expr->operator.value)) {
                ds_dynamic_array mapping = {0}; // pair_t
                ds_dynamic_array_init(&mapping, sizeof(pair_t));
                if (solver_make_mapping(&reference, expr, &mapping)) {
                    DS_UNREACHABLE(solver_apply_mapping(&statement->equality->rhs, mapping, iter));
                    expression_t s = {0};
                    expression_clone(substitution, &s);
                    DS_UNREACHABLE(ds_dynamic_array_append(substitutions, &s));

                    result = true;
                }

                ds_dynamic_array_free(&mapping);
            }

            // We can also try to substitute the rhs of the operator with the reference
            expression_clone(expr, iter);
            if (solver_substitute(expr->operator.rhs, statement, substitution, iter->operator.rhs, substitutions)) {
                result = true;
            } else {
                expression_free(iter);
            }

            break;
        case EXPRESSION_KIND_PAREN:
            // If the reference is an operator and the expression is a parenthesis, we can substitute the inner expression
            expression_clone(expr, iter);
            if (solver_substitute(expr->paren.expr, statement, substitution, iter->paren.expr, substitutions)) {
                result = true;
            } else {
                expression_free(iter);
            }

            break;
        }
    case EXPRESSION_KIND_PAREN:
        switch (expr->kind) {
        case EXPRESSION_KIND_SET:
            // If the reference is a parenthesis and the expression is a set, we can call substitute on each item
            DS_PANIC("This is not implemented yet");
            break;
        case EXPRESSION_KIND_NAME:
            // Dead end: cannot substitute a set name with a parenthesis
            break;
        case EXPRESSION_KIND_NUMBER:
            // Dead end: cannot substitute a number with a parenthesis
            break;
        case EXPRESSION_KIND_FUNCTION:
            // If the reference is a parenthesis and the expression is a function, we can call substitute on each argument
            for (unsigned int i = 0; i < expr->function.args.count; i++) {
                expression_clone(expr, iter);

                expression_t *expr_arg = NULL;
                DS_UNREACHABLE(ds_dynamic_array_get_ref(&expr->function.args, i, (void **)&expr_arg));

                expression_t *iter_arg = NULL;
                DS_UNREACHABLE(ds_dynamic_array_get_ref(&iter->function.args, i, (void **)&iter_arg));

                if (solver_substitute(expr_arg, statement, substitution, iter_arg, substitutions)) {
                    result = true;
                } else {
                    expression_free(iter);
                }
            }
            break;
        case EXPRESSION_KIND_OPERATOR:
            expression_clone(expr, iter);
            if (solver_substitute(expr->operator.rhs, statement, substitution, iter->operator.rhs, substitutions)) {
                result = true;
            } else {
                expression_free(iter);
            }

            break;
        case EXPRESSION_KIND_PAREN:
            // If the reference is a parenthesis and the expression is also a parenthesis, we can try to substitute the inner expression
            expression_clone(expr, iter);
            if (solver_substitute(expr->paren.expr, statement, substitution, iter->paren.expr, substitutions)) {
                result = true;
            } else {
                expression_free(iter);
            }

            break;
        }
    }

    return result;
}

static void solver_solve_dfs(ds_dynamic_array statements /* statement_t */,
                                  expression_t *expression,
                                  ds_dynamic_array *visited /* expression_t */,
                                  ds_dynamic_array *parent /* parent_t */) {
    ds_dynamic_array substitutions = {0}; // expression_t
    ds_dynamic_array_init(&substitutions, sizeof(expression_t));

    DS_UNREACHABLE(ds_dynamic_array_append(visited, expression));

    for (unsigned int i = 0; i < statements.count; i++) {
        statement_t *statement = NULL;
        DS_UNREACHABLE(ds_dynamic_array_get_ref(&statements, i, (void **)&statement));
        if (statement->equality == NULL) continue;

        expression_t iter = {0};
        ds_dynamic_array_clear(&substitutions);

        // printf("generate: ");
        // expression_printf(expression);
        // printf(" => ...");
        // printf(" (");
        // statement_printf(statement);
        // printf(")\n");

        solver_substitute(expression, statement, &iter, &iter, &substitutions);

        for (unsigned int j = 0; j < substitutions.count; j++) {
            expression_t *substitution = NULL;
            DS_UNREACHABLE(ds_dynamic_array_get_ref(&substitutions, j, (void **)&substitution));

            if (!solver_find_visited(visited, substitution)) {
                // printf("visit: ");
                // expression_printf(expression);
                // printf(" => ");
                // expression_printf(substitution);
                // printf(" (");
                // statement_printf(statement);
                // printf(")\n");

                parent_t kv = {0};
                kv.expr = DS_MALLOC(NULL, sizeof(expression_t));
                expression_clone(substitution, kv.expr);
                kv.prev = DS_MALLOC(NULL, sizeof(expression_t));
                expression_clone(expression, kv.prev);
                kv.used = i;
                DS_UNREACHABLE(ds_dynamic_array_append(parent, &kv));

                solver_solve_dfs(statements, substitution, visited, parent);
            }
        }
    }

    for (unsigned int i = 0; i < substitutions.count; i++) {
        expression_t *substitution = NULL;
        DS_UNREACHABLE(ds_dynamic_array_get_ref(&substitutions, i, (void **)&substitution));
        expression_free(substitution);
    }

    ds_dynamic_array_free(&substitutions);
}

static int solver_expression_degree(expression_t *expression) {
    // TODO: This can be tweeked more. Find some more heuristics that I can use

    switch (expression->kind) {
    case EXPRESSION_KIND_SET: return 1; // NOTE: maybe also check the items
    case EXPRESSION_KIND_NAME: return 0;
    case EXPRESSION_KIND_NUMBER: return 0;
    case EXPRESSION_KIND_FUNCTION: return 1; // NOTE: maybe also check the args
    case EXPRESSION_KIND_OPERATOR: return 1 + solver_expression_degree(expression->operator.lhs) + solver_expression_degree(expression->operator.rhs);
    case EXPRESSION_KIND_PAREN: return 1 + solver_expression_degree(expression->paren.expr);
    }
}

static ds_result solver_expression_degree_min(ds_dynamic_array expressions, expression_t *expr) {
    ds_result result = DS_OK;

    int degree = INT_MAX;
    for (unsigned int i = 0; i < expressions.count; i++) {
        expression_t *item = NULL;
        DS_UNREACHABLE(ds_dynamic_array_get_ref(&expressions, i, (void **)&item));

        int new_degree = solver_expression_degree(item);
        if (new_degree < degree) {
            degree = new_degree;
            *expr = *item;
        }
    }

    if (expr == NULL) {
        DS_LOG_ERROR("No expression found with minimum degree");
        return_defer(DS_ERR);
    }

defer:
    return result;
}

static void show_path(ds_dynamic_array statements /* statement_t */, ds_dynamic_array parent /* parent_t */, expression_t *result) {
    int index = -1;
    if (!solver_find_mapping_index(parent, result, &index)) return;

    parent_t *p = NULL;
    DS_UNREACHABLE(ds_dynamic_array_get_ref(&parent, index, (void **)&p));

    statement_t *statement = NULL;
    DS_UNREACHABLE(ds_dynamic_array_get_ref(&statements, p->used, (void **)&statement));

    expression_t *next = p->prev;
    show_path(statements, parent, next);

    expression_printf(next);
    printf(" => ");
    expression_printf(result);
    printf(" (");
    statement_printf(statement);
    printf(")\n");
}

static void solver_build_steps(ds_dynamic_array parent /* pair_t */, expression_t *result, ds_dynamic_array *steps /* expression_t */) {
    int index = -1;
    if (!solver_find_mapping_index(parent, result, &index)) return;

    pair_t *kv = NULL;
    DS_UNREACHABLE(ds_dynamic_array_get_ref(&parent, index, (void **)&kv));

    expression_t *next = kv->value;
    solver_build_steps(parent, next, steps);

    DS_UNREACHABLE(ds_dynamic_array_append(steps, result));
}

ds_result solver_solve_eval(ds_dynamic_array statements /* statement_t */,
                            expression_t *eval, expression_t *solution,
                            ds_dynamic_array *steps /* expression_t */) {
    ds_result result = DS_OK;

    ds_dynamic_array visited = {0}; // expression_t
    ds_dynamic_array_init(&visited, sizeof(expression_t));

    ds_dynamic_array parent = {0}; // parent_t
    ds_dynamic_array_init(&parent, sizeof(parent_t));

    solver_solve_dfs(statements, eval, &visited, &parent);

    expression_t expr = {0};
    TRY(solver_expression_degree_min(visited, &expr));

    if (solution == NULL) {
        printf("Question: ");
        expression_printf(eval);
        printf("\n");
        show_path(statements, parent, &expr);
        printf("Response: ");
        expression_printf(&expr);
        printf("\n\n");
    } else {
        *solution = expr;
        if (steps != NULL) {
            ds_dynamic_array_init(steps, sizeof(expression_t));
            solver_build_steps(parent, &expr, steps);
        }
    }

defer:
    ds_dynamic_array_free(&visited);

    return result;
}

ds_result solver_solve_program(program_t *program) {
    ds_result result = DS_OK;

    for (unsigned int i = 0; i < program->evals.count; i++) {
        expression_t *eval = NULL;
        DS_UNREACHABLE(ds_dynamic_array_get_ref(&program->evals, i, (void **)&eval));
        TRY(solver_solve_eval(program->statements, eval, NULL, NULL));
    }

defer:
    return result;
}
