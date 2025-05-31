#include <assert.h>
#include <limits.h>
#include "solver.h"

// TODO: Maybe move this as a tuple data structure in ds.h
typedef struct pair_t {
    expression_t *key;
    expression_t *value;
} pair_t;

typedef struct parent_t {
    expression_t *expr; // The expression that was evaluated
    expression_t *prev; // The previous expression in the path
    int used;           // The index of the statement that was used to evaluate this expression
} parent_t;

static boolean solver_find_mapping(ds_dynamic_array mapping /* pair_t */, expression_t *key, int *index) {
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
    // TODO: implement a more sophisticated mapping algorithm

    if (reference->kind == EXPRESSION_KIND_NUMBER && expr->kind == EXPRESSION_KIND_NUMBER) {
        return ds_string_slice_equals(&reference->number.value, &expr->number.value);
    }

    if (reference->kind == EXPRESSION_KIND_FUNCTION && expr->kind == EXPRESSION_KIND_NUMBER) {
        // NOTE: we still need to check types

        pair_t kv = CLITERAL(pair_t){reference, expr};
        DS_UNREACHABLE(ds_dynamic_array_append(mapping, &kv));

        return true;
    }

    if (reference->kind == EXPRESSION_KIND_FUNCTION && expr->kind == EXPRESSION_KIND_FUNCTION) {
        // NOTE: here we need to check that the types are matching

        pair_t kv = CLITERAL(pair_t){reference, expr};
        DS_UNREACHABLE(ds_dynamic_array_append(mapping, &kv));

        return true;
    }

    if (reference->kind == EXPRESSION_KIND_FUNCTION && expr->kind == EXPRESSION_KIND_OPERATOR) {
        // NOTE: here we need to check that the types are matching

        if (reference->function.args.count > 0) {
            return false;
        }

        pair_t kv = CLITERAL(pair_t){reference, expr};
        DS_UNREACHABLE(ds_dynamic_array_append(mapping, &kv));

        return true;
    }

    if (reference->kind == EXPRESSION_KIND_FUNCTION && expr->kind == EXPRESSION_KIND_PAREN) {
        // NOTE: we still need to check types

        if (reference->function.args.count > 0) {
            // TODO: What to do when function has arguments?

            return false;
        }

        pair_t kv = CLITERAL(pair_t){reference, expr};
        DS_UNREACHABLE(ds_dynamic_array_append(mapping, &kv));

        return true;
    }

    if (reference->kind == EXPRESSION_KIND_OPERATOR && expr->kind == EXPRESSION_KIND_OPERATOR) {
        return ds_string_slice_equals(&reference->operator.value, &expr->operator.value)
            && solver_make_mapping(reference->operator.lhs, expr->operator.lhs, mapping)
            && solver_make_mapping(reference->operator.rhs, expr->operator.rhs, mapping);
    }

    if (reference->kind == EXPRESSION_KIND_PAREN && expr->kind == EXPRESSION_KIND_PAREN) {
        return solver_make_mapping(reference->paren.expr, expr->paren.expr, mapping);
    }

    return false;
}

static ds_result solver_apply_mapping(expression_t *solution, ds_dynamic_array mapping /* pair_t */, expression_t *substitution) {
    ds_result result = DS_OK;
    pair_t *kv = NULL;
    int index = -1;

    switch (solution->kind) {
    case EXPRESSION_KIND_SET:
        substitution->kind = EXPRESSION_KIND_SET;
        ds_dynamic_array_init(&substitution->set.items, sizeof(expression_t));
        for (unsigned int i = 0; i < solution->set.items.count; i++) {
            expression_t *item_i = NULL;
            DS_UNREACHABLE(ds_dynamic_array_get_ref(&solution->set.items, i, (void **)&item_i));

            expression_t item = {0};
            TRY(solver_apply_mapping(item_i, mapping, &item));
            DS_UNREACHABLE(ds_dynamic_array_append(&substitution->set.items, &item));
        }
        break;
    case EXPRESSION_KIND_NAME:
        if (!solver_find_mapping(mapping, solution, &index)) {
            return_defer(DS_ERR);
        }
        DS_UNREACHABLE(ds_dynamic_array_get_ref(&mapping, index, (void **)&kv));
        *substitution = *kv->value;
        break;
    case EXPRESSION_KIND_NUMBER:
        *substitution = *solution;
        break;
    case EXPRESSION_KIND_FUNCTION:
        if (!solver_find_mapping(mapping, solution, &index)) {
            return_defer(DS_ERR);
        }
        DS_UNREACHABLE(ds_dynamic_array_get_ref(&mapping, index, (void **)&kv));
        *substitution = *kv->value;
        break;
    case EXPRESSION_KIND_OPERATOR:
        substitution->kind = EXPRESSION_KIND_OPERATOR;
        substitution->operator.value = solution->operator.value;
        substitution->operator.lhs = DS_MALLOC(NULL, sizeof(expression_t));
        substitution->operator.rhs = DS_MALLOC(NULL, sizeof(expression_t));
        TRY(solver_apply_mapping(solution->operator.lhs, mapping, substitution->operator.lhs));
        TRY(solver_apply_mapping(solution->operator.rhs, mapping, substitution->operator.rhs));
        break;
    case EXPRESSION_KIND_PAREN:
        substitution->kind = EXPRESSION_KIND_PAREN;
        substitution->paren.expr = DS_MALLOC(NULL, sizeof(expression_t));
        TRY(solver_apply_mapping(solution->paren.expr, mapping, substitution->paren.expr));
        break;
    }

defer:
    return result;
}

static ds_result solver_substitute(expression_t *expr, statement_t *statement,
                        expression_t *substitution, expression_t *iter,
                        ds_dynamic_array *substitutions /* expression_t */,
                        ds_dynamic_array *mapping /* pair_t */) {
    // substitutions will contain the list of substitutions that can be made
    // "we can change `expr` to `substitution:substitutions` if `statement` is applied"

    ds_result result = DS_OK;

    if (statement->equality == NULL) {
        DS_LOG_ERROR("Statement has no equality");
        return_defer(DS_ERR);
    }

    expression_t reference = statement->equality->lhs;

    if (reference.kind == EXPRESSION_KIND_NUMBER && expr->kind == EXPRESSION_KIND_NUMBER) {
        if (ds_string_slice_equals(&reference.number.value, &expr->number.value)) {
            // If the reference is a number and the expression is also a number, we can directly substitute
            *iter = statement->equality->rhs;
            DS_UNREACHABLE(ds_dynamic_array_append(substitutions, substitution));
        }
    }

    if (reference.kind == EXPRESSION_KIND_FUNCTION && expr->kind == EXPRESSION_KIND_FUNCTION) {
        // TODO: typecheck

        if (reference.function.args.count == 0) {
            *iter = statement->equality->rhs;
            DS_UNREACHABLE(ds_dynamic_array_append(substitutions, substitution));
        } else {
            // If the reference is a function and the expression is also a function,
            // we can try to substitute the args of the function with the reference
            if (ds_string_slice_equals(&reference.function.value, &expr->function.value)) {
                if (reference.function.args.count == expr->function.args.count) {
                    boolean can_substitute = true;
                    for (unsigned int i = 0; i < reference.function.args.count; i++) {
                        expression_t *ref_arg = NULL;
                        DS_UNREACHABLE(ds_dynamic_array_get_ref(&reference.function.args, i, (void **)&ref_arg));

                        expression_t *expr_arg = NULL;
                        DS_UNREACHABLE(ds_dynamic_array_get_ref(&expr->function.args, i, (void **)&expr_arg));

                        if (!expression_equal(ref_arg, expr_arg)) {
                            can_substitute = false;
                            break;
                        }
                    }
                    if (can_substitute) {
                        // If all the args are equal, we can substitute the function
                        *iter = statement->equality->rhs;
                        DS_UNREACHABLE(ds_dynamic_array_append(substitutions, substitution));
                    }
                }
            }
        }
    }

    if (reference.kind == EXPRESSION_KIND_FUNCTION && expr->kind == EXPRESSION_KIND_OPERATOR) {
        // TODO: typecheck

        if (reference.function.args.count == 0) {
            // If the reference is a variable we can substitute the operator
            *iter = statement->equality->rhs;
            DS_UNREACHABLE(ds_dynamic_array_append(substitutions, substitution));
        }

        // We can also try to substitute the lhs and rhs of the operator with the reference
        iter->kind = EXPRESSION_KIND_OPERATOR;
        iter->operator.value = expr->operator.value;
        iter->operator.lhs = expr->operator.lhs;
        iter->operator.rhs = DS_MALLOC(NULL, sizeof(expression_t));
        TRY(solver_substitute(expr->operator.rhs, statement, substitution, iter->operator.rhs, substitutions, mapping));
    }

    if (reference.kind == EXPRESSION_KIND_FUNCTION && expr->kind == EXPRESSION_KIND_PAREN) {
        if (reference.function.args.count == 0) {
            ds_dynamic_array_clear(mapping);
            if (solver_make_mapping(&reference, expr, mapping)) {
                TRY(solver_apply_mapping(&statement->equality->rhs, *mapping, iter));
                DS_UNREACHABLE(ds_dynamic_array_append(substitutions, substitution));
            }
        }
    }

    if (reference.kind == EXPRESSION_KIND_OPERATOR && expr->kind == EXPRESSION_KIND_OPERATOR) {
        if (ds_string_slice_equals(&reference.operator.value, &expr->operator.value)) {
            ds_dynamic_array_clear(mapping);
            if (solver_make_mapping(&reference, expr, mapping)) {
                TRY(solver_apply_mapping(&statement->equality->rhs, *mapping, iter));
                DS_UNREACHABLE(ds_dynamic_array_append(substitutions, substitution));
            }
        }
    }

    if (reference.kind == EXPRESSION_KIND_PAREN && expr->kind == EXPRESSION_KIND_PAREN) {
        // If the reference is a parenthesis and the expression is also a parenthesis,
        // we can try to substitute the inner expression
        ds_dynamic_array_clear(mapping);
        if (solver_make_mapping(&reference, expr, mapping)) {
            TRY(solver_apply_mapping(&statement->equality->rhs, *mapping, iter));
            DS_UNREACHABLE(ds_dynamic_array_append(substitutions, substitution));
        }
    }

defer:
    return result;
}

static ds_result solver_solve_dfs(ds_dynamic_array statements /* statement_t */,
                                  expression_t *expression,
                                  ds_dynamic_array *visited /* expression_t */,
                                  ds_dynamic_array *parent /* parent_t */) {
    ds_result result = DS_OK;

    ds_dynamic_array mapping = {0}; // pair_t
    ds_dynamic_array_init(&mapping, sizeof(pair_t));

    ds_dynamic_array substitutions = {0}; // expression_t
    ds_dynamic_array_init(&substitutions, sizeof(expression_t));

    // Add the current expression to the visited list
    DS_UNREACHABLE(ds_dynamic_array_append(visited, expression));

    // Iterate through the statements and try to apply them to the current expression
    for (unsigned int i = 0; i < statements.count; i++) {
        // Get the current statement; skip if it has no equality
        statement_t *statement = NULL;
        DS_UNREACHABLE(ds_dynamic_array_get_ref(&statements, i, (void **)&statement));
        if (statement->equality == NULL) continue;

        // Generate all the possible substitutions for the current expression with the current statement
        expression_t iter = {0};
        ds_dynamic_array_clear(&substitutions);
        ds_dynamic_array_clear(&mapping);
        TRY(solver_substitute(expression, statement, &iter, &iter, &substitutions, &mapping));

        for (unsigned int j = 0; j < substitutions.count; j++) {
            expression_t *substitution = NULL;
            DS_UNREACHABLE(ds_dynamic_array_get_ref(&substitutions, j, (void **)&substitution));

            // Check if the substitution is already visited
            if (!solver_find_visited(visited, substitution)) {
                // Create a new expression to hold the evaluation result
                parent_t kv = {0};
                kv.expr = DS_MALLOC(NULL, sizeof(expression_t));
                DS_MEMCPY(kv.expr, substitution, sizeof(expression_t));
                kv.prev = DS_MALLOC(NULL, sizeof(expression_t));
                DS_MEMCPY(kv.prev, expression, sizeof(expression_t));
                kv.used = i;
                DS_UNREACHABLE(ds_dynamic_array_append(parent, &kv));

                TRY(solver_solve_dfs(statements, substitution, visited, parent));
            }
        }
    }

defer:
    ds_dynamic_array_free(&substitutions);

    return result;
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
    if (!solver_find_mapping(parent, result, &index)) return;

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
    if (!solver_find_mapping(parent, result, &index)) return;

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

    TRY(solver_solve_dfs(statements, eval, &visited, &parent));

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
