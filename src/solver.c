#include "limits.h"
#include "solver.h"

static boolean solver_find_mapping(ds_dynamic_array mapping /* pair_t */, expression_t *key, expression_t *value) {
    // NOTE: Ideally this would be implemented using hashmap, but I am too lazy
    // to write the hashing function for the expression, so I just use a
    // dynamic array for now.

    for (unsigned int i = 0; i < mapping.count; i++) {
        pair_t *kv = NULL;
        DS_UNREACHABLE(ds_dynamic_array_get_ref(&mapping, i, (void **)&kv));

        if (expression_equal(kv->key, key)) {
            *value = *(expression_t *)kv->value;
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

    if (reference->kind == EXPRESSION_KIND_PAREN && expr->kind == EXPRESSION_KIND_PAREN) {
        return solver_make_mapping(reference->paren.expr, expr->paren.expr, mapping);
    }

    if (reference->kind == EXPRESSION_KIND_OPERATOR && expr->kind == EXPRESSION_KIND_OPERATOR) {
        return ds_string_slice_equals(&reference->operator.value, &expr->operator.value)
            && solver_make_mapping(reference->operator.lhs, expr->operator.lhs, mapping)
            && solver_make_mapping(reference->operator.rhs, expr->operator.rhs, mapping);
    }

    if (reference->kind == EXPRESSION_KIND_FUNCTION && expr->kind == EXPRESSION_KIND_FUNCTION) {
        // NOTE: here we need to check that the types are matching

        pair_t kv = CLITERAL(pair_t){reference, expr};
        DS_UNREACHABLE(ds_dynamic_array_append(mapping, &kv));

        return true;
    }

    if (reference->kind == EXPRESSION_KIND_FUNCTION && expr->kind == EXPRESSION_KIND_NUMBER) {
        // NOTE: we still need to check types

        pair_t kv = CLITERAL(pair_t){reference, expr};
        DS_UNREACHABLE(ds_dynamic_array_append(mapping, &kv));

        return true;
    }

    if (reference->kind == EXPRESSION_KIND_FUNCTION && expr->kind == EXPRESSION_KIND_PAREN) {
        // NOTE: we still need to check types

        pair_t kv = CLITERAL(pair_t){reference, expr->paren.expr};
        DS_UNREACHABLE(ds_dynamic_array_append(mapping, &kv));

        return true;
    }

    if (reference->kind == EXPRESSION_KIND_NUMBER && expr->kind == EXPRESSION_KIND_NUMBER) {
        return ds_string_slice_equals(&reference->number.value, &expr->number.value);
    }

    return false;
}

static ds_result solver_substitute(expression_t *axiom, ds_dynamic_array mapping /* pair_t */, expression_t *eval) {
    ds_result result = DS_OK;

    switch (axiom->kind) {
    case EXPRESSION_KIND_SET:
        eval->kind = EXPRESSION_KIND_SET;
        ds_dynamic_array_init(&eval->set.items, sizeof(expression_t));
        for (unsigned int i = 0; i < axiom->set.items.count; i++) {
            expression_t *item_i = NULL;
            DS_UNREACHABLE(ds_dynamic_array_get_ref(&axiom->set.items, i, (void **)&item_i));

            expression_t item = {0};
            TRY(solver_substitute(item_i, mapping, &item));
            DS_UNREACHABLE(ds_dynamic_array_append(&eval->set.items, &item));
        }
        break;
    case EXPRESSION_KIND_NAME:
        if (!solver_find_mapping(mapping, axiom, eval)) {
            return_defer(DS_ERR);
        }
        break;
    case EXPRESSION_KIND_NUMBER:
        *eval = *axiom;
        break;
    case EXPRESSION_KIND_FUNCTION:
        if (!solver_find_mapping(mapping, axiom, eval)) {
            return_defer(DS_ERR);
        }
        break;
    case EXPRESSION_KIND_OPERATOR:
        eval->kind = EXPRESSION_KIND_OPERATOR;
        eval->operator.lhs = DS_MALLOC(NULL, sizeof(expression_t));
        eval->operator.rhs = DS_MALLOC(NULL, sizeof(expression_t));
        TRY(solver_substitute(axiom->operator.lhs, mapping, eval->operator.lhs));
        TRY(solver_substitute(axiom->operator.rhs, mapping, eval->operator.rhs));
        break;
    case EXPRESSION_KIND_PAREN:
        eval->kind = EXPRESSION_KIND_PAREN;
        eval->paren.expr = DS_MALLOC(NULL, sizeof(expression_t));
        TRY(solver_substitute(axiom->paren.expr, mapping, eval->paren.expr));
        break;
    }

defer:
    return result;
}

static ds_result solver_solve_dfs(ds_dynamic_array statements /* statement_t */,
                                  expression_t *expression,
                                  ds_dynamic_array *visited /* expression_t */,
                                  ds_dynamic_array *parent /* pair_t */) {
    ds_result result = DS_OK;
    ds_dynamic_array mapping = {0};
    ds_dynamic_array_init(&mapping, sizeof(pair_t));

    // Add the current expression to the visited list
    DS_UNREACHABLE(ds_dynamic_array_append(visited, expression));

    // Iterate through the statements and check if any of them can be applied
    for (unsigned int i = 0; i < statements.count; i++) {
        // Get the current statement; skip if it has no equality
        statement_t *statement = NULL;
        DS_UNREACHABLE(ds_dynamic_array_get_ref(&statements, i, (void **)&statement));
        if (statement->equality == NULL) continue;

        // Check if the left-hand side of the equality can be mapped to the current expression
        ds_dynamic_array_clear(&mapping);
        expression_t reference = statement->equality->lhs;
        if (!solver_make_mapping(&reference, expression, &mapping)) {
            ds_dynamic_array_free(&mapping);
            continue;
        }

        // Apply the mapping to the right-hand side of the equality
        expression_t solution = statement->equality->rhs;
        expression_t substitution = {0};
        TRY(solver_substitute(&solution, mapping, &substitution));

        // Check if the substitution is already visited
        if (!solver_find_visited(visited, &substitution)) {
            // Create a new expression to hold the evaluation result
            pair_t kv = {0};
            kv.key = DS_MALLOC(NULL, sizeof(expression_t));
            DS_MEMCPY(kv.key, &substitution, sizeof(expression_t));
            kv.value = DS_MALLOC(NULL, sizeof(expression_t));
            DS_MEMCPY(kv.value, expression, sizeof(expression_t));
            DS_UNREACHABLE(ds_dynamic_array_append(parent, &kv));

            TRY(solver_solve_dfs(statements, &substitution, visited, parent));
        }
    }

defer:
    ds_dynamic_array_free(&mapping);

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

static void show_path(ds_dynamic_array parent /* pair_t */, expression_t *result) {
    expression_t next = {0};
    if (!solver_find_mapping(parent, result, &next)) return;

    show_path(parent, &next);

    expression_printf(&next);
    printf(" => ");
    expression_printf(result);
    printf("\n");
}

static void solver_build_steps(ds_dynamic_array parent /* pair_t */, expression_t *result, ds_dynamic_array *steps /* expression_t */) {
    expression_t next = {0};
    if (!solver_find_mapping(parent, result, &next)) return;

    solver_build_steps(parent, &next, steps);

    DS_UNREACHABLE(ds_dynamic_array_append(steps, result));
}

ds_result solver_solve_eval(ds_dynamic_array statements /* statement_t */,
                            expression_t *eval, expression_t *solution,
                            ds_dynamic_array *steps /* expression_t */) {
    ds_result result = DS_OK;

    ds_dynamic_array visited = {0}; // expression_t
    ds_dynamic_array_init(&visited, sizeof(expression_t));

    ds_dynamic_array parent = {0}; // pair_t
    ds_dynamic_array_init(&parent, sizeof(pair_t));

    TRY(solver_solve_dfs(statements, eval, &visited, &parent));

    expression_t expr = {0};
    TRY(solver_expression_degree_min(visited, &expr));

    if (solution == NULL) {
        printf("The path is:\n");
        show_path(parent, &expr);

        printf("\nThe result is: ");
        expression_printf(&expr);
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
