#include "parser.h"

static token_t parser_read(parser_t *parser) {
    parser->tok = parser->next_tok;
    lexer_next(&parser->lexer, &parser->next_tok);

    return parser->tok;
}

ds_result parser_init(parser_t *parser, lexer_t lexer) {
    parser->lexer = lexer;

    parser_read(parser);
    parser_read(parser);

    return DS_OK;
}

boolean expression_equal(expression_t *expr1, expression_t *expr2) {
    if (expr1->kind == EXPRESSION_KIND_PAREN && expr2->kind == EXPRESSION_KIND_PAREN) {
        return expression_equal(expr1->paren.expr, expr2->paren.expr);
    }

    if (expr1->kind == EXPRESSION_KIND_OPERATOR && expr2->kind == EXPRESSION_KIND_OPERATOR) {
        return ds_string_slice_equals(&expr1->operator.value, &expr2->operator.value)
            && expression_equal(expr1->operator.lhs, expr2->operator.lhs)
            && expression_equal(expr1->operator.rhs, expr2->operator.rhs);
    }

    if (expr1->kind == EXPRESSION_KIND_FUNCTION && expr2->kind == EXPRESSION_KIND_FUNCTION) {
        boolean is_same_fun = ds_string_slice_equals(&expr1->function.value, &expr2->function.value);
        boolean is_same_len = expr1->function.args.count == expr2->function.args.count;

        if (!is_same_fun || !is_same_len) return false;
        for (unsigned int i = 0; i < expr1->function.args.count; i++) {
            expression_t *arg1_i = NULL;
            DS_UNREACHABLE(ds_dynamic_array_get_ref(&expr1->function.args, i, (void **)&arg1_i));

            expression_t *arg2_i = NULL;
            DS_UNREACHABLE(ds_dynamic_array_get_ref(&expr2->function.args, i, (void **)&arg2_i));

            if (!expression_equal(arg1_i, arg2_i)) {
                return false;
            }
        }

        return true;
    }

    if (expr1->kind == EXPRESSION_KIND_NUMBER && expr2->kind == EXPRESSION_KIND_NUMBER) {
        return ds_string_slice_equals(&expr1->number.value, &expr2->number.value);
    }

    if (expr1->kind == EXPRESSION_KIND_NAME && expr2->kind == EXPRESSION_KIND_NAME) {
        return ds_string_slice_equals(&expr1->name.value, &expr2->name.value);
    }

    if (expr1->kind == EXPRESSION_KIND_SET && expr2->kind == EXPRESSION_KIND_SET) {
        boolean is_same_len = expr1->set.items.count == expr2->set.items.count;

        if (!is_same_len) return false;
        for (unsigned int i = 0; i < expr1->set.items.count; i++) {
            expression_t *item1_i = NULL;
            DS_UNREACHABLE(ds_dynamic_array_get_ref(&expr1->set.items, i, (void **)&item1_i));

            expression_t *item2_i = NULL;
            DS_UNREACHABLE(ds_dynamic_array_get_ref(&expr2->set.items, i, (void **)&item2_i));

            if (!expression_equal(item1_i, item2_i)) {
                return false;
            }
        }

        return true;
    }

    return false;
}

static void type_dump(type_t *type) {
    printf(" :");

    for (unsigned int i = 0; i < type->names.count; i++) {
        ds_string_slice *name = NULL;
        DS_UNREACHABLE(ds_dynamic_array_get_ref(&type->names, i, (void **)&name));
        printf(" %.*s", (int)name->len, name->str);
        if (i + 1 < type->names.count) {
            printf(" ->");
        }
    }
}

static void define_dump(define_t *define) {
    switch (define->quantifier) {
    case QUANTIFIER_FORALL: printf("FORALL"); break;
    case QUANTIFIER_EXISTS: printf("EXISTS"); break;
    }

    printf(" %.*s", (int)define->name.len, define->name.str);

    type_dump(&define->type);

    printf("\n");
}

static void expression_set_dump(expression_set_t *set) {
    printf("<SET {");

    for (unsigned int i = 0; i < set->items.count; i++) {
        expression_t *arg_i = NULL;
        DS_UNREACHABLE(ds_dynamic_array_get_ref(&set->items, i, (void **)&arg_i));
        expression_dump(arg_i);

        if (i + 1 < set->items.count) printf(",");
    }

    printf("}>");
}

static void expression_name_dump(expression_name_t *name) {
    printf("<NAME %.*s>", (int)name->value.len, name->value.str);
}

static void expression_number_dump(expression_number_t *number) {
    printf("<NUMBER %.*s>", (int)number->value.len, number->value.str);
}

static void expression_function_dump(expression_function_t *function) {
    printf("<FUNCTION %.*s>", (int)function->value.len, function->value.str);

    if (function->args.count > 0) printf("(");
    for (unsigned int i = 0; i < function->args.count; i++) {
        expression_t *arg_i = NULL;
        DS_UNREACHABLE(ds_dynamic_array_get_ref(&function->args, i, (void **)&arg_i));
        expression_dump(arg_i);

        if (i + 1 < function->args.count) printf(",");
    }
    if (function->args.count > 0) printf(")");
}

static void expression_operator_dump(expression_operator_t *operator) {
    expression_dump(operator->lhs);

    printf(" <OPERATOR %.*s> ", (int)operator->value.len, operator->value.str);

    expression_dump(operator->rhs);
}

static void expression_paren_dump(expression_paren_t *paren) {
    printf(" <PAREN (");

    expression_dump(paren->expr);

    printf(")>");
}

void expression_dump(expression_t *expression) {
    switch (expression->kind) {
    case EXPRESSION_KIND_SET: return expression_set_dump(&expression->set);
    case EXPRESSION_KIND_NAME: return expression_name_dump(&expression->name);
    case EXPRESSION_KIND_NUMBER: return expression_number_dump(&expression->number);
    case EXPRESSION_KIND_FUNCTION: return expression_function_dump(&expression->function);
    case EXPRESSION_KIND_OPERATOR: return expression_operator_dump(&expression->operator);
    case EXPRESSION_KIND_PAREN: return expression_paren_dump(&expression->paren);
    }
}

static void equality_dump(equality_t *equality) {
    expression_dump(&equality->lhs);

    printf(" = ");

    expression_dump(&equality->rhs);

    printf("\n");
}

static void statement_dump(statement_t *statement) {
    for (unsigned int i = 0; i < statement->defines.count; i++) {
        define_t *define = NULL;
        DS_UNREACHABLE(ds_dynamic_array_get_ref(&statement->defines, i, (void **)&define));
        define_dump(define);
    }

    if (statement->equality != NULL) equality_dump(statement->equality);
}

void program_dump(program_t *program) {
    for (unsigned int i = 0; i < program->statements.count; i++) {
        statement_t *statement = NULL;
        DS_UNREACHABLE(ds_dynamic_array_get_ref(&program->statements, i, (void **)&statement));
        statement_dump(statement);
        printf("\n");
    }

    for (unsigned int i = 0; i < program->evals.count; i++) {
        expression_t *eval = NULL;
        DS_UNREACHABLE(ds_dynamic_array_get_ref(&program->evals, i, (void **)&eval));
        printf("eval: \n");
        expression_dump(eval);
        printf("\n\n");
    }
}

static void type_printf(type_t *type) {
    printf(" :");

    for (unsigned int i = 0; i < type->names.count; i++) {
        ds_string_slice *name = NULL;
        DS_UNREACHABLE(ds_dynamic_array_get_ref(&type->names, i, (void **)&name));
        printf(" %.*s", (int)name->len, name->str);
        if (i + 1 < type->names.count) {
            printf(" ->");
        }
    }
}

static void define_printf(define_t *define) {
    switch (define->quantifier) {
    case QUANTIFIER_FORALL: printf("forall"); break;
    case QUANTIFIER_EXISTS: printf("exists"); break;
    }

    printf(" %.*s", (int)define->name.len, define->name.str);

    type_printf(&define->type);
}

static void expression_set_printf(expression_set_t *set) {
    printf("{");

    for (unsigned int i = 0; i < set->items.count; i++) {
        expression_t *arg_i = NULL;
        DS_UNREACHABLE(ds_dynamic_array_get_ref(&set->items, i, (void **)&arg_i));
        expression_printf(arg_i);

        if (i + 1 < set->items.count) printf(", ");
    }

    printf("}");
}

static void expression_name_printf(expression_name_t *name) {
    printf("%.*s", (int)name->value.len, name->value.str);
}

static void expression_number_printf(expression_number_t *number) {
    printf("%.*s", (int)number->value.len, number->value.str);
}

static void expression_function_printf(expression_function_t *function) {
    printf("%.*s", (int)function->value.len, function->value.str);

    if (function->args.count > 0) printf("(");
    for (unsigned int i = 0; i < function->args.count; i++) {
        expression_t *arg_i = NULL;
        DS_UNREACHABLE(ds_dynamic_array_get_ref(&function->args, i, (void **)&arg_i));
        expression_printf(arg_i);

        if (i + 1 < function->args.count) printf(", ");
    }
    if (function->args.count > 0) printf(")");
}

static void expression_operator_printf(expression_operator_t *operator) {
    expression_printf(operator->lhs);

    printf(" %.*s ", (int)operator->value.len, operator->value.str);

    expression_printf(operator->rhs);
}

static void expression_paren_printf(expression_paren_t *paren) {
    printf("(");

    expression_printf(paren->expr);

    printf(")");
}

void expression_printf(expression_t *expression) {
    switch (expression->kind) {
    case EXPRESSION_KIND_SET: return expression_set_printf(&expression->set);
    case EXPRESSION_KIND_NAME: return expression_name_printf(&expression->name);
    case EXPRESSION_KIND_NUMBER: return expression_number_printf(&expression->number);
    case EXPRESSION_KIND_FUNCTION: return expression_function_printf(&expression->function);
    case EXPRESSION_KIND_OPERATOR: return expression_operator_printf(&expression->operator);
    case EXPRESSION_KIND_PAREN: return expression_paren_printf(&expression->paren);
    }
}

static void equality_printf(equality_t *equality) {
    expression_printf(&equality->lhs);
    printf(" = ");
    expression_printf(&equality->rhs);
}

void statement_printf(statement_t *statement) {
    for (unsigned int i = 0; i < statement->defines.count; i++) {
        define_t *define = NULL;
        DS_UNREACHABLE(ds_dynamic_array_get_ref(&statement->defines, i, (void **)&define));
        define_printf(define);
        if (i + 1 < statement->defines.count) {
            printf(", ");
        }
    }

    if (statement->defines.count > 0) {
        printf(" => ");
    }

    if (statement->equality != NULL) {
        equality_printf(statement->equality);
    }
}

static ds_result parser_parse_type(parser_t *parser, type_t *type) {
    ds_result result = DS_OK;
    token_t token = {0};

    ds_dynamic_array_init(&type->names, sizeof(ds_string_slice));

    while (true) {
        token = parser->tok;
        if (token.kind != TOKEN_SET) {
            int line, column;
            lexer_pos_to_lc(&parser->lexer, token.pos, &line, &column);
            DS_LOG_ERROR("Expected a Set but found %s at %d:%d", token_kind_to_string(token.kind), line, column);
            return_defer(DS_ERR);
        }
        DS_UNREACHABLE(ds_dynamic_array_append(&type->names, &token.value));

        token = parser_read(parser);
        if (token.kind != TOKEN_ARROW) {
            break;
        }

        token = parser_read(parser);
    }

defer:
    return result;
}

static ds_result parser_parse_define(parser_t *parser, define_t *define) {
    ds_result result = DS_OK;
    token_t token = {0};

    token = parser->tok;
    if (token.kind == TOKEN_FORALL) {
        define->quantifier = QUANTIFIER_FORALL;
    } else if (token.kind == TOKEN_EXISTS) {
        define->quantifier = QUANTIFIER_EXISTS;
    } else {
        int line, column;
        lexer_pos_to_lc(&parser->lexer, token.pos, &line, &column);
        DS_LOG_ERROR("Expected a quantifier (`forall` or `exists`) but found %s at %d:%d", token_kind_to_string(token.kind), line, column);
        return_defer(DS_ERR);
    }

    token = parser_read(parser);
    if (token.kind != TOKEN_NAME && token.kind != TOKEN_OPERATOR) {
        int line, column;
        lexer_pos_to_lc(&parser->lexer, token.pos, &line, &column);
        DS_LOG_ERROR("Expected a name or an operator but found %s at %d:%d", token_kind_to_string(token.kind), line, column);
        return_defer(DS_ERR);
    }
    define->name = token.value;

    token = parser_read(parser);
    if (token.kind != TOKEN_COLON) {
        int line, column;
        lexer_pos_to_lc(&parser->lexer, token.pos, &line, &column);
        DS_LOG_ERROR("Expected a `:` but found %s at %d:%d", token_kind_to_string(token.kind), line, column);
        return_defer(DS_ERR);
    }

    token = parser_read(parser);
    if (parser_parse_type(parser, &define->type) != DS_OK) {
        // TODO: recover from error
        return_defer(DS_ERR);
    }

defer:
    return result;
}

static ds_result parser_parse_defines(parser_t *parser, ds_dynamic_array *defines /* define_t */) {
    ds_result result = DS_OK;
    token_t token = {0};

    while (true) {
        token = parser->tok;
        if (token.kind == TOKEN_FORALL || token.kind == TOKEN_EXISTS) {
            define_t define = {0};
            parser_parse_define(parser, &define);
            DS_UNREACHABLE(ds_dynamic_array_append(defines, &define));
        } else {
            break;
        }

        if (parser->tok.kind != TOKEN_COMMA) {
            break;
        }

        token = parser_read(parser);
    }

    return_defer(DS_OK);

defer:
    return result;
}

static ds_result parser_parse_expression(parser_t *parser, expression_t *expression) {
    ds_result result = DS_OK;
    token_t token = {0};

    token = parser->tok;
    if (token.kind == TOKEN_NUMBER) {
        expression_number_t number = CLITERAL(expression_number_t){token.value};
        token = parser_read(parser);

        if (token.kind == TOKEN_OPERATOR) {
            expression->kind = EXPRESSION_KIND_OPERATOR;
            expression->operator = CLITERAL(expression_operator_t){token.value, NULL, NULL};

            expression->operator.lhs = DS_MALLOC(NULL, sizeof(expression_t));
            if (expression->operator.lhs == NULL) DS_PANIC(DS_ERROR_OOM);
            expression->operator.lhs->kind = EXPRESSION_KIND_NUMBER;
            expression->operator.lhs->number = number;

            parser_read(parser);

            expression->operator.rhs = DS_MALLOC(NULL, sizeof(expression_t));
            if (expression->operator.rhs == NULL) DS_PANIC(DS_ERROR_OOM);
            TRY(parser_parse_expression(parser, expression->operator.rhs));
        } else {
            expression->kind = EXPRESSION_KIND_NUMBER;
            expression->number = number;
        }
    } else if (token.kind == TOKEN_NAME) {
        expression_function_t function = CLITERAL(expression_function_t){token.value, {0}};
        ds_dynamic_array_init(&function.args, sizeof(expression_t));
        token = parser_read(parser);

        if (token.kind == TOKEN_LPAREN) {
            do {
                token = parser_read(parser);

                expression_t arg = {0};
                TRY(parser_parse_expression(parser, &arg));

                DS_UNREACHABLE(ds_dynamic_array_append(&function.args, &arg));

                token = parser->tok;
                if (token.kind == TOKEN_COMMA) {
                    continue;
                } else if (token.kind == TOKEN_RPAREN) {
                    break;
                } else {
                    int line, column;
                    lexer_pos_to_lc(&parser->lexer, token.pos, &line, &column);
                    DS_LOG_ERROR("Expected `,` or `)` but found %s at %d:%d", token_kind_to_string(token.kind), line, column);
                    return_defer(DS_ERR);
                }
            } while (true);

            token = parser_read(parser);
        }

        if (token.kind == TOKEN_OPERATOR) {
            expression->kind = EXPRESSION_KIND_OPERATOR;
            expression->operator = CLITERAL(expression_operator_t){token.value, NULL, NULL};

            expression->operator.lhs = DS_MALLOC(NULL, sizeof(expression_t));
            if (expression->operator.lhs == NULL) DS_PANIC(DS_ERROR_OOM);
            expression->operator.lhs->kind = EXPRESSION_KIND_FUNCTION;
            expression->operator.lhs->function = function;

            parser_read(parser);

            expression->operator.rhs = DS_MALLOC(NULL, sizeof(expression_t));
            if (expression->operator.rhs == NULL) DS_PANIC(DS_ERROR_OOM);
            TRY(parser_parse_expression(parser, expression->operator.rhs));
        } else {
            expression->kind = EXPRESSION_KIND_FUNCTION;
            expression->function = function;
        }
    } else if (token.kind == TOKEN_SET) {
        expression_name_t name = CLITERAL(expression_name_t){token.value};
        token = parser_read(parser);

        expression->kind = EXPRESSION_KIND_NAME;
        expression->name = name;
    } else if (token.kind == TOKEN_LBRACE) {
        expression_set_t set = CLITERAL(expression_set_t){{0}};
        ds_dynamic_array_init(&set.items, sizeof(expression_t));

        do {
            token = parser_read(parser);

            expression_t item = {0};
            TRY(parser_parse_expression(parser, &item));

            DS_UNREACHABLE(ds_dynamic_array_append(&set.items, &item));

            token = parser->tok;
            if (token.kind == TOKEN_COMMA) {
                continue;
            } else if (token.kind == TOKEN_RBRACE) {
                break;
            } else {
                int line, column;
                lexer_pos_to_lc(&parser->lexer, token.pos, &line, &column);
                DS_LOG_ERROR("Expected `,` or `}` but found %s at %d:%d", token_kind_to_string(token.kind), line, column);
                return_defer(DS_ERR);
            }
        } while (true);

        token = parser_read(parser);

        expression->kind = EXPRESSION_KIND_SET;
        expression->set = set;
    } else if (token.kind == TOKEN_LPAREN) {
        expression_paren_t paren = CLITERAL(expression_paren_t){NULL};
        paren.expr = DS_MALLOC(NULL, sizeof(expression_t));
        token = parser_read(parser);

        TRY(parser_parse_expression(parser, paren.expr));

        token = parser->tok;
        if (token.kind != TOKEN_RPAREN) {
            int line, column;
            lexer_pos_to_lc(&parser->lexer, token.pos, &line, &column);
            DS_LOG_ERROR("Expected `)` but found %s at %d:%d", token_kind_to_string(token.kind), line, column);
            return_defer(DS_ERR);
        }
        token = parser_read(parser);

        if (token.kind == TOKEN_OPERATOR) {
            expression->kind = EXPRESSION_KIND_OPERATOR;
            expression->operator = CLITERAL(expression_operator_t){token.value, NULL, NULL};

            expression->operator.lhs = DS_MALLOC(NULL, sizeof(expression_t));
            if (expression->operator.lhs == NULL) DS_PANIC(DS_ERROR_OOM);
            expression->operator.lhs->kind = EXPRESSION_KIND_PAREN;
            expression->operator.lhs->paren = paren;

            parser_read(parser);

            expression->operator.rhs = DS_MALLOC(NULL, sizeof(expression_t));
            if (expression->operator.rhs == NULL) DS_PANIC(DS_ERROR_OOM);
            TRY(parser_parse_expression(parser, expression->operator.rhs));
        } else {
            expression->kind = EXPRESSION_KIND_PAREN;
            expression->paren = paren;
        }
    } else {
        int line, column;
        lexer_pos_to_lc(&parser->lexer, token.pos, &line, &column);
        DS_LOG_ERROR("Expected `{`, `(`, a symbol, a function, or a name but found %s at %d:%d", token_kind_to_string(token.kind), line, column);
        return_defer(DS_ERR);
    }

defer:
    return result;
}

static ds_result parser_parse_equality(parser_t *parser, equality_t *equality) {
    ds_result result = DS_OK;
    token_t token = {0};

    if (parser_parse_expression(parser, &equality->lhs) != DS_OK) {
        // TODO: recover from error
        return_defer(DS_ERR);
    }

    token = parser->tok;
    if (token.kind != TOKEN_EQUAL) {
        int line, column;
        lexer_pos_to_lc(&parser->lexer, token.pos, &line, &column);
        DS_LOG_ERROR("Expected `=` but found %s at %d:%d", token_kind_to_string(token.kind), line, column);
        return_defer(1);
    }
    token = parser_read(parser);

    if (parser_parse_expression(parser, &equality->rhs) != DS_OK) {
        // TODO: recover from error
        return_defer(DS_ERR);
    }

defer:
    return result;
}

static ds_result parser_parse_statement(parser_t *parser, statement_t *statement) {
    ds_result result = DS_OK;
    token_t token = {0};

    ds_dynamic_array_init(&statement->defines, sizeof(define_t));
    statement->equality = NULL;

    if (parser_parse_defines(parser, &statement->defines) != DS_OK) {
        // TODO: recover from error
        return_defer(DS_ERR);
    }

    boolean parse_equality = false;
    if (statement->defines.count == 0) {
        parse_equality = true;
    } else {
        token = parser->tok;
        if (token.kind == TOKEN_THEN) {
            token = parser_read(parser);
            parse_equality = true;
        }
    }

    if (parse_equality) {
        statement->equality = DS_MALLOC(NULL, sizeof(equality_t));
        if (statement->equality == NULL) DS_PANIC(DS_ERROR_OOM);
        if (parser_parse_equality(parser, statement->equality) != DS_OK) {
            // TODO: recover from error
            return_defer(DS_ERR);
        }
    }

defer:
    return result;
}

ds_result parser_parse_program(parser_t *parser, program_t *program) {
    ds_result result = DS_OK;
    ds_dynamic_array_init(&program->statements, sizeof(statement_t));
    ds_dynamic_array_init(&program->evals, sizeof(expression_t));

    while (true) {
        token_t token = parser->tok;

        if (token.kind == TOKEN_EOF) {
            break;
        }

        if (token.kind == TOKEN_EVAL) {
            token = parser_read(parser);

            expression_t eval = {0};
            TRY(parser_parse_expression(parser, &eval));
            DS_UNREACHABLE(ds_dynamic_array_append(&program->evals, &eval));
        } else if (token.kind == TOKEN_PROOF) {
            token = parser_read(parser);

            statement_t statement = {0};
            TRY(parser_parse_statement(parser, &statement));

            // printf("proof: \n");
            // statement_dump(&statement);
            // printf("\n\n");
        } else {
            statement_t statement = {0};
            if (parser_parse_statement(parser, &statement) != DS_OK) {
                // TODO: recover from error
                return_defer(DS_ERR);
            }
            DS_UNREACHABLE(ds_dynamic_array_append(&program->statements, &statement));
        }
    }

defer:
    return result;
}
