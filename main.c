#include <limits.h>
#include <string.h>
#define DS_IO_IMPLEMENTATION
#include "ds.h"
#include <stdio.h>

#define CLITERAL(type) (type)

#define TOKEN_SYMBOL_CH "+-*/=<>"

typedef enum token_kind_t {
    TOKEN_EOF,
    TOKEN_ILLEGAL,
    TOKEN_LBRACE,
    TOKEN_RBRACE,
    TOKEN_LPAREN,
    TOKEN_RPAREN,
    TOKEN_COMMA,
    TOKEN_COLON,
    TOKEN_ARROW,
    TOKEN_EQUAL,
    TOKEN_THEN,
    TOKEN_OPERATOR,
    TOKEN_NUMBER,
    TOKEN_SET,
    TOKEN_NAME,
    TOKEN_FORALL,
    TOKEN_EXISTS,
    TOKEN_EVAL,
    TOKEN_PROOF,
} token_kind_t;

static const char* token_kind_to_string(token_kind_t kind) {
    switch (kind) {
    case TOKEN_EOF: return "<EOF>";
    case TOKEN_ILLEGAL: return "ILLEGAL";
    case TOKEN_LBRACE: return "{";
    case TOKEN_RBRACE: return "}";
    case TOKEN_LPAREN: return "(";
    case TOKEN_RPAREN: return ")";
    case TOKEN_COMMA: return ",";
    case TOKEN_COLON: return ":";
    case TOKEN_ARROW: return "->";
    case TOKEN_EQUAL: return "=";
    case TOKEN_THEN: return "=>";
    case TOKEN_OPERATOR: return "OPERATOR";
    case TOKEN_NUMBER: return "NUMBER";
    case TOKEN_SET: return "SET";
    case TOKEN_NAME: return "NAME";
    case TOKEN_FORALL: return "FORALL";
    case TOKEN_EXISTS: return "EXISTS";
    case TOKEN_EVAL: return "EVAL";
    case TOKEN_PROOF: return "PROOF";
    }
}

typedef struct token_t {
    token_kind_t kind;
    ds_string_slice value;
    unsigned int pos;
} token_t;

static void token_printf(token_t token) {
    printf("%s", token_kind_to_string(token.kind));
    if (token.value.len > 0) {
        printf("(%.*s)", (int)token.value.len, token.value.str);
    }
    printf("\n");
}

typedef struct lexer_t {
    ds_string_slice buffer;
    unsigned int pos;
    unsigned int read_pos;
    char ch;
} lexer_t;

static char lexer_peek_ch(lexer_t *lexer) {
    if (lexer->read_pos >= lexer->buffer.len) {
        return EOF;
    }

    return lexer->buffer.str[lexer->read_pos];
}

static char lexer_read(lexer_t *lexer) {
    lexer->ch = lexer_peek_ch(lexer);

    lexer->pos = lexer->read_pos;
    lexer->read_pos += 1;

    return lexer->ch;
}

static int lexer_init(lexer_t *lexer, ds_string_slice buffer) {
    lexer->buffer = buffer;
    lexer->pos = 0;
    lexer->read_pos = 0;
    lexer->ch = 0;

    lexer_read(lexer);

    return 0;
}

static void lexer_skip_whitespace(lexer_t *lexer) {
    while (isspace(lexer->ch)) {
        lexer_read(lexer);
    }
}

static boolean issymbol(char ch) {
    return strchr(TOKEN_SYMBOL_CH, ch) != NULL;
}

static int lexer_tokenize_symbol(lexer_t *lexer, token_t *token) {
    int result = 0;
    unsigned int position = lexer->pos;

    if (!issymbol(lexer->ch)) {
        DS_LOG_ERROR("Failed to parse symbol: expected [symbol] but got '%c'", lexer->ch);
        return_defer(1);
    }

    ds_string_slice slice = { .str = (char *)lexer->buffer.str + lexer->pos, .len = 0 };
    while (issymbol(lexer->ch)) {
        slice.len += 1;
        lexer_read(lexer);
    }

    if (ds_string_slice_equals(&slice, &DS_STRING_SLICE("->"))) {
        *token = CLITERAL(token_t){TOKEN_ARROW, {0}, position};
    } else if (ds_string_slice_equals(&slice, &DS_STRING_SLICE("="))) {
        *token = CLITERAL(token_t){TOKEN_EQUAL, {0}, position};
    } else if (ds_string_slice_equals(&slice, &DS_STRING_SLICE("=>"))) {
        *token = CLITERAL(token_t){TOKEN_THEN, {0}, position};
    } else {
        *token = CLITERAL(token_t){TOKEN_OPERATOR, slice, position};
    }

defer:
    return result;
}

static int lexer_tokenize_number(lexer_t *lexer, token_t *token) {
    int result = 0;
    unsigned int position = lexer->pos;

    if (!isdigit(lexer->ch)) {
        DS_LOG_ERROR("Failed to parse number: expected [0-9] but got '%c'", lexer->ch);
        return_defer(1);
    }

    ds_string_slice slice = { .str = (char *)lexer->buffer.str + lexer->pos, .len = 0 };
    while (isdigit(lexer->ch)) {
        slice.len += 1;
        lexer_read(lexer);
    }

    *token = CLITERAL(token_t){TOKEN_NUMBER, slice, position};

defer:
    return result;
}

static int lexer_tokenize_set(lexer_t *lexer, token_t *token) {
    int result = 0;
    unsigned int position = lexer->pos;

    if (!isupper(lexer->ch)) {
        DS_LOG_ERROR("Failed to parse set: expected [A-Z] but got '%c'", lexer->ch);
        return_defer(1);
    }

    ds_string_slice slice = { .str = (char *)lexer->buffer.str + lexer->pos, .len = 0 };
    while (isalnum(lexer->ch)) {
        slice.len += 1;
        lexer_read(lexer);
    }

    *token = CLITERAL(token_t){TOKEN_SET, slice, position};

defer:
    return result;
}

static int lexer_tokenize_name(lexer_t *lexer, token_t *token) {
    int result = 0;
    unsigned int position = lexer->pos;

    if (!islower(lexer->ch)) {
        DS_LOG_ERROR("Failed to parse name: expected [a-z] but got '%c'", lexer->ch);
        return_defer(1);
    }

    ds_string_slice slice = { .str = (char *)lexer->buffer.str + lexer->pos, .len = 0 };
    while (isalnum(lexer->ch)) {
        slice.len += 1;
        lexer_read(lexer);
    }

    if (ds_string_slice_equals(&slice, &DS_STRING_SLICE("forall"))) {
        *token = CLITERAL(token_t){TOKEN_FORALL, {0}, position};
    } else if (ds_string_slice_equals(&slice, &DS_STRING_SLICE("exists"))) {
        *token = CLITERAL(token_t){TOKEN_EXISTS, {0}, position};
    } else if (ds_string_slice_equals(&slice, &DS_STRING_SLICE("eval"))) {
        *token = CLITERAL(token_t){TOKEN_EVAL, {0}, position};
    } else if (ds_string_slice_equals(&slice, &DS_STRING_SLICE("proof"))) {
        *token = CLITERAL(token_t){TOKEN_PROOF, {0}, position};
    } else {
        *token = CLITERAL(token_t){TOKEN_NAME, slice, position};
    }

defer:
    return result;
}

static int lexer_next(lexer_t *lexer, token_t *token) {
    int result = 0;
    lexer_skip_whitespace(lexer);

    unsigned int position = lexer->pos;
    if (lexer->ch == EOF) {
        lexer_read(lexer);
        *token = CLITERAL(token_t){TOKEN_EOF, {0}, position};
        return_defer(0);
    } else if (lexer->ch == '{') {
        lexer_read(lexer);
        *token = CLITERAL(token_t){TOKEN_LBRACE, {0}, position};
        return_defer(0);
    } else if (lexer->ch == '}') {
        lexer_read(lexer);
        *token = CLITERAL(token_t){TOKEN_RBRACE, {0}, position};
        return_defer(0);
    } else if (lexer->ch == '(') {
        lexer_read(lexer);
        *token = CLITERAL(token_t){TOKEN_LPAREN, {0}, position};
        return_defer(0);
    } else if (lexer->ch == ')') {
        lexer_read(lexer);
        *token = CLITERAL(token_t){TOKEN_RPAREN, {0}, position};
        return_defer(0);
    } else if (lexer->ch == ',') {
        lexer_read(lexer);
        *token = CLITERAL(token_t){TOKEN_COMMA, {0}, position};
        return_defer(0);
    } else if (lexer->ch == ':') {
        lexer_read(lexer);
        *token = CLITERAL(token_t){TOKEN_COLON, {0}, position};
        return_defer(0);
    } else if (issymbol(lexer->ch)) {
        return_defer(lexer_tokenize_symbol(lexer, token));
    } else if (isdigit(lexer->ch)) {
        return_defer(lexer_tokenize_number(lexer, token));
    } else if (isupper(lexer->ch)) {
        return_defer(lexer_tokenize_set(lexer, token));
    } else if (islower(lexer->ch)) {
        return_defer(lexer_tokenize_name(lexer, token));
    } else {
        ds_string_slice slice = { .str = (char *)lexer->buffer.str + lexer->pos, .len = 1 };

        lexer_read(lexer);
        *token = CLITERAL(token_t){TOKEN_ILLEGAL, slice, position};
        return_defer(0);
    }

defer:
    return result;
}

static int lexer_pos_to_lc(lexer_t *lexer, unsigned int pos, int *line, int *column) {
    int result = 0;
    int n = (pos > lexer->buffer.len) ? lexer->buffer.len : pos;

    *line = 1;
    *column = 1;

    for (int i = 0; i < n; i++) {
        if (lexer->buffer.str[i] == '\n') {
            *line += 1;
            *column = 0;
        } else {
            *column += 1;
        }
    }

    return result;
}


static void lexer_free(lexer_t *lexer) {
    lexer->pos = 0;
    lexer->read_pos = 0;
    lexer->ch = 0;
}

typedef struct parser_t {
    lexer_t lexer;
    token_t tok;
    token_t next_tok;
} parser_t;

static token_t parser_read(parser_t *parser) {
    parser->tok = parser->next_tok;
    lexer_next(&parser->lexer, &parser->next_tok);

    return parser->tok;
}

static int parser_init(parser_t *parser, lexer_t lexer) {
    parser->lexer = lexer;

    parser_read(parser);
    parser_read(parser);

    return 0;
}

typedef enum quantifier_t {
    QUANTIFIER_FORALL,
    QUANTIFIER_EXISTS,
} quantifier_t;

typedef struct type_t {
    ds_dynamic_array names; /* ds_string_slice */
} type_t;

typedef struct define_t {
    quantifier_t quantifier;
    ds_string_slice name;
    type_t type;
} define_t;

typedef enum expression_kind_t {
    EXPRESSION_KIND_SET,
    EXPRESSION_KIND_NAME,
    EXPRESSION_KIND_NUMBER,
    EXPRESSION_KIND_FUNCTION,
    EXPRESSION_KIND_OPERATOR,
    EXPRESSION_KIND_PAREN,
} expression_kind_t;

typedef struct expression_set_t {
    ds_dynamic_array items; /* expression_t */
} expression_set_t;

typedef struct expression_name_t {
    ds_string_slice value;
} expression_name_t;

typedef struct expression_number_t {
    ds_string_slice value;
} expression_number_t;

typedef struct expression_function_t {
    ds_string_slice value;
    ds_dynamic_array args; /* expression_t */
} expression_function_t;

typedef struct expression_operator_t {
    ds_string_slice value;
    struct expression_t *lhs;
    struct expression_t *rhs;
} expression_operator_t;

typedef struct expression_paren_t {
    struct expression_t *expr;
} expression_paren_t;

typedef struct expression_t {
    expression_kind_t kind;
    union {
        expression_set_t set;
        expression_name_t name;
        expression_number_t number;
        expression_function_t function;
        expression_operator_t operator;
        expression_paren_t paren;
    };
} expression_t;

typedef struct equality_t {
    expression_t lhs;
    expression_t rhs;
} equality_t;

typedef struct statement_t {
    ds_dynamic_array defines; /* define_t */
    equality_t *equality;
} statement_t;

typedef struct program_t {
    ds_dynamic_array statements; /* statement_t */
    ds_dynamic_array evals; /* expression_t */
} program_t;

static boolean expression_equal(expression_t *expr1, expression_t *expr2) {
    if (expr1->kind == EXPRESSION_KIND_PAREN && expr1->kind == EXPRESSION_KIND_PAREN) {
        return expression_equal(expr1->paren.expr, expr2->paren.expr);
    }

    if (expr1->kind == EXPRESSION_KIND_OPERATOR && expr2->kind == EXPRESSION_KIND_OPERATOR) {
        return ds_string_slice_equals(&expr1->operator.value, &expr2->operator.value)
            && expression_equal(expr1->operator.lhs, expr2->operator.lhs)
            && expression_equal(expr2->operator.rhs, expr2->operator.rhs);
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

static void expression_dump(expression_t *expression);

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

static void expression_dump(expression_t *expression) {
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

static void program_dump(program_t *program) {
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

static void expression_printf(expression_t *expression);

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

static void expression_printf(expression_t *expression) {
    switch (expression->kind) {
    case EXPRESSION_KIND_SET: return expression_set_printf(&expression->set);
    case EXPRESSION_KIND_NAME: return expression_name_printf(&expression->name);
    case EXPRESSION_KIND_NUMBER: return expression_number_printf(&expression->number);
    case EXPRESSION_KIND_FUNCTION: return expression_function_printf(&expression->function);
    case EXPRESSION_KIND_OPERATOR: return expression_operator_printf(&expression->operator);
    case EXPRESSION_KIND_PAREN: return expression_paren_printf(&expression->paren);
    }
}

static int parser_parse_type(parser_t *parser, type_t *type) {
    int result = 0;
    token_t token = {0};

    ds_dynamic_array_init(&type->names, sizeof(ds_string_slice));

    while (true) {
        token = parser->tok;
        if (token.kind != TOKEN_SET) {
            int line, column;
            lexer_pos_to_lc(&parser->lexer, token.pos, &line, &column);
            DS_LOG_ERROR("Expected a Set but found %s at %d:%d", token_kind_to_string(token.kind), line, column);
            return_defer(1);
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

static int parser_parse_define(parser_t *parser, define_t *define) {
    int result = 0;
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
        return_defer(1);
    }

    token = parser_read(parser);
    if (token.kind != TOKEN_NAME && token.kind != TOKEN_OPERATOR) {
        int line, column;
        lexer_pos_to_lc(&parser->lexer, token.pos, &line, &column);
        DS_LOG_ERROR("Expected a name or an operator but found %s at %d:%d", token_kind_to_string(token.kind), line, column);
        return_defer(1);
    }
    define->name = token.value;

    token = parser_read(parser);
    if (token.kind != TOKEN_COLON) {
        int line, column;
        lexer_pos_to_lc(&parser->lexer, token.pos, &line, &column);
        DS_LOG_ERROR("Expected a `:` but found %s at %d:%d", token_kind_to_string(token.kind), line, column);
        return_defer(1);
    }

    token = parser_read(parser);
    if (parser_parse_type(parser, &define->type) != 0) {
        // TODO: recover from error
        return_defer(1);
    }

defer:
    return result;
}

static int parser_parse_defines(parser_t *parser, ds_dynamic_array *defines /* define_t */) {
    int result = 0;
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

    return_defer(0);

defer:
    return result;
}

static int parser_parse_expression(parser_t *parser, expression_t *expression) {
    int result = 0;
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
            if (parser_parse_expression(parser, expression->operator.rhs) != 0) {
                return_defer(1);
            }
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
                if (parser_parse_expression(parser, &arg) != 0) {
                    return_defer(1);
                }

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
                    return_defer(1);
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
            if (parser_parse_expression(parser, expression->operator.rhs) != 0) {
                return_defer(1);
            }
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
            if (parser_parse_expression(parser, &item) != 0) {
                return_defer(1);
            }

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
                return_defer(1);
            }
        } while (true);

        token = parser_read(parser);

        expression->kind = EXPRESSION_KIND_SET;
        expression->set = set;
    } else if (token.kind == TOKEN_LPAREN) {
        expression_paren_t paren = CLITERAL(expression_paren_t){NULL};
        paren.expr = DS_MALLOC(NULL, sizeof(expression_t));
        token = parser_read(parser);

        if (parser_parse_expression(parser, paren.expr) != 0) {
            return_defer(1);
        }

        token = parser->tok;
        if (token.kind != TOKEN_RPAREN) {
            int line, column;
            lexer_pos_to_lc(&parser->lexer, token.pos, &line, &column);
            DS_LOG_ERROR("Expected `)` but found %s at %d:%d", token_kind_to_string(token.kind), line, column);
            return_defer(1);
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
            if (parser_parse_expression(parser, expression->operator.rhs) != 0) {
                return_defer(1);
            }
        } else {
            expression->kind = EXPRESSION_KIND_PAREN;
            expression->paren = paren;
        }
    } else {
        int line, column;
        lexer_pos_to_lc(&parser->lexer, token.pos, &line, &column);
        DS_LOG_ERROR("Expected `{`, `(`, a symbol, a function, or a name but found %s at %d:%d", token_kind_to_string(token.kind), line, column);
        return_defer(1);
    }

defer:
    return result;
}

static int parser_parse_equality(parser_t *parser, equality_t *equality) {
    int result = 0;
    token_t token = {0};

    if (parser_parse_expression(parser, &equality->lhs) != 0) {
        // TODO: recover from error
        return_defer(1);
    }

    token = parser->tok;
    if (token.kind != TOKEN_EQUAL) {
        int line, column;
        lexer_pos_to_lc(&parser->lexer, token.pos, &line, &column);
        DS_LOG_ERROR("Expected `=` but found %s at %d:%d", token_kind_to_string(token.kind), line, column);
        return_defer(1);
    }
    token = parser_read(parser);

    if (parser_parse_expression(parser, &equality->rhs) != 0) {
        // TODO: recover from error
        return_defer(1);
    }

defer:
    return result;
}

static int parser_parse_statement(parser_t *parser, statement_t *statement) {
    int result = 0;
    token_t token = {0};

    ds_dynamic_array_init(&statement->defines, sizeof(define_t));
    statement->equality = NULL;

    if (parser_parse_defines(parser, &statement->defines) != 0) {
        // TODO: recover from error
        return_defer(1);
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
        if (parser_parse_equality(parser, statement->equality) != 0) {
            // TODO: recover from error
            return_defer(1);
        }
    }

defer:
    return result;
}

static int parser_parse_program(parser_t *parser, program_t *program) {
    int result = 0;
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
            if (parser_parse_expression(parser, &eval) != 0) {
                return_defer(1);
            }
            DS_UNREACHABLE(ds_dynamic_array_append(&program->evals, &eval));
        } else if (token.kind == TOKEN_PROOF) {
            token = parser_read(parser);

            statement_t statement = {0};
            if (parser_parse_statement(parser, &statement) != 0) {
                return_defer(1);
            }

            // printf("proof: \n");
            // statement_dump(&statement);
            // printf("\n\n");
        } else {
            statement_t statement = {0};
            if (parser_parse_statement(parser, &statement) != 0) {
                // TODO: recover from error
                return_defer(1);
            }
            DS_UNREACHABLE(ds_dynamic_array_append(&program->statements, &statement));
        }
    }

defer:
    return result;
}

typedef struct pair_t {
    expression_t *key;
    expression_t *value;
} pair_t;

static boolean find_mapping(ds_dynamic_array mapping, expression_t *key, expression_t *value) {
    for (unsigned int i = 0; i < mapping.count; i++) {
        pair_t *kv = NULL;
        DS_UNREACHABLE(ds_dynamic_array_get_ref(&mapping, i, (void **)&kv));

        if (expression_equal(kv->key, key)) {
            *value = *kv->value;
            return true;
        }
    }

    return false;
}

static boolean is_compatible(expression_t *axiom, expression_t *expr, ds_dynamic_array *mapping /* pair_t */) {
    if (axiom->kind == EXPRESSION_KIND_PAREN && expr->kind == EXPRESSION_KIND_PAREN) {
        return is_compatible(axiom->paren.expr, expr->paren.expr, mapping);
    }

    if (axiom->kind == EXPRESSION_KIND_OPERATOR && expr->kind == EXPRESSION_KIND_OPERATOR) {
        return ds_string_slice_equals(&axiom->operator.value, &expr->operator.value)
            && is_compatible(axiom->operator.lhs, expr->operator.lhs, mapping)
            && is_compatible(axiom->operator.rhs, expr->operator.rhs, mapping);
    }

    if (axiom->kind == EXPRESSION_KIND_FUNCTION && expr->kind == EXPRESSION_KIND_FUNCTION) {
        // NOTE: here we need to check that the types are matching

        pair_t kv = CLITERAL(pair_t){axiom, expr};
        DS_UNREACHABLE(ds_dynamic_array_append(mapping, &kv));

        return true;
    }

    if (axiom->kind == EXPRESSION_KIND_FUNCTION && expr->kind == EXPRESSION_KIND_NUMBER) {
        // NOTE: we still need to check types

        pair_t kv = CLITERAL(pair_t){axiom, expr};
        DS_UNREACHABLE(ds_dynamic_array_append(mapping, &kv));

        return true;
    }

    if (axiom->kind == EXPRESSION_KIND_FUNCTION && expr->kind == EXPRESSION_KIND_PAREN) {
        // NOTE: we still need to check types

        pair_t kv = CLITERAL(pair_t){axiom, expr->paren.expr};
        DS_UNREACHABLE(ds_dynamic_array_append(mapping, &kv));

        return true;
    }

    if (axiom->kind == EXPRESSION_KIND_NUMBER && expr->kind == EXPRESSION_KIND_NUMBER) {
        return ds_string_slice_equals(&axiom->number.value, &expr->number.value);
    }

    return false;
}

static boolean is_visited(ds_dynamic_array *visited /* expression_t */, expression_t *expr) {
    for (unsigned int i = 0; i < visited->count; i++) {
        expression_t *item = NULL;
        DS_UNREACHABLE(ds_dynamic_array_get_ref(visited, i, (void **)&item));

        // TODO: implement something like equavalence instead
        if (expression_equal(expr, item)) {
            return true;
        }
    }

    return false;
}

static int substitute(expression_t *axiom, ds_dynamic_array mapping /* pair_t */, expression_t *eval) {
    int result = 0;

    switch (axiom->kind) {
    case EXPRESSION_KIND_SET:
        eval->kind = EXPRESSION_KIND_SET;
        ds_dynamic_array_init(&eval->set.items, sizeof(expression_t));
        for (unsigned int i = 0; i < axiom->set.items.count; i++) {
            expression_t *item_i = NULL;
            DS_UNREACHABLE(ds_dynamic_array_get_ref(&axiom->set.items, i, (void **)&item_i));

            expression_t item = {0};
            if (substitute(item_i, mapping, &item) != 0) {
                return_defer(1);
            }
            DS_UNREACHABLE(ds_dynamic_array_append(&eval->set.items, &item));
        }
        break;
    case EXPRESSION_KIND_NAME:
        if (!find_mapping(mapping, axiom, eval)) {
            return_defer(1);
        }
        break;
    case EXPRESSION_KIND_NUMBER:
        *eval = *axiom;
        break;
    case EXPRESSION_KIND_FUNCTION:
        if (!find_mapping(mapping, axiom, eval)) {
            return_defer(1);
        }
        break;
    case EXPRESSION_KIND_OPERATOR:
        eval->kind = EXPRESSION_KIND_OPERATOR;
        eval->operator.lhs = DS_MALLOC(NULL, sizeof(expression_t));
        eval->operator.rhs = DS_MALLOC(NULL, sizeof(expression_t));
        if (substitute(axiom->operator.lhs, mapping, eval->operator.lhs) != 0) {
            return_defer(1);
        }
        if (substitute(axiom->operator.rhs, mapping, eval->operator.rhs) != 0) {
            return_defer(1);
        }
        break;
    case EXPRESSION_KIND_PAREN:
        eval->kind = EXPRESSION_KIND_PAREN;
        eval->paren.expr = DS_MALLOC(NULL, sizeof(expression_t));
        if (substitute(axiom->paren.expr, mapping, eval->paren.expr) != 0) {
            return_defer(1);
        }
        break;
    }

defer:
    return result;
}

static int solver_solve_dfs(ds_dynamic_array statements /* statement_t */,
                            expression_t *eval,
                            ds_dynamic_array *visited /* expression_t */,
                            ds_dynamic_array *parent /* pair_t */) {
    int result = 0;

    DS_UNREACHABLE(ds_dynamic_array_append(visited, eval));
    for (unsigned int i = 0; i < statements.count; i++) {
        statement_t *statement = NULL;
        DS_UNREACHABLE(ds_dynamic_array_get_ref(&statements, i, (void **)&statement));

        // NOTE: we ignore the types for now

        if (statement->equality == NULL) continue;

        ds_dynamic_array mapping = {0};
        ds_dynamic_array_init(&mapping, sizeof(pair_t));
        if (is_compatible(&statement->equality->lhs, eval, &mapping)) {
            expression_t eval1 = {0};
            if (substitute(&statement->equality->rhs, mapping, &eval1) != 0) {
                return_defer(1);
            }

            ds_dynamic_array_free(&mapping);

            if (!is_visited(visited, &eval1)) {
                pair_t kv = CLITERAL(pair_t){NULL, NULL};
                kv.key = DS_MALLOC(NULL, sizeof(expression_t));
                DS_MEMCPY(kv.key, &eval1, sizeof(expression_t));
                kv.value = DS_MALLOC(NULL, sizeof(expression_t));
                DS_MEMCPY(kv.value, eval, sizeof(expression_t));
                DS_UNREACHABLE(ds_dynamic_array_append(parent, &kv));

                if (solver_solve_dfs(statements, &eval1, visited, parent) != 0) {
                    return_defer(1);
                }
            }
        } else {
            ds_dynamic_array_free(&mapping);
        }
    }

defer:
    return result;
}

static int expression_degree(expression_t *expression) {
    switch (expression->kind) {
    case EXPRESSION_KIND_SET: return 1; // NOTE: maybe also check the items
    case EXPRESSION_KIND_NAME: return 0;
    case EXPRESSION_KIND_NUMBER: return 0;
    case EXPRESSION_KIND_FUNCTION: return 1; // NOTE: maybe also check the args
    case EXPRESSION_KIND_OPERATOR: return 1 + expression_degree(expression->operator.lhs) + expression_degree(expression->operator.rhs);
    case EXPRESSION_KIND_PAREN: return 1 + expression_degree(expression->paren.expr);
    }
}

static int find_smallest_expression(ds_dynamic_array expressions, expression_t *expr) {
    int result = 0;

    int degree = INT_MAX;
    for (unsigned int i = 0; i < expressions.count; i++) {
        expression_t *item = NULL;
        DS_UNREACHABLE(ds_dynamic_array_get_ref(&expressions, i, (void **)&item));

        int new_degree = expression_degree(item);
        if (new_degree < degree) {
            *expr = *item;
        }
    }

defer:
    return result;
}

static void show_path(ds_dynamic_array parent /* pair_t */, expression_t *result) {
    expression_t next = {0};
    if (!find_mapping(parent, result, &next)) return;

    show_path(parent, &next);

    expression_printf(&next);
    printf(" => ");
    expression_printf(result);
    printf("\n");
}

int solver_solve_eval(ds_dynamic_array statements /* statement_t */, expression_t *eval) {
    int result = 0;

    ds_dynamic_array visited = {0}; // expression_t
    ds_dynamic_array_init(&visited, sizeof(expression_t));

    ds_dynamic_array parent = {0}; // pair_t
    ds_dynamic_array_init(&parent, sizeof(pair_t));

    if (solver_solve_dfs(statements, eval, &visited, &parent) != 0) {
        return_defer(1);
    }

    expression_t expr = {0};
    find_smallest_expression(visited, &expr);

    printf("\nthe path is:\n");
    show_path(parent, &expr);

    printf("the result is: ");
    expression_printf(&expr);

defer:
    ds_dynamic_array_free(&visited);

    return result;
}

int solver_solve_program(program_t *program) {
    int result = 0;

    for (unsigned int i = 0; i < program->evals.count; i++) {
        expression_t *eval = NULL;
        DS_UNREACHABLE(ds_dynamic_array_get_ref(&program->evals, i, (void **)&eval));

        if (solver_solve_eval(program->statements, eval) != 0) {
            return_defer(1);
        }
    }

defer:
    return result;
}

int main () {
    long buffer_len = 0;
    char *buffer = NULL;
    lexer_t lexer = {0};
    parser_t parser = {0};
    program_t program = {0};

    int result = 0;

    buffer_len = ds_io_read(NULL, &buffer, "r");
    if (buffer_len < 0) {
        return_defer(1);
    }

    ds_string_slice slice = {0};
    ds_string_slice_init(&slice, buffer, buffer_len);
    lexer_init(&lexer, slice);
    parser_init(&parser, lexer);

    if (parser_parse_program(&parser, &program) != 0) {
        return_defer(1);
    }
    program_dump(&program);

    solver_solve_program(&program);

defer:
    if (buffer != NULL) DS_FREE(NULL, buffer);
    lexer_free(&lexer);

    return result;
}
