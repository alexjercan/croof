#ifndef PARSER_H
#define PARSER_H

#include "ds.h"
#include "lexer.h"

typedef struct parser_t {
    lexer_t lexer;
    token_t tok;
    token_t next_tok;
} parser_t;

ds_result parser_init(parser_t *parser, lexer_t lexer);

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

void expression_dump(expression_t *expression);
boolean expression_equal(expression_t *expr1, expression_t *expr2);
void program_dump(program_t *program);
void expression_printf(expression_t *expression);
void statement_printf(statement_t *statement);

ds_result parser_parse_program(parser_t *parser, program_t *program);

#endif // PARSER_H
