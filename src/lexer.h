#ifndef LEXER_H
#define LEXER_H

#include "ds.h"

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

const char* token_kind_to_string(token_kind_t kind);

typedef struct token_t {
    token_kind_t kind;
    ds_string_slice value;
    unsigned int pos;
} token_t;

void token_printf(token_t token);

typedef struct lexer_t {
    ds_string_slice buffer;
    unsigned int pos;
    unsigned int read_pos;
    char ch;
} lexer_t;

ds_result lexer_init(lexer_t *lexer, ds_string_slice buffer);
ds_result lexer_next(lexer_t *lexer, token_t *token);
ds_result lexer_pos_to_lc(lexer_t *lexer, unsigned int pos, int *line, int *column);

void lexer_free(lexer_t *lexer);

#endif // LEXER_H
