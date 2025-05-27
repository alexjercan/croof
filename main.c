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

int main () {
    long buffer_len = 0;
    char *buffer = NULL;
    lexer_t lexer = {0};

    int result = 0;

    buffer_len = ds_io_read(NULL, &buffer, "r");
    if (buffer_len < 0) {
        return_defer(1);
    }

    ds_string_slice slice = {0};
    ds_string_slice_init(&slice, buffer, buffer_len);
    lexer_init(&lexer, slice);

    token_t token = {0};
    do {
        if (lexer_next(&lexer, &token) != 0) {
            DS_PANIC("fail");
        }

        token_printf(token);
    } while (token.kind != TOKEN_EOF);

defer:
    if (buffer != NULL) DS_FREE(NULL, buffer);
    lexer_free(&lexer);

    return result;
}
