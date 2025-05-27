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
    EXPRESSION_KIND_NUMBER,
    EXPRESSION_KIND_FUNCTION,
    EXPRESSION_KIND_OPERATOR,
    EXPRESSION_KIND_PAREN,
} expression_kind_t;

typedef struct expression_set_t {
    ds_string_slice value;
} expression_set_t;

typedef struct expression_number_t {
    ds_string_slice value;
} expression_number_t;

typedef struct expression_name_t {
    ds_string_slice value;
    ds_dynamic_array args; /* expression_t */
} expression_name_t;

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
        expression_number_t number;
        expression_name_t name;
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
} program_t;

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

static void statement_dump(statement_t *statement) {
    for (unsigned int i = 0; i < statement->defines.count; i++) {
        define_t *define = NULL;
        DS_UNREACHABLE(ds_dynamic_array_get_ref(&statement->defines, i, (void **)&define));
        define_dump(define);
    }
}

static void program_dump(program_t *program) {
    for (unsigned int i = 0; i < program->statements.count; i++) {
        statement_t *statement = NULL;
        DS_UNREACHABLE(ds_dynamic_array_get_ref(&program->statements, i, (void **)&statement));
        statement_dump(statement);
        printf("\n");
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

defer:
    return result;
}

static int parser_parse_equality(parser_t *parser, equality_t *equality) {
    // TODO: implement me
    return 0;
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

    while (true) {
        if (parser->tok.kind == TOKEN_EOF) {
            break;
        }

        statement_t statement = {0};
        if (parser_parse_statement(parser, &statement) != 0) {
            // TODO: recover from error
            return_defer(1);
        }
        DS_UNREACHABLE(ds_dynamic_array_append(&program->statements, &statement));
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

    parser_parse_program(&parser, &program);
    program_dump(&program);

defer:
    if (buffer != NULL) DS_FREE(NULL, buffer);
    lexer_free(&lexer);

    return result;
}
