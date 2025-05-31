#include <limits.h>
#include <string.h>
#include <stdio.h>
#include "lexer.h"
#include "parser.h"
#include "solver.h"

ds_result main () {
    ds_result result = DS_OK;

    long buffer_len = 0;
    char *buffer = NULL;
    lexer_t lexer = {0};
    parser_t parser = {0};
    program_t program = {0};

    buffer_len = ds_io_read(NULL, &buffer, "r");
    if (buffer_len < 0) {
        return_defer(DS_ERR);
    }

    ds_string_slice slice = {0};
    ds_string_slice_init(&slice, buffer, buffer_len);
    lexer_init(&lexer, slice);
    parser_init(&parser, lexer);

    TRY(parser_parse_program(&parser, &program));
    TRY(solver_solve_program(&program));

defer:
    if (buffer != NULL) DS_FREE(NULL, buffer);
    lexer_free(&lexer);

    return result;
}
