#include "mycc.h"
#include "cmm.tab.h"
#include "genir.h"
#include "parser_state.h"
#include "semantic.h"

#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>


void mycc_error(const char* error_type, unsigned lineno, const char* format, ...) {
  ++parser_state->nerror;
  fprintf(stderr, "error type %s at line %d: ", error_type, lineno);
  va_list args;
  va_start(args, format);
  vfprintf(stderr, format, args);
  fputc('\n', stderr);
  va_end(args);
}

extern int yylineno;
void yyerror(const char* msg) {
  mycc_error("B", yylineno, "%s", msg);
}

ParserState globalstate;
ParserState* parser_state = &globalstate;

extern FILE* yyin;
int main(int argc, char **argv) {
  if (argc != 3) {
    fprintf(stderr, "usage %s <file name> <output name>\n", argv[0]);
    return 0;
  }
  FILE* input = fopen(argv[1], "r");
  if (!input) {
    fprintf(stderr, "can not open file: %s\n", argv[1]);
    return 1;
  }
  yyin = input;
  pstate_init(parser_state);
  yyparse();
  if (parser_state->nerror == 0) {
    semantic_checktype(parser_state, parser_state->program);
  }
  Code code;
  if (parser_state->nerror == 0) {
    code = ir_gen((CstList*)parser_state->program, &parser_state->typetbl, parser_state->symtbl, parser_state->strtbl);
    if (code.code == NULL) ++parser_state->nerror;
  }
  if (parser_state->nerror == 0) {
    FILE* fout = fopen(argv[2], "w");
    if (!fout) {
      fprintf(stderr, "failed to open file: %s\n", argv[2]);
    } else {
      ir_print(&code, parser_state->strtbl, fout);
    }
  }
  free(code.code);
  pstate_destroy(parser_state);
  fclose(input);
  return 0;
}
