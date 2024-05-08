#ifndef _MYCC_H_
#define _MYCC_H_

#include "parser_state.h"

extern ParserState* parser_state;


void mycc_error(const char* error_type, unsigned lineno, const char* format, ...);
void yyerror(const char* msg);

#endif
