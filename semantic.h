#ifndef _SEMANTIC_H_
#define _SEMANTIC_H_

#include "parser_state.h"
#include "type.h"
#include "typetbl.h"

void semantic_checktype(ParserState* pstate, Cst* program);

#endif
