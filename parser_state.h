#ifndef _PARSER_STATE_H_
#define _PARSER_STATE_H_

#include "cst.h"
#include "strtbl.h"
#include "symtbl.h"
#include "typetbl.h"

typedef struct tagParserState {
  StrTbl* strtbl;
  SymTbl* symtbl;
  Cst* allcsts;
  Cst* program;         /* this is the root node */
  unsigned nerror;
  StringId dummyname;
  TypeTbl typetbl;
  unsigned varid;
  struct {
    Cst* error;
  } noattrtokennode;
  struct {
    BaseTypeId inttype;
    BaseTypeId floattype;
    BaseTypeId errortype;
  } commontype;
} ParserState;

#define pstate_appendcst(pstate, cst)   pstate_appendcst_raw((pstate), (Cst*)(cst))

static inline Cst* pstate_appendcst_raw(ParserState* pstate, Cst* cst) {
  cst->next = pstate->allcsts;
  pstate->allcsts = cst;
  return cst;
}

void pstate_init(ParserState* pstate);
void pstate_destroy(ParserState* pstate);

#endif
