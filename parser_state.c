#include "parser_state.h"
#include "cst.h"
#include "symtbl.h"
#include "typetbl.h"

void pstate_init(ParserState* pstate) {
  pstate->allcsts = NULL;
  pstate->nerror = 0;
  pstate->varid = 0;
  utils_oom_ifnull(pstate->strtbl = strtbl_create());
  char* dummyname = strtbl_newstring(pstate->strtbl, "");
  utils_oom_ifnull(dummyname);
  pstate->dummyname = strtbl_stringid(pstate->strtbl, dummyname);
  pstate->noattrtokennode.error = pstate_appendcst(pstate, cst_create_noattrtoken(0, CST_ERROR));
  pstate->symtbl = symtbl_create(16, pstate->strtbl);
  utils_oom_ifnull(pstate->symtbl);
  if (!typetbl_init(&pstate->typetbl))
    utils_oom();
  BaseType* type = typetbl_newbasic(&pstate->typetbl, BTYPE_INT);
  utils_oom_ifnull(type);
  pstate->commontype.inttype = type->id;
  type = typetbl_newbasic(&pstate->typetbl, BTYPE_FLOAT);
  utils_oom_ifnull(type);
  pstate->commontype.floattype = type->id;
  type = typetbl_newerror(&pstate->typetbl);
  utils_oom_ifnull(type);
  pstate->commontype.errortype = type->id;
}

void pstate_destroy(ParserState* pstate) {
  pstate->nerror = 0;
  strtbl_delete(pstate->strtbl);
  Cst* csts = pstate->allcsts;
  while (csts) {
    Cst* tmp = csts->next;
    free(csts);
    csts = tmp;
  }
  symtbl_delete(pstate->symtbl);
  typetbl_destroy(&pstate->typetbl);
}
