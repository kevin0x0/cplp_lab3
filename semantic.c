#include "semantic.h"
#include "cst.h"
#include "mycc.h"
#include "parser_state.h"
#include "symtbl.h"
#include "type.h"
#include "typetbl.h"
#include "utils.h"
#include <assert.h>
#include <stdlib.h>

#define ETYPE_VARIABLE_UNDEF          ("1")
#define ETYPE_STRUCT_UNDEF            ("17")
#define ETYPE_VARIABLE_REDEF          ("3")
#define ETYPE_FUNCTION_REDEF          ("4")
#define ETYPE_STRUCT_REDEF            ("16")
#define ETYPE_STRUCT_UNKNOWNFIELD     ("14")
#define ETYPE_ASSIGN_TYPEMISMATCH     ("5")
#define ETYPE_OPERAND_TYPEMISMATCH    ("7")
#define ETYPE_ASSIGN_RVALUE           ("6")
#define ETYPE_INDEX_NOTINTEGER        ("12")
#define ETYPE_INDEX_NOTARRAY          ("10")
#define ETYPE_CALL_NOTCALLABLE        ("11")

#define semantic_haserror(pstate, t1, t2)     ((t1).basetype == (pstate)->commontype.errortype || (t2).basetype == (pstate)->commontype.errortype)
#define semantic_iserror(pstate, t1)          ((t1).basetype == (pstate)->commontype.errortype)
#define semantic_isinteger(pstate, t1)        ((t1).basetype == (pstate)->commontype.inttype && (t1).dim == 0)
#define semantic_isfloat(pstate, t1)          ((t1).basetype == (pstate)->commontype.floattype && (t1).dim == 0)
#define semantic_isfunction(pstate, t1)       (typetbl_get(&(pstate)->typetbl, (t1).basetype)->kind == TYPE_FUNC && (t1).dim == 0)
#define semantic_isstruct(pstate, t1)         (typetbl_get(&(pstate)->typetbl, (t1).basetype)->kind == TYPE_STRUCT && (t1).dim == 0)
#define semantic_isarray(pstate, t1)          ((t1).dim != 0)

#define makeerror(pstate)                     (maketype((pstate)->commontype.errortype, 0, 0))


static BaseTypeId semantic_type_specifier(ParserState* pstate, Cst* cst);
static void semantic_type_stmtcomp(ParserState* pstate, CstStmtComp* comp);
/* evaluate type of expression */
static Type semantic_type_expr(ParserState* pstate, Cst* cst);
/* evaluate type of statement */
static void semantic_type_stmt(ParserState* pstate, Cst* stmt);
/* handle extern definiton list.
 * including function definiton. extern variable declations. */
static void semantic_type_extdeflist(ParserState* pstate, CstList* extdeflist);
static void semantic_preinsert(ParserState* pstate);


void semantic_checktype(ParserState* pstate, Cst* program) {
  assert(!program || cst_checkkind(program, CST_LIST));
  semantic_preinsert(pstate);
  semantic_type_extdeflist(pstate, (CstList*)program);
}

/* get length of a list */
static size_t semantic_list_length(ParserState* pstate, CstList* list) {
  (void)pstate;
  size_t len = 0;
  while (list) {
    ++len;
    list = cstlist_next(list);
  }
  return len;
}

static Symbol* semantic_new_function(ParserState* pstate, StringId name, unsigned lineno) {
  Symbol* symbol = symtbl_search(pstate->symtbl, name);
  if (symbol) { /* function redefinition */
    mycc_error(ETYPE_FUNCTION_REDEF, lineno, "function redefinition: %s", strtbl_getstring(pstate->strtbl, name));
    return symbol;
  }
  symbol = symtbl_insert(pstate->symtbl, name);
  symbol->attr.kind = SYMBOL_FUNCTION;
  utils_oom_ifnull(symbol);
  return symbol;
}

static Symbol* semantic_new_struct(ParserState* pstate, StringId name, unsigned lineno) {
  Symbol* symbol = symtbl_search(pstate->symtbl, name);
  if (symbol) { /* symbol redefinition */
    mycc_error(ETYPE_STRUCT_REDEF, lineno, "struct redefinition: %s", strtbl_getstring(pstate->strtbl, name));
    return symbol;
  }
  symbol = symtbl_insert(pstate->symtbl, name);
  symbol->attr.kind = SYMBOL_STRUCT;
  utils_oom_ifnull(symbol);
  return symbol;
}

static Symbol* semantic_new_variable(ParserState* pstate, StringId name, unsigned lineno) {
  Symbol* symbol = symtbl_search(pstate->symtbl, name);
  if (symbol) { /* symbol redefinition */
    mycc_error(ETYPE_VARIABLE_REDEF, lineno, "variable redefinition: %s", strtbl_getstring(pstate->strtbl, name));
    return symbol;
  }
  symbol = symtbl_insert(pstate->symtbl, name);
  symbol->attr.kind = SYMBOL_VARIABLE;
  utils_oom_ifnull(symbol);
  return symbol;
}

static Symbol* semantic_get_variable_or_function(ParserState* pstate, StringId name, unsigned lineno) {
  Symbol* symbol = symtbl_search(pstate->symtbl, name);
  if (!symbol) {
    mycc_error(ETYPE_VARIABLE_UNDEF, lineno, "undefined variable: %s", strtbl_getstring(pstate->strtbl, name));
    return NULL;
  }
  if (symbol->attr.kind != SYMBOL_VARIABLE && symbol->attr.kind != SYMBOL_FUNCTION)
    mycc_error(ETYPE_VARIABLE_UNDEF, lineno, "symbol '%s' is not a variable or function", strtbl_getstring(pstate->strtbl, name));
  return symbol;
}

static size_t semantic_struct_nfield(ParserState* pstate, CstList* deflist) {
  size_t nfield = 0;
  while (deflist) {
    /* deflist->cst is def */
    CstDef* def = cstlist_get(deflist, CstDef*);
    nfield += semantic_list_length(pstate, (CstList*)def->declist);
    deflist = cstlist_next(deflist);
  }
  return nfield;
}

static Type semantic_type_vardec_instruct(ParserState* pstate, Cst* cst, BaseTypeId base, size_t dim, StructFieldDesc* fielddesc) {
  if (cst_checkkind(cst, CST_ID)) {
    CstId* id = (CstId*)cst;
    fielddesc->type = maketype(base, dim, 0);
    fielddesc->name = id->val;
    return fielddesc->type;
  }
  assert(cst_checkkind(cst, CST_DECARR));
  CstDecArr* decarr = (CstDecArr*)cst;
  if (cst_checkkind(decarr->vardec, CST_ID)) {
    CstId* id = (CstId*)cst;
    fielddesc->type = maketype(base, dim + 1, decarr->nelem);
    fielddesc->name = id->val;
    return fielddesc->type;
  }
  return semantic_type_vardec_instruct(pstate, decarr->vardec, base, dim + 1, fielddesc);
}

/* evaluate type and insert the variable and its type into symbol table. */
static Type semantic_type_vardec(ParserState* pstate, Cst* cst, BaseTypeId base, size_t dim) {
  if (cst_checkkind(cst, CST_ID)) {
    CstId* id = (CstId*)cst;
    Type type = maketype(base, dim, 0);
    Symbol* symbol = semantic_new_variable(pstate, id->val, id->lineno);
    symbol->attr.type = type;
    return type;
  }
  assert(cst_checkkind(cst, CST_DECARR));
  CstDecArr* decarr = (CstDecArr*)cst;
  if (cst_checkkind(decarr->vardec, CST_ID)) {
    CstId* id = (CstId*)decarr->vardec;
    Type type = maketype(base, dim + 1, decarr->nelem);
    Symbol* symbol = semantic_new_variable(pstate, id->val, id->lineno);
    symbol->attr.type = type;
    return type;
  }
  return semantic_type_vardec(pstate, decarr->vardec, base, dim + 1);
}

/* handle declaration list in a struct definition.
 * evaluate the type and set name and type in fielddesc.
 * return number of struct field. */
static size_t semantic_type_declist_instruct(ParserState* pstate, BaseTypeId base, CstList* declist, StructFieldDesc* fielddesc) {
  StructFieldDesc* fieldbegin = fielddesc;
  while (declist) {
    CstDec* dec = cstlist_get(declist, CstDec*);
    assert(cst_checkkind(dec, CST_DEC));
    semantic_type_vardec_instruct(pstate, dec->vardec, base, 0, fielddesc++);
    declist = cstlist_next(declist);
  }
  return fielddesc - fieldbegin;
}

/* handle declaration list in a function body.
 * evaluate the type and insert variable and type into symbol table.
 * also evaluate initial value. */
static void semantic_type_declist(ParserState* pstate, BaseTypeId base, CstList* declist) {
  while (declist) {
    CstDec* dec = cstlist_get(declist, CstDec*);
    assert(cst_checkkind(dec, CST_DEC));
    Type lval = semantic_type_vardec(pstate, dec->vardec, base, 0);
    if (dec->initval) {
      Type rval = semantic_type_expr(pstate, dec->initval);
      if (!type_is_same(lval, rval) && !semantic_haserror(pstate, lval, rval))
        mycc_error(ETYPE_ASSIGN_TYPEMISMATCH, dec->vardec->lineno, "type mismatching");
    }
    declist = cstlist_next(declist);
  }
}

/* handle extern declaration list.
 * evaluate the type and insert variable and type into symbol table. */
static void semantic_type_extdeclist(ParserState* pstate, BaseTypeId base, CstList* declist) {
  while (declist) {
    assert(cst_checkkind(declist->cst, CST_ID) || cst_checkkind(declist->cst, CST_DECARR));
    semantic_type_vardec(pstate, declist->cst, base, 0);
    declist = cstlist_next(declist);
  }
}

/* handle extern function declaration.
 * evaluate the type and insert variable and type into symbol table. */
static void semantic_type_extfuncdec(ParserState* pstate, Type rettype, CstFuncDec* funcdec) {
  /* create function */
  Symbol* symbol = semantic_new_function(pstate, funcdec->funcname, funcdec->lineno);
  BaseType* functype = typetbl_newfunction(&pstate->typetbl);
  utils_oom_ifnull(functype);
  functype->function_rettype = rettype;
  symbol->attr.type = maketype(functype->id, 0, 0);
  /* handle parameters */
  CstList* paramlist = (CstList*)funcdec->paramlist;
  while (paramlist) {
    CstParam* param = cstlist_get(paramlist, CstParam*);
    assert(cst_checkkind(param, CST_PARAM));
    BaseTypeId base = semantic_type_specifier(pstate, param->specifier);
    semantic_type_vardec(pstate, param->vardec, base, 0);
    paramlist = cstlist_next(paramlist);
  }
}

/* handle extern definiton list.
 * including function definiton. extern variable declations. */
static void semantic_type_extdeflist(ParserState* pstate, CstList* extdeflist) {
  while (extdeflist) {
    Cst* extdef = cstlist_get(extdeflist, Cst*);
    if (cst_checkkind(extdef, CST_EXTDEFFUNC)) {
      CstExtDefFunc* extdeffunc = (CstExtDefFunc*)extdef;
      BaseTypeId base = semantic_type_specifier(pstate, extdeffunc->specifier);
      semantic_type_extfuncdec(pstate, maketype(base, 0, 0), (CstFuncDec*)extdeffunc->funcdec);
      /* handle function body (compound statement) */
      assert(cst_checkkind(extdeffunc->stmt, CST_STMTCOMP));
      semantic_type_stmtcomp(pstate, (CstStmtComp*)extdeffunc->stmt);
    } else {
      assert(cst_checkkind(extdef, CST_EXTDEFDEC));
      CstExtDefDec* extdefdec = (CstExtDefDec*)extdef;
      BaseTypeId base = semantic_type_specifier(pstate, extdefdec->specifier);
      semantic_type_extdeclist(pstate, base, (CstList*)extdefdec->declist);
    }
    extdeflist = cstlist_next(extdeflist);
  }
}

/* handle definition list in a struct definition.
 * evaluate the type and set name and type in fielddesc. */
static void semantic_type_deflist_instruct(ParserState* pstate, CstList* deflist, StructFieldDesc* fielddesc) {
  while (deflist) {
    CstDef* def = cstlist_get(deflist, CstDef*);
    assert(cst_checkkind(def, CST_DEF));
    BaseTypeId base = semantic_type_specifier(pstate, def->specifier); 
    fielddesc += semantic_type_declist_instruct(pstate, base, (CstList*)def->declist, fielddesc);
    deflist = cstlist_next(deflist);
  }
}

/* handle definition list in a function body.
 * evaluate the type and set name and type in fielddesc. */
static void semantic_type_deflist(ParserState* pstate, CstList* deflist) {
  while (deflist) {
    CstDef* def = cstlist_get(deflist, CstDef*);
    assert(cst_checkkind(def, CST_DEF));
    BaseTypeId base = semantic_type_specifier(pstate, def->specifier); 
    semantic_type_declist(pstate, base, (CstList*)def->declist);
    deflist = cstlist_next(deflist);
  }
}

static BaseTypeId semantic_type_structdef(ParserState* pstate, CstStructDef* structdef) {
  CstList* deflist = (CstList*)structdef->deflist;
  size_t nfield = semantic_struct_nfield(pstate, deflist);
  BaseType* structtype = typetbl_newstruct(&pstate->typetbl, nfield);
  utils_oom_ifnull(structtype);
  semantic_type_deflist_instruct(pstate, deflist, structtype->structtype->fields);
  if (structdef->tagname != pstate->dummyname) {
    Symbol* symbol = semantic_new_struct(pstate, structdef->tagname, structdef->lineno);
    symbol->attr.type = maketype(structtype->id, 0, 0);
  }
  return structtype->id;
}

static BaseTypeId semantic_type_structtype(ParserState* pstate, CstStructType* structtype) {
  Symbol* symbol = symtbl_search(pstate->symtbl, structtype->tagname);
  if (!symbol || symbol->attr.kind != SYMBOL_STRUCT) {
    mycc_error(ETYPE_STRUCT_UNDEF, structtype->lineno, "undefined struct name: %s", strtbl_getstring(pstate->strtbl, structtype->tagname));
    return pstate->commontype.errortype;
  }
  assert(symbol->attr.type.dim == 0); /* structure is not a array */
  return symbol->attr.type.basetype;
}

static BaseTypeId semantic_type_specifier(ParserState* pstate, Cst* cst) {
  if (cst_checkkind(cst, CST_TYPE)) {
    CstType* csttype = (CstType*)cst;
    assert(csttype->val == BTYPE_INT || csttype->val == BTYPE_FLOAT);
    return csttype->val == BTYPE_INT ? pstate->commontype.inttype
                                     : pstate->commontype.floattype;
  } else if (cst_checkkind(cst, CST_STRUCTDEF)) {
    return semantic_type_structdef(pstate, (CstStructDef*)cst);
  } else {
    assert(cst_checkkind(cst, CST_STRUCTTYPE));
    return semantic_type_structtype(pstate, (CstStructType*)cst);
  }
}

static bool semantic_is_lvalue(ParserState* pstate, Cst* expr) {
  (void)pstate;
  return cst_checkkind(expr, CST_ID) || cst_checkkind(expr, CST_INDEX) || cst_checkkind(expr, CST_DOT);
}

static Type semantic_type_exprbin(ParserState* pstate, CstBin* binary) {
  Type ltype = semantic_type_expr(pstate, binary->loperand);
  Type rtype = semantic_type_expr(pstate, binary->roperand);
  if (semantic_haserror(pstate, ltype, rtype))
    return makeerror(pstate);
  switch (binary->op) {
    case CSTOP_LE:
    case CSTOP_LT:
    case CSTOP_GE:
    case CSTOP_GT:
    case CSTOP_NE:
    case CSTOP_EQ: {
      if (semantic_isinteger(pstate, ltype) && semantic_isinteger(pstate, rtype)) {
        return ltype;
      } else if (semantic_isfloat(pstate, ltype) && semantic_isfloat(pstate, rtype)) {
        return maketype(pstate->commontype.inttype, 0, 0);
      }
      mycc_error(ETYPE_OPERAND_TYPEMISMATCH, binary->lineno, "the types of operands in the copmparison operation do not match");
      return makeerror(pstate);
    }
    case CSTOP_ADD:
    case CSTOP_SUB:
    case CSTOP_MUL:
    case CSTOP_DIV: {
      if (semantic_isinteger(pstate, ltype) && semantic_isinteger(pstate, rtype)) {
        return ltype;
      } else if (semantic_isfloat(pstate, ltype) && semantic_isfloat(pstate, rtype)) {
        return ltype;
      }
      mycc_error(ETYPE_OPERAND_TYPEMISMATCH, binary->lineno, "the types of operands in the arithmetic operation do not match");
      return makeerror(pstate);
    }
    case CSTOP_OR:
    case CSTOP_AND: {
      if (semantic_isinteger(pstate, ltype) && semantic_isinteger(pstate, rtype))
        return ltype;
      mycc_error(ETYPE_OPERAND_TYPEMISMATCH, binary->lineno, "logic operator can only be applied to integer");
      return makeerror(pstate);
    }
    case CSTOP_ASSIGN: {
      if (!semantic_is_lvalue(pstate, binary->loperand)) {
        mycc_error(ETYPE_ASSIGN_RVALUE, binary->lineno, "lvalue expected in left hand side of assignment");
        return makeerror(pstate);
      } else if (!type_is_same(ltype, rtype)) {
        mycc_error(ETYPE_ASSIGN_TYPEMISMATCH, binary->lineno, "type mismatching in assignment");
        return makeerror(pstate);
      } else if (!semantic_isinteger(pstate, ltype)) {
        mycc_error(ETYPE_ASSIGN_TYPEMISMATCH, binary->lineno, "only support integer assignment");
        return makeerror(pstate);
      }
      return ltype;
    }
    default: {
      assert(false);
      return makeerror(pstate);
    }
  }
}

static Type semantic_type_exprpre(ParserState* pstate, CstPre* prefix) {
  Type type = semantic_type_expr(pstate, prefix->operand);
  if (semantic_iserror(pstate, type))
    return type;
  switch (prefix->op) {
    case CSTOP_NEG: {
      if (semantic_isinteger(pstate, type) || semantic_isfloat(pstate, type))
        return type;
      mycc_error(ETYPE_OPERAND_TYPEMISMATCH, prefix->lineno, "unary '-' can only be applied to integer and floating number");
      return makeerror(pstate);
    }
    case CSTOP_NOT: {
      if (semantic_isinteger(pstate, type)) 
        return type;
      mycc_error(ETYPE_OPERAND_TYPEMISMATCH, prefix->lineno, "logic operator can only be applied to integer");
      return makeerror(pstate);
    }
    default: {
      assert(false);
      return makeerror(pstate);
    }
  }
}

static Type semantic_type_exprcall(ParserState* pstate, CstCall* call) {
  Type functype = semantic_type_expr(pstate, call->func);
  if (semantic_iserror(pstate, functype))
    return functype;
  CstList* arglist = (CstList*)call->args;
  Type resulttype;
  if (!semantic_isfunction(pstate, functype)) {
    mycc_error(ETYPE_CALL_NOTCALLABLE, call->func->lineno, "expected a function type");
    resulttype = makeerror(pstate);
  } else {
    resulttype = typetbl_get(&pstate->typetbl, functype.basetype)->function_rettype;
  }
  while (arglist) {
    Cst* arg = cstlist_get(arglist, Cst*);
    /* we do not need to check number and types of parameters.
     * so just evaluate and discard the type. */
    semantic_type_expr(pstate, arg);
    arglist = cstlist_next(arglist);
  }
  return resulttype;
}

/* find struct field by field name.
 * return NULL if no such field. */
static StructFieldDesc* semantic_get_structfield(ParserState* pstate, StructType* structtype, StringId fieldname) {
  char* name = strtbl_getstring(pstate->strtbl, fieldname);
  for (size_t i = 0; i < structtype->nfield; ++i) {
    if (0 == strcmp(name, strtbl_getstring(pstate->strtbl, structtype->fields[i].name)))
      return &structtype->fields[i];
  }
  return NULL;
}

static Type semantic_type_exprdot(ParserState* pstate, CstDot* dot) {
  Type type = semantic_type_expr(pstate, dot->loperand);
  if (semantic_iserror(pstate, type))
    return type;
  if (!semantic_isstruct(pstate, type)) {
    mycc_error(ETYPE_CALL_NOTCALLABLE, dot->loperand->lineno, "expected a structure");
    return makeerror(pstate);
  }
  StructType* structtype = typetbl_get(&pstate->typetbl, type.basetype)->structtype;
  StructFieldDesc* fielddesc = semantic_get_structfield(pstate, structtype, dot->name);
  if (!fielddesc) {
    mycc_error(ETYPE_STRUCT_UNKNOWNFIELD, dot->lineno, "no field named '%s' in this structure", strtbl_getstring(pstate->strtbl, dot->name));
    return makeerror(pstate);
  }
  return fielddesc->type;
}

static Type semantic_type_exprindex(ParserState* pstate, CstIndex* indexexpr) {
  Type arrtype = semantic_type_expr(pstate, indexexpr->arr);
  if (semantic_iserror(pstate, arrtype))
    return arrtype;
  if (!semantic_isarray(pstate, arrtype)) {
    mycc_error(ETYPE_INDEX_NOTARRAY, indexexpr->arr->lineno, "expected an array");
    return makeerror(pstate);
  }
  Type indextype = semantic_type_expr(pstate, indexexpr->index);
  if (semantic_iserror(pstate, indextype))
    return indextype;
  if (!semantic_isinteger(pstate, indextype)) {
    mycc_error(ETYPE_INDEX_NOTINTEGER, indexexpr->index->lineno, "expected an integer");
    return makeerror(pstate);
  }
  --arrtype.dim;
  return arrtype;
}

static Type semantic_type_expr(ParserState* pstate, Cst* cst) {
  switch (cst->kind) {
    case CST_BIN: {
      return semantic_type_exprbin(pstate, (CstBin*)cst);
    }
    case CST_PRE: {
      return semantic_type_exprpre(pstate, (CstPre*)cst);
    }
    case CST_CALL: {
      return semantic_type_exprcall(pstate, (CstCall*)cst);
    }
    case CST_DOT: {
      return semantic_type_exprdot(pstate, (CstDot*)cst);
    }
    case CST_INDEX: {
      return semantic_type_exprindex(pstate, (CstIndex*)cst);
    }
    case CST_ID: {
      CstId* id = (CstId*)cst;
      Symbol* symbol = semantic_get_variable_or_function(pstate, id->val, id->lineno);
      if (!symbol) return makeerror(pstate);
      return symbol->attr.type;
    }
    case CST_FLOAT: {
      return maketype(pstate->commontype.floattype, 0, 0);
    }
    case CST_INT: {
      return maketype(pstate->commontype.inttype, 0, 0);
    }
    default: {
      assert(false);
      return makeerror(pstate);
    }
  }
}

static void semantic_type_stmtcomp(ParserState* pstate, CstStmtComp* comp) {
  semantic_type_deflist(pstate, (CstList*)comp->deflist);
  CstList* stmtlist = (CstList*)comp->stmtlist;
  while (stmtlist) {
    semantic_type_stmt(pstate, cstlist_get(stmtlist, Cst*));
    stmtlist = cstlist_next(stmtlist);
  }
}

static void semantic_type_stmtif(ParserState* pstate, CstStmtIf* stmtif) {
  Type condtype = semantic_type_expr(pstate, stmtif->cond);
  if (!semantic_iserror(pstate, condtype) && !semantic_isinteger(pstate, condtype))
    mycc_error(ETYPE_OPERAND_TYPEMISMATCH, stmtif->cond->lineno, "condition should be evaluated to be an integer");
  semantic_type_stmt(pstate, stmtif->if_stmt);
  if (stmtif->else_stmt)
    semantic_type_stmt(pstate, stmtif->else_stmt);
}

static void semantic_type_stmtwhile(ParserState* pstate, CstStmtWhile* stmtwhile) {
  Type condtype = semantic_type_expr(pstate, stmtwhile->cond);
  if (!semantic_iserror(pstate, condtype) && !semantic_isinteger(pstate, condtype))
    mycc_error(ETYPE_OPERAND_TYPEMISMATCH, stmtwhile->cond->lineno, "condition should be evaluated to be an integer");
  semantic_type_stmt(pstate, stmtwhile->stmt);
}

static void semantic_type_stmtexpr(ParserState* pstate, CstStmtExpr* stmtexpr) {
  semantic_type_expr(pstate, stmtexpr->expr);
}

static void semantic_type_stmtreturn(ParserState* pstate, CstStmtReturn* stmtreturn) {
  Type type = semantic_type_expr(pstate, stmtreturn->expr);
  if (!semantic_isinteger(pstate, type))
    mycc_error("C", stmtreturn->lineno, "return array and structure not supported");
}

static void semantic_type_stmt(ParserState* pstate, Cst* stmt) {
  switch (stmt->kind) {
    case CST_STMTWHILE: {
      semantic_type_stmtwhile(pstate, (CstStmtWhile*)stmt);
      break;
    }
    case CST_STMTIF: {
      semantic_type_stmtif(pstate, (CstStmtIf*)stmt);
      break;
    }
    case CST_STMTEXPR: {
      semantic_type_stmtexpr(pstate, (CstStmtExpr*)stmt);
      break;
    }
    case CST_STMTRETURN: {
      semantic_type_stmtreturn(pstate, (CstStmtReturn*)stmt);
      break;
    }
    case CST_STMTCOMP: {
      semantic_type_stmtcomp(pstate, (CstStmtComp*)stmt);
      break;
    }
    default: {
      assert(false);
      break;
    }
  }
}

static void semantic_preinsertfunction(ParserState* pstate, StringId name) {
  Symbol* symbol = semantic_new_function(pstate, name, 0);
  BaseType* functype = typetbl_newfunction(&pstate->typetbl);
  utils_oom_ifnull(functype);
  functype->function_rettype = maketype(pstate->commontype.inttype, 0, 0);
  symbol->attr.type = maketype(functype->id, 0, 0);
}

static void semantic_preinsert(ParserState* pstate) {
  char* funcname = strtbl_newstring(pstate->strtbl, "read");
  utils_oom_ifnull(funcname);
  StringId nameid = strtbl_stringid(pstate->strtbl, funcname);
  semantic_preinsertfunction(pstate, nameid);
  funcname = strtbl_newstring(pstate->strtbl, "write");
  utils_oom_ifnull(funcname);
  nameid = strtbl_stringid(pstate->strtbl, funcname);
  semantic_preinsertfunction(pstate, nameid);
}
