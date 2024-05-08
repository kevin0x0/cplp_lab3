#include "genir.h"
#include "cst.h"
#include "iroperand.h"
#include "mycc.h"
#include "symtbl.h"
#include "typetbl.h"
#include <setjmp.h>

kgarray_impl(IR, IRArray, irarr, pass_val,);

typedef struct tagGenerator {
  IRArray code;
  unsigned varid;
  unsigned labelid;
  StrTbl* strtbl;
  SymTbl* symtbl;
  TypeTbl* typetbl;
  jmp_buf errorpos;
} Generator;

static void ir_exprbool(Generator* gen, Cst* cst, unsigned labelid, bool jmpcond);
static void ir_exprbin(Generator* gen, CstBin* bincst, VarOperand result, bool isref);
static void ir_exprassign(Generator* gen, CstBin* bincst, VarOperand result, bool isref, bool result_valid);
static void ir_exprcall(Generator* gen, CstCall* callcst, VarOperand result, bool isref);
static void ir_exprindex(Generator* gen, CstIndex* indexcst, VarOperand result, bool isref);
static void ir_exprdot(Generator* gen, CstDot* dotcst, VarOperand result, bool isref);
static void ir_expr(Generator* gen, Cst* cst, VarOperand result, bool isref);

static void ir_vardec(Generator* gen, CstDec* stmt);
static void ir_deflist(Generator* gen, CstList* deflist);

static void ir_stmt(Generator* gen, Cst* stmt);
static void ir_stmtcomp(Generator* gen, CstStmtComp* comp);
static void ir_stmtif(Generator* gen, CstStmtIf* stmtif);
static void ir_stmtwhile(Generator* gen, CstStmtWhile* stmtwhile);
static void ir_stmtexpr(Generator* gen, CstStmtExpr* stmtexpr);
static void ir_stmtreturn(Generator* gen, CstStmtReturn* stmtreturn);

static inline unsigned ir_newlabel(Generator* gen);
static inline VarOperand ir_newtemp(Generator* gen);

static inline Operand ir_constoperand(ConstOperand val);
static inline Operand ir_varoperand(VarOperand val);

static inline void ir_emit(Generator* gen, IR ir);
static inline void ir_emit_assign_fromvar(Generator* gen, VarOperand result, VarOperand val, bool result_isref);
static inline void ir_emit_assign_fromconst(Generator* gen, VarOperand result, ConstOperand val, bool result_isref);
static inline void ir_emit_arith(Generator* gen, IRKind op, VarOperand result, VarOperand loperand, VarOperand roperand, unsigned loptag, bool result_isref);
static inline void ir_emit_arithi(Generator* gen, IRKind op, VarOperand result, VarOperand loperand, ConstOperand roperand, unsigned loptag, bool result_isref);
static inline void ir_emit_gotoifi(Generator* gen, unsigned labelid, VarOperand loperand, ConstOperand roperand, CstOp relop, bool jmpcond);
static inline void ir_emit_gotoif(Generator* gen, unsigned labelid, VarOperand loperand, VarOperand roperand, CstOp relop, bool jmpcond);
static inline void ir_emit_goto(Generator* gen, unsigned labelid);
static inline void ir_emit_label(Generator* gen, unsigned labelid);

static void ir_error(Generator* gen, int lineno, const char* message);
static void ir_fatalerror(Generator* gen, const char* message);

static inline unsigned ir_newlabel(Generator* gen) {
  return gen->labelid++;
}

static inline VarOperand ir_newtemp(Generator* gen) {
  return (VarOperand)gen->varid++;
}

static inline Operand ir_constoperand(ConstOperand val) {
  return (Operand) { .constant = val };
}

static inline Operand ir_varoperand(VarOperand val) {
  return (Operand) { .variable = val };
}

static inline void ir_emit(Generator* gen, IR ir) {
  if (!irarr_push_back(&gen->code, ir))
    ir_fatalerror(gen, "out of memory");
}

static inline void ir_emit_assign_fromconst(Generator* gen, VarOperand result, ConstOperand val, bool result_isref) {
  if(result_isref) {
    ir_emit(gen, (IR) { .kind = IR_REF_ASSIGN, .optag = IRTAG_LOP_CONST, .ref_assign = { .result = result, .operand = ir_constoperand(val) } });
  } else {
    ir_emit(gen, (IR) { .kind = IR_ASSIGN, .optag = IRTAG_LOP_CONST, .assign = { .result = result, .operand = ir_constoperand(val) } });
  }
}

static inline void ir_emit_assign_fromvar(Generator* gen, VarOperand result, VarOperand val, bool result_isref) {
  if(result_isref) {
    ir_emit(gen, (IR) { .kind = IR_REF_ASSIGN, .optag = IRTAG_NORMAL, .ref_assign = { .result = result, .operand = ir_varoperand(val) } });
  } else {
    ir_emit(gen, (IR) { .kind = IR_ASSIGN, .optag = IRTAG_NORMAL, .assign = { .result = result, .operand = ir_varoperand(val) } });
  }
}

static inline void ir_emit_arith(Generator* gen, IRKind op, VarOperand result, VarOperand loperand, VarOperand roperand, unsigned loptag, bool result_isref) {
  assert(op == IR_ADD || op == IR_SUB || op == IR_MUL || op == IR_DIV);
  assert((loptag & (IRTAG_ROP_CONST | IRTAG_ROP_DEREF)) == 0);
  ir_emit(gen, (IR) { .kind = op, .optag = loptag | (result_isref ? IRTAG_RES_DEREF : IRTAG_NORMAL), .bin = { .result = result, .loperand = loperand, .roperand = ir_varoperand(roperand) } });
}

static inline void ir_emit_arithi(Generator* gen, IRKind op, VarOperand result, VarOperand loperand, ConstOperand roperand, unsigned loptag, bool result_isref) {
  assert(op == IR_ADD || op == IR_SUB || op == IR_MUL || op == IR_DIV);
  assert((loptag & (IRTAG_ROP_CONST | IRTAG_ROP_DEREF)) == 0);
  ir_emit(gen, (IR) { .kind = op, .optag = loptag | IRTAG_ROP_CONST | (result_isref ? IRTAG_RES_DEREF : IRTAG_NORMAL), .bin = { .result = result, .loperand = loperand, .roperand = ir_constoperand(roperand) } });
}

static inline void ir_emit_gotoifi(Generator* gen, unsigned labelid, VarOperand loperand, ConstOperand roperand, CstOp relop, bool jmpcond) {
  if (jmpcond == false) {
    static const CstOp reverse[] = {
      [CSTOP_EQ] = CSTOP_NE,
      [CSTOP_NE] = CSTOP_EQ,
      [CSTOP_LE] = CSTOP_GT,
      [CSTOP_LT] = CSTOP_GE,
      [CSTOP_GE] = CSTOP_LT,
      [CSTOP_GT] = CSTOP_LE,
    };
    relop = reverse[relop];
  }
  ir_emit(gen, (IR) { .kind = IR_COND_GOTO, .optag = IRTAG_ROP_CONST, .cond_goto = { .relop = relop, .labelid = labelid, .loperand = loperand, .roperand = ir_constoperand(roperand) } });
}

static inline void ir_emit_gotoif(Generator* gen, unsigned labelid, VarOperand loperand, VarOperand roperand, CstOp relop, bool jmpcond) {
  if (jmpcond == false) {
    static const CstOp reverse[] = {
      [CSTOP_EQ] = CSTOP_NE,
      [CSTOP_NE] = CSTOP_EQ,
      [CSTOP_LE] = CSTOP_GT,
      [CSTOP_LT] = CSTOP_GE,
      [CSTOP_GE] = CSTOP_LT,
      [CSTOP_GT] = CSTOP_LE,
    };
    relop = reverse[relop];
  }
  ir_emit(gen, (IR) { .kind = IR_COND_GOTO, .optag = IRTAG_NORMAL, .cond_goto = { .relop = relop, .labelid = labelid, .loperand = loperand, .roperand = ir_varoperand(roperand) } });
}

static inline void ir_emit_goto(Generator* gen, unsigned labelid) {
  ir_emit(gen, (IR) { .kind = IR_GOTO, .optag = IRTAG_NORMAL, .ir_goto = { .labelid = labelid } });
}

static inline void ir_emit_label(Generator* gen, unsigned labelid) {
  ir_emit(gen, (IR) { .kind = IR_LABEL, .optag = IRTAG_NORMAL, .label = { .labelid = labelid } });
}

static void ir_exprbini(Generator* gen, CstBin* bincst, VarOperand result, bool isref) {
  int roperand = ((CstInt*)(bincst->roperand))->val;
  VarOperand loperand;
  if (cst_checkkind(bincst->loperand, CST_ID)) {
    loperand = symtbl_search(gen->symtbl, ((CstId*)bincst->loperand)->val)->attr.var;
  } else {
    loperand = ir_newtemp(gen);
    ir_expr(gen, bincst->loperand, loperand, false);
  }
  switch (bincst->op) {
    case CSTOP_ADD: {
      ir_emit_arithi(gen, IR_ADD, result, loperand, (ConstOperand)roperand, IRTAG_NORMAL, isref);
      return;
    }
    case CSTOP_SUB: {
      ir_emit_arithi(gen, IR_SUB, result, loperand, (ConstOperand)roperand, IRTAG_NORMAL, isref);
      return;
    }
    case CSTOP_MUL: {
      ir_emit_arithi(gen, IR_MUL, result, loperand, (ConstOperand)roperand, IRTAG_NORMAL, isref);
      return;
    }
    case CSTOP_DIV: {
      ir_emit_arithi(gen, IR_DIV, result, loperand, (ConstOperand)roperand, IRTAG_NORMAL, isref);
      return;
    }
    case CSTOP_ASSIGN: {
    }
    default: {
      assert(false);
      return;
    }
  }
}

static void ir_exprboolrelop(Generator* gen, CstBin* relcst, unsigned labelid, bool jmpcond) {
  VarOperand loperand;
  if (cst_checkkind(relcst->loperand, CST_ID)) {
    loperand = symtbl_search(gen->symtbl, ((CstId*)relcst->loperand)->val)->attr.var;
  } else {
    loperand = ir_newtemp(gen);
    ir_expr(gen, relcst->loperand, loperand, false);
  }
  if (cst_checkkind(relcst->roperand, CST_INT)) {
    ir_emit_gotoifi(gen, labelid, loperand, (ConstOperand)((CstInt*)relcst->roperand)->val, relcst->op, jmpcond);
  } else {
    VarOperand tmp = ir_newtemp(gen);
    ir_expr(gen, relcst->roperand, tmp, false);
    ir_emit_gotoif(gen, labelid, loperand, tmp, relcst->op, jmpcond);
  }
}

static void ir_exprbool(Generator* gen, Cst* cst, unsigned labelid, bool jmpcond) {
  if (cst_checkkind(cst, CST_PRE)) {
    if (((CstPre*)cst)->op == CSTOP_NOT) {
      ir_exprbool(gen, ((CstPre*)cst)->operand, labelid, !jmpcond);
      return;
    }
    /* else fall through */
  } else if (cst_checkkind(cst, CST_BIN)) {
    CstBin* bin = (CstBin*)cst;
    if (cstop_isrelop(bin->op)) {
      ir_exprboolrelop(gen, bin, labelid, jmpcond);
      return;
    } else if (bin->op == CSTOP_AND) {
      if (jmpcond == true) {
        unsigned falselabel = ir_newlabel(gen);
        ir_exprbool(gen, bin->loperand, falselabel, false);
        ir_exprbool(gen, bin->roperand, labelid, true);
        ir_emit_label(gen, falselabel);
      } else {
        ir_exprbool(gen, bin->loperand, labelid, false);
        ir_exprbool(gen, bin->roperand, labelid, false);
      }
    } else if (bin->op == CSTOP_OR) {
      if (jmpcond == false) {
        unsigned truelabel = ir_newlabel(gen);
        ir_exprbool(gen, bin->loperand, truelabel, true);
        ir_exprbool(gen, bin->roperand, labelid, false);
        ir_emit_label(gen, truelabel);
      } else {
        ir_exprbool(gen, bin->loperand, labelid, true);
        ir_exprbool(gen, bin->roperand, labelid, true);
      }
    }
    /* else fall through */
  }
  if (cst_checkkind(cst, CST_INT)) {
    if ((((CstInt*)cst)->val != 0) == jmpcond)
      ir_emit_goto(gen, labelid);
    return;
  }
  VarOperand temp = ir_newtemp(gen);
  ir_expr(gen, cst, temp, false);
  ir_emit_gotoifi(gen, labelid, temp, (ConstOperand)0, CSTOP_NE, jmpcond);
}

static void ir_exprbin(Generator* gen, CstBin* bincst, VarOperand result, bool isref) {
  if (bincst->op == CSTOP_ASSIGN) {
    ir_exprassign(gen, bincst, result, isref, true);
    return;
  }
  if (cstop_isbool(bincst->op)) {
    unsigned truelabel = ir_newlabel(gen);
    unsigned continuelabel = ir_newlabel(gen);
    ir_exprbool(gen, (Cst*)bincst, truelabel, true);
    ir_emit_assign_fromconst(gen, result, (ConstOperand)0, isref);
    ir_emit_goto(gen, continuelabel);
    ir_emit_label(gen, truelabel);
    ir_emit_assign_fromconst(gen, result, (ConstOperand)1, isref);
    ir_emit_label(gen, continuelabel);
    return;
  }
  if (cst_checkkind(bincst->roperand, CST_INT)) {  /* constant, do compile time computation */
    ir_exprbini(gen, bincst, result, isref);
    return;
  }
  VarOperand loperand;
  if (cst_checkkind(bincst->loperand, CST_ID)) {
    loperand = symtbl_search(gen->symtbl, ((CstId*)bincst->loperand)->val)->attr.var;
  } else {
    loperand = ir_newtemp(gen);
    ir_expr(gen, bincst->loperand, loperand, false);
  }
  VarOperand roperand;
  if (cst_checkkind(bincst->roperand, CST_ID)) {
    roperand = symtbl_search(gen->symtbl, ((CstId*)bincst->roperand)->val)->attr.var;
  } else {
    roperand = ir_newtemp(gen);
    ir_expr(gen, bincst->roperand, roperand, false);
  }
  switch (bincst->op) {
    case CSTOP_ADD: {
      ir_emit_arith(gen, IR_ADD, result, loperand, roperand, IRTAG_NORMAL, isref);
      return;
    }
    case CSTOP_SUB: {
      ir_emit_arith(gen, IR_SUB, result, loperand, roperand, IRTAG_NORMAL, isref);
      return;
    }
    case CSTOP_MUL: {
      ir_emit_arith(gen, IR_MUL, result, loperand, roperand, IRTAG_NORMAL, isref);
      return;
    }
    case CSTOP_DIV: {
      ir_emit_arith(gen, IR_DIV, result, loperand, roperand, IRTAG_NORMAL, isref);
      return;
    }
    default: {
      assert(false);
      return;
    }
  }
}

static void ir_exprassign(Generator* gen, CstBin* bincst, VarOperand result, bool isref, bool result_valid) {
  Cst* lval = bincst->loperand;
  if (cst_checkkind(lval, CST_ID)) {
    ir_expr(gen, bincst->roperand, symtbl_search(gen->symtbl, ((CstId*)lval)->val)->attr.var, false);
    if (result_valid)
      ir_emit_assign_fromvar(gen, result, symtbl_search(gen->symtbl, ((CstId*)lval)->val)->attr.var, isref);
  } else {
    if (cst_checkkind(lval, CST_DOT)) {
      ir_error(gen, lval->lineno, "structure is not supported");
      ir_emit_assign_fromconst(gen, result, (ConstOperand)0, false);
      return;
    }
    assert(cst_checkkind(lval, CST_INDEX));
    CstIndex* indexcst = (CstIndex*)lval;
    Cst* arraypart = indexcst->arr;
    Cst* indexpart = indexcst->index;
    if (!cst_checkkind(arraypart, CST_ID)) {
      ir_error(gen, arraypart->lineno, "high dimension array, array returned by function, and structure are not supported");
      ir_emit_assign_fromconst(gen, result, (ConstOperand)0, false);
      return;
    }
    VarOperand addr = ir_newtemp(gen);
    if (cst_checkkind(indexpart, CST_INT)) {
      ir_emit_arithi(gen, IR_ADD, addr, symtbl_search(gen->symtbl, ((CstId*)arraypart)->val)->attr.var, ((CstInt*)indexpart)->val * 4, IRTAG_LOP_REF, false);
    } else if (cst_checkkind(indexcst, CST_ID)) {
      VarOperand offset = ir_newtemp(gen);
      ir_emit_arithi(gen, IR_MUL, offset, symtbl_search(gen->symtbl, ((CstId*)indexcst)->val)->attr.var, (ConstOperand)4, IRTAG_NORMAL, false);
      ir_emit_arith(gen, IR_ADD, addr, symtbl_search(gen->symtbl, ((CstId*)arraypart)->val)->attr.var, offset, IRTAG_LOP_REF, false);
    } else {
      VarOperand i = ir_newtemp(gen);
      ir_expr(gen, indexpart, i, false);
      VarOperand offset = ir_newtemp(gen);
      ir_emit_arithi(gen, IR_MUL, offset, i, (ConstOperand)4, IRTAG_NORMAL, false);
      ir_emit_arith(gen, IR_ADD, addr, symtbl_search(gen->symtbl, ((CstId*)arraypart)->val)->attr.var, offset, IRTAG_LOP_REF, false);
    }
    ir_expr(gen, bincst->roperand, addr, true);
    if (result_valid) {
      if (!isref) {
        ir_emit(gen, (IR) { .kind = IR_DEREF, .optag = IRTAG_NORMAL, .deref = { .result = result, .operand = addr } } );
        return;
      }
      VarOperand temp = ir_newtemp(gen);
      ir_emit(gen, (IR) { .kind = IR_DEREF, .optag = IRTAG_NORMAL, .deref = { .result = temp, .operand = addr } } );
      ir_emit_assign_fromvar(gen, result, temp, isref);
    }
  }
}

static void ir_exprpassargs(Generator* gen, CstList* arglist) {
  if (!arglist) return;
  if (arglist->isconstant) {
    ir_emit(gen, (IR) { .kind = IR_ARG, .optag = IRTAG_LOP_CONST, .arg = { .arg = arglist->tmp } });
  } else {
    ir_emit(gen, (IR) { .kind = IR_ARG, .optag = IRTAG_NORMAL, .arg = { .arg = arglist->tmp } });
  }
  ir_exprpassargs(gen, cstlist_next(arglist));
}

static void ir_exprcall(Generator* gen, CstCall* callcst, VarOperand result, bool isref) {
  if (!cst_checkkind(callcst->func, CST_ID)) {
    ir_error(gen, callcst->func->lineno, "calling an expression is not supported");
    ir_emit_assign_fromconst(gen, result, (ConstOperand)0, isref);
    return;
  }
  CstList* arglist = (CstList*)callcst->args;
  while (arglist) {
    Cst* arg = cstlist_get(arglist, Cst*);
    if (cst_checkkind(arg, CST_INT)) {
      arglist->tmp = ir_constoperand(((CstInt*)arg)->val);
      arglist->isconstant = true;
    } else if (cst_checkkind(arg, CST_ID)) {
      arglist->tmp = ir_varoperand(symtbl_search(gen->symtbl, ((CstId*)arg)->val)->attr.var);
      arglist->isconstant = false;
    } else {
      VarOperand temp = ir_newtemp(gen);
      arglist->tmp = ir_varoperand(temp);
      arglist->isconstant = false;
      ir_expr(gen, arg, temp, false);
    }
    arglist = cstlist_next(arglist);
  }
  ir_exprpassargs(gen, (CstList*)callcst->args);
  StringId funcname = ((CstId*)callcst->func)->val;
  if (isref) {
    VarOperand tmp = ir_newtemp(gen);
    ir_emit(gen, (IR) { .kind = IR_CALL, .optag = IRTAG_NORMAL, .call = { .result = tmp, .funcname = funcname } });
    ir_emit_assign_fromvar(gen, result, tmp, isref);
  } else {
    ir_emit(gen, (IR) { .kind = IR_CALL, .optag = IRTAG_NORMAL, .call = { .result = result, .funcname = funcname } });
  }
}

static void ir_exprindex(Generator* gen, CstIndex* indexcst, VarOperand result, bool isref) {
  Cst* arraypart = indexcst->arr;
  Cst* indexpart = indexcst->index;
  if (!cst_checkkind(arraypart, CST_ID)) {
    ir_error(gen, arraypart->lineno, "high dimension array, array returned by function, and structure are not supported");
    ir_emit_assign_fromconst(gen, result, (ConstOperand)0, false);
    return;
  }
  VarOperand addr = ir_newtemp(gen);
  if (cst_checkkind(indexpart, CST_INT)) {
    ir_emit_arithi(gen, IR_ADD, addr, symtbl_search(gen->symtbl, ((CstId*)arraypart)->val)->attr.var, ((CstInt*)indexpart)->val * 4, IRTAG_LOP_REF, false);
  } else if (cst_checkkind(indexcst, CST_ID)) {
    VarOperand offset = ir_newtemp(gen);
    ir_emit_arithi(gen, IR_MUL, offset, symtbl_search(gen->symtbl, ((CstId*)indexcst)->val)->attr.var, (ConstOperand)4, IRTAG_NORMAL, false);
    ir_emit_arith(gen, IR_ADD, addr, symtbl_search(gen->symtbl, ((CstId*)arraypart)->val)->attr.var, offset, IRTAG_LOP_REF, false);
  } else {
    VarOperand i = ir_newtemp(gen);
    ir_expr(gen, indexpart, i, false);
    VarOperand offset = ir_newtemp(gen);
    ir_emit_arithi(gen, IR_MUL, offset, i, (ConstOperand)4, IRTAG_NORMAL, false);
    ir_emit_arith(gen, IR_ADD, addr, symtbl_search(gen->symtbl, ((CstId*)arraypart)->val)->attr.var, offset, IRTAG_LOP_REF, false);
  }
  if (!isref) {
    ir_emit(gen, (IR) { .kind = IR_DEREF, .optag = IRTAG_NORMAL, .deref = { .result = result, .operand = addr } } );
    return;
  }
  VarOperand temp = ir_newtemp(gen);
  ir_emit(gen, (IR) { .kind = IR_DEREF, .optag = IRTAG_NORMAL, .deref = { .result = temp, .operand = addr } } );
  ir_emit_assign_fromvar(gen, result, temp, isref);
}

static void ir_exprdot(Generator* gen, CstDot* dotcst, VarOperand result, bool isref) {
  ir_error(gen, dotcst->lineno, "not supported");
  ir_emit_assign_fromconst(gen, result, (ConstOperand)0, isref);
}

static void ir_expr(Generator* gen, Cst* cst, VarOperand result, bool isref) {
  switch (cst_kind(cst)) {
    case CST_INT: {
      ir_emit_assign_fromconst(gen, result, ((CstInt*)cst)->val, isref);
      return;
    }
    case CST_FLOAT: {
      ir_error(gen, cst->lineno, "floating constant is not supported");
      ir_emit_assign_fromconst(gen, result, (ConstOperand)0, isref);
      return;
    }
    case CST_ID: {
      ir_emit_assign_fromvar(gen, result, symtbl_search(gen->symtbl, ((CstId*)cst)->val)->attr.var, isref);
      return;
    }
    case CST_BIN: {
      ir_exprbin(gen, (CstBin*)cst, result, isref);
      return;
    }
    case CST_PRE: {
      CstPre* precst = (CstPre*)cst;
      if (precst->op == CSTOP_NOT) {
        unsigned truelabel = ir_newlabel(gen);
        unsigned continuelabel = ir_newlabel(gen);
        ir_exprbool(gen, (Cst*)precst, truelabel, true);
        ir_emit_assign_fromconst(gen, result, (ConstOperand)0, isref);
        ir_emit_goto(gen, continuelabel);
        ir_emit_label(gen, truelabel);
        ir_emit_assign_fromconst(gen, result, (ConstOperand)1, isref);
        ir_emit_label(gen, continuelabel);
        return;
      } else {  /* else is CSTOP_NEG */
        assert(precst->op == CSTOP_NEG);
        if (cst_checkkind(precst->operand, CST_INT)) {  /* constant, do compile time computation */
          ir_emit_assign_fromconst(gen, result, (ConstOperand)(-((CstInt*)precst->operand)->val), isref);
          return;
        }
        VarOperand tmp_zero = ir_newtemp(gen);
        ir_emit_assign_fromconst(gen, tmp_zero, (ConstOperand)0, false);
        VarOperand operand = ir_newtemp(gen);
        ir_expr(gen, precst->operand, operand, false);
        ir_emit_arithi(gen, IR_SUB, result, tmp_zero, operand, IRTAG_NORMAL, isref);
        return;
      }
    }
    case CST_CALL: {
      ir_exprcall(gen, (CstCall*)cst, result, isref);
      return;
    }
    case CST_INDEX: {
      ir_exprindex(gen, (CstIndex*)cst, result, isref);
      return;
    }
    case CST_DOT: {
      ir_exprdot(gen, (CstDot*)cst, result, isref);
      return;
    }
    default: {
      assert(false);
      return;
    }
  }
}

static void ir_vardec(Generator* gen, CstDec* dec) {
  assert(cst_checkkind(dec, CST_DEC));
  Cst* vardec = dec->vardec;
  while (!cst_checkkind(vardec, CST_ID))
    vardec = ((CstDecArr*)vardec)->vardec;
  StringId varname = ((CstId*)vardec)->val;
  Symbol* symbol = symtbl_search(gen->symtbl, varname);
  assert(symbol);
  BaseType* base = typetbl_get(gen->typetbl, symbol->attr.type.basetype);
  if (base->kind != TYPE_BASIC || base->basic != BTYPE_INT) {
    ir_error(gen, dec->lineno, "unsupported type");
    return;
  }
  if (symbol->attr.type.dim >= 2) {
    ir_error(gen, dec->lineno, "high dimension array");
    return;
  }
  VarOperand var = ir_newtemp(gen);
  symbol->attr.var = var;
  if (symbol->attr.type.dim == 1)
    ir_emit(gen, (IR) { .kind = IR_DEC, .optag = IRTAG_NORMAL, .dec = { .result = var, .size = symbol->attr.type.size * 4  } });
  if (dec->initval)
    ir_expr(gen, dec->initval, var, false);
}

static void ir_deflist(Generator* gen, CstList* deflist) {
  while (deflist) {
    CstDef* def = cstlist_get(deflist, CstDef*);
    assert(cst_checkkind(def, CST_DEF));
    CstList* declist = (CstList*)def->declist;
    while (declist) {
      assert(cst_checkkind(cstlist_get(declist, CstDec*), CST_DEC));
      ir_vardec(gen, cstlist_get(declist, CstDec*));
      declist = cstlist_next(declist);
    }
    deflist = cstlist_next(deflist);
  }
}

static void ir_stmt(Generator* gen, Cst* stmt) {
  switch (stmt->kind) {
    case CST_STMTWHILE: {
      ir_stmtwhile(gen, (CstStmtWhile*)stmt);
      break;
    }
    case CST_STMTIF: {
      ir_stmtif(gen, (CstStmtIf*)stmt);
      break;
    }
    case CST_STMTEXPR: {
      ir_stmtexpr(gen, (CstStmtExpr*)stmt);
      break;
    }
    case CST_STMTRETURN: {
      ir_stmtreturn(gen, (CstStmtReturn*)stmt);
      break;
    }
    case CST_STMTCOMP: {
      ir_stmtcomp(gen, (CstStmtComp*)stmt);
      break;
    }
    default: {
      assert(false);
      break;
    }
  }
}

static void ir_stmtcomp(Generator* gen, CstStmtComp* comp) {
  ir_deflist(gen, (CstList*)comp->deflist);
  CstList* stmtlist = (CstList*)comp->stmtlist;
  while (stmtlist) {
    ir_stmt(gen, cstlist_get(stmtlist, Cst*));
    stmtlist = cstlist_next(stmtlist);
  }
}

static void ir_stmtif(Generator* gen, CstStmtIf* stmtif) {
  unsigned falselabel = ir_newlabel(gen);
  ir_exprbool(gen, stmtif->cond, falselabel, false);
  ir_stmt(gen, stmtif->if_stmt);
  if (stmtif->else_stmt) {
    unsigned outlabel = ir_newlabel(gen);
    ir_emit_goto(gen, outlabel);
    ir_emit_label(gen, falselabel);
    ir_stmt(gen, stmtif->else_stmt);
    ir_emit_label(gen, outlabel);
  } else {
    ir_emit_label(gen, falselabel);
  }
}

static void ir_stmtwhile(Generator* gen, CstStmtWhile* stmtwhile) {
  unsigned looplabel = ir_newlabel(gen);
  unsigned loopentry = ir_newlabel(gen);
  ir_emit_goto(gen, loopentry);
  ir_emit_label(gen, looplabel);
  ir_stmt(gen, stmtwhile->stmt);
  ir_emit_label(gen, loopentry);
  ir_exprbool(gen, stmtwhile->cond, looplabel, true);
}

static void ir_stmtexpr(Generator* gen, CstStmtExpr* stmtexpr) {
  Cst* expr = stmtexpr->expr;
  if (cst_checkkind(expr, CST_BIN) && ((CstBin*)expr)->op == CSTOP_ASSIGN) {
    /* the 'result' is not not important */
    ir_exprassign(gen, (CstBin*)expr, (VarOperand)0, false, false);
  } else {
    VarOperand temp = ir_newtemp(gen);
    ir_expr(gen, expr, temp, false);
  }
}

static void ir_stmtreturn(Generator* gen, CstStmtReturn* stmtreturn) {
  Cst* expr = stmtreturn->expr;
  if (cst_checkkind(expr, CST_INT)) {
    ir_emit(gen, (IR) { .kind = IR_RETURN, .optag = IRTAG_LOP_CONST, .ir_return = { .retval = ir_constoperand(((CstInt*)expr)->val) } });
  } else if (cst_checkkind(expr, CST_ID)) {
    ir_emit(gen, (IR) { .kind = IR_RETURN, .optag = IRTAG_NORMAL, .ir_return = { .retval = ir_varoperand(symtbl_search(gen->symtbl, ((CstId*)expr)->val)->attr.var) } });
  } else {
    VarOperand retval = ir_newtemp(gen);
    ir_expr(gen, expr, retval, false);
    ir_emit(gen, (IR) { .kind = IR_RETURN, .optag = IRTAG_NORMAL, .ir_return = { .retval = ir_varoperand(retval) } });
  }
}

static void ir_function(Generator* gen, CstExtDefFunc* deffunc) {
  CstFuncDec* funcdec = (CstFuncDec*)deffunc->funcdec;
  CstList* paramlist = (CstList*)funcdec->paramlist;
  ir_emit(gen, (IR) { .kind = IR_FUNCTION, .optag = IRTAG_NORMAL, .function = { .name =  funcdec->funcname } });
  while (paramlist) {
    CstParam* param = cstlist_get(paramlist, CstParam*);
    assert(cst_checkkind(param, CST_PARAM));
    Cst* vardec = param->vardec;
    while (!cst_checkkind(vardec, CST_ID))
      vardec = ((CstDecArr*)vardec)->vardec;
    StringId varname = ((CstId*)vardec)->val;
    Symbol* symbol = symtbl_search(gen->symtbl, varname);
    assert(symbol);
    BaseType* base = typetbl_get(gen->typetbl, symbol->attr.type.basetype);
    if (base->kind != TYPE_BASIC || base->basic != BTYPE_INT) {
      ir_error(gen, paramlist->lineno, "unsupported type");
      return;
    }
    if (symbol->attr.type.dim >= 2) {
      ir_error(gen, paramlist->lineno, "high dimension array");
      return;
    }
    VarOperand var = ir_newtemp(gen);
    symbol->attr.var = var;
    ir_emit(gen, (IR) { .kind = IR_PARAM, .optag = IRTAG_NORMAL, .param = { .paramid = var } });
    paramlist = cstlist_next(paramlist);
  }
  ir_stmt(gen, deffunc->stmt);
}

static void ir_append_stdlib(Generator* gen) {
  const char* read = strtbl_newstring(gen->strtbl, "read");
  if (!read) ir_fatalerror(gen, "out of memory");
  StringId readid = strtbl_stringid(gen->strtbl, read);
  const char* write = strtbl_newstring(gen->strtbl, "write");
  if (!write) ir_fatalerror(gen, "out of memory");
  StringId writeid = strtbl_stringid(gen->strtbl, write);
  ir_emit(gen, (IR) { .kind = IR_FUNCTION, .optag = IRTAG_NORMAL, .function = { .name = readid } });
  VarOperand result = ir_newtemp(gen);
  ir_emit(gen, (IR) { .kind = IR_READ, .optag = IRTAG_NORMAL, .read = { .result = result } });
  ir_emit(gen, (IR) { .kind = IR_RETURN, .optag = IRTAG_NORMAL, .ir_return = { .retval = ir_varoperand(result) } });

  ir_emit(gen, (IR) { .kind = IR_FUNCTION, .optag = IRTAG_NORMAL, .function = { .name = writeid } });
  VarOperand param = ir_newtemp(gen);
  ir_emit(gen, (IR) { .kind = IR_PARAM, .optag = IRTAG_NORMAL, .param = { .paramid = param } });
  ir_emit(gen, (IR) { .kind = IR_WRITE, .optag = IRTAG_NORMAL, .write = { .writeval = ir_varoperand(param) } });
  ir_emit(gen, (IR) { .kind = IR_RETURN, .optag = IRTAG_LOP_CONST, .ir_return = { .retval = ir_constoperand(0) } });
}

Code ir_gen(CstList* extdeflist, TypeTbl* typetbl, SymTbl* symtbl, StrTbl* strtbl) {
  Generator gen = {
    .typetbl = typetbl,
    .symtbl = symtbl,
    .strtbl = strtbl,
    .labelid = 0,
    .varid = 0,
  };
  if (!irarr_init(&gen.code, 32)) {
    ir_error(&gen, extdeflist->lineno, "out of memory");
    return (Code) { .code = NULL, .codelen = 0 };
  }
  if (setjmp(gen.errorpos) == 0) {
    while (extdeflist) {
      Cst* extdef = cstlist_get(extdeflist, Cst*);
      if (cst_checkkind(extdef, CST_EXTDEFFUNC)) {
        CstExtDefFunc* extdeffunc = (CstExtDefFunc*)extdef;
        ir_function(&gen, extdeffunc);
      } else {
        /* need not to handle */
      }
      extdeflist = cstlist_next(extdeflist);
    }
    ir_append_stdlib(&gen);
  } else {
    irarr_destroy(&gen.code);
    return (Code) { .code = NULL, .codelen = 0 };
  }
  irarr_shrink(&gen.code);
  unsigned codelen = irarr_size(&gen.code);
  return (Code) { .code = irarr_steal(&gen.code), .codelen = codelen };
}

static void ir_print_arith(IR ir, FILE* out, char op) {
  fprintf(out, "%st%u := %ct%u %c ", ir.optag & IRTAG_RES_DEREF ? "*" : "", ir.bin.result,
          ir.optag & IRTAG_LOP_REF    ? '&' :
          ir.optag & IRTAG_LOP_DEREF  ? '*' : ' ',
          ir.bin.loperand, op);
  if (ir.optag & IRTAG_ROP_CONST) {
    fprintf(out, "#%i\n", ir.bin.roperand.constant);
  } else {
    assert((ir.optag & (IRTAG_ROP_DEREF | IRTAG_ROP_CONST | IRTAG_ROP_REF)) == 0);
    fprintf(out, "t%u\n", ir.bin.roperand.variable);
  }
}

void ir_print(Code* code, StrTbl* strtbl, FILE* out) {
  for (size_t i = 0; i < code->codelen; ++i) {
    IR ir = code->code[i];
    switch (ir.kind) {
      case IR_LABEL: {
        fprintf(out, "LABEL L%u :\n", ir.label.labelid);
        break;
      }
      case IR_FUNCTION: {
        if (i != 0) fputc('\n', out);
        fprintf(out, "FUNCTION %s :\n", strtbl_getstring(strtbl, ir.function.name));
        break;
      }
      case IR_ASSIGN: {
        fprintf(out, "t%u := ", ir.assign.result);
        if (ir.optag & IRTAG_LOP_CONST) {
          fprintf(out, "#%i\n", ir.assign.operand.constant);
        } else {
          fprintf(out, "t%u\n", ir.assign.operand.variable);
        }
        break;
      }
      case IR_ADD: {
        ir_print_arith(ir, out, '+');
        break;
      }
      case IR_SUB: {
        ir_print_arith(ir, out, '-');
        break;
      }
      case IR_MUL: {
        ir_print_arith(ir, out, '*');
        break;
      }
      case IR_DIV: {
        ir_print_arith(ir, out, '/');
        break;
      }
      case IR_DEREF: {
        fprintf(out, "t%u := *t%u\n", ir.deref.result, ir.deref.operand);
        break;
      }
      case IR_REF_ASSIGN: {
        fprintf(out, "*t%u := ", ir.ref_assign.result);
        if (ir.optag & IRTAG_LOP_CONST) {
          fprintf(out, "#%i\n", ir.ref_assign.operand.constant);
        } else {
          fprintf(out, "t%u\n", ir.ref_assign.operand.variable);
        }
        break;
      }
      case IR_GOTO: {
        fprintf(out, "GOTO L%u\n", ir.ir_goto.labelid);
        break;
      }
      case IR_COND_GOTO: {
        static const char* relopname[] = {
          [CSTOP_NE] = "!=",
          [CSTOP_EQ] = "==",
          [CSTOP_LE] = "<=",
          [CSTOP_GE] = ">=",
          [CSTOP_LT] = "<",
          [CSTOP_GT] = ">",
        };
        fprintf(out, "IF t%u %s ", ir.cond_goto.loperand, relopname[ir.cond_goto.relop]);
        if (ir.optag & IRTAG_ROP_CONST) {
          fprintf(out, "#%i GOTO L%u\n", ir.cond_goto.roperand.constant, ir.cond_goto.labelid);
        } else {
          fprintf(out, "t%u GOTO L%u\n", ir.cond_goto.roperand.variable, ir.cond_goto.labelid);
        }
        break;
      }
      case IR_RETURN: {
        if (ir.optag & IRTAG_LOP_CONST) {
          fprintf(out, "RETURN #%i\n", ir.ir_return.retval.constant);
        } else {
          fprintf(out, "RETURN t%u\n", ir.ir_return.retval.variable);
        }
        break;
      }
      case IR_DEC: {
        fprintf(out, "DEC t%u %u\n", ir.dec.result, ir.dec.size);
        break;
      }
      case IR_ARG: {
        if (ir.optag & IRTAG_LOP_CONST) {
          fprintf(out, "ARG #%i\n", ir.arg.arg.constant);
        } else {
          fprintf(out, "ARG t%u\n", ir.arg.arg.variable);
        }
        break;
      }
      case IR_CALL: {
        fprintf(out, "t%u := CALL %s\n", ir.call.result, strtbl_getstring(strtbl, ir.call.funcname));
        break;
      }
      case IR_PARAM: {
        fprintf(out, "PARAM t%u\n", ir.param.paramid);
        break;
      }
      case IR_READ: {
        fprintf(out, "READ t%u\n", ir.read.result);
        break;
      }
      case IR_WRITE: {
        if (ir.optag & IRTAG_LOP_CONST) {
          fprintf(out, "WRITE #%i\n", ir.write.writeval.constant);
        } else {
          fprintf(out, "WRITE t%u\n", ir.write.writeval.variable);
        }
        break;
      }
      default: {
        assert(false);
        break;
      }
    }
  }
}

static void ir_fatalerror(Generator* gen, const char* message) {
  fprintf(stderr, "fatal error: %s\n", message);
  longjmp(gen->errorpos, 1);
}

static void ir_error(Generator* gen, int lineno, const char* message) {
  (void)gen;
  mycc_error("C", lineno, message);
}
