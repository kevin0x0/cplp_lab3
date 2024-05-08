#ifndef _GENIR_H_
#define _GENIR_H_

#include "iroperand.h"
#include "cst.h"
#include "kgarray.h"
#include "strtbl.h"
#include "symtbl.h"
#include "typetbl.h"

typedef enum tagIRKind {
  IR_LABEL,
  IR_FUNCTION,
  IR_ASSIGN,
  IR_ADD,
  IR_SUB,
  IR_MUL,
  IR_DIV,
  IR_DEREF,
  IR_REF_ASSIGN,
  IR_GOTO,
  IR_COND_GOTO,
  IR_RETURN,
  IR_DEC,
  IR_ARG,
  IR_CALL,
  IR_PARAM,
  IR_READ,
  IR_WRITE,
} IRKind;

#define bit(n)            ((unsigned)1 << (n))
#define IRTAG_NORMAL      (0)
#define IRTAG_LOP_DEREF   bit(0)
#define IRTAG_LOP_REF     bit(1)
#define IRTAG_LOP_CONST   bit(2)
#define IRTAG_ROP_DEREF   bit(3)
#define IRTAG_ROP_REF     bit(4)
#define IRTAG_ROP_CONST   bit(5)
#define IRTAG_RES_DEREF   bit(6)

typedef struct tagIR {
  IRKind kind;
  unsigned optag; /* operand tag */
  union {
    struct {
      VarOperand result;
      VarOperand loperand;
      Operand roperand;
    } bin;
    struct {
      VarOperand result;
      Operand operand;
    } assign;
    struct {
      VarOperand result;
      Operand operand;
    } ref_assign;
    struct {
      VarOperand result;
      VarOperand operand;
    } deref;
    struct {
      VarOperand result;
      VarOperand operand;
    } ref;
    struct {
      StringId name;
    } function;
    struct {
      VarOperand result;
      unsigned size;
    } dec;
    struct {
      VarOperand result;
      StringId funcname;
    } call;
    struct {
      unsigned labelid;
    } ir_goto;
    struct {
      CstOp relop;
      VarOperand loperand;
      Operand roperand;
      unsigned labelid;
    } cond_goto;
    struct {
      VarOperand paramid;
    } param;
    struct {
      Operand arg;
    } arg;
    struct {
      Operand retval;
    } ir_return;
    struct {
      unsigned labelid;
    } label;
    struct {
      VarOperand result;
    } read;
    struct {
      Operand writeval;
    } write;
  };
} IR;

kgarray_decl(IR, IRArray, irarr, pass_val,);

/* this serves as the final result of IR generator */
typedef struct tagCode {
  IR* code;
  unsigned codelen;
} Code;

Code ir_gen(CstList* extdeflist, TypeTbl* typetbl, SymTbl* symtbl, StrTbl* strtbl);
void ir_print(Code* code, StrTbl* strtbl, FILE* out);


#endif
