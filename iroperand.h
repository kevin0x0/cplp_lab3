#ifndef _IROPERAND_H_
#define _IROPERAND_H_

typedef int ConstOperand;
typedef unsigned VarOperand;
typedef union tagOperand {
  ConstOperand constant;
  VarOperand variable;
} Operand;


#endif
