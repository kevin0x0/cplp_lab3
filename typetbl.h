#ifndef _TYPETBL_H_
#define _TYPETBL_H_

#include "array.h"
#include "cst.h"
#include "strtbl.h"
#include "type.h"

typedef enum tagTypeKind {
  TYPE_FUNC,
  TYPE_STRUCT,
  TYPE_BASIC,
  TYPE_ERROR,
} TypeKind;

typedef struct tagStructFieldDesc {
  StringId name;
  Type type;
} StructFieldDesc;

typedef struct tagStructType {
  size_t nfield;
  StructFieldDesc fields[];
} StructType;

typedef struct tagBaseType {
  BaseTypeId id;
  TypeKind kind;
  union {
    BasicType basic;
    /* for function, under the conditions required by the experiment,
     * It's not necessary to check whether the number and types of parameters match
     * that of arguments. So we only need to record the return type. */
    Type function_rettype;
    StructType* structtype;
  };
} BaseType;

typedef struct tagTypeTbl {
  Array types;       /* all entries */
} TypeTbl;


bool typetbl_init(TypeTbl* typetbl);
void typetbl_destroy(TypeTbl* typetbl);

BaseType* typetbl_newstruct(TypeTbl* typetbl, size_t nfield);
BaseType* typetbl_newerror(TypeTbl* typetbl);
BaseType* typetbl_newfunction(TypeTbl* typetbl);
BaseType* typetbl_newbasic(TypeTbl* typetbl, BasicType basictype);

static inline BaseType* typetbl_get(TypeTbl* typetbl, BaseTypeId id) {
  assert(id < array_size(&typetbl->types));
  return (BaseType*)array_access(&typetbl->types, id);
}

#endif
