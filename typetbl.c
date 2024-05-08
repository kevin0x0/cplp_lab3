#include "typetbl.h"
#include "array.h"

bool typetbl_init(TypeTbl* typetbl) {
  if (!array_init(&typetbl->types))
    return false;
  return true;
}

void typetbl_destroy(TypeTbl* typetbl) {
  for (size_t i = 0; i < array_size(&typetbl->types); ++i) {
    BaseType* type = array_access(&typetbl->types, i);
    if (type->kind == TYPE_STRUCT)
      free(type->structtype);
    free(type);
  }
  array_destroy(&typetbl->types);
}

BaseType* typetbl_newstruct(TypeTbl* typetbl, size_t nfield) {
  StructType* structtype = (StructType*)malloc(sizeof (StructType) + sizeof (StructFieldDesc) * nfield);
  if (!structtype) return NULL;
  structtype->nfield = nfield;
  BaseType* type = (BaseType*)malloc(sizeof (BaseType));
  if (!type) {
    free(structtype);
    return NULL;
  }
  if (!array_push_back(&typetbl->types, type)) {
    free(structtype);
    free(type);
    return NULL;
  }
  type->structtype = structtype;
  type->kind = TYPE_STRUCT;
  type->id = array_size(&typetbl->types) - 1;
  return type;
}

BaseType* typetbl_newerror(TypeTbl* typetbl) {
  BaseType* type = (BaseType*)malloc(sizeof (BaseType));
  if (!type) return NULL;
  if (!array_push_back(&typetbl->types, type)) {
    free(type);
    return NULL;
  }
  type->kind = TYPE_ERROR;
  type->id = array_size(&typetbl->types) - 1;
  return type;
}

BaseType* typetbl_newfunction(TypeTbl* typetbl) {
  BaseType* type = (BaseType*)malloc(sizeof (BaseType));
  if (!type) return NULL;
  if (!array_push_back(&typetbl->types, type)) {
    free(type);
    return NULL;
  }
  type->kind = TYPE_FUNC;
  type->id = array_size(&typetbl->types) - 1;
  return type;
}

BaseType* typetbl_newbasic(TypeTbl* typetbl, BasicType basictype) {
  BaseType* type = (BaseType*)malloc(sizeof (BaseType));
  if (!type) return NULL;
  if (!array_push_back(&typetbl->types, type)) {
    free(type);
    return NULL;
  }
  type->kind = TYPE_BASIC;
  type->basic = basictype;
  type->id = array_size(&typetbl->types) - 1;
  return type;
}

