#ifndef _SYMTBL_H_
#define _SYMTBL_H_

#include "iroperand.h"
#include "strtbl.h"
#include "type.h"
#include "typetbl.h"
#include <stdlib.h>

typedef struct tagSymbol Symbol;

typedef enum tagSymBolKind {
  SYMBOL_VARIABLE,
  SYMBOL_FUNCTION,
  SYMBOL_STRUCT,
} SymbolKind;

typedef struct tagSymbolAttr {
  SymbolKind kind;
  Type type;
  VarOperand var;
} SymbolAttr;

struct tagSymbol {
  StringId name;
  SymbolAttr attr;
  size_t hash;
  Symbol* next;
};

typedef struct tagSymTbl SymTbl;
struct tagSymTbl {
  Symbol** array;
  size_t capacity;
  size_t size;
  StrTbl* strtbl;
};


bool symtbl_init(SymTbl* symtbl, size_t capacity, StrTbl* strtbl);
void symtbl_destroy(SymTbl* symtbl);
SymTbl* symtbl_create(size_t capacity, StrTbl* strtbl);
void symtbl_delete(SymTbl* symtbl);

static inline Symbol* symtbl_iter_begin(SymTbl* symtbl);
static inline Symbol* symtbl_iter_next(SymTbl* symtbl, Symbol* symbol);

Symbol* symtbl_insert(SymTbl* symtbl, StringId name);
Symbol* symtbl_search(SymTbl* symtbl, StringId name);
static inline size_t symtbl_size(SymTbl* symtbl);

static inline Symbol* symtbl_iter_begin(SymTbl* symtbl) {
  for (size_t i = 0; i < symtbl->capacity; ++i) {
    if (symtbl->array[i])
      return symtbl->array[i];
  }
  return NULL;
}

static inline Symbol* symtbl_iter_next(SymTbl* symtbl, Symbol* symbol) {
  if (symbol->next) return symbol->next;
  size_t index = symbol->hash & (symtbl->capacity - 1);
  for (size_t i = index + 1; i < symtbl->capacity; ++i) {
    if (symtbl->array[i])
      return symtbl->array[i];
  }
  return NULL;
}

static inline size_t symtbl_size(SymTbl* symtbl) {
  return symtbl->size;
}

#endif
