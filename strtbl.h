#ifndef _STRTBL_H_
#define _STRTBL_H_

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <string.h>
#include <assert.h>

#define KLSTRTAB_EXTRA    (4096)

typedef struct tagStrTbl {
  char* stack;
  char* curr;
  char* end;
} StrTbl;

typedef uint32_t StringId;

StrTbl* strtbl_create(void);
void strtbl_delete(StrTbl* strtbl);

static inline size_t strtbl_residual(StrTbl* strtbl);
static inline size_t strtbl_capacity(StrTbl* strtbl);
static inline size_t strtbl_size(StrTbl* strtbl);

char* strtbl_grow(StrTbl* strtbl, size_t extra);
static inline bool strtbl_checkspace(StrTbl* strtbl, size_t space);
/* get a pointer to the top of the stack. */
static inline char* strtbl_allocstring(StrTbl* strtbl, size_t size);
/* length includes the trailing '\0' */
static inline StringId strtbl_pushstring(StrTbl* strtbl, size_t length);
static inline char* strtbl_newstring(StrTbl* strtbl, const char* str);
/* get offset(id) of a string in the string table. */
static inline StringId strtbl_stringid(StrTbl* strtbl, const char* str);
/* get string by offset(id). */
static inline char* strtbl_getstring(StrTbl* strtbl, StringId id);


static inline size_t strtbl_residual(StrTbl* strtbl) {
  return strtbl->end - strtbl->curr;
}

static inline size_t strtbl_capacity(StrTbl* strtbl) {
  return strtbl->end - strtbl->stack;
}

static inline size_t strtbl_size(StrTbl* strtbl) {
  return strtbl->curr - strtbl->stack;
}

static inline bool strtbl_checkspace(StrTbl* strtbl, size_t space) {
  return strtbl_residual(strtbl) >= space;
}

static inline char* strtbl_allocstring(StrTbl* strtbl, size_t size) {
  if (!strtbl_checkspace(strtbl, size))
    return strtbl_grow(strtbl, size);
  return strtbl->curr;
}

static inline StringId strtbl_pushstring(StrTbl* strtbl, size_t length) {
  StringId id = strtbl->curr - strtbl->stack;
  strtbl->curr += length;
  return id;
}

static inline char* strtbl_newstring(StrTbl* strtbl, const char* str) {
  int len = strlen(str) + 1;
  char* mystr = strtbl_allocstring(strtbl, len);
  if (!mystr) return mystr;
  strcpy(mystr, str);
  strtbl_pushstring(strtbl, len);
  return mystr;
}

static inline StringId strtbl_stringid(StrTbl* strtbl, const char* str) {
  assert(str >= strtbl->stack && str <= strtbl->curr);

  return str - strtbl->stack;
}

static inline char* strtbl_getstring(StrTbl* strtbl, StringId id) {
  assert(id <= strtbl_size(strtbl));

  return strtbl->stack + id;
}

#endif
