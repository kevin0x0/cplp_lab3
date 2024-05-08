#include "strtbl.h"
#include <stdlib.h>
#include <string.h>

StrTbl* strtbl_create(void) {
  StrTbl* strtab = (StrTbl*)malloc(sizeof (StrTbl));
  if (!strtab) return NULL;
  strtab->stack = NULL;
  strtab->curr = NULL;
  strtab->end = NULL;
  if ((!strtbl_grow(strtab, KLSTRTAB_EXTRA))) {
    free(strtab);
    return NULL;
  }
  return strtab;
}

void strtbl_delete(StrTbl* strtab) {
  assert(strtab != NULL && strtab->stack != NULL);

  free(strtab->stack);
  free(strtab);
}

char* strtbl_grow(StrTbl* strtab, size_t extra) {
  size_t expectedcap = strtbl_size(strtab) + extra;
  size_t newcap = 2 * strtbl_capacity(strtab);
  if (newcap < expectedcap) newcap = expectedcap;
  char* newstk = (char*)realloc(strtab->stack, sizeof (char) * newcap);
  if ((!newstk)) return NULL;
  size_t curroffset = strtbl_size(strtab);
  strtab->stack = newstk;
  strtab->curr = newstk + curroffset;
  strtab->end = newstk + newcap;
  return strtab->curr;
}
