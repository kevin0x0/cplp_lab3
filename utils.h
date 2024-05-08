#ifndef _UTILS_H_
#define _UTILS_H_

#include <stdio.h>
#include <stdlib.h>

static inline void utils_oom(void) {
  fprintf(stderr, "out of memory\n");
  exit(1);
}

static inline void utils_oom_ifnull(void* p) {
  if (!p) utils_oom();
}

#endif
