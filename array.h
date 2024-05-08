#ifndef _ARRAY_H_
#define _ARRAY_H_

#include <stddef.h>
#include <stdbool.h>
#include <stdlib.h>

typedef struct tagArray {
  void** begin;
  void** end;
  void** current;
} Array;

bool array_init(Array* array);
void array_destroy(Array* array);
Array* array_create(void);
void array_delete(Array* array);

static inline void* array_swap(Array* array, size_t index, void* value);
static inline bool array_push_back(Array* array, void* addr);
static inline void array_pop_back(Array* array);
static inline void array_make_empty(Array* array);
bool array_expand(Array* array);
static inline void* array_access(Array* array, size_t index);
static inline void* array_top(Array* array);
static inline void* array_front(Array* array);
static inline size_t array_size(Array* array);
static inline size_t array_capacity(Array* array);
/* shrink the array to exactly fit its size */
static inline void array_shrink(Array* array);
static inline void** array_steal(Array* array);
static inline void** array_raw(Array* array);

static inline size_t array_size(Array* array) {
  return array->current - array->begin;
}

static inline size_t array_capacity(Array* array) {
  return array->end - array->begin;
}

static inline void array_shrink(Array* array) {
  size_t size = array_size(array);
  size_t shrinksize = size == 0 ? 1 : size;
  void** newarr = (void**)realloc(array->begin, shrinksize * sizeof (void*));
  if (newarr) {
    array->begin = newarr;
    array->current = array->begin + size;
    array->end = array->begin + shrinksize;
  }
}

static inline bool array_push_back(Array* array, void* addr) {
  if (array->current == array->end &&
      !array_expand(array)) {
    return false;
  }
  *array->current++ = addr;
  return true;
}

static inline void array_pop_back(Array* array) {
  array->current--;
}

static inline void* array_access(Array* array, size_t index) {
  return array->begin[index];
}

static inline void* array_top(Array* array) {
  return *(array->current - 1);
}

static inline void* array_front(Array* array) {
  return array->begin[0];
}

static inline void array_make_empty(Array* array) {
  array->current = array->begin;
}

static inline void** array_steal(Array* array) {
  void** ret = array->begin;
  array->begin = NULL;
  array->current = NULL;
  array->end = NULL;
  return ret;
}

static inline void** array_raw(Array* array) {
  return array->begin;
}

static inline void* array_swap(Array* array, size_t index, void* value) {
  void* ret = array->begin[index];
  array->begin[index] = value;
  return ret;
}

#endif
