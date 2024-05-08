#include "array.h"

#include <stdlib.h>

#define KARRAY_SIZE       (4)

bool array_init(Array* array) {
  if (!array) return false;
  if (!(array->begin = (void**)malloc(sizeof (void*) * KARRAY_SIZE))) {
    array->end = NULL;
    array->current = NULL;
    return false;
  }

  array->end = array->begin + KARRAY_SIZE;
  array->current = array->begin;
  return true;
}

void array_destroy(Array* array) {
  if (!array) return;
  free(array->begin);
  array->begin = NULL;
  array->end = NULL;
  array->current = NULL;
}

Array* array_create(void) {
  Array* array = (Array*)malloc(sizeof (Array));
  if (!array || !array_init(array)) {
    array_delete(array);
    return NULL;
  }
  return array;
}

void array_delete(Array* array) {
  array_destroy(array);
  free(array);
}

bool array_expand(Array* array) {
  size_t new_size = array_size(array) * 2;
  void** new_array = (void**)realloc(array->begin, sizeof (void*) * new_size);
  if (!new_array) return false;
  array->current = new_array + (array->current - array->begin);
  array->begin = new_array;
  array->end = new_array + new_size;
  return true;
}


