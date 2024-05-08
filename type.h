#ifndef _TYPE_H_
#define _TYPE_H_


typedef unsigned BaseTypeId;
/* Under the conditions required by the experiment,
 * arrays are considered identical as long as their base types and dimensions
 * are the same. So we only need to record the base type and dimension.
 * (Non-array type is considered to have 0 dimension). */
typedef struct tagType {
  BaseTypeId basetype;
  unsigned dim;
  unsigned size; /* size (count by element) of the highest dimension */
} Type;

#define type_is_same(t1, t2)  ((t1).basetype == (t2).basetype && (t1).dim == (t2).dim)

static inline Type maketype(BaseTypeId base, unsigned dim, unsigned size) {
  return (Type) { .basetype = base, .dim = dim, .size = size };
}

#endif
