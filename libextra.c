#include <stddef.h>
#include <stdio.h>
#include <stdint.h>
#include <stdbool.h>
#include <math.h>

#define STORABLE(ty)\
ty peek_##ty(ty* ptr) {\
  return *ptr;\
}\
\
void poke_##ty(ty* ptr, ty x) {\
  *ptr = x;\
}

STORABLE(uint8_t)
STORABLE(uint16_t)
STORABLE(uint32_t)
STORABLE(uint64_t)
STORABLE(int8_t)
STORABLE(int16_t)
STORABLE(int32_t)
STORABLE(int64_t)
STORABLE(float)
STORABLE(double)

bool ptr_eq(void *ptr_a, void *ptr_b) {
  return ptr_a == ptr_b;
}

void* ptr_plus(void *ptr, ssize_t offset) {
  return ptr + offset;
}

typedef uint32_t cfloat;

float cfloat_to_float(cfloat x) {
  return *(float *)&x;
}

cfloat float_to_cfloat(float x) {
  return *(cfloat *)&x;
}

cfloat double_to_cfloat(double x) {
  return float_to_cfloat((float)x);
}

double cfloat_to_double(cfloat x) {
  return (double)cfloat_to_float(x);
}

cfloat cfloat_add(cfloat x, cfloat y) {
  return float_to_cfloat(cfloat_to_float(x) + cfloat_to_float(y));
}

cfloat cfloat_neg(cfloat x) {
  return float_to_cfloat(-cfloat_to_float(x));
}

cfloat cfloat_sub(cfloat x, cfloat y) {
  return float_to_cfloat(cfloat_to_float(x) - cfloat_to_float(y));
}

cfloat cfloat_mul(cfloat x, cfloat y) {
  return float_to_cfloat(cfloat_to_float(x) * cfloat_to_float(y));
}

cfloat cfloat_div(cfloat x, cfloat y) {
  return float_to_cfloat(cfloat_to_float(x) / cfloat_to_float(y));
}

cfloat cfloat_recip(cfloat x) {
  return float_to_cfloat(1 / cfloat_to_float(x));
}

cfloat cfloat_abs(cfloat x) {
  return float_to_cfloat(fabs(cfloat_to_float(x)));
}
