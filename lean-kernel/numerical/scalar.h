#ifndef VASTITAS_NUMERICAL_SCALAR_H
#define VASTITAS_NUMERICAL_SCALAR_H

#include <stdint.h>

/* NativeFast scalar ABI. Components are raw native-endian words, real first.
 * Each array points to two words. Arguments can overlap the result. */
uint32_t vfloat32_rdiv(uint32_t x, uint32_t y);
uint64_t vfloat64_rdiv(uint64_t x, uint64_t y);
void vfloat32_cdiv(const uint32_t x[2], const uint32_t y[2], uint32_t out[2]);
void vfloat64_cdiv(const uint64_t x[2], const uint64_t y[2], uint64_t out[2]);
void vfloat32_cinv(const uint32_t x[2], uint32_t out[2]);
void vfloat64_cinv(const uint64_t x[2], uint64_t out[2]);

#endif
