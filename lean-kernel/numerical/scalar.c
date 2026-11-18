#include "scalar.h"
#include <float.h>
#include <string.h>

_Static_assert(FLT_RADIX == 2 && FLT_EVAL_METHOD == 0, "same-precision binary arithmetic required");
_Static_assert(sizeof(float) == 4 && FLT_MANT_DIG == 24 && FLT_MAX_EXP == 128, "binary32 required");
_Static_assert(sizeof(double) == 8 && DBL_MANT_DIG == 53 && DBL_MAX_EXP == 1024, "binary64 required");
#ifdef __FAST_MATH__
#error "NativeFast uses separate baseline host operations"
#endif
#ifdef __clang__
#pragma STDC FP_CONTRACT OFF
#endif

#define SCALAR float
#define WORD uint32_t
#define FN(name) vfloat32_##name
#define SIGN_MASK (UINT32_C(1) << 31)
#define ONE_BITS UINT32_C(0x3f800000)
#include "scalar_kernels.inc"

#define SCALAR double
#define WORD uint64_t
#define FN(name) vfloat64_##name
#define SIGN_MASK (UINT64_C(1) << 63)
#define ONE_BITS UINT64_C(0x3ff0000000000000)
#include "scalar_kernels.inc"
