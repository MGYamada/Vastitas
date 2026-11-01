#ifndef VASTITAS_PACKING_OBSERVER_H
#define VASTITAS_PACKING_OBSERVER_H
#include <stddef.h>
void vpack_before(const char *, unsigned, unsigned, long, long, const void *, long, void *);
void vpack_after(void);
void vpack_route(const char *, unsigned, long, long, long, unsigned, unsigned,
                 const void *, long, const void *, long, const void *, long);
void vpack_end(void);
void vpack_dump(void);
#define VPACK_STRING_1(x) #x
#define VPACK_STRING(x) VPACK_STRING_1(x)
#if defined(DOUBLE) && !defined(XDOUBLE) && !defined(GEMM3M)
#if defined(DYNAMIC_ARCH) || defined(SMP) || defined(FUSED_GEMM) || defined(BFLOAT16) || defined(HFLOAT16)
#error "Unsupported packing observation profile"
#endif
#if defined(CBLAS)
#define VPACK_ROUTE(PATH) vpack_route(PATH, COMPSIZE, args.m, args.n, args.k, \
    transa, transb, args.a, args.lda, args.b, args.ldb, args.c, args.ldc)
#define VPACK_END() vpack_end()
#endif
#endif
#ifndef VPACK_ROUTE
#define VPACK_ROUTE(PATH) ((void)0)
#define VPACK_END() ((void)0)
#endif
#if defined(VPACK_GEMM_PROFILE) && defined(DOUBLE) && !defined(XDOUBLE)
#define VPACK_CALL(ROLE, COPY, M, N, A, LDA, B) do { \
    _Static_assert(sizeof(IFLOAT) == 8 && sizeof(XFLOAT) == 8, "double ABI"); \
    const BLASLONG vp_m = (M), vp_n = (N), vp_lda = (LDA); \
    IFLOAT *vp_a = (A); XFLOAT *vp_b = (B); \
    vpack_before(VPACK_STRING(COPY), ROLE, COMPSIZE, vp_m, vp_n, vp_a, vp_lda, vp_b); \
    COPY(vp_m, vp_n, vp_a, vp_lda, vp_b); \
    vpack_after(); \
} while (0)
#else
#define VPACK_CALL(ROLE, COPY, M, N, A, LDA, B) COPY(M, N, A, LDA, B)
#endif
#endif
