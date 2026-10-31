#ifndef PUBLIC_GEMM_BENCH_CALLS_H
#define PUBLIC_GEMM_BENCH_CALLS_H
#include <cblas.h>
void bench_dgemm(enum CBLAS_ORDER, enum CBLAS_TRANSPOSE, enum CBLAS_TRANSPOSE,
    blasint, blasint, blasint, double, const double *, blasint, const double *, blasint, double, double *, blasint);
void bench_zgemm(enum CBLAS_ORDER, enum CBLAS_TRANSPOSE, enum CBLAS_TRANSPOSE,
    blasint, blasint, blasint, const void *, const void *, blasint, const void *, blasint, const void *, void *, blasint);
#endif
