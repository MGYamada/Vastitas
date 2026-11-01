#ifndef SHAPE_EXPERIMENT_CALLS_H
#define SHAPE_EXPERIMENT_CALLS_H
#include <cblas.h>
void shape_dgemm(enum CBLAS_ORDER, enum CBLAS_TRANSPOSE, enum CBLAS_TRANSPOSE,
    blasint, blasint, blasint, double, const double *, blasint,
    const double *, blasint, double, double *, blasint);
void shape_zgemm(enum CBLAS_ORDER, enum CBLAS_TRANSPOSE, enum CBLAS_TRANSPOSE,
    blasint, blasint, blasint, const void *, const void *, blasint,
    const void *, blasint, const void *, void *, blasint);
#endif
