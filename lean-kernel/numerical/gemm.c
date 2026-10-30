#include "gemm.h"
#include <cblas.h>
#include <float.h>
#include <limits.h>
#include <string.h>

_Static_assert(sizeof(blasint) == 4 && (blasint)-1 < 0, "OpenBLAS LP64 integer ABI required");
_Static_assert(sizeof(double) == 8 && FLT_RADIX == 2 && DBL_MANT_DIG == 53 && DBL_MAX_EXP == 1024,
               "binary64 component ABI required");
_Static_assert(sizeof(openblas_complex_double) == 16 && _Alignof(openblas_complex_double) <= 8,
               "interleaved binary64 complex ABI required");
#ifdef OPENBLAS_USE64BITINT
#error "OpenBLAS ILP64 headers are unsupported"
#endif

const char *vgemm_configuration(void) { return openblas_get_config(); }

VStorageStatus vgemm_backend_check(void) {
    const char *configuration = vgemm_configuration();
    /* The linked library can differ from the compile-time header. Inspect both
     * before calling an integer-ABI-sensitive entry point. Never reset threads
     * or process-wide settings inside an operation. */
    if (!strstr(OPENBLAS_VERSION, " OpenBLAS 0.3.34 ") || !configuration ||
        strncmp(configuration, "OpenBLAS 0.3.34 ", 16) != 0 ||
        strstr(configuration, "USE64BITINT") ||
        openblas_get_parallel() != OPENBLAS_SEQUENTIAL) return VS_ABI;
    return VS_OK;
}

static int overlaps(const VStorageDense *a, const VStorageDense *b) {
    return a->allocation == b->allocation && a->start < a->end && b->start < b->end &&
        a->start < b->end && b->start < a->end;
}

static enum CBLAS_TRANSPOSE operation(const VStorageDense *view, uint8_t conjugate) {
    return conjugate && view->scalar ? CblasConjTrans : view->transposed ? CblasTrans : CblasNoTrans;
}

VStorageStatus vgemm_execute(VStorageArena *arena,
    uint32_t left, VStorageLayout left_view, uint8_t left_conjugate,
    uint32_t right, VStorageLayout right_view, uint8_t right_conjugate,
    uint32_t output, VStorageLayout output_view, VGemmMode mode, VGemmReport *report) {
    if ((mode != VGEMM_OVERWRITE && mode != VGEMM_ACCUMULATE) ||
        left_conjugate > 1 || right_conjugate > 1 ||
        (left_conjugate && !left_view.transposed) ||
        (right_conjugate && !right_view.transposed) || output_view.transposed)
        return VS_OPERATION;
    VStorageStatus status = vgemm_backend_check();
    if (status != VS_OK) return status;
    VStorageDense a, b, c;
    if ((status = vstorage_prepare_dense(arena, left, left_view, &a)) != VS_OK ||
        (status = vstorage_prepare_dense(arena, right, right_view, &b)) != VS_OK ||
        (status = vstorage_prepare_dense(arena, output, output_view, &c)) != VS_OK)
        return status;
    if (a.scalar != b.scalar || a.scalar != c.scalar) return VS_SCALAR;
    if (a.columns != b.rows || c.rows != a.rows || c.columns != b.columns) return VS_SHAPE;
    if (overlaps(&a, &c) || overlaps(&b, &c)) return VS_ALIAS;
    /* All physical shape/stride/bounds/LP64 checks precede the first write.
     * Initialization and nominal endpoint/frame/metric checks belong to the
     * actual checked source plan; matching dimensions cannot establish them. */
    if (c.bytes && (a.columns || mode == VGEMM_OVERWRITE) &&
        (status = vstorage_prepare_write(arena, c.bytes)) != VS_OK) return status;
    VGemmReport result = {0, 0};
    if (c.rows && c.columns) {
        if (!a.columns) {
            if (mode == VGEMM_OVERWRITE) {
                status = vstorage_fill(arena, output, output_view, c.scalar, 0, 0);
                if (status != VS_OK) return status;
                result.written_bytes = c.bytes;
            }
        } else {
            /* No scan, implicit packing, defensive copy or temporary output.
             * A and B may alias; C was independently checked against each. */
            enum CBLAS_TRANSPOSE ta = operation(&a, left_conjugate);
            enum CBLAS_TRANSPOSE tb = operation(&b, right_conjugate);
            if (a.scalar == 0) {
                cblas_dgemm(CblasColMajor, ta, tb, (blasint)c.rows, (blasint)c.columns,
                    (blasint)a.columns, 1.0, a.data, (blasint)a.leading, b.data,
                    (blasint)b.leading, mode == VGEMM_OVERWRITE ? 0.0 : 1.0, c.data, (blasint)c.leading);
            } else {
                const double alpha[2] = {1.0, 0.0};
                const double beta[2] = {mode == VGEMM_OVERWRITE ? 0.0 : 1.0, 0.0};
                cblas_zgemm(CblasColMajor, ta, tb, (blasint)c.rows, (blasint)c.columns,
                    (blasint)a.columns, alpha, a.data, (blasint)a.leading, b.data,
                    (blasint)b.leading, beta, c.data, (blasint)c.leading);
            }
            vstorage_record_write(arena, c.bytes);
            result = (VGemmReport){1, c.bytes};
        }
    }
    if (report) *report = result;
    return VS_OK;
}
