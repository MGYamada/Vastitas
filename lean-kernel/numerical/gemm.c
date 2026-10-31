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
    if (conjugate && view->scalar)
        return view->transposed ? CblasConjTrans : CblasConjNoTrans;
    return view->transposed ? CblasTrans : CblasNoTrans;
}

static VStorageStatus coefficient(VStorageArena *arena, VGemmCoefficient input,
        const VStorageDense *output, double fallback, double value[2]) {
    value[0] = fallback;
    value[1] = 0.0;
    if (input.kind == VGEMM_DEFAULT) return VS_OK;
    if (input.kind == VGEMM_LITERAL) {
        if (input.scalar != output->scalar) return VS_SCALAR;
        memcpy(&value[0], &input.real, sizeof(double));
        if (input.scalar) memcpy(&value[1], &input.imaginary, sizeof(double));
        return VS_OK;
    }
    if (input.kind != VGEMM_VIEW) return VS_OPERATION;
    VStorageDense source;
    VStorageStatus status = vstorage_prepare_dense(arena, input.allocation,
        (VStorageLayout){input.offset, 1, 1, 1, 0}, &source);
    if (status != VS_OK) return status;
    if (source.scalar != output->scalar) return VS_SCALAR;
    if (overlaps(&source, output)) return VS_ALIAS;
    memcpy(value, source.data, source.scalar ? 2 * sizeof(double) : sizeof(double));
    return VS_OK;
}

VStorageStatus vgemm_execute_scaled(VStorageArena *arena,
    uint32_t left, VStorageLayout left_view, uint8_t left_conjugate,
    uint32_t right, VStorageLayout right_view, uint8_t right_conjugate,
    uint32_t output, VStorageLayout output_view, VGemmMode mode,
    VGemmCoefficient alpha_input, VGemmCoefficient beta_input, VGemmReport *report) {
    if ((mode != VGEMM_OVERWRITE && mode != VGEMM_ACCUMULATE) ||
        left_conjugate > 1 || right_conjugate > 1 ||
        output_view.transposed ||
        (mode == VGEMM_OVERWRITE && beta_input.kind != VGEMM_DEFAULT))
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
    double alpha[2], beta[2];
    if ((status = coefficient(arena, alpha_input, &c, 1.0, alpha)) != VS_OK ||
        (status = coefficient(arena, beta_input, &c,
            mode == VGEMM_OVERWRITE ? 0.0 : 1.0, beta)) != VS_OK) return status;
    const int beta_one = beta[0] == 1.0 && beta[1] == 0.0;
    /* All physical shape/stride/bounds/LP64 checks precede the first write.
     * Initialization and nominal endpoint/frame/metric checks belong to the
     * actual checked source plan; matching dimensions cannot establish them. */
    if (c.bytes && (a.columns || !beta_one) &&
        (status = vstorage_prepare_write(arena, c.bytes)) != VS_OK) return status;
    VGemmReport result = {0, 0};
    if (c.rows && c.columns) {
        if (!a.columns) {
            /* For the empty product the defined degenerate operation is beta*C,
             * independent of alpha. Zero beta does not read old C, including
             * NaN/uninitialized overwrite destinations; one beta does no write. */
            if (beta[0] == 0.0 && beta[1] == 0.0) {
                status = vstorage_fill(arena, output, output_view, c.scalar, 0, 0);
                if (status != VS_OK) return status;
                result.written_bytes = c.bytes;
            } else if (!beta_one) {
                double *data = c.data;
                for (uint64_t j = 0; j < c.columns; ++j) {
                    for (uint64_t i = 0; i < c.rows; ++i) {
                        uint64_t index = i + j * c.leading;
                        if (!c.scalar) data[index] *= beta[0];
                        else {
                            double real = data[2 * index], imaginary = data[2 * index + 1];
                            data[2 * index] = beta[0] * real - beta[1] * imaginary;
                            data[2 * index + 1] = beta[0] * imaginary + beta[1] * real;
                        }
                    }
                }
                vstorage_record_write(arena, c.bytes);
                result.written_bytes = c.bytes;
            }
        } else {
            /* No scan, implicit packing, defensive copy or temporary output.
             * A and B may alias; C was independently checked against each. */
            enum CBLAS_TRANSPOSE ta = operation(&a, left_conjugate);
            enum CBLAS_TRANSPOSE tb = operation(&b, right_conjugate);
            if (a.scalar == 0) {
                cblas_dgemm(CblasColMajor, ta, tb, (blasint)c.rows, (blasint)c.columns,
                    (blasint)a.columns, alpha[0], a.data, (blasint)a.leading, b.data,
                    (blasint)b.leading, beta[0], c.data, (blasint)c.leading);
            } else {
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

VStorageStatus vgemm_execute(VStorageArena *arena,
    uint32_t left, VStorageLayout left_view, uint8_t left_conjugate,
    uint32_t right, VStorageLayout right_view, uint8_t right_conjugate,
    uint32_t output, VStorageLayout output_view, VGemmMode mode, VGemmReport *report) {
    VGemmCoefficient defaults = {VGEMM_DEFAULT, 0, 0, 0, 0, 0};
    return vgemm_execute_scaled(arena, left, left_view, left_conjugate,
        right, right_view, right_conjugate, output, output_view, mode, defaults, defaults, report);
}
