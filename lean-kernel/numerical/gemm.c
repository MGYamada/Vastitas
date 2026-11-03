#include "gemm.h"
#include <cblas.h>
#include <float.h>
#include <limits.h>
#include <pthread.h>
#include <string.h>

_Static_assert(sizeof(blasint) == 4 && (blasint)-1 < 0, "OpenBLAS LP64 integer ABI required");
_Static_assert(sizeof(double) == 8 && FLT_RADIX == 2 && DBL_MANT_DIG == 53 && DBL_MAX_EXP == 1024,
               "binary64 component ABI required");
_Static_assert(sizeof(openblas_complex_double) == 16 && _Alignof(openblas_complex_double) <= 8,
               "interleaved binary64 complex ABI required");
#ifdef OPENBLAS_USE64BITINT
#error "OpenBLAS ILP64 headers are unsupported"
#endif

static pthread_once_t backend_once = PTHREAD_ONCE_INIT;
static VStorageStatus backend_status = VS_ABI;
static char backend_configuration[256];
static int has_configuration;

static void initialize_backend(void) {
    /* The pinned provider rewrites one global buffer on every get_config call.
     * Call it once and publish our own immutable snapshot, shared by checks and
     * reporting. Never expose the provider's mutable buffer to callers. */
    const char *configuration = openblas_get_config();
    if (!configuration) return;
    size_t length = 0;
    while (length < sizeof(backend_configuration) && configuration[length]) ++length;
    if (length == sizeof(backend_configuration)) return;
    memcpy(backend_configuration, configuration, length + 1);
    has_configuration = 1;
    /* The linked library can differ from the compile-time header. Inspect both
     * before calling an integer-ABI-sensitive entry point. Never reset threads
     * or process-wide settings inside an operation. A sequential 0.3.34 build
     * serializes its shared buffer pool only when made with USE_LOCKING=1, and
     * concurrent operations on distinct arenas rely on that pool lock. Its
     * configuration reports the flag as one space-delimited token. */
    if (!strstr(OPENBLAS_VERSION, " OpenBLAS 0.3.34 ") ||
        strncmp(backend_configuration, "OpenBLAS 0.3.34 ", 16) != 0 ||
        strstr(backend_configuration, "USE64BITINT") ||
        !strstr(backend_configuration + 15, " USE_LOCKING ") ||
        openblas_get_parallel() != OPENBLAS_SEQUENTIAL) return;
    backend_status = VS_OK;
}

const char *vgemm_configuration(void) {
    if (pthread_once(&backend_once, initialize_backend) != 0) return NULL;
    return has_configuration ? backend_configuration : NULL;
}

VStorageStatus vgemm_backend_check(void) {
    if (pthread_once(&backend_once, initialize_backend) != 0) return VS_ABI;
    return backend_status;
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

/* Component step between consecutive elements of a 1-by-k row (row != 0) or
 * k-by-1 column vector view, following the same physical layout as GEMM. */
static uint64_t vector_step(const VStorageDense *view, int row) {
    uint64_t step = (row ? view->transposed : !view->transposed) ? 1 : view->leading;
    return view->scalar ? 2 * step : step;
}

/* Fused 1-by-1 output: c := beta*c + alpha*sum_p op(a_p) op(b_p) for a 1-by-k
 * row a and k-by-1 column b, k >= 1, replacing a dgemm/zgemm call with M = N = 1.
 * The order is fixed and host independent: the sum starts at +0 and adds each
 * product in increasing p; every product, difference and sum is separately
 * rounded (no FMA contraction; GCC keeps ISO C11 mode off and clang obeys the
 * pragma). The pinned BLAS kernels may instead use FMA and their own order, so
 * results can differ from the former call in the last bits. Zero beta reads no
 * old output, one beta preserves it, and zero alpha reads neither input, as in
 * the pinned level-3 driver; an alpha of one is applied exactly. */
static void dot_update(const VStorageDense *a, uint8_t conjugate_a,
                       const VStorageDense *b, uint8_t conjugate_b,
                       const VStorageDense *c, const double alpha[2], const double beta[2]) {
#if defined(__clang__)
#pragma STDC FP_CONTRACT OFF
#endif
    const int is_complex = c->scalar != 0;
    const int beta_zero = beta[0] == 0.0 && beta[1] == 0.0, beta_one = beta[0] == 1.0 && beta[1] == 0.0;
    const int alpha_zero = alpha[0] == 0.0 && alpha[1] == 0.0, alpha_one = alpha[0] == 1.0 && alpha[1] == 0.0;
    double *out = c->data;
    double base[2] = {0.0, 0.0};
    if (beta_one) {
        base[0] = out[0];
        if (is_complex) base[1] = out[1];
    } else if (!beta_zero) {
        if (!is_complex) base[0] = beta[0] * out[0];
        else {
            double rr = beta[0] * out[0], ii = beta[1] * out[1];
            double ri = beta[0] * out[1], ir = beta[1] * out[0];
            base[0] = rr - ii;
            base[1] = ri + ir;
        }
    }
    if (alpha_zero) {
        out[0] = base[0];
        if (is_complex) out[1] = base[1];
        return;
    }
    const double *x = a->data, *y = b->data;
    const uint64_t k = a->columns, sx = vector_step(a, 1), sy = vector_step(b, 0);
    double sum[2] = {0.0, 0.0};
    if (!is_complex) {
        for (uint64_t p = 0; p < k; ++p) {
            double product = x[p * sx] * y[p * sy];
            sum[0] = sum[0] + product;
        }
    } else {
        for (uint64_t p = 0; p < k; ++p) {
            const double *u = x + p * sx, *v = y + p * sy;
            double ur = u[0], ui = conjugate_a ? -u[1] : u[1];
            double vr = v[0], vi = conjugate_b ? -v[1] : v[1];
            double rr = ur * vr, ii = ui * vi, ri = ur * vi, ir = ui * vr;
            double re = rr - ii, im = ri + ir;
            sum[0] = sum[0] + re;
            sum[1] = sum[1] + im;
        }
    }
    double scaled[2] = {sum[0], sum[1]};
    if (!alpha_one) {
        if (!is_complex) scaled[0] = alpha[0] * sum[0];
        else {
            double rr = alpha[0] * sum[0], ii = alpha[1] * sum[1];
            double ri = alpha[0] * sum[1], ir = alpha[1] * sum[0];
            scaled[0] = rr - ii;
            scaled[1] = ri + ir;
        }
    }
    out[0] = base[0] + scaled[0];
    if (is_complex) out[1] = base[1] + scaled[1];
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
        } else if (c.rows == 1 && c.columns == 1) {
            /* A scalar result needs no GEMM driver, packing or BLAS workspace.
             * It still counts as the operation's one kernel call. */
            dot_update(&a, left_conjugate, &b, right_conjugate, &c, alpha, beta);
            vstorage_record_write(arena, c.bytes);
            result = (VGemmReport){1, c.bytes};
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

VStorageStatus vgemm_diagonal_pair(VStorageArena *arena,
    uint32_t left, VStorageLayout left_view, uint32_t right, VStorageLayout right_view,
    uint32_t output, VStorageLayout output_view, uint32_t scratch, VStorageLayout scratch_view,
    VDiagonal diagonal, uint8_t conjugate_left, uint8_t conjugate_right, VGemmReport *report) {
    if (conjugate_left > 1 || conjugate_right > 1 || left_view.transposed > 1 ||
        output_view.transposed || scratch_view.transposed) return VS_OPERATION;
    VStorageStatus status = vgemm_backend_check();
    if (status != VS_OK) return status;
    VStorageDense a, original_right, b, c;
    left_view.transposed = !left_view.transposed;
    if ((status = vstorage_prepare_dense(arena, left, left_view, &a)) != VS_OK ||
        (status = vstorage_prepare_dense(arena, right, right_view, &original_right)) != VS_OK ||
        (status = vstorage_prepare_dense(arena, output, output_view, &c)) != VS_OK ||
        (status = vstorage_prepare_dense(arena, scratch, scratch_view, &b)) != VS_OK) return status;
    if (a.scalar != b.scalar || a.scalar != c.scalar || a.scalar != original_right.scalar) return VS_SCALAR;
    if (a.rows != 1 || b.columns != 1 || original_right.columns != 1 ||
        a.columns != b.rows || original_right.rows != b.rows || c.rows != 1 || c.columns != 1) return VS_SHAPE;
    /* The owner-only scratch contract is stricter than a disjoint loan. */
    if (scratch == left || scratch == right || scratch == output ||
        overlaps(&a, &c) || overlaps(&original_right, &c)) return VS_ALIAS;
    if ((status = vdiagonal_validate(diagonal, b.rows)) != VS_OK) return status;
    if (b.bytes > UINT64_MAX - c.bytes) return VS_OVERFLOW;
    if ((status = vstorage_prepare_write(arena, b.bytes + c.bytes)) != VS_OK) return status;
    /* Everything that can return failure has completed. The arena is used
     * synchronously; no allocation, alias repair, packing or second preflight
     * occurs between the first scratch write and final output initialization. */
    vdiagonal_weight_prepared(&original_right, &b, diagonal, conjugate_right);
    vstorage_record_write(arena, b.bytes);
    VGemmReport result = {0, c.bytes};
    if (!b.rows) {
        c.data[0] = 0.0;
        if (c.scalar) c.data[1] = 0.0;
    } else {
        /* The scalar pairing reads the weighted scratch vector back through the
         * same fused 1-by-1 path as an overwrite GEMM with default alpha. */
        const double alpha[2] = {1.0, 0.0}, beta[2] = {0.0, 0.0};
        dot_update(&a, conjugate_left, &b, 0, &c, alpha, beta);
        result.kernel_calls = 1;
    }
    vstorage_record_write(arena, c.bytes);
    if (report) *report = result;
    return VS_OK;
}
