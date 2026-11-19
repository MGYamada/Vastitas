#include "gemm.h"
#include <cblas.h>
#include <float.h>
#include <limits.h>
#include <pthread.h>
#include <string.h>

_Static_assert(sizeof(blasint) == 4 && (blasint)-1 < 0, "OpenBLAS LP64 integer ABI required");
_Static_assert(sizeof(openblas_complex_float) == 8 && _Alignof(openblas_complex_float) <= 4,
               "interleaved binary32 complex ABI required");
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
    if (conjugate && vstorage_is_complex(view->scalar))
        return view->transposed ? CblasConjTrans : CblasConjNoTrans;
    return view->transposed ? CblasTrans : CblasNoTrans;
}

/* Component step between consecutive elements of a 1-by-k row (row != 0) or
 * k-by-1 column vector view, following the same physical layout as GEMM. */
static uint64_t vector_step(const VStorageDense *view, int row) {
    uint64_t step = (row ? view->transposed : !view->transposed) ? 1 : view->leading;
    return vstorage_is_complex(view->scalar) ? 2 * step : step;
}

#define COMPONENT float
#define WORD uint32_t
#define LOCAL(name) name##32
#define REAL_GEMM cblas_sgemm
#define COMPLEX_GEMM cblas_cgemm
#include "gemm_kernels.inc"
#undef COMPLEX_GEMM
#undef REAL_GEMM
#undef LOCAL
#undef WORD
#undef COMPONENT

#define COMPONENT double
#define WORD uint64_t
#define LOCAL(name) name##64
#define REAL_GEMM cblas_dgemm
#define COMPLEX_GEMM cblas_zgemm
#include "gemm_kernels.inc"
#undef COMPLEX_GEMM
#undef REAL_GEMM
#undef LOCAL
#undef WORD
#undef COMPONENT

VStorageStatus vgemm_execute_scaled_as(VStorageArena *arena, int expected_scalar,
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
    if (a.scalar != b.scalar || a.scalar != c.scalar ||
        (expected_scalar != -1 && c.scalar != expected_scalar)) return VS_SCALAR;
    if (a.columns != b.rows || c.rows != a.rows || c.columns != b.columns) return VS_SHAPE;
    if (overlaps(&a, &c) || overlaps(&b, &c)) return VS_ALIAS;
    if (vstorage_component_bytes(c.scalar) == 4)
        return update32(arena, output, output_view, a, b, c, left_conjugate, right_conjugate,
                        mode, alpha_input, beta_input, report);
    return update64(arena, output, output_view, a, b, c, left_conjugate, right_conjugate,
                    mode, alpha_input, beta_input, report);
}

VStorageStatus vgemm_execute_scaled(VStorageArena *arena,
    uint32_t left, VStorageLayout left_view, uint8_t left_conjugate,
    uint32_t right, VStorageLayout right_view, uint8_t right_conjugate,
    uint32_t output, VStorageLayout output_view, VGemmMode mode,
    VGemmCoefficient alpha_input, VGemmCoefficient beta_input, VGemmReport *report) {
    return vgemm_execute_scaled_as(arena, -1, left, left_view, left_conjugate,
        right, right_view, right_conjugate, output, output_view, mode, alpha_input, beta_input, report);
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
    if (vstorage_component_bytes(a.scalar) != 8 || a.scalar != b.scalar || a.scalar != c.scalar || a.scalar != original_right.scalar) return VS_SCALAR;
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
        double *out = c.data;
        out[0] = 0.0;
        if (vstorage_is_complex(c.scalar)) out[1] = 0.0;
    } else {
        /* The scalar pairing reads the weighted scratch vector back through the
         * same fused 1-by-1 path as an overwrite GEMM with default alpha. */
        const double alpha[2] = {1.0, 0.0}, beta[2] = {0.0, 0.0};
        dot_update64(&a, conjugate_left, &b, 0, &c, alpha, beta);
        result.kernel_calls = 1;
    }
    vstorage_record_write(arena, c.bytes);
    if (report) *report = result;
    return VS_OK;
}
