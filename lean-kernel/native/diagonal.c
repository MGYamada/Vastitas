#include "diagonal.h"
#include <float.h>
#include <string.h>

_Static_assert(sizeof(double) == 8 && FLT_RADIX == 2 && DBL_MANT_DIG == 53 && DBL_MAX_EXP == 1024,
               "binary64 component ABI required");

/* Coefficients are borrowed little-endian binary64 bit patterns at any byte
 * alignment. One memcpy decodes a whole entry (a single load on the supported
 * hosts); a big-endian host swaps it, and an unknown byte order is rejected. */
#if defined(__BYTE_ORDER__) && defined(__ORDER_LITTLE_ENDIAN__) && __BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__
static inline uint64_t from_little_endian(uint64_t bits) { return bits; }
#elif defined(__BYTE_ORDER__) && defined(__ORDER_BIG_ENDIAN__) && __BYTE_ORDER__ == __ORDER_BIG_ENDIAN__
static inline uint64_t from_little_endian(uint64_t bits) { return __builtin_bswap64(bits); }
#else
#error "diagonal coefficients require a known host byte order"
#endif

/* Entry index of a validated coefficient table; uniform tables use index 0.
 * Callers test uniformity once, outside their element loops. */
static inline uint64_t bits_at(const uint8_t *data, uint64_t index) {
    uint64_t bits;
    memcpy(&bits, data + 8 * index, sizeof(bits));
    return from_little_endian(bits);
}
static inline double weight_at(const uint8_t *data, uint64_t index) {
    uint64_t bits = bits_at(data, index);
    double value;
    memcpy(&value, &bits, sizeof(value));
    return value;
}

VStorageStatus vdiagonal_validate(VDiagonal diagonal, uint64_t dimension) {
    if (diagonal.uniform > 1 || diagonal.bytes % 8) return VS_OPERATION;
    size_t count = diagonal.bytes / 8;
    if ((diagonal.uniform && count != 1) || (!diagonal.uniform && (count != dimension || count > 4096)) ||
        (count && !diagonal.data)) return VS_SHAPE;
    for (size_t i = 0; i < count; ++i) {
        uint64_t bits = bits_at(diagonal.data, i);
        uint64_t exponent = (bits >> 52) & 2047;
        uint64_t significand = (UINT64_C(1) << 52) | (bits & ((UINT64_C(1) << 52) - 1));
        if (exponent < 1023 || exponent > 1076) return VS_OPERATION;
        if (exponent <= 1075) {
            unsigned shift = (unsigned)(1075 - exponent);
            if (significand & ((UINT64_C(1) << shift) - 1)) return VS_OPERATION;
        } else if (significand != (UINT64_C(1) << 52)) return VS_OPERATION;
    }
    return VS_OK;
}

double vdiagonal_entry(VDiagonal diagonal, uint64_t index) {
    return weight_at(diagonal.data, diagonal.uniform ? 0 : index);
}

int vdiagonal_overlaps(const VStorageDense *a, const VStorageDense *b) {
    return a->allocation == b->allocation && a->start < a->end && b->start < b->end &&
        a->start < b->end && b->start < a->end;
}

static uint64_t coordinate(const VStorageDense *view, uint64_t row, uint64_t column) {
    return (view->transposed ? row * view->leading + column : column * view->leading + row) *
        (view->scalar ? 2 : 1);
}

/* Each kernel is specialized at its call by a constant uniform argument, so
 * a uniform weight is decoded once and no element loop tests uniformity.
 * Arithmetic and its order are unchanged by the specialization. */
#if defined(__GNUC__)
#define SPECIALIZED static inline __attribute__((always_inline))
#else
#define SPECIALIZED static inline
#endif

SPECIALIZED void weight_kernel(const VStorageDense *input, const VStorageDense *output,
                                 const uint8_t *weights, const int uniform, uint8_t conjugate) {
    const double fixed = uniform ? weight_at(weights, 0) : 0.0;
    /* Ordinary columns are contiguous even when their enclosing allocations
     * have padded leading dimensions. Select representation/stride once, not
     * per element. A transposed physical row retains the explicit stride path. */
    if (!input->transposed && !input->scalar) {
        const double *from=input->data; double *to=output->data;
        for (uint64_t i=0;i<input->rows;++i) to[i]=from[i]*(uniform?fixed:weight_at(weights,i));
        return;
    }
    if (!input->transposed && input->scalar) {
        const double *from=input->data; double *to=output->data;
        for (uint64_t i=0;i<input->rows;++i) {
            double weight=uniform?fixed:weight_at(weights,i);
            to[2*i]=from[2*i]*weight;
            to[2*i+1]=(conjugate?-from[2*i+1]:from[2*i+1])*weight;
        }
        return;
    }
    for (uint64_t i = 0; i < input->rows; ++i) {
        uint64_t a = coordinate(input, i, 0), b = coordinate(output, i, 0);
        double weight = uniform ? fixed : weight_at(weights, i);
        output->data[b] = input->data[a] * weight;
        if (input->scalar) output->data[b + 1] = (conjugate ? -input->data[a + 1] : input->data[a + 1]) * weight;
    }
}

void vdiagonal_weight_prepared(const VStorageDense *input, const VStorageDense *output,
                              VDiagonal diagonal, uint8_t conjugate) {
    if (diagonal.uniform) weight_kernel(input, output, diagonal.data, 1, conjugate);
    else weight_kernel(input, output, diagonal.data, 0, conjugate);
}

static VStorageStatus operands(VStorageArena *arena, uint32_t input, VStorageLayout input_view,
        uint32_t output, VStorageLayout output_view, uint8_t conjugate,
        VStorageDense *a, VStorageDense *b) {
    if (conjugate > 1 || output_view.transposed) return VS_OPERATION;
    VStorageStatus status = vstorage_prepare_dense(arena, input, input_view, a);
    if (status != VS_OK) return status;
    status = vstorage_prepare_dense(arena, output, output_view, b);
    if (status != VS_OK) return status;
    if (a->scalar != b->scalar) return VS_SCALAR;
    if (vdiagonal_overlaps(a, b)) return VS_ALIAS;
    return VS_OK;
}

VStorageStatus vdiagonal_scale(VStorageArena *arena,
    uint32_t input, VStorageLayout input_view, uint32_t output, VStorageLayout output_view,
    VDiagonal diagonal, uint8_t conjugate) {
    VStorageDense a, b;
    VStorageStatus status = operands(arena, input, input_view, output, output_view, conjugate, &a, &b);
    if (status != VS_OK) return status;
    if (a.columns != 1 || b.columns != 1 || a.rows != b.rows) return VS_SHAPE;
    if ((status = vdiagonal_validate(diagonal, a.rows)) != VS_OK ||
        (status = vstorage_prepare_write(arena, b.bytes)) != VS_OK) return status;
    vdiagonal_weight_prepared(&a, &b, diagonal, conjugate);
    vstorage_record_write(arena, b.bytes);
    return VS_OK;
}

/* The target weight is decoded once per destination column. A nonuniform
 * source weight is one load per element; a uniform one is decoded once. */
SPECIALIZED void adjoint_kernel(const VStorageDense *a, const VStorageDense *b,
                                  const uint8_t *source, const int source_uniform,
                                  VDiagonal target, uint8_t conjugate) {
    const double fixed = source_uniform ? weight_at(source, 0) : 0.0;
    const uint64_t target_step = target.uniform ? 0 : 1;
    if (!a->transposed && !a->scalar) {
        for (uint64_t j=0;j<b->columns;++j) {
            double target_weight=weight_at(target.data,j*target_step);
            for (uint64_t i=0;i<b->rows;++i)
                b->data[j*b->leading+i]=(a->data[i*a->leading+j]*target_weight)/
                    (source_uniform?fixed:weight_at(source,i));
        }
    } else if (!a->transposed && a->scalar) {
        for (uint64_t j=0;j<b->columns;++j) {
            double target_weight=weight_at(target.data,j*target_step);
            for (uint64_t i=0;i<b->rows;++i) {
                uint64_t from=2*(i*a->leading+j),to=2*(j*b->leading+i);
                double source_weight=source_uniform?fixed:weight_at(source,i);
                b->data[to]=(a->data[from]*target_weight)/source_weight;
                b->data[to+1]=((conjugate?-a->data[from+1]:a->data[from+1])*target_weight)/source_weight;
            }
        }
    } else {
        for (uint64_t j = 0; j < b->columns; ++j) {
            double target_weight = weight_at(target.data, j * target_step);
            for (uint64_t i = 0; i < b->rows; ++i) {
                uint64_t from = coordinate(a, j, i), to = coordinate(b, i, j);
                double source_weight = source_uniform ? fixed : weight_at(source, i);
                b->data[to] = (a->data[from] * target_weight) / source_weight;
                if (a->scalar) b->data[to + 1] = ((conjugate ? -a->data[from + 1] : a->data[from + 1]) * target_weight) / source_weight;
            }
        }
    }
}

VStorageStatus vdiagonal_adjoint(VStorageArena *arena,
    uint32_t input, VStorageLayout input_view, uint32_t output, VStorageLayout output_view,
    VDiagonal source, VDiagonal target, uint8_t conjugate) {
    VStorageDense a, b;
    VStorageStatus status = operands(arena, input, input_view, output, output_view, conjugate, &a, &b);
    if (status != VS_OK) return status;
    if (a.columns != b.rows || a.rows != b.columns) return VS_SHAPE;
    if ((status = vdiagonal_validate(source, a.columns)) != VS_OK ||
        (status = vdiagonal_validate(target, a.rows)) != VS_OK ||
        (status = vstorage_prepare_write(arena, b.bytes)) != VS_OK) return status;
    if (!b.bytes) return VS_OK;
    /* Column-major destination traversal. No inverse matrix, coefficient copy,
     * data allocation, BLAS invocation, tolerance test or old-output read.
     * Source uniformity is tested once here, not per element. */
    if (source.uniform) adjoint_kernel(&a, &b, source.data, 1, target, conjugate);
    else adjoint_kernel(&a, &b, source.data, 0, target, conjugate);
    vstorage_record_write(arena, b.bytes);
    return VS_OK;
}
