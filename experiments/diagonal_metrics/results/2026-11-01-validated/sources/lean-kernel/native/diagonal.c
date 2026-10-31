#include "diagonal.h"
#include <float.h>
#include <string.h>

_Static_assert(sizeof(double) == 8 && FLT_RADIX == 2 && DBL_MANT_DIG == 53 && DBL_MAX_EXP == 1024,
               "binary64 component ABI required");

static uint64_t bits_at(VDiagonal diagonal, uint64_t index) {
    const uint8_t *data = diagonal.data + 8 * (diagonal.uniform ? 0 : index);
    uint64_t bits = 0;
    for (unsigned i = 0; i < 8; ++i) bits |= (uint64_t)data[i] << (8 * i);
    return bits;
}

VStorageStatus vdiagonal_validate(VDiagonal diagonal, uint64_t dimension) {
    if (diagonal.uniform > 1 || diagonal.bytes % 8) return VS_OPERATION;
    size_t count = diagonal.bytes / 8;
    if ((diagonal.uniform && count != 1) || (!diagonal.uniform && (count != dimension || count > 4096)) ||
        (count && !diagonal.data)) return VS_SHAPE;
    for (size_t i = 0; i < count; ++i) {
        uint64_t bits = bits_at(diagonal, i);
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
    uint64_t bits = bits_at(diagonal, index);
    double value;
    memcpy(&value, &bits, sizeof(value));
    return value;
}

int vdiagonal_overlaps(const VStorageDense *a, const VStorageDense *b) {
    return a->allocation == b->allocation && a->start < a->end && b->start < b->end &&
        a->start < b->end && b->start < a->end;
}

static uint64_t coordinate(const VStorageDense *view, uint64_t row, uint64_t column) {
    return (view->transposed ? row * view->leading + column : column * view->leading + row) *
        (view->scalar ? 2 : 1);
}

void vdiagonal_weight_prepared(const VStorageDense *input, const VStorageDense *output,
                              VDiagonal diagonal, uint8_t conjugate) {
    /* Ordinary columns are contiguous even when their enclosing allocations
     * have padded leading dimensions. Select representation/stride once, not
     * per element. A transposed physical row retains the explicit stride path. */
    if (!input->transposed && !input->scalar) {
        const double *from=input->data; double *to=output->data;
        if (diagonal.uniform) {
            double weight=vdiagonal_entry(diagonal,0);
            for (uint64_t i=0;i<input->rows;++i) to[i]=from[i]*weight;
        } else {
            for (uint64_t i=0;i<input->rows;++i) to[i]=from[i]*vdiagonal_entry(diagonal,i);
        }
        return;
    }
    if (!input->transposed && input->scalar) {
        const double *from=input->data; double *to=output->data;
        for (uint64_t i=0;i<input->rows;++i) {
            double weight=vdiagonal_entry(diagonal,i);
            to[2*i]=from[2*i]*weight;
            to[2*i+1]=(conjugate?-from[2*i+1]:from[2*i+1])*weight;
        }
        return;
    }
    for (uint64_t i = 0; i < input->rows; ++i) {
        uint64_t a = coordinate(input, i, 0), b = coordinate(output, i, 0);
        double weight = vdiagonal_entry(diagonal, i);
        output->data[b] = input->data[a] * weight;
        if (input->scalar) output->data[b + 1] = (conjugate ? -input->data[a + 1] : input->data[a + 1]) * weight;
    }
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
     * data allocation, BLAS invocation, tolerance test or old-output read. */
    if (!a.transposed && !a.scalar) {
        for (uint64_t j=0;j<b.columns;++j) {
            double target_weight=vdiagonal_entry(target,j);
            for (uint64_t i=0;i<b.rows;++i)
                b.data[j*b.leading+i]=(a.data[i*a.leading+j]*target_weight)/vdiagonal_entry(source,i);
        }
    } else if (!a.transposed && a.scalar) {
        for (uint64_t j=0;j<b.columns;++j) {
            double target_weight=vdiagonal_entry(target,j);
            for (uint64_t i=0;i<b.rows;++i) {
                uint64_t from=2*(i*a.leading+j),to=2*(j*b.leading+i);
                double source_weight=vdiagonal_entry(source,i);
                b.data[to]=(a.data[from]*target_weight)/source_weight;
                b.data[to+1]=((conjugate?-a.data[from+1]:a.data[from+1])*target_weight)/source_weight;
            }
        }
    } else {
    for (uint64_t j = 0; j < b.columns; ++j) {
        double target_weight = vdiagonal_entry(target, j);
        for (uint64_t i = 0; i < b.rows; ++i) {
            uint64_t from = coordinate(&a, j, i), to = coordinate(&b, i, j);
            double source_weight = vdiagonal_entry(source, i);
            b.data[to] = (a.data[from] * target_weight) / source_weight;
            if (a.scalar) b.data[to + 1] = ((conjugate ? -a.data[from + 1] : a.data[from + 1]) * target_weight) / source_weight;
        }
    }
    }
    vstorage_record_write(arena, b.bytes);
    return VS_OK;
}
