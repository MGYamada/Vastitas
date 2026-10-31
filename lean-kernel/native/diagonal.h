#ifndef VASTITAS_DIAGONAL_H
#define VASTITAS_DIAGONAL_H
#include "storage.h"
#include <stddef.h>

/* Borrowed immutable little-endian binary64 bits; never an arena allocation
 * or caller-provided Gram witness. Native callers still receive no authority. */
typedef struct { const uint8_t *data; size_t bytes; uint8_t uniform; } VDiagonal;
VStorageStatus vdiagonal_validate(VDiagonal diagonal, uint64_t dimension);
double vdiagonal_entry(VDiagonal diagonal, uint64_t index);
int vdiagonal_overlaps(const VStorageDense *left, const VStorageDense *right);
void vdiagonal_weight_prepared(const VStorageDense *input, const VStorageDense *output,
                              VDiagonal diagonal, uint8_t conjugate);
VStorageStatus vdiagonal_scale(VStorageArena *arena,
    uint32_t input, VStorageLayout input_view, uint32_t output, VStorageLayout output_view,
    VDiagonal diagonal, uint8_t conjugate);
VStorageStatus vdiagonal_adjoint(VStorageArena *arena,
    uint32_t input, VStorageLayout input_view, uint32_t output, VStorageLayout output_view,
    VDiagonal source, VDiagonal target, uint8_t conjugate);
#endif
