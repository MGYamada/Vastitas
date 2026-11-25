#ifndef VASTITAS_LLVM_STORAGE_ABI_H
#define VASTITAS_LLVM_STORAGE_ABI_H

#include "diagonal.h"
#include <stdio.h>

static inline int32_t checked(VStorageStatus status) {
    if (status == VS_OK) return 0;
    fprintf(stderr, "uncaught exception: %s\n", vstorage_error(status));
    return 1;
}

static inline VStorageLayout view(uint64_t offset, uint64_t rows, uint64_t columns,
                           uint64_t leading, uint64_t transposed) {
    return (VStorageLayout){offset, rows, columns, leading, (uint8_t)transposed};
}

/* Native kernels compare all view representations. Bind their first view to
 * the explicit representation word in the LLVM call before any writes. */
static inline VStorageStatus diagonal_element(VStorageArena *arena, uint64_t element,
                                              uint32_t id, VStorageLayout layout) {
    if (element > VS_COMPLEX_F32) return VS_SCALAR;
    VStorageDense input;
    VStorageStatus status = vstorage_prepare_dense(arena, id, layout, &input);
    if (status != VS_OK) return status;
    return input.scalar == element ? VS_OK : VS_SCALAR;
}

static inline VStorageStatus diagonal_descriptor(const uint8_t *data, uint64_t bytes,
                                                  uint64_t uniform, VDiagonal *result) {
    if (bytes > 4096 * 8 || bytes % 8 || (bytes && !data) || uniform > 1) return VS_OPERATION;
    *result = (VDiagonal){data, (size_t)bytes, (uint8_t)uniform};
    return VS_OK;
}

#endif
