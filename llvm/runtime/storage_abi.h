#ifndef VASTITAS_LLVM_STORAGE_ABI_H
#define VASTITAS_LLVM_STORAGE_ABI_H

#include "storage.h"
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

#endif
