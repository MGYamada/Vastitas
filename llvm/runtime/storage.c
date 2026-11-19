#include "storage_abi.h"

/* Fixed scalar ABI for emitted LLVM. Each i64 arrives as one unsigned word.
 * Views are constructed here using the host C ABI for VStorageLayout. */
VStorageArena *vq_storage_new(uint64_t budget) {
    VStorageArena *arena = vstorage_new(budget);
    if (arena == NULL) (void)checked(VS_ALLOCATION);
    return arena;
}

int32_t vq_storage_allocate(VStorageArena *arena, uint64_t id, uint64_t scalar,
                            uint64_t elements) {
    if (id > UINT32_MAX) return checked(VS_HANDLE);
    if (scalar > VS_COMPLEX_F32) return checked(VS_SCALAR);
    return checked(vstorage_allocate(arena, (uint32_t)id, (uint8_t)scalar, elements));
}

int32_t vq_storage_drop(VStorageArena *arena, uint64_t id) {
    if (id > UINT32_MAX) return checked(VS_HANDLE);
    return checked(vstorage_drop(arena, (uint32_t)id));
}

static VStorageStatus operands(uint64_t id, uint64_t transposed, uint64_t scalar) {
    if (id > UINT32_MAX) return VS_HANDLE;
    if (transposed > 1) return VS_LAYOUT;
    if (scalar > VS_COMPLEX_F32) return VS_SCALAR;
    return VS_OK;
}

int32_t vq_storage_fill(VStorageArena *arena, uint64_t id, uint64_t offset,
                        uint64_t rows, uint64_t columns, uint64_t leading, uint64_t transposed,
                        uint64_t scalar, uint64_t real, uint64_t imaginary) {
    VStorageStatus status = operands(id, transposed, scalar);
    if (status != VS_OK) return checked(status);
    return checked(vstorage_fill(arena, (uint32_t)id, view(offset, rows, columns, leading, transposed),
                                 (uint8_t)scalar, real, imaginary));
}

int32_t vq_storage_store(VStorageArena *arena, uint64_t id, uint64_t offset,
                         uint64_t rows, uint64_t columns, uint64_t leading, uint64_t transposed,
                         uint64_t row, uint64_t column, uint64_t scalar, uint64_t real, uint64_t imaginary) {
    VStorageStatus status = operands(id, transposed, scalar);
    if (status != VS_OK) return checked(status);
    return checked(vstorage_store(arena, (uint32_t)id, view(offset, rows, columns, leading, transposed),
                                  row, column, (uint8_t)scalar, real, imaginary));
}

int32_t vq_storage_expect(VStorageArena *arena, uint64_t id, uint64_t offset,
                          uint64_t rows, uint64_t columns, uint64_t leading, uint64_t transposed,
                          uint64_t row, uint64_t column, uint64_t scalar, uint64_t real, uint64_t imaginary) {
    VStorageStatus status = operands(id, transposed, scalar);
    if (status != VS_OK) return checked(status);
    uint64_t observed[2];
    status = vstorage_expect_observed(arena, (uint32_t)id, view(offset, rows, columns, leading, transposed),
                                     row, column, (uint8_t)scalar, real, imaginary, observed);
    if (status == VS_EXPECT) {
        const uint64_t expected[2] = {real, imaginary};
        char message[VSTORAGE_EXPECT_MESSAGE_BYTES];
        if (vstorage_expect_message(message, sizeof(message), row, column, (uint8_t)scalar,
                                    observed, expected)) {
            fprintf(stderr, "uncaught exception: %s\n", message);
            return 1;
        }
    }
    return checked(status);
}

int32_t vq_storage_copy(VStorageArena *arena, uint64_t source, uint64_t in_offset,
                        uint64_t in_rows, uint64_t in_columns, uint64_t in_leading, uint64_t in_transposed,
                        uint64_t target, uint64_t out_offset, uint64_t out_rows, uint64_t out_columns,
                        uint64_t out_leading, uint64_t out_transposed) {
    if (source > UINT32_MAX || target > UINT32_MAX) return checked(VS_HANDLE);
    if (in_transposed > 1 || out_transposed > 1) return checked(VS_LAYOUT);
    return checked(vstorage_copy(arena, (uint32_t)source, view(in_offset, in_rows, in_columns, in_leading, in_transposed),
                                 (uint32_t)target, view(out_offset, out_rows, out_columns, out_leading, out_transposed)));
}
