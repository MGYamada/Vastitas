#ifndef VASTITAS_STORAGE_H
#define VASTITAS_STORAGE_H

#include <stdint.h>

/* Synchronous CPU adapter. Initialized reads and loan permissions are supplied
 * by the exact checked schedule. This ABI independently validates live handles,
 * representations, layouts and copy aliasing before touching element storage. */
typedef struct VStorageArena VStorageArena;
typedef struct {
    uint64_t offset, rows, columns, leading;
    uint8_t transposed;
} VStorageLayout;
typedef struct {
    uint64_t data_allocations, data_frees, live_bytes, peak_bytes;
    uint64_t written_bytes, copied_bytes, metadata_allocations, metadata_bytes;
} VStorageStats;
typedef enum {
    VS_OK, VS_ALLOCATION, VS_HANDLE, VS_SCALAR, VS_LAYOUT, VS_OVERFLOW,
    VS_BOUNDS, VS_ALIAS, VS_EXPECT
} VStorageStatus;

VStorageArena *vstorage_new(uint64_t byte_budget);
void vstorage_close(VStorageArena *arena);
void vstorage_delete(VStorageArena *arena);
VStorageStats vstorage_stats(const VStorageArena *arena);
const char *vstorage_error(VStorageStatus status);
VStorageStatus vstorage_allocate(VStorageArena *arena, uint32_t id, uint8_t scalar, uint64_t elements);
VStorageStatus vstorage_drop(VStorageArena *arena, uint32_t id);
VStorageStatus vstorage_fill(VStorageArena *arena, uint32_t id, VStorageLayout view,
                            uint8_t scalar, uint64_t real, uint64_t imaginary);
VStorageStatus vstorage_store(VStorageArena *arena, uint32_t id, VStorageLayout view,
                             uint64_t row, uint64_t column, uint8_t scalar,
                             uint64_t real, uint64_t imaginary);
VStorageStatus vstorage_expect(VStorageArena *arena, uint32_t id, VStorageLayout view,
                              uint64_t row, uint64_t column, uint8_t scalar,
                              uint64_t real, uint64_t imaginary);
VStorageStatus vstorage_copy(VStorageArena *arena, uint32_t source, VStorageLayout input,
                            uint32_t target, VStorageLayout output);
#endif
