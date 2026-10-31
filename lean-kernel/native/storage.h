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
    VS_BOUNDS, VS_ALIAS, VS_EXPECT, VS_ABI, VS_SHAPE, VS_OPERATION
} VStorageStatus;

/* Internal synchronous-backend access. Only the arena creates these ephemeral
 * descriptors. They must not outlive this operation or an intervening drop.
 * Logical loan rights and initialization remain the checked caller's duty. */
typedef struct {
    double *data;
    uint64_t start, end, rows, columns, leading, bytes;
    uint32_t allocation;
    uint8_t scalar, transposed;
} VStorageDense;

VStorageStatus vstorage_prepare_dense(VStorageArena *arena, uint32_t id,
                                     VStorageLayout view, VStorageDense *out);
VStorageStatus vstorage_prepare_write(VStorageArena *arena, uint64_t bytes);
void vstorage_record_write(VStorageArena *arena, uint64_t bytes);

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
/* Pack the nontransposed i-by-(k*j) view into (i*j)-by-k without allocation:
 * output(x+i*y,z) := input(x,z+k*y). Nonempty envelopes must be disjoint. */
VStorageStatus vstorage_pack3(VStorageArena *arena, uint32_t source, VStorageLayout input,
                             uint32_t target, VStorageLayout output,
                             uint64_t i, uint64_t k, uint64_t j);
/* Regroup the same rank-three coordinates between explicit rectangles.
 * A code is axis0 + 3*axis1 + 9*axis2 + 27*(split-1), where the axes form
 * a permutation of 0,1,2 and split is 1 or 2. First axes vary fastest.
 * Nonempty envelopes must be disjoint, including identical mappings. */
VStorageStatus vstorage_regroup3(VStorageArena *arena, uint32_t source, VStorageLayout input,
                                uint32_t target, VStorageLayout output,
                                uint64_t d0, uint64_t d1, uint64_t d2,
                                uint64_t input_grouping, uint64_t output_grouping);
#endif
