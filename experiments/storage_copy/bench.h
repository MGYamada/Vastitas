#ifndef STORAGE_COPY_BENCH_H
#define STORAGE_COPY_BENCH_H
#include "../../lean-kernel/native/storage.h"

/* Experiment-private fixture access; never linked into the runtime package. */
typedef struct {
    uint64_t rows, columns;
    uint8_t scalar, source_pad, target_pad, source_transpose, target_transpose, self;
} BenchCase;
typedef struct {
    VStorageArena *arena;
    VStorageLayout input, output;
    double *source, *target;
    uint64_t source_words, target_words, fixture_written_bytes;
    uint8_t scalar, self;
} BenchFixture;
typedef struct BenchPrepared BenchPrepared;
typedef VStorageStatus (*CheckedCopy)(VStorageArena *, uint32_t, VStorageLayout,
                                      uint32_t, VStorageLayout);
typedef void (*PreparedCopy)(BenchPrepared *);

VStorageStatus bench_c_copy(VStorageArena *, uint32_t, VStorageLayout, uint32_t, VStorageLayout);
int bench_open(BenchFixture *, BenchCase);
VStorageStats bench_close(BenchFixture *);
int bench_verify(const BenchFixture *);
uint64_t bench_observe(const BenchFixture *);
BenchPrepared *bench_prepare(BenchFixture *);
void bench_unprepare(BenchPrepared *);
void bench_adapter_loop(BenchPrepared *);
void bench_c_loop(BenchPrepared *);
void bench_contract_tests(void);
#endif
