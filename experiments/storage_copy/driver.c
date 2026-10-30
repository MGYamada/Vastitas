#define _POSIX_C_SOURCE 200809L
#include "bench.h"
#include <assert.h>
#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

static volatile uint64_t observed;
static uint64_t now(void) {
    struct timespec t; assert(clock_gettime(CLOCK_MONOTONIC, &t) == 0);
    return (uint64_t)t.tv_sec * UINT64_C(1000000000) + (uint64_t)t.tv_nsec;
}
typedef struct {
    uint64_t ns, checksum, init_bytes;
    VStorageStats timed, fixture;
} Sample;
static void accumulate(VStorageStats *a, VStorageStats b) {
    a->data_allocations += b.data_allocations; a->data_frees += b.data_frees;
    a->live_bytes = b.live_bytes;
    if (b.peak_bytes > a->peak_bytes) a->peak_bytes = b.peak_bytes;
    a->written_bytes += b.written_bytes; a->copied_bytes += b.copied_bytes;
    a->metadata_allocations += b.metadata_allocations;
    if (b.metadata_bytes > a->metadata_bytes) a->metadata_bytes = b.metadata_bytes;
}
static Sample sample(BenchCase c, unsigned mode, unsigned impl, uint64_t reps) {
    CheckedCopy copy = impl ? bench_c_copy : vstorage_copy;
    PreparedCopy loop = impl ? bench_c_loop : bench_adapter_loop;
    Sample s = {0}; BenchFixture f;
    uint64_t copied = c.self ? 0 : c.rows * c.columns * (c.scalar ? 16 : 8);
    if (mode == 0) {
        uint64_t start = now();
        for (uint64_t i = 0; i < reps; ++i) {
            assert(bench_open(&f, c));
            assert(copy(f.arena, 0, f.input, c.self ? 0 : 1, f.output) == VS_OK);
            s.checksum += bench_observe(&f);
            s.init_bytes += f.fixture_written_bytes;
            VStorageStats stats = bench_close(&f);
            assert(stats.copied_bytes == copied && stats.written_bytes == copied);
            accumulate(&s.timed, stats);
        }
        s.ns = now() - start;
        s.fixture = s.timed;
    } else {
        assert(bench_open(&f, c));
        BenchPrepared *p = mode == 2 ? bench_prepare(&f) : NULL;
        assert(mode != 2 || p);
        VStorageStats before = vstorage_stats(f.arena);
        uint64_t start = now();
        if (mode == 1) {
            for (uint64_t i = 0; i < reps; ++i)
                assert(copy(f.arena, 0, f.input, c.self ? 0 : 1, f.output) == VS_OK);
        } else {
            for (uint64_t i = 0; i < reps; ++i) loop(p);
        }
        s.ns = now() - start;
        VStorageStats after = vstorage_stats(f.arena);
        s.timed = (VStorageStats){.live_bytes = after.live_bytes, .peak_bytes = after.peak_bytes,
            .written_bytes = after.written_bytes - before.written_bytes,
            .copied_bytes = after.copied_bytes - before.copied_bytes};
        assert(after.data_allocations == before.data_allocations && after.data_frees == before.data_frees);
        assert(after.metadata_allocations == before.metadata_allocations);
        assert(s.timed.copied_bytes == (mode == 1 ? copied * reps : 0));
        assert(s.timed.written_bytes == s.timed.copied_bytes);
        assert(bench_verify(&f)); /* all words and padding after every batch */
        s.checksum = bench_observe(&f); s.init_bytes = f.fixture_written_bytes;
        bench_unprepare(p); s.fixture = bench_close(&f);
    }
    observed += s.checksum;
    return s;
}
static void verify_case(BenchCase c) {
    for (unsigned impl = 0; impl < 2; ++impl) {
        BenchFixture f; assert(bench_open(&f, c));
        CheckedCopy copy = impl ? bench_c_copy : vstorage_copy;
        assert(copy(f.arena, 0, f.input, c.self ? 0 : 1, f.output) == VS_OK);
        assert(bench_verify(&f));
        VStorageStats stats = bench_close(&f);
        uint64_t expected = c.self ? 0 : c.rows * c.columns * (c.scalar ? 16 : 8);
        assert(stats.copied_bytes == expected && stats.written_bytes == expected);
    }
}
static void emit(const char *phase, unsigned mode, unsigned impl, unsigned pair, unsigned order,
                 uint64_t reps, Sample s) {
    const char *modes[] = {"lifecycle", "checked_call", "loop_only"};
    printf("%s,%s,%s,%u,%u,%" PRIu64 ",%" PRIu64 ",%" PRIu64,
           phase, modes[mode], impl ? "c" : "adapter", pair, order, reps, s.ns, s.checksum);
    printf(",%" PRIu64 ",%" PRIu64 ",%" PRIu64 ",%" PRIu64 ",%" PRIu64 ",%" PRIu64,
           s.timed.data_allocations, s.timed.data_frees, s.timed.live_bytes,
           s.timed.peak_bytes, s.timed.written_bytes, s.timed.copied_bytes);
    printf(",%" PRIu64 ",%" PRIu64 ",%" PRIu64 ",%" PRIu64 ",%" PRIu64 ",%" PRIu64 ",%" PRIu64 "\n",
           s.timed.metadata_allocations, s.timed.metadata_bytes, s.init_bytes,
           s.fixture.data_allocations, s.fixture.data_frees, s.fixture.live_bytes,
           s.fixture.metadata_allocations);
}
static uint64_t number(const char *s, uint64_t maximum) {
    char *end; uint64_t n = strtoull(s, &end, 10);
    assert(*s && !*end && s[0] != '-' && n <= maximum); return n;
}
int main(int argc, char **argv) {
    if (argc == 2 && !strcmp(argv[1], "--contracts")) { bench_contract_tests(); return 0; }
    if (argc != 12) { fprintf(stderr, "rows cols scalar spad dpad st dt self samples target_ns offset\n"); return 2; }
    BenchCase c = {number(argv[1],8192), number(argv[2],8192),
        (uint8_t)number(argv[3],1), (uint8_t)number(argv[4],1), (uint8_t)number(argv[5],1),
        (uint8_t)number(argv[6],1), (uint8_t)number(argv[7],1), (uint8_t)number(argv[8],1)};
    unsigned samples = (unsigned)number(argv[9],1000);
    uint64_t target = number(argv[10],UINT64_C(1000000000));
    unsigned offset = (unsigned)number(argv[11],1);
    puts("phase,scope,implementation,pair,order,repetitions,elapsed_ns,checksum,timed_data_allocations,timed_data_frees,live_bytes,peak_bytes,timed_written_bytes,timed_copied_bytes,timed_metadata_allocations,metadata_bytes,fixture_written_bytes,fixture_data_allocations,fixture_data_frees,fixture_live_bytes,fixture_metadata_allocations");
    verify_case(c);
    for (unsigned mode = 0; mode < 3; ++mode) {
        /* Self and empty calls have no element kernel: do not present wrapper
         * call timing as copy throughput or a prepared-loop measurement. */
        if (mode == 2 && (c.self || !c.rows || !c.columns)) continue;
        for (unsigned w = 0; w < 2; ++w)
            for (unsigned j = 0; j < 2; ++j) {
                unsigned impl = (w + j + offset) % 2;
                emit("warmup",mode,impl,w,j,1,sample(c,mode,impl,1));
            }
        uint64_t reps = 1;
        for (unsigned attempt = 0; ; ++attempt) {
            uint64_t fastest = UINT64_MAX;
            for (unsigned j = 0; j < 2; ++j) {
                unsigned impl = (attempt + j + offset) % 2;
                Sample s = sample(c,mode,impl,reps);
                if (s.ns < fastest) fastest = s.ns;
                emit("calibration",mode,impl,attempt,j,reps,s);
            }
            if (fastest >= target || reps >= 2000000) break;
            uint64_t factor = fastest ? target / fastest + 1 : 10;
            if (factor > 10) factor = 10;
            reps = reps > 2000000 / factor ? 2000000 : reps * factor;
        }
        for (unsigned i = 0; i < samples; ++i)
            for (unsigned j = 0; j < 2; ++j) {
                unsigned impl = (i + j + offset) % 2;
                emit("measurement",mode,impl,i,j,reps,sample(c,mode,impl,reps));
            }
    }
    verify_case(c); /* exhaustive post-timing lifecycle-path check */
    fprintf(stderr,"verified all source/output/padding words; sink=%" PRIu64 "\n",observed);
    return 0;
}
