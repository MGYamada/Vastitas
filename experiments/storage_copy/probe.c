/* Test-only translation unit: the production file is included unchanged.
 * Private prepare/copy_kernel access is confined here. No runtime API, package,
 * generated program or public protocol gains an unchecked entry point. */
#include "../../lean-kernel/native/storage.c"
#include "bench.h"
#include <assert.h>
#include <stdio.h>

/* Independent conventional C loop, with the same logical column/row order,
 * interleaved complex representation and single-pass memory traffic. Per-column
 * base pointers replace the adapter's full indexed cell calculations. Neither baseline
 * tiles, packs, conjugates, changes loop order, or uses non-temporal stores. */
static void c_kernel(const double *restrict source, double *restrict target,
                     const Prepared *a, const Prepared *b) {
    for (uint64_t col = 0; col < a->columns; ++col) {
        const double *s = source + col * a->column_step;
        double *d = target + col * b->column_step;
        if (a->components == 1) {
            for (uint64_t row = 0; row < a->rows; ++row)
                d[row * b->row_step] = s[row * a->row_step];
        } else {
            for (uint64_t row = 0; row < a->rows; ++row) {
                d[row * b->row_step] = s[row * a->row_step];
                d[row * b->row_step + 1] = s[row * a->row_step + 1];
            }
        }
    }
}

/* Deliberately share the exact physical preflight and accounting contract.
 * This is a controlled copy-loop baseline, not an independent reimplementation
 * of storage safety. The boundary below mirrors vstorage_copy and is tested
 * against it, including early returns and preservation on rejected inputs. */
VStorageStatus bench_c_copy(VStorageArena *arena, uint32_t source, VStorageLayout input,
                            uint32_t target, VStorageLayout output) {
    Prepared a, b;
    VStorageStatus status = prepare(arena, source, input, &a);
    if (status != VS_OK) return status;
    status = prepare(arena, target, output, &b);
    if (status != VS_OK) return status;
    if (a.buffer->scalar != b.buffer->scalar) return VS_SCALAR;
    if (a.rows != b.rows || a.columns != b.columns) return VS_LAYOUT;
    if (!a.bytes) return VS_OK;
    if (source == target) {
        if (a.start == b.start && a.row_step == b.row_step && a.column_step == b.column_step) return VS_OK;
        if (!(a.end <= b.start || b.end <= a.start)) return VS_ALIAS;
    }
    if (!counter_fits(arena->stats.written_bytes, b.bytes) || !counter_fits(arena->stats.copied_bytes, b.bytes))
        return VS_OVERFLOW;
    const double *s = a.buffer->data + a.start / 8;
    double *d = b.buffer->data + b.start / 8;
    c_kernel(s, d, &a, &b);
    arena->stats.written_bytes += b.bytes;
    arena->stats.copied_bytes += b.bytes;
    return VS_OK;
}

static const uint64_t sentinel = UINT64_C(0x7ff80000deadbeef);
static uint64_t input_bits(uint64_t i) {
    const uint64_t special[] = {0, UINT64_C(0x8000000000000000),
        UINT64_C(0x7ff0000000000000), UINT64_C(0xfff0000000000000),
        UINT64_C(0x7ff8000000000042), UINT64_C(0x7ff0000000000001)};
    return i % 97 < 6 ? special[i % 97] :
        UINT64_C(0x3ff0000000000000) | ((i * UINT64_C(0x9e3779b97f4a7c15)) & UINT64_C(0xfffffffffffff));
}
static uint64_t bits_at(const double *data, uint64_t i) {
    uint64_t bits; memcpy(&bits, data + i, 8); return bits;
}
static VStorageLayout layout(BenchCase c, int target, uint64_t *elements) {
    uint8_t t = target ? c.target_transpose : c.source_transpose;
    uint8_t pad = target ? c.target_pad : c.source_pad;
    uint64_t rows = t ? c.columns : c.rows, cols = t ? c.rows : c.columns;
    uint64_t prefix = pad ? (target ? 3 : 2) : 0;
    uint64_t leading = (rows ? rows : 1) + (pad ? (target ? 5 : 3) : 0);
    *elements = !pad && (!rows || !cols) ? 0 : prefix + leading * cols + (pad ? 3 : 0);
    return (VStorageLayout){prefix * (c.scalar ? 16 : 8), rows, cols, leading, t};
}
static int initialize(BenchFixture *f, uint32_t id, uint64_t elements, int source, double **data) {
    Prepared p;
    VStorageLayout full = {0, elements, 1, elements ? elements : 1, 0};
    if (prepare(f->arena, id, full, &p) != VS_OK) return 0;
    *data = p.buffer->data;
    uint64_t words = elements * (f->scalar ? 2 : 1);
    for (uint64_t i = 0; i < words; ++i) {
        uint64_t bits = source ? input_bits(i) : sentinel;
        memcpy(*data + i, &bits, 8);
    }
    /* Fixture writes are distinct from actual runtime write/copy counters. */
    f->fixture_written_bytes += words * 8;
    return 1;
}
int bench_open(BenchFixture *f, BenchCase c) {
    *f = (BenchFixture){0};
    f->scalar = c.scalar; f->self = c.self;
    uint64_t se, de;
    f->input = layout(c, 0, &se); f->output = layout(c, 1, &de);
    if (c.self) { f->output = f->input; de = 0; }
    f->arena = vstorage_new((se + de) * (c.scalar ? 16 : 8));
    if (!f->arena) return 0;
    if (vstorage_allocate(f->arena, 0, c.scalar, se) != VS_OK ||
        (!c.self && vstorage_allocate(f->arena, 1, c.scalar, de) != VS_OK) ||
        !initialize(f, 0, se, 1, &f->source) ||
        (!c.self && !initialize(f, 1, de, 0, &f->target))) {
        vstorage_delete(f->arena); f->arena = NULL; return 0;
    }
    f->source_words = se * (c.scalar ? 2 : 1);
    f->target_words = c.self ? f->source_words : de * (c.scalar ? 2 : 1);
    if (c.self) f->target = f->source;
    return 1;
}
VStorageStats bench_close(BenchFixture *f) {
    vstorage_close(f->arena);
    VStorageStats stats = vstorage_stats(f->arena);
    assert(!stats.live_bytes && stats.data_allocations == stats.data_frees);
    vstorage_delete(f->arena); f->arena = NULL;
    return stats;
}
int bench_verify(const BenchFixture *f) {
    for (uint64_t i = 0; i < f->source_words; ++i)
        if (bits_at(f->source, i) != input_bits(i)) return 0;
    if (f->self) return 1;
    /* Independent inverse physical-layout oracle: inspect every destination
     * word, including prefix, inter-column padding, final padding and suffix. */
    uint64_t components = f->scalar ? 2 : 1;
    for (uint64_t i = 0; i < f->target_words; ++i) {
        uint64_t expected = sentinel, byte = i * 8;
        if (byte >= f->output.offset) {
            uint64_t word = (byte - f->output.offset) / 8;
            uint64_t physical = word / components;
            uint64_t pr = physical % f->output.leading, pc = physical / f->output.leading;
            if (pr < f->output.rows && pc < f->output.columns) {
                uint64_t r = f->output.transposed ? pc : pr, c = f->output.transposed ? pr : pc;
                uint64_t sr = f->input.transposed ? c : r, sc = f->input.transposed ? r : c;
                expected = input_bits(f->input.offset / 8 +
                    (sc * f->input.leading + sr) * components + word % components);
            }
        }
        if (bits_at(f->target, i) != expected) return 0;
    }
    return 1;
}
uint64_t bench_observe(const BenchFixture *f) {
    /* O(1) observation inside lifecycle timing; exhaustive checks are outside
     * timing. External calls without LTO also keep every repeated copy present. */
    uint64_t n = f->target_words;
    return n ? bits_at(f->target, 0) ^ bits_at(f->target, n / 2) ^ bits_at(f->target, n - 1) : 0;
}
struct BenchPrepared { Prepared a, b; const double *s; double *d; int no_work; };
BenchPrepared *bench_prepare(BenchFixture *f) {
    /* Check the actual boundary before exposing an experiment-local kernel.
     * This preliminary copy and its counters are outside all timed intervals. */
    if (vstorage_copy(f->arena, 0, f->input, f->self ? 0 : 1, f->output) != VS_OK) return NULL;
    BenchPrepared *p = calloc(1, sizeof(*p));
    if (!p) return NULL;
    if (prepare(f->arena, 0, f->input, &p->a) != VS_OK ||
        prepare(f->arena, f->self ? 0 : 1, f->output, &p->b) != VS_OK) { free(p); return NULL; }
    p->no_work = !p->a.bytes || f->self;
    if (!p->no_work) {
        p->s = p->a.buffer->data + p->a.start / 8;
        p->d = p->b.buffer->data + p->b.start / 8;
        p->a.start = p->b.start = 0;
    }
    return p;
}
void bench_unprepare(BenchPrepared *p) { free(p); }
void bench_adapter_loop(BenchPrepared *p) { if (!p->no_work) copy_kernel(p->s, p->d, &p->a, &p->b); }
void bench_c_loop(BenchPrepared *p) { if (!p->no_work) c_kernel(p->s, p->d, &p->a, &p->b); }

void bench_contract_tests(void) {
    CheckedCopy copies[] = {vstorage_copy, bench_c_copy};
    for (unsigned impl = 0; impl < 2; ++impl) {
        VStorageArena *a = vstorage_new(256); assert(a);
        assert(vstorage_allocate(a, 0, 0, 16) == VS_OK);
        assert(vstorage_allocate(a, 1, 0, 16) == VS_OK);
        VStorageLayout full = {0,16,1,16,0}, x = {0,4,1,4,0}, y = {32,4,1,4,0};
        assert(vstorage_fill(a,0,full,0,sentinel,0) == VS_OK);
        assert(vstorage_fill(a,1,full,0,sentinel,0) == VS_OK);
        VStorageStats initial = vstorage_stats(a);
        VStorageLayout bad[] = {{1,4,1,4,0},{0,4,1,3,0},{0,32,1,32,0},
            {0,4,1,4,2},{UINT64_MAX,4,1,4,0},{0,4,1,(uint64_t)INT32_MAX+1,0}};
        for (unsigned i = 0; i < sizeof(bad)/sizeof(*bad); ++i) {
            assert(copies[impl](a,0,x,1,bad[i]) == VS_LAYOUT);
            assert(copies[impl](a,0,bad[i],1,x) == VS_LAYOUT);
        }
        assert(copies[impl](a,9,x,1,x) == VS_HANDLE);
        assert(copies[impl](a,0,x,9,x) == VS_HANDLE);
        assert(copies[impl](a,0,x,1,full) == VS_LAYOUT);
        VStorageLayout overlap = {8,4,1,4,0};
        assert(copies[impl](a,0,x,0,overlap) == VS_ALIAS);
        assert(copies[impl](a,0,x,0,x) == VS_OK);
        assert(vstorage_stats(a).copied_bytes == 0);
        assert(vstorage_stats(a).written_bytes == initial.written_bytes);
        a->stats.copied_bytes = UINT64_MAX;
        assert(copies[impl](a,0,x,1,x) == VS_OVERFLOW);
        assert(copies[impl](a,0,x,0,x) == VS_OK);
        a->stats.copied_bytes = 0;
        a->stats.written_bytes = UINT64_MAX;
        assert(copies[impl](a,0,x,1,x) == VS_OVERFLOW);
        a->stats.written_bytes = initial.written_bytes;
        for (uint64_t i = 0; i < 16; ++i) {
            assert(vstorage_expect(a,0,full,i,0,0,sentinel,0) == VS_OK);
            assert(vstorage_expect(a,1,full,i,0,0,sentinel,0) == VS_OK);
        }
        assert(copies[impl](a,0,x,0,y) == VS_OK); /* disjoint same allocation */
        assert(a->stats.copied_bytes == 32);
        assert(vstorage_allocate(a,2,0,1) == VS_ALLOCATION);
        vstorage_close(a);
        assert(vstorage_stats(a).live_bytes == 0 && vstorage_stats(a).data_frees == 2);
        assert(copies[impl](a,0,x,1,x) == VS_HANDLE);
        vstorage_delete(a);
        a = vstorage_new(64); assert(a);
        assert(vstorage_allocate(a,0,0,2) == VS_OK);
        assert(vstorage_allocate(a,1,1,2) == VS_OK);
        VStorageLayout one = {0,1,1,1,0};
        assert(copies[impl](a,0,one,1,one) == VS_SCALAR);
        vstorage_delete(a);
    }
    /* Ensure the exhaustive oracle detects output, source and padding damage. */
    BenchFixture f;
    assert(bench_open(&f, (BenchCase){2,3,1,1,1,1,0,0}));
    assert(vstorage_copy(f.arena,0,f.input,1,f.output) == VS_OK);
    assert(bench_verify(&f));
    uint64_t at[] = {0, f.output.offset / 8, f.target_words - 1};
    for (unsigned i = 0; i < 3; ++i) {
        uint64_t original = bits_at(f.target,at[i]), bad = original ^ 1;
        memcpy(f.target + at[i], &bad, 8); assert(!bench_verify(&f));
        memcpy(f.target + at[i], &original, 8); assert(bench_verify(&f));
    }
    uint64_t original = bits_at(f.source,0), bad = original ^ 1;
    memcpy(f.source, &bad, 8); assert(!bench_verify(&f));
    memcpy(f.source, &original, 8); assert(bench_verify(&f));
    (void)bench_close(&f);
    puts("checked baseline contract: failure-before-write, alias, overflow, self and cleanup passed");
}
