/* Experiment only. This translation unit replaces storage.c ONLY in a private
 * runtime copy. It exposes fixtures/counters without changing production APIs. */
#define _POSIX_C_SOURCE 200809L
#ifdef __APPLE__
#define _DARWIN_C_SOURCE 1
#endif
#define vstorage_new storage_new_impl
#define vstorage_drop storage_drop_impl
#define vstorage_delete storage_delete_impl
#define vstorage_pack3 storage_pack3_impl
#include "../../lean-kernel/native/storage.c"
#undef vstorage_new
#undef vstorage_drop
#undef vstorage_delete
#undef vstorage_pack3
#include "../../lean-kernel/numerical/gemm.h"
#include "calls.h"
#include <assert.h>
#include <math.h>
#include <stdio.h>
#include <time.h>
#include <sys/resource.h>
#include "case.h"

static VStorageArena *active;
static VStorageStats total, before, timed;
static uint64_t start_ns, elapsed_ns, kernel_ns, kernel_calls, pack_ns, pack_calls, repetitions, deletes;
static unsigned scope;
static int verify_on_drop;
static volatile uint64_t observed;
static uint64_t checksum;

static void require(int valid) {
    if (!valid) { fputs("benchmark contract failure\n", stderr); abort(); }
}
static void ok(VStorageStatus s) { require(s == VS_OK); }
static uint64_t now_ns(void) {
    struct timespec t;
#if defined(__APPLE__) || defined(CLOCK_MONOTONIC_RAW)
    require(clock_gettime(CLOCK_MONOTONIC_RAW, &t) == 0);
#else
    require(clock_gettime(CLOCK_MONOTONIC, &t) == 0);
#endif
    return (uint64_t)t.tv_sec * UINT64_C(1000000000) + (uint64_t)t.tv_nsec;
}
static uint64_t word(double x) { uint64_t u; memcpy(&u, &x, 8); return u; }
static uint64_t maximum(uint64_t a, uint64_t b) { return a > b ? a : b; }

void bench_dgemm(enum CBLAS_ORDER o, enum CBLAS_TRANSPOSE ta, enum CBLAS_TRANSPOSE tb,
    blasint m, blasint n, blasint k, double a, const double *x, blasint lx,
    const double *y, blasint ly, double b, double *z, blasint lz) {
    uint64_t t = scope == 3 ? now_ns() : 0;
    cblas_dgemm(o, ta, tb, m, n, k, a, x, lx, y, ly, b, z, lz);
    if (scope == 3) { kernel_ns += now_ns() - t; ++kernel_calls; }
}
void bench_zgemm(enum CBLAS_ORDER o, enum CBLAS_TRANSPOSE ta, enum CBLAS_TRANSPOSE tb,
    blasint m, blasint n, blasint k, const void *a, const void *x, blasint lx,
    const void *y, blasint ly, const void *b, void *z, blasint lz) {
    uint64_t t = scope == 3 ? now_ns() : 0;
    cblas_zgemm(o, ta, tb, m, n, k, a, x, lx, y, ly, b, z, lz);
    if (scope == 3) { kernel_ns += now_ns() - t; ++kernel_calls; }
}

typedef struct { long double r, i; } Z;
static Z z(const double *v) { return (Z){v[0], v[1]}; }
static Z plus(Z a, Z b) { return (Z){a.r+b.r, a.i+b.i}; }
static Z times(Z a, Z b) { return (Z){a.r*b.r-a.i*b.i, a.r*b.i+a.i*b.r}; }
static Z entry(unsigned id, uint64_t r, uint64_t c) {
    for (unsigned p = 0; p < 2; ++p)
        if (patches[id][p].row == r && patches[id][p].col == c) return z(patches[id][p].value);
    return z(values[id]);
}
/* Direct coordinate contraction oracle. Never reads packed storage or BLAS. */
static Z product(uint64_t r, uint64_t c) {
    uint64_t x = r % dim_i, y = r / dim_i;
    Z result = {0,0};
    for (uint64_t z = 0; z < dim_k; ++z)
        result = plus(result,times(entry(0,x,z+dim_k*y),entry(1,z,c)));
    return result;
}
static int verify(VStorageArena *a, uint64_t reps) {
    (void)reps;
    uint64_t hash = UINT64_C(1469598103934665603);
    for (unsigned id = 0; id < 4; ++id) {
        Buffer *buffer = lookup(a,id);
        if (!buffer) return 0;
        uint64_t offset = views[id].offset / (scalar ? 16 : 8);
        for (uint64_t index = 0; index < elements[id]; ++index) {
            uint64_t rel = index >= offset ? index-offset : UINT64_MAX;
            uint64_t r = rel % views[id].leading, c = rel / views[id].leading;
            int logical = index >= offset && r < views[id].rows && c < views[id].columns;
            Z want = !logical ? z(sentinel) : id < 2 ? entry(id,r,c) : id == 2 ? entry(0,r%dim_i,c+dim_k*(r/dim_i)) : product(r,c);
            for (unsigned part = 0; part <= scalar; ++part) {
                double got = buffer->data[index*(scalar+1)+part];
                long double target = part ? want.i : want.r;
                if (!isfinite(got)) return 0;
                if (!logical || id < 3) {
                    if (word(got) != word((double)target)) return 0;
                } else {
                    long double tol = 32 * DBL_EPSILON * (dim_k+1) * fmaxl(1,fabsl(target));
                    if (fabsl((long double)got-target) > tol) return 0;
                }
                hash = (hash ^ word(got)) * UINT64_C(1099511628211);
            }
        }
    }
    checksum = hash;
    return 1;
}

VStorageArena *vstorage_new(uint64_t budget) {
    require(active == NULL);
    active = storage_new_impl(budget);
    return active;
}
VStorageStatus vstorage_drop(VStorageArena *a, uint32_t id) {
    if (id == 3 && lookup(a,id)) {
        if (verify_on_drop) require(verify(a,1));
        observed ^= word(lookup(a,id)->data[views[3].offset/8]);
    }
    return storage_drop_impl(a,id);
}
void vstorage_delete(VStorageArena *a) {
    if (!a) return;
    vstorage_close(a);
    VStorageStats s = vstorage_stats(a);
    require(s.live_bytes == 0 && s.data_allocations == s.data_frees);
    total.data_allocations += s.data_allocations; total.data_frees += s.data_frees;
    total.written_bytes += s.written_bytes; total.copied_bytes += s.copied_bytes;
    total.peak_bytes = maximum(total.peak_bytes,s.peak_bytes);
    total.metadata_allocations += s.metadata_allocations;
    total.metadata_bytes = maximum(total.metadata_bytes,s.metadata_bytes);
    ++deletes;
    require(active == a); active = NULL;
    storage_delete_impl(a);
}

/* Matched standalone C algorithm: physical preparation, explicit contiguous
 * x-block pack, direct pinned CBLAS. No vstorage_pack3/vgemm_execute call. */
static void c_pack(VStorageArena *arena) {
    uint64_t start = scope == 2 ? now_ns() : 0;
    VStorageDense input, output;
    ok(vstorage_prepare_dense(arena,0,views[0],&input));
    ok(vstorage_prepare_dense(arena,2,views[2],&output));
    require(input.scalar == output.scalar && input.scalar == scalar);
    require(input.rows == dim_i && input.columns == dim_k*dim_j);
    require(output.rows == dim_i*dim_j && output.columns == dim_k);
    require(input.allocation != output.allocation);
    ok(vstorage_prepare_write(arena,output.bytes));
    require(arena->stats.copied_bytes <= UINT64_MAX-output.bytes);
    uint64_t width = scalar ? 16 : 8;
    for (uint64_t z = 0; z < dim_k; ++z)
        for (uint64_t y = 0; y < dim_j; ++y)
            memcpy((char *)output.data+(dim_i*y+output.leading*z)*width,
                   (const char *)input.data+input.leading*(z+dim_k*y)*width,dim_i*width);
    vstorage_record_write(arena,output.bytes);
    arena->stats.copied_bytes += output.bytes;
    if (scope == 2) { pack_ns += now_ns()-start; ++pack_calls; }
}
VStorageStatus vstorage_pack3(VStorageArena *arena, uint32_t source, VStorageLayout input,
    uint32_t target, VStorageLayout output, uint64_t i, uint64_t k, uint64_t j) {
    uint64_t start = scope == 2 ? now_ns() : 0;
    VStorageStatus status = storage_pack3_impl(arena,source,input,target,output,i,k,j);
    if (scope == 2) { pack_ns += now_ns()-start; ++pack_calls; }
    return status;
}
static void c_gemm(VStorageArena *arena) {
    ok(vgemm_backend_check());
    VStorageDense a,b,c;
    ok(vstorage_prepare_dense(arena,2,views[2],&a));
    ok(vstorage_prepare_dense(arena,1,views[1],&b));
    ok(vstorage_prepare_dense(arena,3,views[3],&c));
    require(a.scalar == b.scalar && b.scalar == c.scalar && a.scalar == scalar);
    require(a.columns == b.rows && a.rows == c.rows && b.columns == c.columns);
    require(a.allocation != c.allocation && b.allocation != c.allocation);
    ok(vstorage_prepare_write(arena,c.bytes));
    if (!scalar)
        bench_dgemm(CblasColMajor,CblasNoTrans,CblasNoTrans,(blasint)c.rows,(blasint)c.columns,
                    (blasint)a.columns,alpha[0],a.data,(blasint)a.leading,b.data,(blasint)b.leading,
                    beta[0],c.data,(blasint)c.leading);
    else
        bench_zgemm(CblasColMajor,CblasNoTrans,CblasNoTrans,(blasint)c.rows,(blasint)c.columns,
                    (blasint)a.columns,alpha,a.data,(blasint)a.leading,b.data,(blasint)b.leading,
                    beta,c.data,(blasint)c.leading);
    vstorage_record_write(arena,c.bytes);
}
static VStorageArena *c_setup(void) {
    VStorageArena *arena = vstorage_new(INT64_MAX); require(arena != NULL);
    for (unsigned id = 0; id < 4; ++id) {
        ok(vstorage_allocate(arena,id,(uint8_t)scalar,elements[id]));
        VStorageLayout all = {0,elements[id],1,elements[id],0};
        ok(vstorage_fill(arena,id,all,(uint8_t)scalar,word(sentinel[0]),word(sentinel[1])));
        if (id < 2) {
            ok(vstorage_fill(arena,id,views[id],(uint8_t)scalar,word(values[id][0]),word(values[id][1])));
            for (unsigned p = 0; p < 2; ++p) {
                const Patch *v = &patches[id][p];
                ok(vstorage_store(arena,id,views[id],v->row,v->col,(uint8_t)scalar,word(v->value[0]),word(v->value[1])));
            }
        }
    }
    return arena;
}
static void c_cleanup(VStorageArena *a) {
    ok(vstorage_drop(a,3)); ok(vstorage_drop(a,2)); ok(vstorage_drop(a,1)); ok(vstorage_drop(a,0));
    vstorage_close(a); vstorage_delete(a);
}
void bench_begin(uint32_t which, uint64_t reps, uint8_t checking) {
    require(which <= 3 && reps > 0 && reps <= 1000000);
    scope = which; repetitions = reps; verify_on_drop = checking && !which;
    total = (VStorageStats){0}; before = vstorage_stats(active); timed = (VStorageStats){0};
    deletes = 0; kernel_calls = 0; kernel_ns = 0; pack_calls = 0; pack_ns = 0; checksum = 0; observed = 0;
    start_ns = now_ns();
}
void bench_stop(void) {
    elapsed_ns = now_ns()-start_ns;
    if (scope) {
        VStorageStats s = vstorage_stats(active);
        timed.data_allocations = s.data_allocations-before.data_allocations;
        timed.data_frees = s.data_frees-before.data_frees;
        timed.written_bytes = s.written_bytes-before.written_bytes;
        timed.copied_bytes = s.copied_bytes-before.copied_bytes;
        timed.metadata_allocations = s.metadata_allocations-before.metadata_allocations;
        if (scope == 2) {
            require(pack_calls == repetitions);
            elapsed_ns = pack_ns;
        }
        if (scope == 3) {
            require(kernel_calls == repetitions);
            elapsed_ns = kernel_ns;
        }
    } else timed = total;
}
void bench_verify(VStorageArena *arena, uint64_t reps) { require(verify(arena,reps)); }
void bench_c_run(uint32_t which, uint64_t reps, uint8_t checking) {
    VStorageArena *arena = which ? c_setup() : NULL;
    bench_begin(which,reps,checking);
    for (uint64_t i = 0; i < reps; ++i) {
        if (!which) arena = c_setup();
        c_pack(arena); c_gemm(arena);
        if (!which) c_cleanup(arena);
    }
    bench_stop();
    if (which) { bench_verify(arena,reps); c_cleanup(arena); }
}
void bench_report(void) {
    uint64_t width = scalar ? 16 : 8, peak = 0;
    for (unsigned i = 0; i < 4; ++i) peak += elements[i]*width;
    uint64_t init = peak + width*(views[0].rows*views[0].columns + views[1].rows*views[1].columns+4);
    uint64_t output = width*views[3].rows*views[3].columns;
    uint64_t packed = width*dim_i*dim_k*dim_j;
    uint64_t lives = scope ? 1 : repetitions;
    require(!active && deletes == lives && total.data_allocations == 4*lives);
    require(total.metadata_allocations == 2*lives);
    require(total.peak_bytes == peak && total.copied_bytes == packed*repetitions);
    require(total.written_bytes == init*lives+(packed+output)*repetitions);
    require(timed.data_allocations == (scope ? 0 : 4*repetitions) && timed.copied_bytes == packed*repetitions);
    require(timed.data_frees == (scope ? 0 : 4*repetitions));
    if (scope) require(timed.metadata_allocations == 0 && timed.written_bytes == (packed+output)*repetitions);
    struct rusage usage; require(getrusage(RUSAGE_SELF,&usage) == 0);
    long rss_kib = usage.ru_maxrss;
#ifdef __APPLE__
    rss_kib /= 1024;
#endif
    printf("{\"elapsed_ns\":%llu,\"repetitions\":%llu,\"checksum\":\"%016llx\","
           "\"data_allocations\":%llu,\"data_frees\":%llu,\"live_bytes_after\":0,"
           "\"peak_data_bytes\":%llu,\"written_bytes\":%llu,\"copied_bytes\":%llu,"
           "\"metadata_allocations\":%llu,\"peak_metadata_bytes\":%llu,"
           "\"timed_data_allocations\":%llu,\"timed_data_frees\":%llu,"
           "\"timed_written_bytes\":%llu,\"timed_copied_bytes\":%llu,\"timed_metadata_allocations\":%llu,"
           "\"pack_calls_timed\":%llu,\"blas_calls_timed\":%llu,\"process_maxrss_kib\":%ld,\"observed\":\"%016llx\"}\n",
           (unsigned long long)elapsed_ns,(unsigned long long)repetitions,(unsigned long long)checksum,
           (unsigned long long)total.data_allocations,(unsigned long long)total.data_frees,
           (unsigned long long)total.peak_bytes,(unsigned long long)total.written_bytes,
           (unsigned long long)total.copied_bytes,(unsigned long long)total.metadata_allocations,
           (unsigned long long)total.metadata_bytes,(unsigned long long)timed.data_allocations,
           (unsigned long long)timed.data_frees,(unsigned long long)timed.written_bytes,
           (unsigned long long)timed.copied_bytes,(unsigned long long)timed.metadata_allocations,
           (unsigned long long)pack_calls,(unsigned long long)kernel_calls,rss_kib,(unsigned long long)observed);
}

#ifdef BENCH_STANDALONE
static void native_operation(VStorageArena *a) {
    ok(vstorage_pack3(a,0,views[0],2,views[2],dim_i,dim_k,dim_j));
    ok(vgemm_execute(a,2,views[2],0,1,views[1],0,3,views[3],VGEMM_OVERWRITE,NULL));
}
/* Deliberately wrong pack: preserve logical input flat order. Keep output
 * physical padding intact so the coordinate oracle, not sentinels, rejects it. */
static void flat_copy_mutation(VStorageArena *a) {
    VStorageDense input, packed, output;
    ok(vstorage_prepare_dense(a,0,views[0],&input));
    ok(vstorage_prepare_dense(a,2,views[2],&packed));
    ok(vstorage_prepare_dense(a,3,views[3],&output));
    uint64_t width = scalar ? 16 : 8;
    for (uint64_t n = 0; n < dim_i*dim_k*dim_j; ++n)
        memcpy((char *)packed.data+(n%(dim_i*dim_j)+packed.leading*(n/(dim_i*dim_j)))*width,
               (const char *)input.data+(n%dim_i+input.leading*(n/dim_i))*width,width);
    ok(vgemm_execute(a,2,views[2],0,1,views[1],0,3,views[3],VGEMM_OVERWRITE,NULL));
    require(!verify(a,1));
    /* Also check a resulting output directly: rejecting stale packed bytes
     * alone would not demonstrate that the contraction sees the mutation. */
    uint64_t row = dim_i-1, col = views[3].columns-1;
    Z want = product(row,col);
    const double *got = output.data+(row+output.leading*col)*(scalar+1);
    long double tol = 32*DBL_EPSILON*(dim_k+1)*fmaxl(1,fabsl(want.r));
    require(fabsl((long double)got[0]-want.r) > tol);
    native_operation(a);
    require(verify(a,1));
    fputs("flat-copy mutation rejected by packed and output coordinate oracles\n",stderr);
}
int main(void) {
    require(vgemm_backend_check() == VS_OK);
    fprintf(stderr,"backend=%s; parallel=%d; threads=%d\n",vgemm_configuration(),openblas_get_parallel(),openblas_get_num_threads());
    VStorageArena *a = c_setup(); native_operation(a); require(verify(a,1));
    uint64_t native_hash = checksum;
    flat_copy_mutation(a); require(checksum == native_hash);
    /* All four logical buffers and all four padded envelopes are observed. */
    for (unsigned id = 0; id < 4; ++id) {
        double *cell = &a->buffers[id].data[views[id].offset/8];
        double old = *cell; *cell = old+1; require(!verify(a,1)); *cell = old;
        if (views[id].offset) {
            old = a->buffers[id].data[0]; a->buffers[id].data[0] = 0;
            require(!verify(a,1)); a->buffers[id].data[0] = old;
        }
    }
    VStorageStats saved = vstorage_stats(a);
    /* Shape and alias failures must leave output, inputs, padding and counters. */
    require(vstorage_pack3(a,0,views[0],2,views[2],dim_i,dim_k+1,dim_j) != VS_OK);
    require(vstorage_pack3(a,0,views[0],0,views[2],dim_i,dim_k,dim_j) != VS_OK);
    require(vgemm_execute(a,2,views[2],0,1,views[1],0,2,views[3],VGEMM_OVERWRITE,NULL) != VS_OK);
    require(vstorage_stats(a).written_bytes == saved.written_bytes &&
            vstorage_stats(a).copied_bytes == saved.copied_bytes && verify(a,1));
    c_cleanup(a);
    a = c_setup(); c_pack(a); c_gemm(a); require(verify(a,1) && checksum == native_hash); c_cleanup(a);
    for (unsigned mode = 0; mode < 4; ++mode) {
        bench_c_run(mode,7,1); bench_report();
        a = mode ? c_setup() : NULL; bench_begin(mode,7,1);
        for (unsigned r = 0; r < 7; ++r) {
            if (!mode) a = c_setup();
            native_operation(a);
            if (!mode) c_cleanup(a);
        }
        bench_stop(); if (mode) { bench_verify(a,7); c_cleanup(a); } bench_report();
    }
    fputs("native/C coordinate, padding, cost, corruption and preflight checks passed\n",stderr);
    return 0;
}
#endif
