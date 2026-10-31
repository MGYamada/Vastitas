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
#define vstorage_regroup3 storage_regroup3_impl
#include "../../lean-kernel/native/storage.c"
#undef vstorage_new
#undef vstorage_drop
#undef vstorage_delete
#undef vstorage_pack3
#undef vstorage_regroup3
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
static uint64_t start_ns, elapsed_ns, kernel_ns, kernel_calls, pack_ns, pack_calls, repetitions, deletes, blas_sequence;
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
    unsigned selected = 4+(unsigned)(blas_sequence++%2);
    uint64_t t = scope == selected ? now_ns() : 0;
    cblas_dgemm(o, ta, tb, m, n, k, a, x, lx, y, ly, b, z, lz);
    if (scope == selected) { kernel_ns += now_ns() - t; ++kernel_calls; }
}
void bench_zgemm(enum CBLAS_ORDER o, enum CBLAS_TRANSPOSE ta, enum CBLAS_TRANSPOSE tb,
    blasint m, blasint n, blasint k, const void *a, const void *x, blasint lx,
    const void *y, blasint ly, const void *b, void *z, blasint lz) {
    unsigned selected = 4+(unsigned)(blas_sequence++%2);
    uint64_t t = scope == selected ? now_ns() : 0;
    cblas_zgemm(o, ta, tb, m, n, k, a, x, lx, y, ly, b, z, lz);
    if (scope == selected) { kernel_ns += now_ns() - t; ++kernel_calls; }
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
/* Coordinate oracle uses only fixture inputs, never packed storage or BLAS.
 * Sparse corrections avoid a k-by-j reference loop per output coordinate. */
static Z minus(Z a, Z b) { return (Z){a.r-b.r,a.i-b.i}; }
static Z middle(uint64_t x, uint64_t y, uint64_t col) {
    Z t = z(values[0]), a = z(values[1]);
    Z result = times((Z){dim_k,0},times(t,a));
    for (unsigned p = 0; p < 2; ++p) {
        const Patch *v = &patches[1][p];
        if (v->col == col) result = plus(result,times(t,minus(z(v->value),a)));
    }
    for (unsigned p = 0; p < 2; ++p) {
        const Patch *v = &patches[0][p];
        if (v->row == x && v->col/dim_k == y)
            result = plus(result,times(minus(z(v->value),t),entry(1,v->col%dim_k,col)));
    }
    return result;
}
static Z product(uint64_t row, uint64_t col) {
    uint64_t x = row%dim_i, a = row/dim_i;
    Z result = {0,0};
    for (uint64_t y = 0; y < dim_j; ++y) result = plus(result,times(middle(x,y,a),entry(2,y,col)));
    return result;
}
static int logical_cell(unsigned view, uint64_t index, uint64_t *row, uint64_t *column) {
    uint64_t offset = views[view].offset/(scalar ? 16 : 8);
    if (index < offset) return 0;
    uint64_t relative = index-offset;
    *row = relative%views[view].leading; *column = relative/views[view].leading;
    return *row < views[view].rows && *column < views[view].columns;
}
static int verify(VStorageArena *a, uint64_t reps) {
    (void)reps;
    uint64_t hash = UINT64_C(1469598103934665603);
    for (unsigned id = 0; id < 6; ++id) {
        Buffer *buffer = lookup(a,id);
        if (!buffer) return 0;
        for (uint64_t index = 0; index < elements[id]; ++index) {
            uint64_t r=0,c=0;
            Z want = z(sentinel);
            int arithmetic = 0;
            if (id == 3) {
                /* Second regroup overwrites only its own cells. All first-pack
                 * cells outside that footprint survive, including in padding. */
                if (logical_cell(6,index,&r,&c)) { want = middle(r%dim_i,c,r/dim_i); arithmetic = 1; }
                else if (logical_cell(3,index,&r,&c)) want = entry(0,r%dim_i,c+dim_k*(r/dim_i));
            } else if (logical_cell(id,index,&r,&c)) {
                if (id < 3) want = entry(id,r,c);
                else { want = id == 4 ? middle(r%dim_i,r/dim_i,c) : product(r,c); arithmetic = 1; }
            }
            for (unsigned part = 0; part <= scalar; ++part) {
                double got = buffer->data[index*(scalar+1)+part];
                long double target = part ? want.i : want.r;
                if (!isfinite(got)) return 0;
                if (!arithmetic) { if (word(got) != word((double)target)) return 0; }
                else {
                    long double tol = 64*DBL_EPSILON*(dim_k+1)*(dim_j+1)*fmaxl(1,fabsl(target));
                    if (fabsl((long double)got-target) > tol) return 0;
                }
                hash = (hash ^ word(got))*UINT64_C(1099511628211);
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
    if (id == 5 && lookup(a,id)) {
        if (verify_on_drop) require(verify(a,1));
        observed ^= word(lookup(a,id)->data[views[5].offset/8]);
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
    ok(vstorage_prepare_dense(arena,3,views[3],&output));
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
static void c_regroup(VStorageArena *arena) {
    uint64_t start = scope == 3 ? now_ns() : 0;
    VStorageDense input,output;
    ok(vstorage_prepare_dense(arena,4,views[4],&input));
    ok(vstorage_prepare_dense(arena,3,views[6],&output));
    require(input.scalar == output.scalar && input.scalar == scalar);
    require(input.rows == dim_i*dim_j && input.columns == dim_a);
    require(output.rows == dim_i*dim_a && output.columns == dim_j);
    require(input.allocation != output.allocation);
    ok(vstorage_prepare_write(arena,output.bytes));
    require(arena->stats.copied_bytes <= UINT64_MAX-output.bytes);
    uint64_t width = scalar ? 16 : 8;
    for (uint64_t a = 0; a < dim_a; ++a)
        for (uint64_t y = 0; y < dim_j; ++y)
            for (uint64_t x = 0; x < dim_i; ++x)
                memcpy((char *)output.data+(x+dim_i*a+output.leading*y)*width,
                       (const char *)input.data+(x+dim_i*y+input.leading*a)*width,width);
    vstorage_record_write(arena,output.bytes); arena->stats.copied_bytes += output.bytes;
    if (scope == 3) { pack_ns += now_ns()-start; ++pack_calls; }
}
VStorageStatus vstorage_regroup3(VStorageArena *arena, uint32_t source, VStorageLayout input,
    uint32_t target, VStorageLayout output, uint64_t d0,uint64_t d1,uint64_t d2,uint64_t from,uint64_t to) {
    uint64_t start = scope == 3 ? now_ns() : 0;
    VStorageStatus status = storage_regroup3_impl(arena,source,input,target,output,d0,d1,d2,from,to);
    if (scope == 3) { pack_ns += now_ns()-start; ++pack_calls; }
    return status;
}
static void c_gemm(VStorageArena *arena, unsigned stage) {
    ok(vgemm_backend_check());
    VStorageDense a,b,c;
    ok(vstorage_prepare_dense(arena,3,views[stage ? 6 : 3],&a));
    ok(vstorage_prepare_dense(arena,stage ? 2 : 1,views[stage ? 2 : 1],&b));
    ok(vstorage_prepare_dense(arena,stage ? 5 : 4,views[stage ? 5 : 4],&c));
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
static void c_operation(VStorageArena *arena) {
    c_pack(arena); c_gemm(arena,0); c_regroup(arena); c_gemm(arena,1);
}
static VStorageArena *c_setup(void) {
    VStorageArena *arena = vstorage_new(INT64_MAX); require(arena != NULL);
    for (unsigned id = 0; id < 6; ++id) {
        ok(vstorage_allocate(arena,id,(uint8_t)scalar,elements[id]));
        VStorageLayout all = {0,elements[id],1,elements[id],0};
        ok(vstorage_fill(arena,id,all,(uint8_t)scalar,word(sentinel[0]),word(sentinel[1])));
        if (id < 3) {
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
    for (unsigned n = 0; n < 3; ++n)
        ok(vstorage_expect(a,5,views[5],expected[n].row,expected[n].col,(uint8_t)scalar,
            word(expected[n].value[0]),word(expected[n].value[1])));
    for (unsigned id = 6; id > 0; --id) ok(vstorage_drop(a,id-1));
    vstorage_close(a); vstorage_delete(a);
}
void bench_begin(uint32_t which, uint64_t reps, uint8_t checking) {
    require(which <= 5 && reps > 0 && reps <= 1000000);
    scope = which; repetitions = reps; verify_on_drop = checking && !which;
    total = (VStorageStats){0}; before = vstorage_stats(active); timed = (VStorageStats){0};
    deletes = 0; blas_sequence = 0; kernel_calls = 0; kernel_ns = 0; pack_calls = 0; pack_ns = 0; checksum = 0; observed = 0;
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
        if (scope == 2 || scope == 3) {
            require(pack_calls == repetitions);
            elapsed_ns = pack_ns;
        }
        if (scope >= 4) {
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
        c_operation(arena);
        if (!which) c_cleanup(arena);
    }
    bench_stop();
    if (which) { bench_verify(arena,reps); c_cleanup(arena); }
}
void bench_report(void) {
    uint64_t width = scalar ? 16 : 8, peak = 0;
    for (unsigned i = 0; i < 6; ++i) peak += elements[i]*width;
    uint64_t init = peak + width*(views[0].rows*views[0].columns + views[1].rows*views[1].columns+views[2].rows*views[2].columns+6);
    uint64_t output = width*(views[4].rows*views[4].columns+views[5].rows*views[5].columns);
    uint64_t packed = width*(dim_i*dim_k*dim_j+dim_i*dim_j*dim_a);
    uint64_t lives = scope ? 1 : repetitions;
    require(!active && deletes == lives && total.data_allocations == 6*lives);
    require(total.metadata_allocations == 2*lives);
    require(total.peak_bytes == peak && total.copied_bytes == packed*repetitions);
    require(total.written_bytes == init*lives+(packed+output)*repetitions);
    require(timed.data_allocations == (scope ? 0 : 6*repetitions) && timed.copied_bytes == packed*repetitions);
    require(timed.data_frees == (scope ? 0 : 6*repetitions));
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
           "\"selected_pack_calls_timed\":%llu,\"blas_calls_timed\":%llu,\"process_maxrss_kib\":%ld,\"observed\":\"%016llx\"}\n",
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
    ok(vstorage_pack3(a,0,views[0],3,views[3],dim_i,dim_k,dim_j));
    ok(vgemm_execute(a,3,views[3],0,1,views[1],0,4,views[4],VGEMM_OVERWRITE,NULL));
    ok(vstorage_regroup3(a,4,views[4],3,views[6],dim_i,dim_j,dim_a,48,42));
    ok(vgemm_execute(a,3,views[6],0,2,views[2],0,5,views[5],VGEMM_OVERWRITE,NULL));
}
static int output_differs(VStorageArena *a) {
    VStorageDense output; ok(vstorage_prepare_dense(a,5,views[5],&output));
    for (uint64_t c = 0; c < output.columns; ++c)
        for (uint64_t r = 0; r < output.rows; ++r) {
            Z want = product(r,c);
            const double *got = output.data+(r+output.leading*c)*(scalar+1);
            long double tol = 64*DBL_EPSILON*(dim_k+1)*(dim_j+1)*fmaxl(1,fabsl(want.r));
            if (fabsl((long double)got[0]-want.r) > tol) return 1;
        }
    return 0;
}
/* Mutate each regroup independently to a logical flat copy. Padding remains
 * intact. Both the buffer oracle and final product must detect each mutation. */
static void flat_copy_mutation(VStorageArena *a, unsigned stage) {
    native_operation(a);
    VStorageDense input,output;
    ok(vstorage_prepare_dense(a,stage ? 4 : 0,views[stage ? 4 : 0],&input));
    ok(vstorage_prepare_dense(a,3,views[stage ? 6 : 3],&output));
    uint64_t width = scalar ? 16 : 8;
    for (uint64_t n = 0; n < input.rows*input.columns; ++n)
        memcpy((char *)output.data+(n%output.rows+output.leading*(n/output.rows))*width,
               (const char *)input.data+(n%input.rows+input.leading*(n/input.rows))*width,width);
    if (!stage) {
        ok(vgemm_execute(a,3,views[3],0,1,views[1],0,4,views[4],VGEMM_OVERWRITE,NULL));
        ok(vstorage_regroup3(a,4,views[4],3,views[6],dim_i,dim_j,dim_a,48,42));
    }
    ok(vgemm_execute(a,3,views[6],0,2,views[2],0,5,views[5],VGEMM_OVERWRITE,NULL));
    require(!verify(a,1) && output_differs(a));
    native_operation(a); require(verify(a,1));
    fprintf(stderr,"flat-copy stage %u rejected by buffer and final output oracles\n",stage+1);
}
int main(void) {
    require(vgemm_backend_check() == VS_OK);
    fprintf(stderr,"backend=%s; parallel=%d; threads=%d\n",vgemm_configuration(),openblas_get_parallel(),openblas_get_num_threads());
    VStorageArena *a = c_setup(); native_operation(a); require(verify(a,1));
    uint64_t native_hash = checksum;
    flat_copy_mutation(a,0); flat_copy_mutation(a,1); require(checksum == native_hash);
    for (unsigned id = 0; id < 6; ++id) {
        double *cell = &a->buffers[id].data[views[id].offset/8];
        double old = *cell; *cell = old+1; require(!verify(a,1)); *cell = old;
        if (views[id].offset) {
            old = a->buffers[id].data[0]; a->buffers[id].data[0] = 0;
            require(!verify(a,1)); a->buffers[id].data[0] = old;
        }
    }
    VStorageStats saved = vstorage_stats(a);
    require(vstorage_pack3(a,0,views[0],3,views[3],dim_i,dim_k+1,dim_j) != VS_OK);
    require(vstorage_regroup3(a,4,views[4],3,views[6],dim_i,dim_j,dim_a,0,42) != VS_OK);
    require(vstorage_regroup3(a,4,views[4],4,views[4],dim_i,dim_j,dim_a,48,48) == VS_ALIAS);
    require(vgemm_execute(a,3,views[6],0,2,views[2],0,3,views[5],VGEMM_OVERWRITE,NULL) != VS_OK);
    require(vstorage_stats(a).written_bytes == saved.written_bytes &&
            vstorage_stats(a).copied_bytes == saved.copied_bytes && verify(a,1));
    c_cleanup(a);
    a = c_setup(); c_operation(a); require(verify(a,1) && checksum == native_hash); c_cleanup(a);
    for (unsigned mode = 0; mode < 6; ++mode) {
        bench_c_run(mode,7,1); bench_report();
        a = mode ? c_setup() : NULL; bench_begin(mode,7,1);
        for (unsigned r = 0; r < 7; ++r) {
            if (!mode) a = c_setup();
            native_operation(a);
            if (!mode) c_cleanup(a);
        }
        bench_stop(); if (mode) { bench_verify(a,7); c_cleanup(a); } bench_report();
    }
    fputs("native/C tree coordinate, scratch overlay, padding, cost, corruption and preflight checks passed\n",stderr);
    return 0;
}
#endif
