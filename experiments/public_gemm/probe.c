/* Experiment only. This translation unit replaces storage.c ONLY in a private
 * runtime copy. It exposes fixtures/counters without changing production APIs. */
#define _POSIX_C_SOURCE 200809L
#define vstorage_new storage_new_impl
#define vstorage_drop storage_drop_impl
#define vstorage_delete storage_delete_impl
#include "../../lean-kernel/native/storage.c"
#undef vstorage_new
#undef vstorage_drop
#undef vstorage_delete
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
static uint64_t start_ns, elapsed_ns, kernel_ns, kernel_calls, repetitions, deletes;
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
    require(clock_gettime(CLOCK_MONOTONIC, &t) == 0);
    return (uint64_t)t.tv_sec * UINT64_C(1000000000) + (uint64_t)t.tv_nsec;
}
static uint64_t word(double x) { uint64_t u; memcpy(&u, &x, 8); return u; }
static uint64_t maximum(uint64_t a, uint64_t b) { return a > b ? a : b; }

void bench_dgemm(enum CBLAS_ORDER o, enum CBLAS_TRANSPOSE ta, enum CBLAS_TRANSPOSE tb,
    blasint m, blasint n, blasint k, double a, const double *x, blasint lx,
    const double *y, blasint ly, double b, double *z, blasint lz) {
    uint64_t t = scope == 2 ? now_ns() : 0;
    cblas_dgemm(o, ta, tb, m, n, k, a, x, lx, y, ly, b, z, lz);
    if (scope == 2) { kernel_ns += now_ns() - t; ++kernel_calls; }
}
void bench_zgemm(enum CBLAS_ORDER o, enum CBLAS_TRANSPOSE ta, enum CBLAS_TRANSPOSE tb,
    blasint m, blasint n, blasint k, const void *a, const void *x, blasint lx,
    const void *y, blasint ly, const void *b, void *z, blasint lz) {
    uint64_t t = scope == 2 ? now_ns() : 0;
    cblas_zgemm(o, ta, tb, m, n, k, a, x, lx, y, ly, b, z, lz);
    if (scope == 2) { kernel_ns += now_ns() - t; ++kernel_calls; }
}

typedef struct { long double r, i; } Z;
static Z z(const double *v) { return (Z){v[0], v[1]}; }
static Z plus(Z a, Z b) { return (Z){a.r+b.r, a.i+b.i}; }
static Z minus(Z a, Z b) { return (Z){a.r-b.r, a.i-b.i}; }
static Z times(Z a, Z b) { return (Z){a.r*b.r-a.i*b.i, a.r*b.i+a.i*b.r}; }
static Z divide(Z a, Z b) {
    long double d = b.r*b.r+b.i*b.i;
    return (Z){(a.r*b.r+a.i*b.i)/d, (a.i*b.r-a.r*b.i)/d};
}
static Z power(Z x, uint64_t n) {
    Z result = {1,0};
    for (; n; n >>= 1, x = times(x,x)) if (n & 1) result = times(result,x);
    return result;
}
static Z entry(unsigned id, uint64_t r, uint64_t c) {
    for (unsigned p = 0; p < 2; ++p)
        if (patches[id][p].row == r && patches[id][p].col == c) return z(patches[id][p].value);
    return z(values[id]);
}
/* Independent rank-one + sparse-update identity, not BLAS/index-loop reuse. */
static Z product(uint64_t r, uint64_t c) {
    Z a = z(values[0]), b = z(values[1]);
    Z result = times((Z){views[0].columns,0}, times(a,b));
    for (unsigned p = 0; p < 2; ++p) {
        const Patch *x = &patches[0][p], *y = &patches[1][p];
        if (x->row == r) result = plus(result, times(minus(z(x->value),a),b));
        if (y->col == c) result = plus(result, times(a,minus(z(y->value),b)));
        for (unsigned q = 0; q < 2; ++q) {
            y = &patches[1][q];
            if (x->row == r && y->col == c && x->col == y->row)
                result = plus(result, times(minus(z(x->value),a),minus(z(y->value),b)));
        }
    }
    return result;
}
static Z expected(uint64_t r, uint64_t c, uint64_t reps) {
    Z ab = times(z(alpha),product(r,c)), one = {1,0};
    if (!accumulate) return ab;
    Z bn = power(z(beta),reps);
    return plus(times(ab,divide(minus(one,bn),minus(one,z(beta)))),times(bn,z(values[2])));
}
static int verify(VStorageArena *a, uint64_t reps) {
    uint64_t hash = UINT64_C(1469598103934665603);
    for (unsigned id = 0; id < 3; ++id) {
        Buffer *buffer = lookup(a,id);
        if (!buffer) return 0;
        uint64_t offset = views[id].offset / (scalar ? 16 : 8);
        for (uint64_t index = 0; index < elements[id]; ++index) {
            uint64_t rel = index >= offset ? index-offset : UINT64_MAX;
            uint64_t r = rel % views[id].leading, c = rel / views[id].leading;
            int logical = index >= offset && r < views[id].rows && c < views[id].columns;
            Z want = !logical ? z(sentinel) : id < 2 ? entry(id,r,c) : expected(r,c,reps);
            for (unsigned part = 0; part <= scalar; ++part) {
                double got = buffer->data[index*(scalar+1)+part];
                long double target = part ? want.i : want.r;
                if (!isfinite(got)) return 0;
                if (!logical || id < 2) {
                    if (word(got) != word((double)target)) return 0;
                } else {
                    long double tol = 32 * DBL_EPSILON * (views[0].columns+1) * fmaxl(1,fabsl(target));
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
    if (id == 2 && lookup(a,id)) {
        if (verify_on_drop) require(verify(a,1));
        observed ^= word(lookup(a,id)->data[views[2].offset/8]);
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

/* Independent direct-CBLAS boundary for this finite nonempty, N/N, literal
 * coefficient profile. Same arena, physical preflights and write accounting;
 * no call to vgemm_execute[_scaled]. Not a second proof of the shared checks. */
static void c_gemm(VStorageArena *arena) {
    ok(vgemm_backend_check());
    VStorageDense a,b,c;
    ok(vstorage_prepare_dense(arena,0,views[0],&a));
    ok(vstorage_prepare_dense(arena,1,views[1],&b));
    ok(vstorage_prepare_dense(arena,2,views[2],&c));
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
    for (unsigned id = 0; id < 3; ++id) {
        ok(vstorage_allocate(arena,id,(uint8_t)scalar,elements[id]));
        VStorageLayout all = {0,elements[id],1,elements[id],0};
        ok(vstorage_fill(arena,id,all,(uint8_t)scalar,word(sentinel[0]),word(sentinel[1])));
        if (id < 2 || accumulate) {
            ok(vstorage_fill(arena,id,views[id],(uint8_t)scalar,word(values[id][0]),word(values[id][1])));
            if (id < 2) for (unsigned p = 0; p < 2; ++p) {
                const Patch *v = &patches[id][p];
                ok(vstorage_store(arena,id,views[id],v->row,v->col,(uint8_t)scalar,word(v->value[0]),word(v->value[1])));
            }
        }
    }
    return arena;
}
static void c_cleanup(VStorageArena *a) {
    ok(vstorage_drop(a,2)); ok(vstorage_drop(a,1)); ok(vstorage_drop(a,0));
    vstorage_close(a); vstorage_delete(a);
}
void bench_begin(uint32_t which, uint64_t reps, uint8_t checking) {
    require(which <= 2 && reps > 0 && reps <= 1000000);
    scope = which; repetitions = reps; verify_on_drop = checking && !which;
    total = (VStorageStats){0}; before = vstorage_stats(active); timed = (VStorageStats){0};
    deletes = 0; kernel_calls = 0; kernel_ns = 0; checksum = 0; observed = 0;
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
            require(kernel_calls == repetitions && kernel_ns > 0);
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
        c_gemm(arena);
        if (!which) c_cleanup(arena);
    }
    bench_stop();
    if (which) { bench_verify(arena,reps); c_cleanup(arena); }
}
void bench_report(void) {
    uint64_t width = scalar ? 16 : 8, peak = 0;
    for (unsigned i = 0; i < 3; ++i) peak += elements[i]*width;
    uint64_t init = peak + width*(views[0].rows*views[0].columns + views[1].rows*views[1].columns+4);
    uint64_t output = width*views[2].rows*views[2].columns;
    if (accumulate) init += output;
    uint64_t lives = scope ? 1 : repetitions;
    require(!active && deletes == lives && total.data_allocations == 3*lives);
    require(total.metadata_allocations == 2*lives);
    require(total.peak_bytes == peak && total.copied_bytes == 0);
    require(total.written_bytes == init*lives+output*repetitions);
    require(timed.data_allocations == (scope ? 0 : 3*repetitions) && timed.copied_bytes == 0);
    require(timed.data_frees == (scope ? 0 : 3*repetitions));
    if (scope) require(timed.metadata_allocations == 0 && timed.written_bytes == output*repetitions);
    struct rusage usage; require(getrusage(RUSAGE_SELF,&usage) == 0);
    printf("{\"elapsed_ns\":%llu,\"repetitions\":%llu,\"checksum\":\"%016llx\","
           "\"data_allocations\":%llu,\"data_frees\":%llu,\"live_bytes_after\":0,"
           "\"peak_data_bytes\":%llu,\"written_bytes\":%llu,\"copied_bytes\":%llu,"
           "\"metadata_allocations\":%llu,\"peak_metadata_bytes\":%llu,"
           "\"timed_data_allocations\":%llu,\"timed_data_frees\":%llu,"
           "\"timed_written_bytes\":%llu,\"timed_copied_bytes\":%llu,\"timed_metadata_allocations\":%llu,"
           "\"blas_calls_timed\":%llu,\"process_maxrss_kib\":%ld,\"observed\":\"%016llx\"}\n",
           (unsigned long long)elapsed_ns,(unsigned long long)repetitions,(unsigned long long)checksum,
           (unsigned long long)total.data_allocations,(unsigned long long)total.data_frees,
           (unsigned long long)total.peak_bytes,(unsigned long long)total.written_bytes,
           (unsigned long long)total.copied_bytes,(unsigned long long)total.metadata_allocations,
           (unsigned long long)total.metadata_bytes,(unsigned long long)timed.data_allocations,
           (unsigned long long)timed.data_frees,(unsigned long long)timed.written_bytes,
           (unsigned long long)timed.copied_bytes,(unsigned long long)timed.metadata_allocations,
           (unsigned long long)kernel_calls,usage.ru_maxrss,(unsigned long long)observed);
}

#ifdef BENCH_STANDALONE
static void native_gemm(VStorageArena *a) {
    VGemmCoefficient x = {VGEMM_LITERAL,(uint8_t)scalar,word(alpha[0]),word(alpha[1]),0,0};
    VGemmCoefficient y = accumulate ? (VGemmCoefficient){VGEMM_LITERAL,(uint8_t)scalar,word(beta[0]),word(beta[1]),0,0} : (VGemmCoefficient){0};
    ok(vgemm_execute_scaled(a,0,views[0],0,1,views[1],0,2,views[2],
                           accumulate ? VGEMM_ACCUMULATE : VGEMM_OVERWRITE,x,y,NULL));
}
int main(void) {
    require(vgemm_backend_check() == VS_OK);
    fprintf(stderr,"backend=%s; parallel=%d; threads=%d\n",vgemm_configuration(),openblas_get_parallel(),openblas_get_num_threads());
    for (uint64_t r = 0; r < views[2].rows; ++r)
        for (uint64_t col = 0; col < views[2].columns; ++col) {
            if (views[0].columns > 32) break;
            Z dense = {0,0};
            for (uint64_t k = 0; k < views[0].columns; ++k)
                dense = plus(dense,times(entry(0,r,k),entry(1,k,col)));
            Z sparse = product(r,col);
            require(dense.r == sparse.r && dense.i == sparse.i);
        }
    VStorageArena *a = c_setup(); native_gemm(a); require(verify(a,1));
    uint64_t native_hash = checksum;
    /* Every oracle channel must reject deliberate corruption. */
    for (unsigned id = 0; id < 3; ++id) {
        double *cell = &a->buffers[id].data[views[id].offset/8];
        double old = *cell; *cell = old+1; require(!verify(a,1)); *cell = old;
    }
    if (views[2].offset) {
        double old = a->buffers[2].data[0]; a->buffers[2].data[0] = 0;
        require(!verify(a,1)); a->buffers[2].data[0] = old;
    }
    /* Aliased output must fail before write. */
    VGemmCoefficient x = {VGEMM_LITERAL,(uint8_t)scalar,word(alpha[0]),word(alpha[1]),0,0};
    VStorageStats saved = vstorage_stats(a);
    require(vgemm_execute_scaled(a,0,views[0],0,1,views[1],0,0,views[2],VGEMM_OVERWRITE,x,(VGemmCoefficient){0},NULL) != VS_OK);
    require(vstorage_stats(a).written_bytes == saved.written_bytes && verify(a,1));
    c_cleanup(a);
    a = c_setup(); c_gemm(a); require(verify(a,1) && checksum == native_hash); c_cleanup(a);
    for (unsigned mode = 0; mode < 3; ++mode) {
        bench_c_run(mode,7,1); bench_report();
        a = mode ? c_setup() : NULL; bench_begin(mode,7,1);
        for (unsigned r = 0; r < 7; ++r) {
            if (!mode) a = c_setup();
            native_gemm(a);
            if (!mode) c_cleanup(a);
        }
        bench_stop(); if (mode) { bench_verify(a,7); c_cleanup(a); } bench_report();
    }
    fputs("native and independent C output/padding/cost/corruption checks passed\n",stderr);
    return 0;
}
#endif
