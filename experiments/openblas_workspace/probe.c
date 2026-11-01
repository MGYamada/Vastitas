/* Actual native adapter, two separately linked stock/diagnostic executables.
 * Integral input/reference arithmetic is exact at the bounded fixture sizes.
 * This is neither a source-authority test nor an operation timing benchmark. */
#include "gemm.h"
#include <cblas.h>
#include <assert.h>
#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#ifdef VOBS_DIAGNOSTIC
#include "observer.h"
#else
static void vobs_mark(unsigned phase) { (void)phase; }
static void vobs_dump(void) {}
#endif
extern void *blas_memory_alloc(int);
extern void blas_memory_free(void *);
extern void *blas_memory_alloc_nolock(int);
extern void blas_memory_free_nolock(void *);
extern void gotoblas_quit(void);

static void ok(VStorageStatus status) { assert(status == VS_OK); }
static uint64_t bits(double x) { uint64_t u; memcpy(&u, &x, 8); return u; }
typedef struct { int64_t r, i; } Z;
static Z input(unsigned which, unsigned r, unsigned c, unsigned scalar) {
    return (Z){(int)((r + 2*c + which)%5)-2,
               scalar ? (int)((2*r + c + which)%3)-1 : 0};
}
static Z product(unsigned r, unsigned c, unsigned n, unsigned scalar, unsigned transform) {
    Z sum = {0, 0};
    for (unsigned k = 0; k < n; ++k) {
        Z a = transform ? input(0, k, r, scalar) : input(0, r, k, scalar);
        Z b = input(1, k, c, scalar);
        if (transform == 2) a.i = -a.i;
        sum.r += a.r*b.r - a.i*b.i;
        sum.i += a.r*b.i + a.i*b.r;
    }
    return sum;
}
static uint64_t verify(VStorageArena *a, unsigned n, unsigned scalar,
                       unsigned transform, unsigned multiplier, uint64_t elements) {
    uint64_t hash = UINT64_C(1469598103934665603), width = UINT64_C(8)*(scalar+1);
    for (unsigned id = 0; id < 3; ++id) {
        VStorageDense view;
        ok(vstorage_prepare_dense(a, id, (VStorageLayout){0,elements,1,elements,0}, &view));
        for (uint64_t index = 0; index < elements; ++index) {
            Z want = {-7, scalar ? -7 : 0};
            uint64_t r = index ? (index-1)%(n+1) : n;
            uint64_t c = index ? (index-1)/(n+1) : n;
            if (r < n && c < n) {
                want = id < 2 ? input(id, (unsigned)r, (unsigned)c, scalar) :
                    product((unsigned)r, (unsigned)c, n, scalar, transform);
                if (id == 2) { want.r *= multiplier; want.i *= multiplier; }
            }
            for (unsigned part = 0; part <= scalar; ++part) {
                double got = view.data[index*(scalar+1)+part];
                assert(got == (double)(part ? want.i : want.r));
                /* Exact integer result comparison treats either zero sign as
                 * zero. Keep input/padding words unchanged in the hash. */
                if (id == 2 && r < n && c < n && got == 0.0) got = 0.0;
                hash = (hash ^ bits(got))*UINT64_C(1099511628211);
            }
        }
        assert(view.bytes == elements*width);
    }
    return hash;
}
int main(int argc, char **argv) {
    assert(vgemm_backend_check() == VS_OK && openblas_get_num_threads() == 1);
    vobs_mark(10);
    if (argc == 2 && strcmp(argv[1], "calibration") == 0) {
        vobs_mark(11); void *a = blas_memory_alloc(0); assert(a);
        vobs_mark(12); void *b = blas_memory_alloc(0); assert(b && a != b);
        vobs_mark(13); blas_memory_free(a);
        vobs_mark(14); void *c = blas_memory_alloc(0); assert(c == a);
        vobs_mark(15); blas_memory_free(b); blas_memory_free(c);
        vobs_mark(16); void *d = blas_memory_alloc_nolock(0); assert(d);
        vobs_mark(17); blas_memory_free_nolock(d);
        printf("{\"kind\":\"calibration\",\"configuration\":\"%s\","
               "\"distinct\":true,\"reuse\":true}\n", vgemm_configuration());
    } else {
        assert(argc == 4);
        unsigned scalar = (unsigned)strtoul(argv[1], NULL, 10);
        unsigned n = (unsigned)strtoul(argv[2], NULL, 10);
        unsigned transform = (unsigned)strtoul(argv[3], NULL, 10);
        assert(scalar <= 1 && (n == 0 || n == 2 || n == 32 || n == 256) && transform <= 2);
        uint64_t width = UINT64_C(8)*(scalar+1), elements = ((uint64_t)n+1)*n+2;
        VStorageArena *a = vstorage_new(3*elements*width); assert(a);
        VStorageLayout v = {width,n,n,n+1,0}, av = v;
        av.transposed = transform != 0;
        for (unsigned id = 0; id < 3; ++id) {
            ok(vstorage_allocate(a, id, scalar, elements));
            ok(vstorage_fill(a, id, (VStorageLayout){0,elements,1,elements,0},
                            scalar, bits(-7), bits(-7)));
            if (id < 2) for (unsigned c = 0; c < n; ++c) for (unsigned r = 0; r < n; ++r) {
                Z z = input(id,r,c,scalar);
                ok(vstorage_store(a,id,v,r,c,scalar,bits((double)z.r),bits((double)z.i)));
            }
        }
        uint64_t checksums[3], calls = 0;
        for (unsigned iteration = 0; iteration < 3; ++iteration) {
            vobs_mark(11+iteration);
            VGemmReport report;
            ok(vgemm_execute(a,0,av,transform == 2,1,v,0,2,v,
                             iteration == 2 ? VGEMM_ACCUMULATE : VGEMM_OVERWRITE, &report));
            assert(report.kernel_calls == (n != 0));
            assert(report.written_bytes == (uint64_t)n*n*width);
            calls += report.kernel_calls;
            checksums[iteration] = verify(a,n,scalar,transform,iteration == 2 ? 2 : 1,elements);
        }
        vobs_mark(14);
        VGemmReport ignored;
        VStorageStatus invalid = vgemm_execute(a,0,av,transform == 2,1,v,0,0,v,
                                              n ? VGEMM_OVERWRITE : (VGemmMode)99, &ignored);
        assert(invalid == (n ? VS_ALIAS : VS_OPERATION));
        assert(verify(a,n,scalar,transform,2,elements) == checksums[2]);
        for (unsigned id = 0; id < 3; ++id) ok(vstorage_drop(a,id));
        VStorageStats stats = vstorage_stats(a);
        assert(stats.live_bytes == 0 && stats.data_allocations == 3 && stats.data_frees == 3);
        vstorage_delete(a);
        printf("{\"kind\":\"gemm\",\"configuration\":\"%s\",\"scalar\":%u,\"n\":%u,"
               "\"transform\":%u,\"kernel_calls\":%" PRIu64 ",\"checksums\":[\"%016" PRIx64
               "\",\"%016" PRIx64 "\",\"%016" PRIx64 "\"],\"arena_data_bytes\":%" PRIu64 "}\n",
               vgemm_configuration(),scalar,n,transform,calls,checksums[0],checksums[1],checksums[2],stats.peak_bytes);
    }
    vobs_mark(18);
    /* Quit, not shutdown alone: this also disables the automatic destructor,
     * avoiding a second shutdown of the pinned non-TLS release table. */
    gotoblas_quit();
    vobs_mark(19);
    vobs_dump();
    return 0;
}
