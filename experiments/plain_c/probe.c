/* Standalone competent-C comparator. No Vastitas runtime, arena or Lean linkage.
 * BENCH_COSTS enables a separate, untimed logical-cost/failure diagnostic build.
 * The timing build contains neither these counters nor per-call preflights. */
#define _POSIX_C_SOURCE 200809L
#ifdef __APPLE__
#define _DARWIN_C_SOURCE 1
#endif
#include <cblas.h>
#include <errno.h>
#include <float.h>
#include <inttypes.h>
#include <limits.h>
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/resource.h>
#include <time.h>

#ifndef BENCH_PROFILE
#error Select a benchmark profile explicitly
#endif
#if BENCH_PROFILE == 0
#define BUFFERS 3
#define INPUTS 2
#define SCOPES 3
#elif BENCH_PROFILE == 1
#define BUFFERS 4
#define INPUTS 2
#define SCOPES 4
#elif BENCH_PROFILE == 2
#define BUFFERS 6
#define INPUTS 3
#define SCOPES 6
#else
#error Unsupported benchmark profile
#endif

typedef struct { uint64_t offset, rows, columns, leading; unsigned transposed; } PlainLayout;
#include "case.h"

static void require(int condition) {
    if (!condition) { fputs("plain-C benchmark contract failure\n", stderr); exit(2); }
}
static uint64_t word(double value) { uint64_t result; memcpy(&result,&value,8); return result; }
static uint64_t width(void) { return (scalar+1)*8; }
static uint64_t now_ns(void) {
    struct timespec t;
#if defined(__APPLE__) || defined(CLOCK_MONOTONIC_RAW)
    require(clock_gettime(CLOCK_MONOTONIC_RAW,&t) == 0);
#else
    require(clock_gettime(CLOCK_MONOTONIC,&t) == 0);
#endif
    return (uint64_t)t.tv_sec*UINT64_C(1000000000)+(uint64_t)t.tv_nsec;
}
static uint64_t mul(uint64_t a, uint64_t b) { require(!a || b <= UINT64_MAX/a); return a*b; }
static uint64_t add(uint64_t a, uint64_t b) { require(b <= UINT64_MAX-a); return a+b; }

#include "reference.h"

typedef struct { double *data[BUFFERS]; } Buffers;
static uint64_t checksum;
static volatile uint64_t observed;
#ifdef BENCH_COSTS
typedef struct { uint64_t allocations, frees, live, peak, written, copied; } Costs;
static Costs costs, before, timed;
static uint64_t allocation_attempts, fail_allocation;
#define ACCOUNT(expression) ((void)(expression))
#else
#define ACCOUNT(expression) ((void)0)
#endif

static void validate_gemm(unsigned ai, unsigned bi, unsigned ci) {
    require(views[ai].columns == views[bi].rows && views[ai].rows == views[ci].rows &&
            views[bi].columns == views[ci].columns);
}
/* Fixture, LP64 and backend checks happen once before any measurement. The
 * admitted experiment has fixed nonempty N/N layouts and separate allocations. */
static void validate_fixture(void) {
    require(scalar <= 1 && sizeof(double) == 8 && sizeof(blasint) == 4);
    for (unsigned id=0; id<BUFFERS; ++id)
        require(elements[id] > 0 && elements[id] <= SIZE_MAX/width());
    for (unsigned v=0; v<sizeof(views)/sizeof(views[0]); ++v) {
        PlainLayout layout=views[v];
        unsigned id=v;
#if BENCH_PROFILE == 2
        if (v == 6) id=3;
#endif
        require(layout.rows > 0 && layout.columns > 0 && layout.leading >= layout.rows &&
                !layout.transposed && layout.offset%width() == 0 &&
                layout.rows <= INT_MAX && layout.columns <= INT_MAX && layout.leading <= INT_MAX);
        uint64_t end=add(layout.offset,mul(add(mul(layout.columns-1,layout.leading),layout.rows),width()));
        require(end <= mul(elements[id],width()));
    }
    for (unsigned id=0; id<INPUTS; ++id)
        for (unsigned p=0; p<2; ++p)
            require(patches[id][p].row < views[id].rows && patches[id][p].col < views[id].columns);
#if BENCH_PROFILE == 0
    require(accumulate <= 1);
    validate_gemm(0,1,2);
#else
    require(dim_i > 0 && dim_j > 0 && dim_k > 0 && views[0].rows == dim_i &&
            views[0].columns == mul(dim_k,dim_j));
#if BENCH_PROFILE == 1
    require(views[2].rows == mul(dim_i,dim_j) && views[2].columns == dim_k);
    validate_gemm(2,1,3);
#else
    require(dim_a > 0 && views[3].rows == mul(dim_i,dim_j) && views[3].columns == dim_k &&
            views[6].rows == mul(dim_i,dim_a) && views[6].columns == dim_j);
    validate_gemm(3,1,4); validate_gemm(6,2,5);
    for (unsigned p=0; p<3; ++p)
        require(expected[p].row < views[5].rows && expected[p].col < views[5].columns);
#endif
#endif
    const char *configuration=openblas_get_config();
    require(configuration && strncmp(configuration,"OpenBLAS 0.3.34 ",16) == 0 &&
            !strstr(configuration,"USE64BITINT") && !strstr(configuration,"USE_OPENMP") &&
            openblas_get_parallel() == 0 && openblas_get_num_threads() == 1);
    fprintf(stderr,"backend=%s; parallel=0; threads=1; comparator=plain_c\n",configuration);
}

static double *at(Buffers *b, unsigned id, unsigned view, uint64_t row, uint64_t col) {
    return b->data[id]+views[view].offset/8+(row+views[view].leading*col)*(scalar+1);
}
static void store(double *destination, const double value[2]) {
    destination[0]=value[0]; if (scalar) destination[1]=value[1];
}
static int verify_buffers(const Buffers *b, uint64_t reps) {
    const double *data[BUFFERS];
    for (unsigned id=0; id<BUFFERS; ++id) data[id]=b->data[id];
    return verify_data(data,reps,&checksum);
}
static void release_buffers(Buffers *b) {
    for (unsigned id=BUFFERS; id>0; --id) if (b->data[id-1]) {
        free(b->data[id-1]); b->data[id-1]=NULL;
        ACCOUNT(++costs.frees); ACCOUNT(costs.live-=elements[id-1]*width());
    }
}
static int setup(Buffers *b) {
    *b=(Buffers){0};
    for (unsigned id=0; id<BUFFERS; ++id) {
        void *allocation=NULL;
#ifdef BENCH_COSTS
        ++allocation_attempts;
        int failed=fail_allocation && allocation_attempts == fail_allocation;
#else
        int failed=0;
#endif
        if (failed || posix_memalign(&allocation,64,(size_t)(elements[id]*width())) != 0) {
            release_buffers(b); return 0;
        }
        b->data[id]=allocation;
        ACCOUNT(++costs.allocations); ACCOUNT(costs.live+=elements[id]*width());
        ACCOUNT(costs.peak=costs.peak > costs.live ? costs.peak : costs.live);
        for (uint64_t n=0; n<elements[id]; ++n) store(b->data[id]+n*(scalar+1),sentinel);
        ACCOUNT(costs.written+=elements[id]*width());
        int initialize=id < INPUTS;
#if BENCH_PROFILE == 0
        initialize=initialize || accumulate;
#endif
        if (initialize) {
            for (uint64_t col=0; col<views[id].columns; ++col)
                for (uint64_t row=0; row<views[id].rows; ++row) store(at(b,id,id,row,col),values[id]);
            ACCOUNT(costs.written+=views[id].rows*views[id].columns*width());
            if (id < INPUTS) for (unsigned p=0; p<2; ++p) {
                const Patch *v=&patches[id][p];
                store(at(b,id,id,v->row,v->col),v->value); ACCOUNT(costs.written+=width());
            }
        }
    }
    return 1;
}
static void gemm(Buffers *b, unsigned aid, unsigned av, unsigned bid, unsigned cid) {
    const PlainLayout a=views[av], right=views[bid], c=views[cid];
    if (!scalar)
        cblas_dgemm(CblasColMajor,CblasNoTrans,CblasNoTrans,(blasint)c.rows,(blasint)c.columns,
                    (blasint)a.columns,alpha[0],at(b,aid,av,0,0),(blasint)a.leading,
                    at(b,bid,bid,0,0),(blasint)right.leading,beta[0],at(b,cid,cid,0,0),(blasint)c.leading);
    else
        cblas_zgemm(CblasColMajor,CblasNoTrans,CblasNoTrans,(blasint)c.rows,(blasint)c.columns,
                    (blasint)a.columns,alpha,at(b,aid,av,0,0),(blasint)a.leading,
                    at(b,bid,bid,0,0),(blasint)right.leading,beta,at(b,cid,cid,0,0),(blasint)c.leading);
    ACCOUNT(costs.written+=c.rows*c.columns*width());
}
#if BENCH_PROFILE != 0
static void pack(Buffers *b) {
    const unsigned output=BENCH_PROFILE == 1 ? 2 : 3;
    for (uint64_t k=0; k<dim_k; ++k)
        for (uint64_t j=0; j<dim_j; ++j)
            memcpy(at(b,output,output,dim_i*j,k),at(b,0,0,0,k+dim_k*j),(size_t)(dim_i*width()));
    ACCOUNT(costs.written+=dim_i*dim_j*dim_k*width());
    ACCOUNT(costs.copied+=dim_i*dim_j*dim_k*width());
}
#endif
#if BENCH_PROFILE == 2
static void regroup(Buffers *b) {
    for (uint64_t a=0; a<dim_a; ++a)
        for (uint64_t j=0; j<dim_j; ++j)
            memcpy(at(b,3,6,dim_i*a,j),at(b,4,4,dim_i*j,a),(size_t)(dim_i*width()));
    ACCOUNT(costs.written+=dim_i*dim_j*dim_a*width());
    ACCOUNT(costs.copied+=dim_i*dim_j*dim_a*width());
}
#endif
static void operation(Buffers *b) {
#if BENCH_PROFILE == 0
    gemm(b,0,0,1,2);
#elif BENCH_PROFILE == 1
    pack(b); gemm(b,2,2,1,3);
#else
    pack(b); gemm(b,3,3,1,4); regroup(b); gemm(b,3,6,2,5);
#endif
}
/* Diagnostic projections execute the whole schedule and time exactly one
 * operation. Primary lifecycle/reuse loops do not call this instrumented path. */
static uint64_t projected_operation(Buffers *b, unsigned selected) {
    uint64_t start=0, elapsed=0;
#define PROJECT(index, expression) do { if (selected == (index)) start=now_ns(); \
    expression; if (selected == (index)) elapsed=now_ns()-start; } while (0)
#if BENCH_PROFILE == 0
    PROJECT(2,gemm(b,0,0,1,2));
#elif BENCH_PROFILE == 1
    PROJECT(2,pack(b)); PROJECT(3,gemm(b,2,2,1,3));
#else
    PROJECT(2,pack(b)); PROJECT(4,gemm(b,3,3,1,4));
    PROJECT(3,regroup(b)); PROJECT(5,gemm(b,3,6,2,5));
#endif
#undef PROJECT
    return elapsed;
}
static void cleanup(Buffers *b, int checking) {
#if BENCH_PROFILE == 2
    /* These three observations also occur in the actual emitted lifecycle. */
    for (unsigned p=0; p<3; ++p) {
        const double *value=at(b,5,5,expected[p].row,expected[p].col);
        for (unsigned part=0; part<=scalar; ++part)
            require(word(value[part]) == word(expected[p].value[part]));
    }
#endif
    if (checking) require(verify_buffers(b,1));
    observed^=word(*at(b,BUFFERS-1,BUFFERS-1,0,0));
    release_buffers(b);
}
static int allocation_failure(void) {
#ifdef BENCH_COSTS
    require(costs.live == 0 && costs.allocations == costs.frees);
    printf("{\"failure\":\"allocation\",\"allocated\":%" PRIu64 ",\"freed\":%" PRIu64
           ",\"live_bytes\":0}\n",costs.allocations,costs.frees);
#endif
    fputs("plain-C allocation failed; allocated buffers released\n",stderr);
    return 3;
}
static int run(unsigned scope, uint64_t reps, int checking) {
    Buffers b={0};
    checksum=0; observed=0;
#ifdef BENCH_COSTS
    costs=(Costs){0}; allocation_attempts=0;
#endif
    if (scope && !setup(&b)) return allocation_failure();
#ifdef BENCH_COSTS
    before=costs;
#endif
    uint64_t elapsed, projection=0, start=now_ns();
    if (!scope) {
        for (uint64_t n=0; n<reps; ++n) {
            if (!setup(&b)) return allocation_failure();
            operation(&b); cleanup(&b,checking);
        }
    } else if (scope == 1) {
        for (uint64_t n=0; n<reps; ++n) operation(&b);
    } else {
        for (uint64_t n=0; n<reps; ++n) projection+=projected_operation(&b,scope);
    }
    elapsed=now_ns()-start;
    if (scope > 1) elapsed=projection;
#ifdef BENCH_COSTS
    timed=(Costs){.allocations=costs.allocations-before.allocations,.frees=costs.frees-before.frees,
                  .written=costs.written-before.written,.copied=costs.copied-before.copied};
#endif
    if (scope) { require(verify_buffers(&b,reps)); cleanup(&b,0); }
    struct rusage usage; require(getrusage(RUSAGE_SELF,&usage) == 0);
    long rss=usage.ru_maxrss;
#ifdef __APPLE__
    rss/=1024;
#endif
    printf("{\"elapsed_ns\":%" PRIu64 ",\"repetitions\":%" PRIu64 ",\"checksum\":\"%016" PRIx64
           "\",\"observed\":\"%016" PRIx64 "\",\"process_maxrss_kib\":%ld",
           elapsed,reps,checksum,(uint64_t)observed,rss);
#ifdef BENCH_COSTS
    require(costs.live == 0 && costs.allocations == costs.frees);
    printf(",\"data_allocations\":%" PRIu64 ",\"data_frees\":%" PRIu64 ",\"live_bytes_after\":0,"
           "\"peak_data_bytes\":%" PRIu64 ",\"written_bytes\":%" PRIu64 ",\"copied_bytes\":%" PRIu64
           ",\"metadata_allocations\":0,\"peak_metadata_bytes\":0,\"timed_data_allocations\":%" PRIu64
           ",\"timed_data_frees\":%" PRIu64 ",\"timed_written_bytes\":%" PRIu64
           ",\"timed_copied_bytes\":%" PRIu64 ",\"timed_metadata_allocations\":0",
           costs.allocations,costs.frees,costs.peak,costs.written,costs.copied,
           timed.allocations,timed.frees,timed.written,timed.copied);
    fputs(",\"cost_instrumentation\":true",stdout);
#else
    fputs(",\"cost_instrumentation\":false",stdout);
#endif
    fputs("}\n",stdout);
    return 0;
}
static void self_test(void) {
    Buffers b={0}; require(setup(&b)); operation(&b); require(verify_buffers(&b,1));
    for (unsigned id=0; id<BUFFERS; ++id) {
        for (unsigned part=0; part<=scalar; ++part) {
            double *cell=at(&b,id,id,0,0)+part;
            double old=*cell; *cell=old+1; require(!verify_buffers(&b,1)); *cell=old;
        }
        if (views[id].offset) {
            double old=b.data[id][0]; b.data[id][0]=old+1;
            require(!verify_buffers(&b,1)); b.data[id][0]=old;
        }
    }
    require(verify_buffers(&b,1)); cleanup(&b,0);
    for (unsigned scope=0; scope<SCOPES; ++scope) require(run(scope,7,1) == 0);
    fputs("plain-C output, input, padding, component and cleanup checks passed\n",stderr);
}
static uint64_t number(const char *s) {
    require(*s >= '0' && *s <= '9');
    char *end; errno=0; unsigned long long n=strtoull(s,&end,10);
    require(!errno && !*end && n <= UINT64_MAX); return (uint64_t)n;
}
int main(int argc, char **argv) {
    validate_fixture();
    if (argc == 2 && !strcmp(argv[1],"self-test")) { self_test(); return 0; }
    require(argc == 4 || argc == 5);
    uint64_t scope=number(argv[1]), reps=number(argv[2]), checking=number(argv[3]);
    require(scope < SCOPES && reps > 0 && reps <= 1000000 && checking <= 1);
    /* Same complete untimed backend warmup as the generated/arena-C arms. */
    Buffers warm={0}; if (!setup(&warm)) return allocation_failure();
    operation(&warm); require(verify_buffers(&warm,1)); cleanup(&warm,0);
#ifdef BENCH_COSTS
    if (argc == 5) { fail_allocation=number(argv[4]); require(fail_allocation <= BUFFERS); }
#else
    require(argc == 4);
#endif
    return run((unsigned)scope,reps,(int)checking);
}
