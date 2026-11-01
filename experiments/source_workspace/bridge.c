/* Private diagnostic only. Bind each actual CBLAS call to its exact backend
 * event interval; no clocks, dynamic observer allocation or invented zeroes. */
#include "bridge.h"
#include <assert.h>
#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#ifndef SOURCE_WORKSPACE_PACKING
#define SOURCE_WORKSPACE_PACKING 0
#endif
#ifdef NDEBUG
#error "The diagnostic bridge requires its guards"
#endif
#if SOURCE_WORKSPACE_DIAGNOSTIC
#include "observer.h"
#if SOURCE_WORKSPACE_PACKING
#include "packing_observer.h"
#endif
#endif
extern void gotoblas_quit(void);

typedef struct {
    unsigned phase, scalar;
    int order, ta, tb, m, n, k, lda, ldb, ldc;
    uint64_t alpha[2], beta[2];
    uintptr_t a, b, c;
    size_t begin, end;
} SourceCall;
static SourceCall calls[256];
static size_t count;
static unsigned phase;
static int active, finished;

static uint64_t bits(double x) { uint64_t word; memcpy(&word,&x,8); return word; }
static size_t cursor(void) {
#if SOURCE_WORKSPACE_DIAGNOSTIC
    return vobs_cursor();
#else
    return 0; /* serialized as null, not as a zero-event observation */
#endif
}
void source_workspace_mark(unsigned next) {
    assert(!finished && !active && next == phase+1 && next <= 4);
    phase = next;
#if SOURCE_WORKSPACE_DIAGNOSTIC
    vobs_mark(10+next);
#endif
}
void source_workspace_begin(unsigned scalar, int order, int ta, int tb,
    int m, int n, int k, int lda, int ldb, int ldc,
    double ar, double ai, double br, double bi, const void *a, const void *b, const void *c) {
    assert(!finished && !active && (phase == 1 || phase == 3));
    assert(count < sizeof(calls)/sizeof(calls[0]) && scalar <= 1);
    assert(m >= 0 && n >= 0 && k >= 0 && lda > 0 && ldb > 0 && ldc > 0);
    SourceCall *call = &calls[count];
    *call = (SourceCall){.phase=phase,.scalar=scalar,.order=order,.ta=ta,.tb=tb,
        .m=m,.n=n,.k=k,.lda=lda,.ldb=ldb,.ldc=ldc,
        .alpha={bits(ar),bits(ai)},.beta={bits(br),bits(bi)},
        .a=(uintptr_t)a,.b=(uintptr_t)b,.c=(uintptr_t)c,.begin=cursor()};
    active = 1;
}
void source_workspace_end(void) {
    assert(active && !finished && count < sizeof(calls)/sizeof(calls[0]));
    calls[count].end = cursor();
    assert(calls[count].begin <= calls[count].end);
    ++count;
    active = 0;
}
void source_workspace_report(void) {
    assert(!finished && !active && phase == 4);
    finished = 1;
#if SOURCE_WORKSPACE_DIAGNOSTIC
    vobs_mark(18);
#endif
    gotoblas_quit();
#if SOURCE_WORKSPACE_DIAGNOSTIC
    vobs_mark(19);
#endif
    printf("{\"kind\":\"source_cblas_calls\",\"schema\":%d,\"backend_events_observed\":%s,"
           "\"observer_static_bytes\":%zu,\"capacity\":256,\"calls\":[",
           SOURCE_WORKSPACE_PACKING ? 2 : 1,
           SOURCE_WORKSPACE_DIAGNOSTIC ? "true" : "false",
           sizeof(calls)+sizeof(count)+sizeof(phase)+sizeof(active)+sizeof(finished));
    for (size_t i = 0; i < count; ++i) {
        SourceCall c = calls[i];
        printf("%s{\"sequence\":%zu,\"phase\":%u,\"scalar\":%u,\"order\":%d,"
               "\"transforms\":[%d,%d],\"shape\":[%d,%d,%d],\"leading\":[%d,%d,%d],"
               "\"alpha\":[\"%016" PRIx64 "\",\"%016" PRIx64 "\"],"
               "\"beta\":[\"%016" PRIx64 "\",\"%016" PRIx64 "\"],",
               i ? "," : "",i,c.phase,c.scalar,c.order,c.ta,c.tb,c.m,c.n,c.k,c.lda,c.ldb,c.ldc,
               c.alpha[0],c.alpha[1],c.beta[0],c.beta[1]);
#if SOURCE_WORKSPACE_PACKING
        printf("\"addresses\":[\"0x%" PRIxPTR "\",\"0x%" PRIxPTR "\",\"0x%" PRIxPTR "\"],",c.a,c.b,c.c);
#endif
#if SOURCE_WORKSPACE_DIAGNOSTIC
        printf("\"begin\":%zu,\"end\":%zu}",c.begin,c.end);
#else
        printf("\"begin\":null,\"end\":null}");
#endif
    }
    puts("]}");
#if SOURCE_WORKSPACE_DIAGNOSTIC
    vobs_dump();
#if SOURCE_WORKSPACE_PACKING
    vpack_dump();
#endif
#endif
}
