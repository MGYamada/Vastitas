/* Included at the end of private memory.c, after the workspace observer.
 * Fixed arrays, no allocation or clocks. Observation failures are fatal even
 * when upstream is compiled with NDEBUG. Reporting follows the final marker. */
#include "vpack.h"
#include <string.h>

typedef struct {
    const char *kernel;
    uintptr_t source, destination;
    size_t before, after, m, n, lda, route;
    unsigned role, components;
} VPackCall;
typedef struct {
    const char *path;
    uintptr_t a, b, c;
    size_t before, after, m, n, k, lda, ldb, ldc;
    unsigned components, ta, tb;
} VPackRoute;
static VPackCall vp_calls[16384];
static VPackRoute vp_routes[256];
static size_t vp_count, vp_route_count;
static int vp_active, vp_route_active, vp_finished;

static void vp_check(int yes) { if (!yes) vobs_fail(); }
void vpack_route(const char *path, unsigned components, long m, long n, long k,
                 unsigned ta, unsigned tb, const void *a, long lda,
                 const void *b, long ldb, const void *c, long ldc) {
    size_t cursor = vobs_cursor(); /* also enforces the one-thread boundary */
    vp_check(!vp_finished && !vp_route_active && !vp_active && vp_route_count < 256);
    vp_check((components == 1 || components == 2) && m >= 0 && n >= 0 && k >= 0 &&
             lda >= 0 && ldb >= 0 && ldc >= 0 && ta <= 3 && tb <= 3);
    vp_routes[vp_route_count] = (VPackRoute){path, (uintptr_t)a, (uintptr_t)b, (uintptr_t)c,
        cursor, 0, (size_t)m, (size_t)n, (size_t)k, (size_t)lda, (size_t)ldb, (size_t)ldc,
        components, ta, tb};
    vp_route_active = 1;
}
void vpack_end(void) {
    size_t cursor = vobs_cursor();
    vp_check(!vp_finished && vp_route_active && !vp_active);
    vp_routes[vp_route_count++].after = cursor;
    vp_route_active = 0;
}
void vpack_before(const char *kernel, unsigned role, unsigned components,
                  long m, long n, const void *source, long lda, void *destination) {
    size_t cursor = vobs_cursor();
    vp_check(!vp_finished && !vp_active && vp_count < 16384 && vp_route_active);
    vp_check(strcmp(vp_routes[vp_route_count].path, "packed") == 0 && role <= 1 &&
             (components == 1 || components == 2) && m > 0 && n > 0 && lda > 0 && source && destination);
    vp_check((size_t)m <= SIZE_MAX / (size_t)n / components / sizeof(double));
    vp_active = 1;
    vp_calls[vp_count] = (VPackCall){kernel, (uintptr_t)source, (uintptr_t)destination,
        cursor, 0, (size_t)m, (size_t)n, (size_t)lda, vp_route_count, role, components};
}
void vpack_after(void) {
    size_t cursor = vobs_cursor();
    vp_check(vp_active && !vp_finished && vp_route_active);
    vp_calls[vp_count++].after = cursor;
    vp_active = 0;
}
void vpack_dump(void) {
    vp_check(!vp_active && !vp_route_active && !vp_finished);
    vp_finished = 1;
    printf("{\"kind\":\"packing\",\"schema\":1,\"observer_static_bytes\":%zu,"
           "\"call_capacity\":16384,\"route_capacity\":256,\"metadata\":{"
           "\"pool_entries\":%d,\"memory_entry_bytes\":%zu,\"memory_array_bytes\":%zu,"
           "\"release_entry_bytes\":%zu,\"release_array_bytes\":%zu,\"declared_bytes\":{",
           sizeof(vp_calls)+sizeof(vp_routes)+sizeof(vp_count)+sizeof(vp_route_count)+
           sizeof(vp_active)+sizeof(vp_route_active)+sizeof(vp_finished), NUM_BUFFERS,
           sizeof(memory[0]),sizeof(memory),sizeof(release_info[0]),sizeof(release_info));
#define VP_META(NAME) printf("\"" #NAME "\":%zu,", sizeof(NAME))
    VP_META(memory); VP_META(release_info); VP_META(newmemory); VP_META(new_release_info);
    VP_META(release_pos); VP_META(alloc_lock); VP_META(base_address);
    VP_META(memory_initialized); VP_META(memory_overflowed); VP_META(hugetlb_allocated);
#if defined(OS_LINUX) && !defined(NO_WARMUP)
    VP_META(hot_alloc); VP_META(init_lock);
#endif
    printf("\"gotoblas_initialized\":%zu}},\"routes\":[", sizeof(gotoblas_initialized));
#undef VP_META
    for (size_t i=0; i<vp_route_count; ++i) {
        const VPackRoute *r=&vp_routes[i];
        printf("%s{\"path\":\"%s\",\"components\":%u,\"m\":%zu,\"n\":%zu,\"k\":%zu,"
               "\"ta\":%u,\"tb\":%u,\"a\":\"0x%" PRIxPTR "\",\"b\":\"0x%" PRIxPTR "\","
               "\"c\":\"0x%" PRIxPTR "\",\"lda\":%zu,\"ldb\":%zu,\"ldc\":%zu,\"before\":%zu,\"after\":%zu}",
               i ? "," : "",r->path,r->components,r->m,r->n,r->k,r->ta,r->tb,r->a,r->b,r->c,
               r->lda,r->ldb,r->ldc,r->before,r->after);
    }
    printf("],\"calls\":[");
    for (size_t i=0; i<vp_count; ++i) {
        const VPackCall *c=&vp_calls[i];
        printf("%s{\"kernel\":\"%s\",\"role\":%u,\"components\":%u,\"m\":%zu,\"n\":%zu,"
               "\"lda\":%zu,\"source\":\"0x%" PRIxPTR "\",\"destination\":\"0x%" PRIxPTR "\","
               "\"before\":%zu,\"after\":%zu,\"route\":%zu}", i ? "," : "",c->kernel,
               c->role,c->components,c->m,c->n,c->lda,c->source,c->destination,c->before,c->after,c->route);
    }
    puts("]}");
}
