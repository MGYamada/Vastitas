/* Private source observer. Preserve startup traffic and atomically close each
 * interval after independently visiting the live heap. No reporting, collection
 * or dynamic observer allocation occurs inside a measured interval. */
#include "heap.h"
#include "lifetime.h"
#include "mimalloc.h"
#include <assert.h>
#include <inttypes.h>
#include <stdio.h>
#include <string.h>

#ifdef NDEBUG
#error "The source lifetime observer requires its guards"
#endif

typedef struct { uint64_t blocks, usable; } Visit;
static VastitasHeapLifetimes before[5], after[5];
static Visit visits[5];
static unsigned next_boundary, inside;

static bool visit(const mi_heap_t *heap, const mi_heap_area_t *area,
                  void *block, size_t size, void *data) {
    (void)heap; (void)area;
    if (block) {
        Visit *v = data;
        ++v->blocks;
        v->usable += size;
    }
    return true;
}

void source_heap_before(unsigned boundary) {
    assert(boundary < 5 && boundary == next_boundary && !inside);
    inside = 1;
    before[boundary] = vastitas_heap_snapshot();
}

void source_heap_after(unsigned boundary) {
    assert(boundary < 5 && boundary == next_boundary && inside);
    assert(mi_heap_visit_blocks(mi_heap_main(), true, visit, &visits[boundary]));
    after[boundary] = vastitas_heap_checkpoint();
    assert(memcmp(&before[boundary], &after[boundary], sizeof(before[boundary])) == 0);
    assert(visits[boundary].blocks == after[boundary].live_blocks);
    assert(visits[boundary].usable == after[boundary].live_usable);
    inside = 0;
    ++next_boundary;
}

static void state(const VastitasHeapLifetimes *s) {
    printf("{\"allocations\":%" PRIu64 ",\"frees\":%" PRIu64
           ",\"bulk_frees\":%" PRIu64 ",\"resizes\":%" PRIu64
           ",\"aligns\":%" PRIu64 ",\"rehomes\":%" PRIu64
           ",\"allocated_requests\":%" PRIu64 ",\"resize_requests\":%" PRIu64
           ",\"allocated_usable\":%" PRIu64 ",\"freed_usable\":%" PRIu64
           ",\"live_blocks\":%" PRIu64 ",\"live_usable\":%" PRIu64
           ",\"peak_usable\":%" PRIu64 ",\"interval_peak_usable\":%" PRIu64 "}",
           s->allocations, s->frees, s->bulk_frees, s->resizes, s->aligns, s->rehomes,
           s->allocated_requests, s->resize_requests, s->allocated_usable, s->freed_usable,
           s->live_blocks, s->live_usable, s->peak_usable, s->interval_peak_usable);
}

void source_heap_report(void) {
    assert(next_boundary == 5 && !inside);
    printf("{\"kind\":\"source_lean_heap_lifetimes\",\"schema\":1,\"mimalloc_version\":%d,"
           "\"capacity\":%zu,\"observer_static_bytes\":%zu,\"phase_storage_bytes\":%zu,\"snapshots\":[",
           MI_MALLOC_VERSION, vastitas_heap_observer_capacity(), vastitas_heap_observer_bytes(),
           sizeof(before) + sizeof(after) + sizeof(visits) + sizeof(next_boundary) + sizeof(inside));
    for (unsigned i = 0; i < 5; ++i) {
        printf("%s{\"boundary\":%u,\"visited_blocks\":%" PRIu64 ",\"visited_usable\":%" PRIu64
               ",\"before\":", i ? "," : "", i, visits[i].blocks, visits[i].usable);
        state(&before[i]); printf(",\"after\":"); state(&after[i]); putchar('}');
    }
    puts("]}");
}
