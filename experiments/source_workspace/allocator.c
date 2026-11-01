/* Private cost observer. No reset, collection, printing or dynamic observer
 * allocation inside the phases; two immediate snapshots expose observer churn.
 * Only calling-thread deltas have the calibrated meaning. Startup on the live
 * initialization thread and allocations outside mimalloc are not accounted. */
#include <lean/lean.h>
#include "mimalloc-stats.h"
#include "allocator.h"
#include <assert.h>
#include <inttypes.h>
#include <stdio.h>

#if UINTPTR_MAX != UINT64_MAX
#error "The allocator observer requires a 64-bit host"
#endif
#ifdef NDEBUG
#error "The allocator observer requires its guards"
#endif

static mi_stats_t samples[5][2];
static unsigned phase;
static int finished;
typedef struct {
    size_t object_requested, object_usable, string_requested, string_usable, string_bytes;
} ErrorObjects;
static ErrorObjects errors[1];
static unsigned error_count;

void source_allocator_error(b_lean_obj_arg value) {
    assert(!finished && phase == 3 && error_count == 0);
    assert(!lean_is_scalar(value) && lean_is_ctor(value) && lean_ctor_num_objs(value) == 1);
    lean_object *message = lean_ctor_get(value, 0);
    assert(!lean_is_scalar(message) && lean_is_string(message));
    assert(strcmp(lean_string_cstr(message), "E_NATIVE_EXPECT: stored bit pattern differs") == 0);
    errors[error_count++] = (ErrorObjects){lean_object_byte_size(value), mi_usable_size(value),
        lean_string_byte_size(message), mi_usable_size(message), lean_string_size(message)};
}

static void sample(unsigned index) {
    assert(index < 5);
    for (unsigned repeat = 0; repeat < 2; ++repeat) {
        mi_stats_t *s = &samples[index][repeat];
        mi_stats_init(s);
        assert(mi_stats_get(s));
    }
}

void source_allocator_mark(unsigned next) {
    assert(!finished && next == phase + 1 && next <= 4);
    sample(phase);
    phase = next;
}

void source_allocator_finish(void) {
    assert(!finished && phase == 4);
    sample(4);
    finished = 1;
}

static void count(const char *name, const mi_stat_count_t *s) {
    printf("\"%s\":{\"total\":%" PRId64 ",\"current\":%" PRId64 ",\"peak\":%" PRId64 "}",
           name, s->total, s->current, s->peak);
}

void source_allocator_report(void) {
    assert(finished);
    printf("{\"kind\":\"source_lean_allocator\",\"schema\":1,\"mimalloc_version\":%d,"
           "\"stats_version\":%d,\"observer_static_bytes\":%zu,\"snapshots\":[",
           MI_MALLOC_VERSION, MI_STAT_VERSION,
           sizeof(samples) + sizeof(phase) + sizeof(finished) + sizeof(errors) + sizeof(error_count));
    for (unsigned i = 0; i < 5; ++i) {
        for (unsigned j = 0; j < 2; ++j) {
            const mi_stats_t *s = &samples[i][j];
            printf("%s{\"boundary\":%u,\"repeat\":%u,\"normal_count\":%" PRId64
                   ",\"huge_count\":%" PRId64 ",", i || j ? "," : "", i, j,
                   s->malloc_normal_count.total, s->malloc_huge_count.total);
            count("normal", &s->malloc_normal); putchar(',');
            count("huge", &s->malloc_huge); putchar(',');
            count("requested", &s->malloc_requested); putchar('}');
        }
    }
    printf("],\"error_objects\":[");
    for (unsigned i = 0; i < error_count; ++i) {
        const ErrorObjects *e = &errors[i];
        printf("%s{\"phase\":3,\"object_requested\":%zu,\"object_usable\":%zu,"
               "\"string_requested\":%zu,\"string_usable\":%zu,\"string_bytes\":%zu}",
               i ? "," : "", e->object_requested, e->object_usable,
               e->string_requested, e->string_usable, e->string_bytes);
    }
    puts("]}");
}
