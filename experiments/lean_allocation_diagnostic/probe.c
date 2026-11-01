#include <lean/lean.h>
#include "../stock_allocation_capabilities/vendor/mimalloc-stats.h"
#include <inttypes.h>
#include <stdio.h>
#include <string.h>

#if UINTPTR_MAX != UINT64_MAX
#error "This calibration requires a 64-bit host"
#endif

/* A single mutator, public Lean allocation/free APIs, and static observation
   storage. No reset, printing or dynamic observer allocation during phases.
   The separate runner selects stock, rebuilt MI_STAT=0 or rebuilt MI_STAT=2. */
#define CASES 5
#define MAX_HELD 1024
#define SNAPSHOTS (3 * CASES + 3)
#define JSON_BYTES (128 * 1024)
static lean_object *held[MAX_HELD];
static uintptr_t addresses[MAX_HELD];
static volatile uint64_t checksum;

static lean_object *small(void) {
  lean_object *o = lean_alloc_ctor(0, 0, 32);
  memset(lean_ctor_scalar_cptr(o), 7, 32);
  checksum += lean_ctor_scalar_cptr(o)[31];
  return o;
}

static lean_object *bytes(size_t capacity) {
  lean_object *o = lean_alloc_sarray(1, capacity, capacity);
  memset(lean_sarray_cptr(o), 11, capacity);
  checksum += lean_sarray_cptr(o)[capacity - 1];
  return o;
}
static lean_object *medium(void) { return bytes(1001); }
static lean_object *large(void) { return bytes(2 * 1024 * 1024); }

static lean_object *closure_body(lean_object *captured, lean_object *arg) {
  lean_dec(arg);
  return captured;
}
static lean_object *closure(void) {
  lean_object *o = lean_alloc_closure((void *)closure_body, 2, 1);
  lean_closure_set(o, 0, lean_box(13));
  checksum += lean_unbox(lean_closure_get(o, 0));
  return o;
}
static lean_object *array(void) {
  lean_object *o = lean_alloc_array(100, 100);
  for (size_t i = 0; i < 100; ++i) lean_array_set_core(o, i, lean_box(i));
  checksum += lean_unbox(lean_array_get_core(o, 99));
  return o;
}

typedef struct {
  const char *name;
  size_t count, churn, object_bytes, usable_bytes;
  lean_object *(*make)(void);
} Workload;
static Workload workloads[CASES] = {
  {"constructor", 1024, 10000, sizeof(lean_ctor_object) + 32, 0, small},
  {"byte_array", 13, 257, sizeof(lean_sarray_object) + 1001, 0, medium},
  {"large_byte_array", 8, 128, sizeof(lean_sarray_object) + 2 * 1024 * 1024, 0, large},
  {"closure", 19, 199, sizeof(lean_closure_object) + sizeof(void *), 0, closure},
  {"array", 17, 263, sizeof(lean_array_object) + 100 * sizeof(void *), 0, array}
};

typedef struct {
  const char *phase, *workload;
  size_t blocks, block_bytes, known, areas, area_blocks, area_bytes;
  bool visit_ok, stats_ok, json_ok;
  mi_stats_t stats;
  char json[JSON_BYTES];
} Snapshot;
static Snapshot snapshots[SNAPSHOTS], warm;

static bool visit(const mi_heap_t *heap, const mi_heap_area_t *area,
                  void *block, size_t size, void *arg) {
  (void)heap;
  Snapshot *s = (Snapshot *)arg;
  if (block == NULL) {
    ++s->areas; s->area_blocks += area->used;
    s->area_bytes += area->used * area->block_size;
  } else {
    ++s->blocks; s->block_bytes += size;
    for (size_t i = 0; i < MAX_HELD; ++i)
      if ((uintptr_t)block == addresses[i]) ++s->known;
  }
  return true;
}

static void snapshot(Snapshot *s, const char *workload, const char *phase) {
  s->workload = workload; s->phase = phase;
  s->visit_ok = mi_heap_visit_blocks(mi_heap_main(), true, visit, s);
  mi_stats_init(&s->stats);
  s->stats_ok = mi_stats_get(&s->stats);
  s->json_ok = mi_stats_as_json(&s->stats, sizeof(s->json), s->json) == s->json;
}

lean_obj_res lean_allocator_diagnostic_probe(void) {
  volatile unsigned char *memory = (volatile unsigned char *)snapshots;
  for (size_t i = 0; i < sizeof(snapshots); i += 4096) memory[i] = 0;
  memory[sizeof(snapshots) - 1] = 0;
  snapshot(&warm, "observer", "warmup");
  size_t cursor = 0;
  snapshot(&snapshots[cursor++], "observer", "baseline");
  snapshot(&snapshots[cursor++], "observer", "repeat");
  bool ok = true;
  for (size_t w = 0; w < CASES; ++w) {
    Workload *v = &workloads[w];
    for (size_t i = 0; i < v->count; ++i) {
      held[i] = v->make(); addresses[i] = (uintptr_t)held[i];
      size_t usable = mi_usable_size(held[i]);
      if (i == 0) v->usable_bytes = usable;
      else ok = ok && usable == v->usable_bytes;
    }
    snapshot(&snapshots[cursor++], v->name, "held");
    for (size_t i = 0; i < v->count; ++i) { lean_dec(held[i]); held[i] = NULL; }
    snapshot(&snapshots[cursor++], v->name, "released");
    memset(addresses, 0, sizeof(addresses));
    for (size_t i = 0; i < v->churn; ++i) {
      lean_object *o = v->make();
      ok = ok && mi_usable_size(o) == v->usable_bytes;
      lean_dec(o);
    }
    snapshot(&snapshots[cursor++], v->name, "churn");
  }
  mi_collect(true);
  snapshot(&snapshots[cursor++], "observer", "collection");
  ok = ok && cursor == SNAPSHOTS;
  printf("{\"kind\":\"configuration\",\"mimalloc_version\":%d,\"stats_version\":%d,"
         "\"snapshot_bytes\":%zu,\"pointer_table_bytes\":%zu,\"workload_table_bytes\":%zu,"
         "\"checksum_bytes\":%zu,\"checksum\":%" PRIu64 ",\"workloads\":[",
         MI_MALLOC_VERSION, MI_STAT_VERSION, sizeof(snapshots) + sizeof(warm),
         sizeof(held) + sizeof(addresses), sizeof(workloads), sizeof(checksum), checksum);
  for (size_t i = 0; i < CASES; ++i) {
    const Workload *v = &workloads[i];
    printf("%s{\"name\":\"%s\",\"held\":%zu,\"churn\":%zu,\"object_bytes\":%zu,"
           "\"usable_bytes\":%zu}", i ? "," : "", v->name, v->count, v->churn,
           v->object_bytes, v->usable_bytes);
  }
  printf("]}\n");
  for (size_t i = 0; i < SNAPSHOTS; ++i) {
    const Snapshot *s = &snapshots[i];
    ok = ok && s->visit_ok && s->stats_ok && s->json_ok;
    printf("{\"kind\":\"snapshot\",\"workload\":\"%s\",\"phase\":\"%s\","
           "\"visit_ok\":%s,\"stats_ok\":%s,\"json_ok\":%s,\"blocks\":%zu,"
           "\"block_bytes\":%zu,\"known\":%zu,\"areas\":%zu,\"area_blocks\":%zu,"
           "\"area_bytes\":%zu,\"stats\":%s}\n", s->workload, s->phase,
           s->visit_ok ? "true" : "false", s->stats_ok ? "true" : "false",
           s->json_ok ? "true" : "false", s->blocks, s->block_bytes, s->known,
           s->areas, s->area_blocks, s->area_bytes, s->json_ok ? s->json : "null");
  }
  return lean_io_result_mk_ok(lean_box_uint32(ok ? 0 : 1));
}
