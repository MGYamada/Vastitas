#include <lean/lean.h>
#include "vendor/mimalloc-stats.h"
#include <inttypes.h>
#include <stdio.h>
#include <string.h>

#if UINTPTR_MAX != UINT64_MAX
#error "This pinned capability profile requires a 64-bit host"
#endif

/* Public APIs only; stock runtime, no allocator replacement or source rebuild.
   Observation memory is static. Printing happens after every measured phase.
   Exactly one probe mutator. Main-heap coverage is calibrated, never assumed. */
#define SMALL_N 1024
#define LARGE_N 8
#define SMALL_CHURN 10000
#define LARGE_CHURN 128
#define LARGE_CAPACITY (2U * 1024U * 1024U)
#define SNAP_N 8
#define JSON_CAPACITY (128U * 1024U)

static lean_object *small[SMALL_N], *large[LARGE_N];
static uintptr_t small_addresses[SMALL_N], large_addresses[LARGE_N];
static volatile uint64_t checksum;
static size_t small_usable, large_usable;

typedef struct {
  const char *name;
  bool visit_ok, stats_ok, json_ok;
  size_t areas, area_used, area_live_bin_bytes, area_reserved, area_committed;
  size_t blocks, block_bytes, known_small, known_large;
  size_t elapsed, user, system, rss, peak_rss, commit, peak_commit, faults;
  mi_stats_t stats;
  char json[JSON_CAPACITY];
} Snapshot;
static Snapshot snapshots[SNAP_N], warm;

static bool visit(const mi_heap_t *heap, const mi_heap_area_t *area,
                  void *block, size_t block_size, void *arg) {
  (void)heap;
  Snapshot *s = (Snapshot *)arg;
  if (!block) {
    s->areas++;
    s->area_used += area->used;
    s->area_live_bin_bytes += area->used * area->block_size;
    s->area_reserved += area->reserved;
    s->area_committed += area->committed;
  } else {
    s->blocks++;
    s->block_bytes += block_size;
    uintptr_t address = (uintptr_t)block;
    for (size_t i = 0; i < SMALL_N; ++i)
      if (address == small_addresses[i]) ++s->known_small;
    for (size_t i = 0; i < LARGE_N; ++i)
      if (address == large_addresses[i]) ++s->known_large;
  }
  return true;
}

static void snapshot(Snapshot *s, const char *name) {
  s->name = name;
  s->visit_ok = mi_heap_visit_blocks(mi_heap_main(), true, visit, s);
  mi_stats_init(&s->stats);
  s->stats_ok = mi_stats_get(&s->stats);
  s->json_ok = mi_stats_as_json(&s->stats, sizeof(s->json), s->json) == s->json;
  mi_process_info(&s->elapsed, &s->user, &s->system, &s->rss, &s->peak_rss,
                  &s->commit, &s->peak_commit, &s->faults);
}

static lean_object *new_small(void) {
  lean_object *o = lean_alloc_ctor(0, 0, 32);
  memset(lean_ctor_scalar_cptr(o), 7, 32);
  checksum += lean_ctor_scalar_cptr(o)[31];
  return o;
}

static lean_object *new_large(void) {
  lean_object *o = lean_alloc_sarray(1, LARGE_CAPACITY, LARGE_CAPACITY);
  /* Touch every payload byte so retained buffers are physically committed.
     This is a capability probe, not an elapsed-time benchmark. */
  memset(lean_sarray_cptr(o), 11, LARGE_CAPACITY);
  checksum += lean_sarray_cptr(o)[LARGE_CAPACITY - 1];
  return o;
}

/* The pinned Lean compiler erases IO's World argument (see emitted Main.c). */
lean_obj_res allocation_capability_probe(void) {
  /* Fault in observer storage before baseline. Do not attribute its pages to
     measured objects. Volatile accesses prevent removing BSS zero writes. */
  volatile unsigned char *observer = (volatile unsigned char *)snapshots;
  for (size_t i = 0; i < sizeof(snapshots); i += 4096) observer[i] = 0;
  observer[sizeof(snapshots) - 1] = 0;
  /* Warm the observation path; no stats reset that would discard baselines. */
  snapshot(&warm, "observer_warmup");
  snapshot(&snapshots[0], "baseline");
  for (size_t i = 0; i < SMALL_N; ++i) {
    small[i] = new_small(); small_addresses[i] = (uintptr_t)small[i];
    small_usable += mi_usable_size(small[i]);
  }
  snapshot(&snapshots[1], "small_held");
  for (size_t i = 0; i < SMALL_N; ++i) { lean_dec(small[i]); small[i] = NULL; }
  snapshot(&snapshots[2], "small_released");
  memset(small_addresses, 0, sizeof(small_addresses));
  for (size_t i = 0; i < LARGE_N; ++i) {
    large[i] = new_large(); large_addresses[i] = (uintptr_t)large[i];
    large_usable += mi_usable_size(large[i]);
  }
  snapshot(&snapshots[3], "large_held");
  for (size_t i = 0; i < LARGE_N; ++i) { lean_dec(large[i]); large[i] = NULL; }
  snapshot(&snapshots[4], "large_released");
  memset(large_addresses, 0, sizeof(large_addresses));
  for (size_t i = 0; i < SMALL_CHURN; ++i) { lean_object *o = new_small(); lean_dec(o); }
  snapshot(&snapshots[5], "small_transient");
  for (size_t i = 0; i < LARGE_CHURN; ++i) { lean_object *o = new_large(); lean_dec(o); }
  snapshot(&snapshots[6], "large_transient");
  /* Explicit separate collection phase, never hidden inside another phase. */
  mi_collect(true);
  snapshot(&snapshots[7], "forced_collection");

  bool ok = true;
  printf("{\"kind\":\"configuration\",\"mimalloc_header_version\":%d,"
         "\"stats_header_version\":%d,\"small_held_count\":%d,\"large_held_count\":%d,"
         "\"small_transient_count\":%d,\"large_transient_count\":%d,"
         "\"small_scalar_bytes\":32,\"small_object_bytes\":%zu,\"large_payload_bytes\":%u,"
         "\"large_object_bytes\":%zu,\"small_held_usable_bytes\":%zu,"
         "\"large_held_usable_bytes\":%zu,\"observer_snapshot_bytes\":%zu,"
         "\"known_object_table_bytes\":%zu,\"checksum\":%" PRIu64 "}\n",
         MI_MALLOC_VERSION, MI_STAT_VERSION, SMALL_N, LARGE_N, SMALL_CHURN, LARGE_CHURN,
         sizeof(lean_ctor_object) + 32, LARGE_CAPACITY, sizeof(lean_sarray_object) + LARGE_CAPACITY,
         small_usable, large_usable, sizeof(snapshots) + sizeof(warm),
         sizeof(small) + sizeof(large) + sizeof(small_addresses) + sizeof(large_addresses), checksum);
  for (size_t i = 0; i < SNAP_N; ++i) {
    const Snapshot *s = &snapshots[i];
    ok = ok && s->visit_ok && s->stats_ok && s->json_ok;
    printf("{\"kind\":\"snapshot\",\"phase\":\"%s\",\"visit_ok\":%s,\"stats_ok\":%s,"
           "\"json_ok\":%s,\"areas\":%zu,\"area_used\":%zu,\"area_live_bin_bytes\":%zu,"
           "\"area_reserved_bytes\":%zu,\"area_committed_bytes\":%zu,\"blocks\":%zu,"
           "\"block_bytes\":%zu,\"known_small\":%zu,\"known_large\":%zu,"
           "\"process\":{\"rss\":%zu,\"peak_rss\":%zu,\"commit\":%zu,\"peak_commit\":%zu,"
           "\"faults\":%zu},\"stats\":%s}\n",
           s->name, s->visit_ok ? "true" : "false", s->stats_ok ? "true" : "false",
           s->json_ok ? "true" : "false", s->areas, s->area_used, s->area_live_bin_bytes,
           s->area_reserved, s->area_committed, s->blocks, s->block_bytes,
           s->known_small, s->known_large, s->rss, s->peak_rss, s->commit, s->peak_commit,
           s->faults, s->json_ok ? s->json : "null");
  }
  return lean_io_result_mk_ok(lean_box_uint32(ok ? 0 : 1));
}
