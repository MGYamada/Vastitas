#include "lifetime.h"
#include <mimalloc.h>
#include <cassert>
#include <cstdio>
#include <cstring>
#include <pthread.h>

#ifdef NDEBUG
#error "The lifetime calibration requires its assertions"
#endif

struct Visit { uint64_t blocks, usable; };
static bool visit(const mi_heap_t *, const mi_heap_area_t *, void *block, size_t size, void *data) {
  if (block) {
    Visit &result = *static_cast<Visit *>(data);
    ++result.blocks;
    result.usable += size;
  }
  return true;
}
static void check_main_heap() {
  Visit visited{};
  assert(mi_heap_visit_blocks(mi_heap_main(), true, visit, &visited));
  const VastitasHeapLifetimes state = vastitas_heap_snapshot();
  assert(state.live_blocks == visited.blocks && state.live_usable == visited.usable);
  assert(state.live_blocks == state.allocations - state.frees);
  assert(state.live_usable == state.allocated_usable - state.freed_usable);
}
static void report(const char *phase) {
  const VastitasHeapLifetimes s = vastitas_heap_checkpoint();
  std::printf("{\"kind\":\"native_heap_lifetime\",\"phase\":\"%s\",\"allocations\":%llu,\"frees\":%llu,\"bulk_frees\":%llu,"
              "\"resizes\":%llu,\"aligns\":%llu,\"rehomes\":%llu,\"live_blocks\":%llu,"
              "\"live_usable\":%llu,\"peak_usable\":%llu,\"interval_peak_usable\":%llu,"
              "\"allocated_requests\":%llu,\"resize_requests\":%llu,"
              "\"allocated_usable\":%llu,\"freed_usable\":%llu}\n",
    phase,(unsigned long long)s.allocations,(unsigned long long)s.frees,
    (unsigned long long)s.bulk_frees,(unsigned long long)s.resizes,(unsigned long long)s.aligns,
    (unsigned long long)s.rehomes,(unsigned long long)s.live_blocks,(unsigned long long)s.live_usable,
    (unsigned long long)s.peak_usable,(unsigned long long)s.interval_peak_usable,
    (unsigned long long)s.allocated_requests,(unsigned long long)s.resize_requests,
    (unsigned long long)s.allocated_usable,(unsigned long long)s.freed_usable);
}
static void *foreign_free(void *pointer) { mi_free(pointer); return nullptr; }
static pthread_mutex_t gate = PTHREAD_MUTEX_INITIALIZER;
static pthread_cond_t changed = PTHREAD_COND_INITIALIZER;
static unsigned ready, done, stage;
struct Worker { uint64_t usable_total, max_held; };
static void *churn(void *context) {
  Worker &totals = *static_cast<Worker *>(context);
  // Separate thread/allocator initialization and termination from the known
  // operation count. The main thread observes while all workers are parked.
  void *warm = mi_malloc(8192); assert(warm); mi_free(warm);
  assert(pthread_mutex_lock(&gate) == 0);
  ++ready;
  assert(pthread_cond_broadcast(&changed) == 0);
  while (stage < 1) assert(pthread_cond_wait(&changed, &gate) == 0);
  assert(pthread_mutex_unlock(&gate) == 0);
  for (size_t i = 0; i < 10000; ++i) {
    void *a = mi_malloc(17 + i % 128), *b = mi_malloc(4097 + i % 8);
    assert(a && b);
    const size_t owned = mi_usable_size(a) + mi_usable_size(b);
    totals.usable_total += owned;
    if (owned > totals.max_held) totals.max_held = owned;
    std::memset(a, 7, 17 + i % 128);
    mi_free(a); mi_free(b);
  }
  assert(pthread_mutex_lock(&gate) == 0);
  ++done;
  assert(pthread_cond_broadcast(&changed) == 0);
  while (stage < 2) assert(pthread_cond_wait(&changed, &gate) == 0);
  assert(pthread_mutex_unlock(&gate) == 0);
  return nullptr;
}

int main(int argc, char **argv) {
  mi_process_init();
  if (argc == 2 && std::strcmp(argv[1], "capacity") == 0) {
    for (size_t i = 0; i <= vastitas_heap_observer_capacity(); ++i) {
      void *p = mi_malloc(8); assert(p);
    }
    return 1; // a full observer must fail instead of truncating the record
  }
  check_main_heap(); report("baseline");
  const VastitasHeapLifetimes base = vastitas_heap_snapshot();
  void *a = mi_malloc(16), *b = mi_malloc(4 * 1024 * 1024), *c = mi_malloc(32 * 1024 * 1024);
  assert(a && b && c);
  const size_t sizes[] = {mi_usable_size(a), mi_usable_size(b), mi_usable_size(c)};
  const size_t held = sizes[0] + sizes[1] + sizes[2];
  assert(vastitas_heap_snapshot().live_usable == base.live_usable + held);
  assert(vastitas_heap_snapshot().interval_peak_usable == base.live_usable + held);
  check_main_heap(); report("held");
  mi_free(a); mi_free(b); mi_free(c);
  assert(vastitas_heap_snapshot().live_usable == base.live_usable);
  check_main_heap(); report("released");
  a = mi_malloc(100); assert(a);
  const uint64_t before_resize = vastitas_heap_snapshot().resizes;
  void *q = mi_realloc(a, mi_usable_size(a) - 1); assert(q == a);
  assert(vastitas_heap_snapshot().resizes == before_resize + 1);
  q = mi_realloc(q, 1024 * 1024); assert(q); mi_free(q);
  a = mi_malloc_aligned_at(123, 256, 13); assert(a);
  assert((reinterpret_cast<uintptr_t>(a) + 13) % 256 == 0);
  q = mi_realloc_aligned_at(a, mi_usable_size(a) - 1, 256, 13); assert(q == a);
  mi_free(q);
  assert(vastitas_heap_snapshot().aligns > 0);
  check_main_heap(); report("reallocation-alignment");
  a = mi_malloc(4096); assert(a);
  pthread_t worker;
  assert(pthread_create(&worker, nullptr, foreign_free, a) == 0);
  assert(pthread_join(worker, nullptr) == 0);
  check_main_heap(); report("cross-thread-free");
  mi_heap_t *heap = mi_heap_new(); assert(heap);
  a = mi_heap_malloc(heap, 1024); assert(a);
  const uint64_t before_destroy = vastitas_heap_snapshot().bulk_frees;
  mi_heap_destroy(heap);
  assert(vastitas_heap_snapshot().bulk_frees == before_destroy + 1);
  check_main_heap(); report("heap-destroy");
  heap = mi_heap_new(); assert(heap);
  a = mi_heap_malloc(heap, 2048); assert(a);
  const uint64_t before_delete = vastitas_heap_snapshot().rehomes;
  mi_heap_delete(heap);
  assert(vastitas_heap_snapshot().rehomes == before_delete + 1);
  check_main_heap(); mi_free(a);
  check_main_heap(); report("heap-delete");
  pthread_t workers[8];
  Worker totals[8]{};
  for (unsigned i = 0; i < 8; ++i) assert(pthread_create(&workers[i], nullptr, churn, &totals[i]) == 0);
  assert(pthread_mutex_lock(&gate) == 0);
  while (ready < 8) assert(pthread_cond_wait(&changed, &gate) == 0);
  const VastitasHeapLifetimes before_churn = vastitas_heap_snapshot();
  check_main_heap(); report("workers-ready");
  stage = 1;
  assert(pthread_cond_broadcast(&changed) == 0);
  while (done < 8) assert(pthread_cond_wait(&changed, &gate) == 0);
  const VastitasHeapLifetimes after_churn = vastitas_heap_snapshot();
  uint64_t usable_total = 0, combined_bound = 0, single_bound = 0;
  for (const auto &worker : totals) {
    usable_total += worker.usable_total;
    combined_bound += worker.max_held;
    if (worker.max_held > single_bound) single_bound = worker.max_held;
  }
  assert(after_churn.allocations - before_churn.allocations == 160000);
  assert(after_churn.frees - before_churn.frees == 160000);
  assert(after_churn.live_blocks == before_churn.live_blocks);
  assert(after_churn.live_usable == before_churn.live_usable);
  assert(after_churn.allocated_usable - before_churn.allocated_usable == usable_total);
  assert(after_churn.freed_usable - before_churn.freed_usable == usable_total);
  assert(after_churn.interval_peak_usable >= before_churn.live_usable + single_bound);
  assert(after_churn.interval_peak_usable <= before_churn.live_usable + combined_bound);
  check_main_heap(); report("concurrent-churn");
  stage = 2;
  assert(pthread_cond_broadcast(&changed) == 0);
  assert(pthread_mutex_unlock(&gate) == 0);
  for (auto &thread : workers) assert(pthread_join(thread, nullptr) == 0);
  check_main_heap(); report("worker-exit");
  const VastitasHeapLifetimes first = vastitas_heap_snapshot(), second = vastitas_heap_snapshot();
  assert(std::memcmp(&first, &second, sizeof(first)) == 0);
  report("done");
  std::printf("{\"kind\":\"native_heap_lifetime_configuration\",\"schema\":1,"
              "\"held_usable\":[%zu,%zu,%zu],\"threads\":8,\"iterations\":10000,"
              "\"allocations_per_iteration\":2,\"churn_usable\":%llu,\"single_bound\":%llu,"
              "\"combined_bound\":%llu,\"capacity\":%zu,\"observer_static_bytes\":%zu}\n",
              sizes[0],sizes[1],sizes[2],(unsigned long long)usable_total,
              (unsigned long long)single_bound,(unsigned long long)combined_bound,
              vastitas_heap_observer_capacity(),vastitas_heap_observer_bytes());
}
