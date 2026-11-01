#pragma once
#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/* Private diagnostic only. These describe tracked mimalloc blocks, not RSS,
 * backing pages, libc/GMP storage, logical Lean object payloads or timings.
 * The allocation request is the request at mimalloc's allocation hook; aligned
 * allocation can include its internal over-allocation. In-place resize requests
 * are reported separately and do not manufacture a physical allocation/free. */
typedef struct {
  uint64_t allocations, frees, bulk_frees, resizes, aligns, rehomes;
  uint64_t allocated_requests, resize_requests;
  uint64_t allocated_usable, freed_usable;
  uint64_t live_blocks, live_usable, peak_usable, interval_peak_usable;
} VastitasHeapLifetimes;

void vastitas_heap_alloc(void *pointer, size_t requested, size_t usable, const void *heap);
void vastitas_heap_free(void *pointer, size_t usable);
void vastitas_heap_align(void *pointer, void *aligned, size_t offset);
void vastitas_heap_resize(void *pointer, size_t old_usable, size_t requested);
void vastitas_heap_rehome(const void *old_heap, const void *new_heap);
void vastitas_heap_destroy(const void *heap);

/* Both APIs serialize with all recorded events. Starting an interval only
 * changes observer metadata: no allocator statistics are reset or collected. */
VastitasHeapLifetimes vastitas_heap_snapshot(void);
/* Return the completed interval and start the next one in the same lock. */
VastitasHeapLifetimes vastitas_heap_checkpoint(void);
size_t vastitas_heap_observer_bytes(void);
size_t vastitas_heap_observer_capacity(void);

#ifdef __cplusplus
}
#endif
