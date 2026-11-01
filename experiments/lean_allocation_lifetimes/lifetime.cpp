#include "lifetime.h"

#include <atomic>
#include <cstdlib>
#include <unistd.h>

namespace {
static_assert(sizeof(uintptr_t) == 8 && sizeof(size_t) == 8, "requires a 64-bit host");
constexpr size_t capacity = 131072;
struct Entry {
  uintptr_t pointer, alias, heap;
  size_t usable;
};
Entry entries[capacity];
std::atomic_flag guard = ATOMIC_FLAG_INIT;
VastitasHeapLifetimes state{};

[[noreturn]] void fail() {
  // No formatting, dynamic allocation or allocator callback on a failed audit.
  constexpr char message[] = "VASTITAS_HEAP_LIFETIME_AUDIT_FAILED\n";
  (void)write(STDERR_FILENO, message, sizeof(message) - 1);
  _Exit(90);
}
void require(bool condition) { if (!condition) fail(); }
uint64_t plus(uint64_t a, uint64_t b) {
  require(b <= UINT64_MAX - a);
  return a + b;
}
struct Lock {
  Lock() { while (guard.test_and_set(std::memory_order_acquire)) {} }
  ~Lock() { guard.clear(std::memory_order_release); }
};
size_t index(uintptr_t pointer) {
  return ((pointer >> 3) * UINT64_C(11400714819323198485)) & (capacity - 1);
}
Entry *find(uintptr_t pointer, bool insert) {
  Entry *tombstone = nullptr;
  for (size_t n = 0, at = index(pointer); n < capacity;
       ++n, at = (at + 1) & (capacity - 1)) {
    Entry &entry = entries[at];
    if (entry.pointer == pointer) return &entry;
    if (entry.pointer == 1 && !tombstone) tombstone = &entry;
    if (entry.pointer == 0) return insert ? (tombstone ? tombstone : &entry) : nullptr;
  }
  return insert ? tombstone : nullptr;
}
Entry *find_alias(uintptr_t pointer) {
  if (Entry *entry = find(pointer, false)) return entry;
  for (Entry &entry : entries)
    if (entry.pointer > 1 && entry.alias == pointer) return &entry;
  return nullptr;
}
void release(Entry &entry, bool bulk) {
  require(entry.pointer > 1 && state.live_blocks > 0 && state.live_usable >= entry.usable);
  state.frees = plus(state.frees, 1);
  state.bulk_frees = plus(state.bulk_frees, bulk ? 1 : 0);
  state.freed_usable = plus(state.freed_usable, entry.usable);
  --state.live_blocks;
  state.live_usable -= entry.usable;
  entry = {1, 0, 0, 0};
}
}

extern "C" void vastitas_heap_alloc(void *pointer, size_t requested, size_t usable,
                                    const void *heap) {
  Lock lock;
  const uintptr_t address = reinterpret_cast<uintptr_t>(pointer);
  const uintptr_t owner = reinterpret_cast<uintptr_t>(heap);
  require(address > 1 && owner != 0 && requested <= usable);
  Entry *entry = find(address, true);
  require(entry && entry->pointer <= 1);
  *entry = {address, address, owner, usable};
  state.allocations = plus(state.allocations, 1);
  state.allocated_requests = plus(state.allocated_requests, requested);
  state.allocated_usable = plus(state.allocated_usable, usable);
  state.live_blocks = plus(state.live_blocks, 1);
  state.live_usable = plus(state.live_usable, usable);
  if (state.live_usable > state.peak_usable) state.peak_usable = state.live_usable;
  if (state.live_usable > state.interval_peak_usable) state.interval_peak_usable = state.live_usable;
}

extern "C" void vastitas_heap_free(void *pointer, size_t usable) {
  Lock lock;
  Entry *entry = find(reinterpret_cast<uintptr_t>(pointer), false);
  require(entry && entry->usable == usable);
  release(*entry, false);
}

extern "C" void vastitas_heap_align(void *pointer, void *aligned, size_t offset) {
  Lock lock;
  Entry *entry = find(reinterpret_cast<uintptr_t>(pointer), false);
  require(entry && offset <= UINTPTR_MAX - entry->pointer && offset < entry->usable);
  require(reinterpret_cast<uintptr_t>(aligned) == entry->pointer + offset);
  entry->alias = reinterpret_cast<uintptr_t>(aligned);
  state.aligns = plus(state.aligns, 1);
}

extern "C" void vastitas_heap_resize(void *pointer, size_t old_usable, size_t requested) {
  Lock lock;
  const uintptr_t address = reinterpret_cast<uintptr_t>(pointer);
  Entry *entry = find_alias(address);
  require(address > 1 && entry && entry->pointer > 1 && address >= entry->pointer);
  const size_t offset = address - entry->pointer;
  require(offset <= entry->usable && old_usable == entry->usable - offset && requested <= old_usable);
  state.resizes = plus(state.resizes, 1);
  state.resize_requests = plus(state.resize_requests, requested);
}

extern "C" void vastitas_heap_rehome(const void *old_heap, const void *new_heap) {
  Lock lock;
  const uintptr_t old_owner = reinterpret_cast<uintptr_t>(old_heap);
  const uintptr_t new_owner = reinterpret_cast<uintptr_t>(new_heap);
  require(old_owner != 0 && new_owner != 0 && old_owner != new_owner);
  for (Entry &entry : entries) {
    if (entry.pointer > 1 && entry.heap == old_owner) {
      entry.heap = new_owner;
      state.rehomes = plus(state.rehomes, 1);
    }
  }
}

extern "C" void vastitas_heap_destroy(const void *heap) {
  Lock lock;
  const uintptr_t owner = reinterpret_cast<uintptr_t>(heap);
  require(owner != 0);
  for (Entry &entry : entries)
    if (entry.pointer > 1 && entry.heap == owner) release(entry, true);
}

extern "C" VastitasHeapLifetimes vastitas_heap_snapshot(void) {
  Lock lock;
  return state;
}
extern "C" VastitasHeapLifetimes vastitas_heap_checkpoint(void) {
  Lock lock;
  const VastitasHeapLifetimes result = state;
  state.interval_peak_usable = state.live_usable;
  return result;
}
extern "C" size_t vastitas_heap_observer_bytes(void) {
  return sizeof(entries) + sizeof(guard) + sizeof(state);
}
extern "C" size_t vastitas_heap_observer_capacity(void) { return capacity; }
