/* Included into a private, pinned OpenBLAS memory.c after common.h. No macro
 * interposition: patch.py rewrites only calls in that exact source file. */
#include "observer.h"
#include <errno.h>
#include <inttypes.h>
#include <pthread.h>
#include <stdatomic.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <sys/mman.h>
#include <unistd.h>

typedef struct {
    uintptr_t address;
    size_t bytes;
    unsigned phase;
    int ok, error;
    const char *operation;
} VObsEvent;
static VObsEvent vobs_events[4096];
static size_t vobs_count;
static unsigned vobs_phase;
static int vobs_owner_set, vobs_finished;
static pthread_t vobs_owner;
static atomic_flag vobs_busy = ATOMIC_FLAG_INIT;

static void vobs_fail(void) {
    const char message[] = "workspace observer capacity/thread/lifecycle failure\n";
    (void)write(STDERR_FILENO, message, sizeof(message)-1);
    _exit(91);
}
static void vobs_record(const char *operation, void *address, size_t bytes, int ok, int error) {
    if (atomic_flag_test_and_set(&vobs_busy)) vobs_fail();
    if (!vobs_owner_set) { vobs_owner = pthread_self(); vobs_owner_set = 1; }
    if (!pthread_equal(vobs_owner, pthread_self()) || vobs_finished ||
        vobs_count == sizeof(vobs_events)/sizeof(vobs_events[0])) vobs_fail();
    vobs_events[vobs_count++] = (VObsEvent){(uintptr_t)address, bytes, vobs_phase, ok, error, operation};
    atomic_flag_clear(&vobs_busy);
}
void vobs_mark(unsigned phase) {
    /* The supported caller never races a marker with a library call. */
    vobs_phase = phase;
    vobs_record("mark", NULL, 0, 1, 0);
}
static void *vobs_malloc(size_t bytes) {
    void *p = malloc(bytes);
    int saved = errno;
    vobs_record("malloc", p, bytes, p != NULL, p ? 0 : saved);
    errno = saved;
    return p;
}
static void vobs_free(void *p) {
    int saved = errno;
    vobs_record("free", p, 0, 1, 0);
    free(p);
    errno = saved;
}
static void *vobs_mmap(void *address, size_t bytes, int prot, int flags, int fd, off_t offset) {
    void *p = mmap(address, bytes, prot, flags, fd, offset);
    int saved = errno;
    vobs_record("mmap", p, bytes, p != MAP_FAILED, p == MAP_FAILED ? saved : 0);
    errno = saved;
    return p;
}
static int vobs_munmap(void *address, size_t bytes) {
    int result = munmap(address, bytes), saved = errno;
    vobs_record("munmap", address, bytes, result == 0, result ? saved : 0);
    errno = saved;
    return result;
}
void vobs_dump(void) {
    if (vobs_finished) vobs_fail();
    vobs_finished = 1;
    const size_t observer_bytes = sizeof(vobs_events) + sizeof(vobs_count) +
        sizeof(vobs_phase) + sizeof(vobs_owner_set) + sizeof(vobs_finished) +
        sizeof(vobs_owner) + sizeof(vobs_busy);
    printf("{\"kind\":\"workspace\",\"buffer_bytes\":%zu,\"page_bytes\":%ld,"
           "\"observer_static_bytes\":%zu,\"event_capacity\":4096,\"events\":[",
           (size_t)BUFFER_SIZE, sysconf(_SC_PAGESIZE), observer_bytes);
    for (size_t i = 0; i < vobs_count; ++i) {
        VObsEvent e = vobs_events[i];
        printf("%s{\"sequence\":%zu,\"phase\":%u,\"operation\":\"%s\","
               "\"address\":\"0x%" PRIxPTR "\",\"bytes\":%zu,\"ok\":%d,\"errno\":%d}",
               i ? "," : "", i, e.phase, e.operation, e.address, e.bytes, e.ok, e.error);
    }
    puts("]}");
}
