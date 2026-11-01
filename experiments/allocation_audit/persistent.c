/* EXPERIMENT ONLY. Immutable IO Unit success; no production file uses this.
 * APIs are pinned Lean 4.35 public constructors/persistence/reference operations.
 * pthread_once publishes the completed persistent object before any return. */
#include <lean/lean.h>
#include <pthread.h>
#include <stdatomic.h>
#include <stdio.h>
#include <stdlib.h>

static pthread_once_t once = PTHREAD_ONCE_INIT;
static lean_object *success;
static _Atomic(unsigned) initializations;
static _Atomic(unsigned) test_calls;
static pthread_mutex_t gate_lock = PTHREAD_MUTEX_INITIALIZER;
static pthread_cond_t gate_ready = PTHREAD_COND_INITIALIZER;
static pthread_t workers[8];
static unsigned arrived;
static void require(int valid) { if (!valid) abort(); }
static void initialize_success(void) {
    success = lean_io_result_mk_ok(lean_box(0));
    lean_mark_persistent(success);
    atomic_fetch_add_explicit(&initializations, 1, memory_order_relaxed);
}
lean_obj_res allocation_persistent_unit(void) {
    require(pthread_once(&once, initialize_success) == 0);
    require(lean_is_persistent(success) && !lean_is_exclusive(success));
    require(lean_io_result_is_ok(success) && lean_ctor_get(success, 0) == lean_box(0));
    lean_inc(success);
    return success;
}
LEAN_EXPORT lean_obj_res allocation_test_unit(void) {
    atomic_fetch_add_explicit(&test_calls, 1, memory_order_relaxed);
    return allocation_persistent_unit();
}
/* Only the separate concurrency executable calls this rendezvous. */
LEAN_EXPORT lean_obj_res allocation_test_gate(void) {
    require(pthread_mutex_lock(&gate_lock) == 0);
    require(arrived < 8);
    for (unsigned i = 0; i < arrived; ++i) require(!pthread_equal(workers[i], pthread_self()));
    workers[arrived++] = pthread_self();
    if (arrived == 8) require(pthread_cond_broadcast(&gate_ready) == 0);
    while (arrived < 8) require(pthread_cond_wait(&gate_ready, &gate_lock) == 0);
    require(pthread_mutex_unlock(&gate_lock) == 0);
    return lean_io_result_mk_ok(lean_box(0));
}
LEAN_EXPORT lean_obj_res allocation_test_error(void) {
    return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string("persistent experiment expected error")));
}
LEAN_EXPORT lean_obj_res allocation_test_validate(uint32_t expected) {
    require(atomic_load_explicit(&initializations, memory_order_relaxed) == 1);
    require(atomic_load_explicit(&test_calls, memory_order_relaxed) == expected);
    require(arrived == 8);
    require(lean_is_persistent(success) && !lean_is_exclusive(success));
    require(lean_io_result_is_ok(success) && lean_ctor_get(success, 0) == lean_box(0));
    printf("{\"persistent_thread_test\":\"passed\",\"workers\":8,\"initializations\":1,\"calls\":%u}\n",expected);
    return lean_io_result_mk_ok(lean_box(0));
}
