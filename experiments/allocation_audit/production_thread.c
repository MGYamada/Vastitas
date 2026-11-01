/* Test only: call the actual production once helper from dedicated Lean tasks.
 * The private FFI copy adds one atomic observation inside its real initializer.
 * No pthread_once prototype, observer pointer table or replacement singleton. */
#include "ffi_result.h"
#include "storage.h"
#include <stdatomic.h>
#include <stdio.h>

extern lean_obj_res vastitas_storage_new(uint64_t);
extern lean_obj_res vastitas_storage_stats(b_lean_obj_arg);
extern lean_obj_res vastitas_storage_drop(b_lean_obj_arg, uint32_t);
static _Thread_local unsigned char worker_token;
static _Atomic(void *) workers[8];
static _Atomic(unsigned) arrived, initializations, calls;
static _Atomic(lean_object *) initialized;

static void require(int valid) {
    if (!valid) lean_internal_panic("production allocation audit thread invariant failed");
}
void allocation_thread_initialize(lean_object *result) {
    require(lean_is_persistent(result) && !lean_is_exclusive(result));
    require(atomic_fetch_add(&initializations, 1) == 0);
    atomic_store(&initialized, result);
}
LEAN_EXPORT lean_obj_res allocation_test_gate(void) {
    unsigned slot = atomic_fetch_add(&arrived, 1);
    require(slot < 8);
    atomic_store(&workers[slot], &worker_token);
    for (unsigned i = 0; i < 8; ++i) {
        void *other;
        while ((other = atomic_load(&workers[i])) == NULL) {}
        require(i == slot || other != &worker_token);
    }
    return lean_io_result_mk_ok(lean_box(0));
}
LEAN_EXPORT lean_obj_res allocation_test_unit(void) {
    lean_object *result = vastitas_io_unit_success();
    require(result == atomic_load(&initialized));
    require(lean_is_persistent(result) && !lean_is_exclusive(result));
    require(lean_io_result_is_ok(result) && lean_ctor_get(result, 0) == lean_box(0));
    atomic_fetch_add(&calls, 1);
    return result;
}
LEAN_EXPORT lean_obj_res allocation_test_error(void) {
    lean_object *owner = vastitas_storage_new(1024);
    require(lean_io_result_is_ok(owner));
    lean_object *error = vastitas_storage_drop(lean_ctor_get(owner, 0), 0);
    require(!lean_io_result_is_ok(error) && !lean_is_persistent(error));
    lean_dec(owner); /* the error does not retain its temporary arena */
    return error;
}
static void fresh_pair(lean_object *a, lean_object *b, int is_ok) {
    require(a != b && lean_is_exclusive(a) && lean_is_exclusive(b));
    require(!lean_is_persistent(a) && !lean_is_persistent(b));
    require(lean_io_result_is_ok(a) == is_ok && lean_io_result_is_ok(b) == is_ok);
}
LEAN_EXPORT lean_obj_res allocation_test_validate(uint32_t expected) {
    require(atomic_load(&initializations) == 1 && atomic_load(&calls) == expected);
    require(atomic_load(&arrived) == 8);
    lean_object *result = atomic_load(&initialized);
    require(result && lean_is_persistent(result) && !lean_is_exclusive(result));
    require(lean_io_result_is_ok(result) && lean_ctor_get(result, 0) == lean_box(0));
    lean_object *a = vastitas_storage_new(1024), *b = vastitas_storage_new(1024);
    fresh_pair(a, b, 1);
    require(lean_ctor_get(a, 0) != lean_ctor_get(b, 0));
    lean_object *sa = vastitas_storage_stats(lean_ctor_get(a, 0));
    lean_object *sb = vastitas_storage_stats(lean_ctor_get(b, 0));
    fresh_pair(sa, sb, 1);
    require(lean_ctor_get(sa, 0) != lean_ctor_get(sb, 0));
    lean_object *ea = vastitas_storage_drop(lean_ctor_get(a, 0), 0);
    lean_object *eb = vastitas_storage_drop(lean_ctor_get(b, 0), 0);
    fresh_pair(ea, eb, 0);
    lean_dec(sa); lean_dec(sb); lean_dec(ea); lean_dec(eb); lean_dec(a); lean_dec(b);
    printf("{\"production_thread_test\":\"passed\",\"workers\":8,\"initializations\":1,\"calls\":%u,\"fresh_arena_results\":2,\"fresh_stats_results\":2,\"fresh_errors\":2}\n", expected);
    return lean_io_result_mk_ok(lean_box(0));
}
