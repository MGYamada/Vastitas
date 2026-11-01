/* Exercise the real shared result through generated Lean callers. */
#include "ffi_result.h"
#include <stdatomic.h>

static _Thread_local unsigned char worker_token;
static _Atomic(void *) workers[8];
static _Atomic(unsigned) arrived;
static _Atomic(lean_object *) observed;
static _Atomic(unsigned) calls;
static void require(int valid) {
    if (!valid) lean_internal_panic("shared FFI result invariant failed");
}

LEAN_EXPORT lean_obj_res vastitas_test_result_gate(void) {
    unsigned slot = atomic_fetch_add(&arrived, 1);
    require(slot < 8);
    atomic_store(&workers[slot], &worker_token);
    /* All eight workers stay alive at this rendezvous, so distinct TLS
     * addresses establish distinct threads without host-specific headers. */
    for (unsigned i = 0; i < 8; ++i) {
        void *other;
        while ((other = atomic_load(&workers[i])) == NULL) {}
        require(i == slot || other != &worker_token);
    }
    return lean_io_result_mk_ok(lean_box(0));
}

LEAN_EXPORT lean_obj_res vastitas_test_result_probe(void) {
    lean_object *result = vastitas_io_unit_success();
    require(lean_is_persistent(result) && !lean_is_exclusive(result));
    require(lean_io_result_is_ok(result) && lean_ctor_get(result, 0) == lean_box(0));
    lean_object *expected = NULL;
    if (!atomic_compare_exchange_strong(&observed, &expected, result))
        require(expected == result);
    atomic_fetch_add(&calls, 1);
    return result;
}

LEAN_EXPORT lean_obj_res vastitas_test_result_validate(uint32_t expected) {
    require(atomic_load(&calls) == expected);
    lean_object *result = atomic_load(&observed);
    require(result && lean_is_persistent(result) && !lean_is_exclusive(result));
    require(lean_io_result_is_ok(result) && lean_ctor_get(result, 0) == lean_box(0));
    return lean_io_result_mk_ok(lean_box(0));
}
