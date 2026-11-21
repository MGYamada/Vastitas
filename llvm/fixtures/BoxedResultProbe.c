#include <lean/lean.h>
#include <stdio.h>
#include <stdlib.h>

extern uint32_t original_exit_status(lean_obj_arg value);

uint32_t vastitas_exit_status_v1(lean_obj_arg value) {
    const char *digits = getenv("VASTITAS_TEST_EXPECT_INTEGER");
    if (digits == NULL) abort();
    lean_obj_res expected = lean_cstr_to_int(digits);
    puts(lean_int_dec_eq(value, expected) ? "match" : "mismatch");
    lean_dec(expected);
    return original_exit_status(value);
}
