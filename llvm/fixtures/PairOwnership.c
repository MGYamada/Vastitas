#include <lean/lean.h>

extern lean_obj_res vq_exact(b_lean_obj_arg pair);

/* The generated export swaps the fields of its borrowed pair. The caller
   holds each heap integer independently of both the argument and the result. */
static int check_swap(b_lean_obj_arg left, b_lean_obj_arg right) {
    int left_rc = lean_internal_get_rc(left);
    int right_rc = lean_internal_get_rc(right);
    int copies = left == right ? 2 : 1;
    lean_obj_res input = lean_alloc_ctor(0, 2, 0);
    lean_inc(left);
    lean_ctor_set(input, 0, left);
    lean_inc(right);
    lean_ctor_set(input, 1, right);

    lean_obj_res output = vq_exact(input);
    int ok = lean_internal_get_rc(input) == 1 && lean_ctor_get(input, 0) == left &&
        lean_ctor_get(input, 1) == right && lean_ctor_get(output, 0) == right &&
        lean_ctor_get(output, 1) == left && lean_internal_get_rc(left) == left_rc + 2 * copies &&
        lean_internal_get_rc(right) == right_rc + 2 * copies;
    lean_dec(input);
    ok = ok && lean_internal_get_rc(left) == left_rc + copies &&
        lean_internal_get_rc(right) == right_rc + copies;
    lean_dec(output);
    return ok && lean_internal_get_rc(left) == left_rc && lean_internal_get_rc(right) == right_rc;
}

uint8_t vq_pair_ownership(uint8_t use_nat) {
    const char *digits = "340282366920938463463374607431768211457";
    lean_obj_res left = use_nat ? lean_cstr_to_nat(digits) : lean_cstr_to_int("-340282366920938463463374607431768211457");
    lean_obj_res right = use_nat ? lean_cstr_to_nat("340282366920938463463374607431768211456") : lean_cstr_to_int(digits);
    int ok = !lean_is_scalar(left) && !lean_is_scalar(right) &&
        check_swap(left, right) && check_swap(left, left);
    lean_dec(right);
    lean_dec(left);
    return ok;
}
