/* Boxed integer and pair ABI. Arithmetic returns an owned object. Predicates borrow both inputs and return 0 or 1 as a C uint32_t. */
#include <lean/lean.h>

lean_obj_res vastitas_nat_decimal_v1(const char *digits) { return lean_cstr_to_nat(digits); }
lean_obj_res vastitas_int_decimal_v1(const char *digits) { return lean_cstr_to_int(digits); }
void vastitas_retain_v1(b_lean_obj_arg value) { lean_inc(value); }
void vastitas_release_v1(lean_obj_arg value) { lean_dec(value); }

lean_obj_res vastitas_nat_add_v1(b_lean_obj_arg a, b_lean_obj_arg b) { return lean_nat_add(a, b); }
lean_obj_res vastitas_nat_sub_v1(b_lean_obj_arg a, b_lean_obj_arg b) { return lean_nat_sub(a, b); }
lean_obj_res vastitas_nat_mul_v1(b_lean_obj_arg a, b_lean_obj_arg b) { return lean_nat_mul(a, b); }
lean_obj_res vastitas_nat_div_v1(b_lean_obj_arg a, b_lean_obj_arg b) { return lean_nat_div(a, b); }
lean_obj_res vastitas_int_add_v1(b_lean_obj_arg a, b_lean_obj_arg b) { return lean_int_add(a, b); }
lean_obj_res vastitas_int_sub_v1(b_lean_obj_arg a, b_lean_obj_arg b) { return lean_int_sub(a, b); }
lean_obj_res vastitas_int_mul_v1(b_lean_obj_arg a, b_lean_obj_arg b) { return lean_int_mul(a, b); }
lean_obj_res vastitas_int_div_v1(b_lean_obj_arg a, b_lean_obj_arg b) { return lean_int_ediv(a, b); }
lean_obj_res vastitas_int_neg_v1(b_lean_obj_arg a) { return lean_int_neg(a); }

uint32_t vastitas_nat_eq_v1(b_lean_obj_arg a, b_lean_obj_arg b) { return lean_nat_dec_eq(a, b); }
uint32_t vastitas_nat_ne_v1(b_lean_obj_arg a, b_lean_obj_arg b) { return !lean_nat_dec_eq(a, b); }
uint32_t vastitas_nat_lt_v1(b_lean_obj_arg a, b_lean_obj_arg b) { return lean_nat_dec_lt(a, b); }
uint32_t vastitas_nat_le_v1(b_lean_obj_arg a, b_lean_obj_arg b) { return lean_nat_dec_le(a, b); }
uint32_t vastitas_nat_gt_v1(b_lean_obj_arg a, b_lean_obj_arg b) { return lean_nat_dec_lt(b, a); }
uint32_t vastitas_nat_ge_v1(b_lean_obj_arg a, b_lean_obj_arg b) { return lean_nat_dec_le(b, a); }

uint32_t vastitas_int_eq_v1(b_lean_obj_arg a, b_lean_obj_arg b) { return lean_int_dec_eq(a, b); }
uint32_t vastitas_int_ne_v1(b_lean_obj_arg a, b_lean_obj_arg b) { return !lean_int_dec_eq(a, b); }
uint32_t vastitas_int_lt_v1(b_lean_obj_arg a, b_lean_obj_arg b) { return lean_int_dec_lt(a, b); }
uint32_t vastitas_int_le_v1(b_lean_obj_arg a, b_lean_obj_arg b) { return lean_int_dec_le(a, b); }
uint32_t vastitas_int_gt_v1(b_lean_obj_arg a, b_lean_obj_arg b) { return lean_int_dec_lt(b, a); }
uint32_t vastitas_int_ge_v1(b_lean_obj_arg a, b_lean_obj_arg b) { return lean_int_dec_le(b, a); }

lean_obj_res vastitas_nat_to_int_v1(b_lean_obj_arg a) {
    /* lean_nat_to_int consumes one reference, including for a heap Nat. */
    lean_inc(a);
    return lean_nat_to_int(a);
}

lean_obj_res vastitas_nat_int_div_v1(b_lean_obj_arg a, b_lean_obj_arg b) {
    lean_obj_res numerator = vastitas_nat_to_int_v1(a);
    lean_obj_res quotient = lean_int_ediv(numerator, b);
    lean_dec(numerator);
    return quotient;
}

lean_obj_res vastitas_int_nat_div_v1(b_lean_obj_arg a, b_lean_obj_arg b) {
    lean_obj_res denominator = vastitas_nat_to_int_v1(b);
    lean_obj_res quotient = lean_int_ediv(a, denominator);
    lean_dec(denominator);
    return quotient;
}

/* Each field owns a reference, including when both fields alias one input. */
static lean_obj_res make_pair(b_lean_obj_arg a, b_lean_obj_arg b) {
    lean_obj_res pair = lean_alloc_ctor(0, 2, 0);
    lean_inc(a);
    lean_ctor_set(pair, 0, a);
    lean_inc(b);
    lean_ctor_set(pair, 1, b);
    return pair;
}

static lean_obj_res pair_field(b_lean_obj_arg pair, unsigned index) {
    b_lean_obj_res value = lean_ctor_get(pair, index);
    lean_inc(value);
    return value;
}

lean_obj_res vastitas_nat_pair_v1(b_lean_obj_arg a, b_lean_obj_arg b) { return make_pair(a, b); }
lean_obj_res vastitas_int_pair_v1(b_lean_obj_arg a, b_lean_obj_arg b) { return make_pair(a, b); }
lean_obj_res vastitas_nat_pair_first_v1(b_lean_obj_arg p) { return pair_field(p, 0); }
lean_obj_res vastitas_nat_pair_second_v1(b_lean_obj_arg p) { return pair_field(p, 1); }
lean_obj_res vastitas_int_pair_first_v1(b_lean_obj_arg p) { return pair_field(p, 0); }
lean_obj_res vastitas_int_pair_second_v1(b_lean_obj_arg p) { return pair_field(p, 1); }

/* This hosted entry calls boxed runtime primitives. It has no generated
   Lean modules or IO initializers. This is the pinned generated-C declaration. */
extern void lean_initialize_runtime_module(void);
void vastitas_initialize_v1(void) {
    lean_initialize_runtime_module();
    lean_io_mark_end_initialization();
}

/* Consume the entry's owned Int. Euclidean remainder is an immediate in [0,255]. */
uint32_t vastitas_exit_status_v1(lean_obj_arg value) {
    lean_obj_res low = lean_int_emod(value, lean_int_to_int(256));
    uint32_t status = (uint32_t)lean_unbox(low);
    lean_dec(low);
    lean_dec(value);
    return status;
}
