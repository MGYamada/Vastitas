/* Foreign ABI qualification only; this is not a production adapter. */
#include <lean/lean.h>
#include <cblas.h>
#include <stdio.h>
#include <string.h>

extern lean_object *initialize_RuntimeProbe(uint8_t builtin);
extern lean_object *vastitas_qual_indexed(lean_object *n);

/* Borrowed inputs, owned result. LLVM crosses only these fixed C signatures. */
lean_object *vq_nat_add(lean_object *a, lean_object *b) { return lean_nat_add(a, b); }
lean_object *vq_nat_mul(lean_object *a, lean_object *b) { return lean_nat_mul(a, b); }
lean_object *vq_nat_sub_five(b_lean_obj_arg a) { return lean_nat_sub(a, lean_box(5)); }
lean_object *vq_int_sub_five(b_lean_obj_arg a) { return lean_int_sub(a, lean_int64_to_int(5)); }
lean_object *vq_nat_to_int_owned(lean_obj_arg a) { return lean_nat_to_int(a); }
void vq_retain(b_lean_obj_arg value) { lean_inc(value); }
lean_obj_res vq_int_ediv(b_lean_obj_arg a, b_lean_obj_arg b) { return lean_int_ediv(a, b); }
void vq_release(lean_object *value) { lean_dec(value); }

int vq_initialize(void) {
    lean_object *result = initialize_RuntimeProbe(1);
    int failed = lean_io_result_is_error(result);
    lean_dec(result);
    return failed;
}

lean_object *vq_big(void) { return lean_cstr_to_nat("18446744073709551616"); }

int vq_check_big(lean_object *value) {
    lean_object *expected = lean_cstr_to_nat("340282366920938463463374607431768211456");
    int failed = !lean_nat_dec_eq(value, expected);
    lean_dec(expected);
    return failed;
}

int vq_check_integer(void) {
    lean_object *n = lean_int64_to_int(-7), *d = lean_int64_to_int(3);
    lean_object *q = lean_int_ediv(n, d), *zero = lean_int_ediv(n, lean_box(0));
    lean_object *monus = lean_nat_sub(lean_box(2), lean_box(5));
    int failed = !lean_int_dec_eq(q, lean_int64_to_int(-3)) ||
        !lean_int_dec_eq(zero, lean_box(0)) || !lean_nat_dec_eq(monus, lean_box(0));
    lean_dec(n); lean_dec(d); lean_dec(q); lean_dec(zero); lean_dec(monus);
    return failed;
}

int vq_check_indexed(void) {
    lean_object *result = vastitas_qual_indexed(lean_box(7));
    int failed = !lean_nat_dec_eq(result, lean_box(7));
    lean_dec(result);
    return failed;
}

int vq_check_blas(void) {
    const char *configuration = openblas_get_config();
    if (!configuration || strncmp(configuration, "OpenBLAS 0.3.34 ", 16) != 0 ||
        openblas_get_parallel() != 0 || strstr(configuration, "USE64BITINT") ||
        !strstr(configuration, " USE_LOCKING ") || sizeof(blasint) != 4) return 1;
    const float as = 2.0f, bs = 3.0f;
    float cs = 0.0f;
    const double ad = 2.0, bd = 3.0;
    double cd = 0.0;
    const float ac[2] = {2.0f, 1.0f}, bc[2] = {3.0f, -1.0f};
    const float onec[2] = {1.0f, 0.0f}, zeroc[2] = {0.0f, 0.0f};
    float cc[2] = {0.0f, 0.0f};
    const double az[2] = {2.0, 1.0}, bz[2] = {3.0, -1.0};
    const double onez[2] = {1.0, 0.0}, zeroz[2] = {0.0, 0.0};
    double cz[2] = {0.0, 0.0};
    cblas_sgemm(CblasRowMajor, CblasNoTrans, CblasNoTrans, 1, 1, 1,
        1.0f, &as, 1, &bs, 1, 0.0f, &cs, 1);
    cblas_dgemm(CblasRowMajor, CblasNoTrans, CblasNoTrans, 1, 1, 1,
        1.0, &ad, 1, &bd, 1, 0.0, &cd, 1);
    cblas_cgemm(CblasRowMajor, CblasNoTrans, CblasNoTrans, 1, 1, 1,
        onec, ac, 1, bc, 1, zeroc, cc, 1);
    cblas_zgemm(CblasRowMajor, CblasNoTrans, CblasNoTrans, 1, 1, 1,
        onez, az, 1, bz, 1, zeroz, cz, 1);
    if (cs != 6.0f || cd != 6.0 || cc[0] != 7.0f || cc[1] != 1.0f ||
        cz[0] != 7.0 || cz[1] != 1.0) return 1;
    printf("openblas=%s\n", configuration);
    return 0;
}

/* l_evaluate is compiled from FamilyComparison.lean by the pinned C emitter.
   For this signature both object inputs are borrowed; both evaluators return
   an owned Int. Test each against an independent decimal expectation too. */
extern lean_object *initialize_FamilyComparison(uint8_t builtin);
extern lean_obj_res l_evaluate(uint8_t flag, b_lean_obj_arg n, b_lean_obj_arg i);
extern lean_obj_res vq_family_evaluate(uint8_t flag, b_lean_obj_arg n, b_lean_obj_arg i);

extern lean_obj_res vq_div_nat_int(b_lean_obj_arg n, b_lean_obj_arg i);
extern lean_obj_res vq_div_int_nat(b_lean_obj_arg i, b_lean_obj_arg n);
extern lean_obj_res l_divNatInt(b_lean_obj_arg n, b_lean_obj_arg i);
extern lean_obj_res l_divIntNat(b_lean_obj_arg i, b_lean_obj_arg n);

static int check_mixed_division(void) {
    int failed = 0;
    const struct { const char *nat, *integer, *left_nat, *right_nat; } cases[] = {
        {"7", "-3", "-2", "-1"}, {"3", "-7", "0", "-3"},
        {"0", "-7", "0", "0"}, {"7", "0", "0", "0"},
        {"18446744073709551616", "-18446744073709551617", "0", "-2"}
    };
    for (size_t k = 0; k < sizeof cases / sizeof cases[0]; ++k) {
        lean_object *n = lean_cstr_to_nat(cases[k].nat), *i = lean_cstr_to_int(cases[k].integer);
        for (int left = 0; left < 2; ++left) {
            lean_object *a = left ? vq_div_nat_int(n, i) : vq_div_int_nat(i, n);
            lean_object *b = left ? l_divNatInt(n, i) : l_divIntNat(i, n);
            lean_object *want = lean_cstr_to_int(left ? cases[k].left_nat : cases[k].right_nat);
            failed |= !lean_int_dec_eq(a, want) || !lean_int_dec_eq(b, want);
            lean_dec(want); lean_dec(b); lean_dec(a);
        }
        lean_dec(i); lean_dec(n);
    }
    return failed;
}

int vq_check_family(void) {
    lean_object *init = initialize_FamilyComparison(1);
    int failed = lean_io_result_is_error(init);
    lean_dec(init);
    if (failed) return 1;
    const struct { const char *n, *i, *nat_result, *int_result; } cases[] = {
        {"2", "2", "0", "-3"},
        {"5", "0", "0", "-5"},
        {"18446744073709551616", "-18446744073709551616",
         "18446744073709551611", "-18446744073709551621"}
    };
    for (size_t k = 0; k < sizeof cases / sizeof cases[0]; ++k) {
        lean_object *n = lean_cstr_to_nat(cases[k].n), *i = lean_cstr_to_int(cases[k].i);
        for (uint8_t flag = 0; flag < 2; ++flag) {
            lean_object *expected = lean_cstr_to_int(flag ? cases[k].nat_result : cases[k].int_result);
            lean_object *reference = l_evaluate(flag, n, i), *actual = vq_family_evaluate(flag, n, i);
            failed |= !lean_int_dec_eq(reference, expected) || !lean_int_dec_eq(actual, expected);
            lean_dec(actual); lean_dec(reference); lean_dec(expected);
        }
        lean_dec(n); lean_dec(i);
    }
    return failed | check_mixed_division();
}
