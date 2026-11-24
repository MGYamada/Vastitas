#include <lean/lean.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

extern void lean_initialize_runtime_module(void);
extern uint32_t vq_exact(b_lean_obj_arg left, b_lean_obj_arg right);

static int references(b_lean_obj_arg value) {
    return lean_is_scalar(value) ? 0 : lean_internal_get_rc(value);
}

int main(int argc, char **argv) {
    if (argc != 5) return 2;
    lean_initialize_runtime_module();
    lean_io_mark_end_initialization();
    int natural = strcmp(argv[1], "Nat") == 0;
    int alias = strcmp(argv[4], "alias") == 0;
    if (alias && strcmp(argv[2], argv[3]) != 0) return 2;
    lean_object *a = natural ? lean_cstr_to_nat(argv[2]) : lean_cstr_to_int(argv[2]);
    lean_object *b = alias ? a : (natural ? lean_cstr_to_nat(argv[3]) : lean_cstr_to_int(argv[3]));
    /* Keep the objects shared while checking that the foreign callee borrows both. */
    lean_inc(a);
    if (!alias) lean_inc(b);
    int before_a = references(a), before_b = references(b);
    uint32_t answer = vq_exact(a, b);
    if (answer > 1 || references(a) != before_a || references(b) != before_b) return 3;
    lean_dec(a);
    lean_dec(a);
    if (!alias) {
        lean_dec(b);
        lean_dec(b);
    }
    puts(answer ? "42" : "7");
    return 0;
}
