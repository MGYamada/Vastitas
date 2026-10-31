/* Appended only to the private runtime's ffi.c; Lean 4.35 IO erases the world. */
void bench_begin(uint32_t, uint64_t, uint8_t);
void bench_stop(void);
void bench_report(void);
void bench_c_run(uint32_t, uint64_t, uint8_t);
void bench_verify(VStorageArena *, uint64_t);
LEAN_EXPORT lean_obj_res bench_begin_lean(uint32_t s, uint64_t n, uint8_t v) {
    bench_begin(s,n,v); return lean_io_result_mk_ok(lean_box(0));
}
LEAN_EXPORT lean_obj_res bench_stop_lean(void) { bench_stop(); return lean_io_result_mk_ok(lean_box(0)); }
LEAN_EXPORT lean_obj_res bench_report_lean(void) { bench_report(); return lean_io_result_mk_ok(lean_box(0)); }
LEAN_EXPORT lean_obj_res bench_c_run_lean(uint32_t s, uint64_t n, uint8_t v) {
    bench_c_run(s,n,v); return lean_io_result_mk_ok(lean_box(0));
}
LEAN_EXPORT lean_obj_res bench_verify_lean(b_lean_obj_arg arena, uint64_t n) {
    bench_verify(lean_get_external_data(arena),n); return lean_io_result_mk_ok(lean_box(0));
}
