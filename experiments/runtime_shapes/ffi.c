/* Appended to experiment-private FFI only. Lean 4.35 erases the IO world. */
void bench_config(uint64_t,uint64_t,uint64_t,uint64_t);
void bench_begin(uint32_t,uint64_t,uint8_t);
void bench_stop(void); void bench_report(void); void bench_guard(void); void bench_narrow(void);
void bench_verify(VStorageArena *);void bench_c_run(uint32_t,uint64_t,uint8_t);
#define UNIT return lean_io_result_mk_ok(lean_box(0))
LEAN_EXPORT lean_obj_res shape_config(uint64_t m,uint64_t k,uint64_t n,uint64_t p){bench_config(m,k,n,p);UNIT;}
LEAN_EXPORT lean_obj_res shape_begin(uint32_t s,uint64_t n,uint8_t v){bench_begin(s,n,v);UNIT;}
LEAN_EXPORT lean_obj_res shape_stop(void){bench_stop();UNIT;}
LEAN_EXPORT lean_obj_res shape_report(void){bench_report();UNIT;}
LEAN_EXPORT lean_obj_res shape_guard(void){bench_guard();UNIT;}
LEAN_EXPORT lean_obj_res shape_narrow(void){bench_narrow();UNIT;}
LEAN_EXPORT lean_obj_res shape_verify(b_lean_obj_arg a){bench_verify(lean_get_external_data(a));UNIT;}
LEAN_EXPORT lean_obj_res shape_c_run(uint32_t s,uint64_t n,uint8_t v){bench_c_run(s,n,v);UNIT;}
