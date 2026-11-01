/* Experiment-only hooks: pinned Lean public APIs, never object-layout writes. */
#ifndef VASTITAS_ALLOCATION_AUDIT_H
#define VASTITAS_ALLOCATION_AUDIT_H
#include <lean/lean.h>
void audit_phase(unsigned phase);
void audit_report(void);
void audit_finalize(void *data);
lean_obj_res audit_ok(lean_obj_arg value);
lean_obj_res audit_shared_create(void);
lean_obj_res audit_shared_return(lean_obj_arg value);
lean_obj_res audit_control_ok(lean_obj_arg value);
lean_obj_res audit_error(lean_obj_arg value);
lean_obj_res audit_ctor(unsigned tag, unsigned objects, unsigned scalars);
lean_obj_res audit_external(lean_external_class *cls, void *data);
void audit_dec(lean_obj_arg value);
void audit_dec_ref(lean_obj_arg value);
void audit_dec_known(lean_obj_arg value, unsigned fields);
#ifndef AUDIT_IMPLEMENTATION
#ifdef AUDIT_GENERATED_MAIN
#define lean_io_result_mk_ok audit_control_ok
#else
#define lean_io_result_mk_ok audit_ok
#endif
#define lean_io_result_mk_error audit_error
#define lean_alloc_ctor audit_ctor
#define lean_alloc_external audit_external
#define lean_dec audit_dec
#define lean_dec_ref audit_dec_ref
#define lean_dec_ref_known audit_dec_known
#endif
#endif
