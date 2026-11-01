#ifndef VASTITAS_SOURCE_ALLOCATOR_H
#define VASTITAS_SOURCE_ALLOCATOR_H
#include <lean/lean.h>
void source_allocator_mark(unsigned next);
void source_allocator_error(b_lean_obj_arg value);
void source_allocator_finish(void);
void source_allocator_report(void);
#endif
