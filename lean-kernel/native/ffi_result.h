#ifndef VASTITAS_FFI_RESULT_H
#define VASTITAS_FFI_RESULT_H

#include <lean/lean.h>

/* Immutable IO Unit success shared by the storage and numerical FFI. Errors
 * and results carrying owned values must keep their ordinary fresh results. */
LEAN_EXPORT lean_obj_res vastitas_io_unit_success(void);

#endif
