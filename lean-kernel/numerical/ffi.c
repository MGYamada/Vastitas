#include "gemm.h"
#include <lean/lean.h>

/* The borrowed Arena is the same external object created by the storage
 * runtime. The compiler emits this synchronous call only after replaying its
 * resource schedule. Physical preflight still runs against the actual arena. */
LEAN_EXPORT lean_obj_res vastitas_gemm_execute(b_lean_obj_arg arena,
        uint32_t left, uint64_t left_offset, uint64_t left_rows, uint64_t left_columns,
        uint64_t left_leading, uint8_t left_transposed, uint8_t conjugate_left,
        uint32_t right, uint64_t right_offset, uint64_t right_rows, uint64_t right_columns,
        uint64_t right_leading, uint8_t right_transposed, uint8_t conjugate_right,
        uint32_t output, uint64_t output_offset, uint64_t output_rows, uint64_t output_columns,
        uint64_t output_leading, uint8_t output_transposed, uint8_t mode) {
    VStorageStatus status = vgemm_execute(lean_get_external_data(arena),
        left, (VStorageLayout){left_offset,left_rows,left_columns,left_leading,left_transposed}, conjugate_left,
        right, (VStorageLayout){right_offset,right_rows,right_columns,right_leading,right_transposed}, conjugate_right,
        output, (VStorageLayout){output_offset,output_rows,output_columns,output_leading,output_transposed},
        (VGemmMode)mode, NULL);
    if (status == VS_OK) return lean_io_result_mk_ok(lean_box(0));
    return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string(vstorage_error(status))));
}
