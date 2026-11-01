#include "gemm.h"
#include "ffi_result.h"

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
    if (status == VS_OK) return vastitas_io_unit_success();
    return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string(vstorage_error(status))));
}

LEAN_EXPORT lean_obj_res vastitas_gemm_execute_scaled(b_lean_obj_arg arena,
        uint32_t left, uint64_t left_offset, uint64_t left_rows, uint64_t left_columns,
        uint64_t left_leading, uint8_t left_transposed, uint8_t conjugate_left,
        uint32_t right, uint64_t right_offset, uint64_t right_rows, uint64_t right_columns,
        uint64_t right_leading, uint8_t right_transposed, uint8_t conjugate_right,
        uint32_t output, uint64_t output_offset, uint64_t output_rows, uint64_t output_columns,
        uint64_t output_leading, uint8_t output_transposed, uint8_t mode,
        uint8_t alpha_kind, uint8_t alpha_scalar, uint64_t alpha_real, uint64_t alpha_imaginary,
        uint32_t alpha_allocation, uint64_t alpha_offset,
        uint8_t beta_kind, uint8_t beta_scalar, uint64_t beta_real, uint64_t beta_imaginary,
        uint32_t beta_allocation, uint64_t beta_offset) {
    VStorageStatus status = vgemm_execute_scaled(lean_get_external_data(arena),
        left, (VStorageLayout){left_offset,left_rows,left_columns,left_leading,left_transposed}, conjugate_left,
        right, (VStorageLayout){right_offset,right_rows,right_columns,right_leading,right_transposed}, conjugate_right,
        output, (VStorageLayout){output_offset,output_rows,output_columns,output_leading,output_transposed},
        (VGemmMode)mode,
        (VGemmCoefficient){(VGemmCoefficientKind)alpha_kind,alpha_scalar,alpha_real,alpha_imaginary,alpha_allocation,alpha_offset},
        (VGemmCoefficient){(VGemmCoefficientKind)beta_kind,beta_scalar,beta_real,beta_imaginary,beta_allocation,beta_offset}, NULL);
    if (status == VS_OK) return vastitas_io_unit_success();
    return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string(vstorage_error(status))));
}

LEAN_EXPORT lean_obj_res vastitas_diagonal_pair(b_lean_obj_arg arena,
        uint32_t left, uint64_t left_offset, uint64_t left_rows, uint64_t left_columns,
        uint64_t left_leading, uint8_t left_transposed,
        uint32_t right, uint64_t right_offset, uint64_t right_rows, uint64_t right_columns,
        uint64_t right_leading, uint8_t right_transposed,
        uint32_t output, uint64_t output_offset, uint64_t output_rows, uint64_t output_columns,
        uint64_t output_leading, uint8_t output_transposed,
        uint32_t scratch, uint64_t scratch_offset, uint64_t scratch_rows, uint64_t scratch_columns,
        uint64_t scratch_leading, uint8_t scratch_transposed,
        uint8_t uniform, b_lean_obj_arg diagonal, uint8_t conjugate_left, uint8_t conjugate_right) {
    VStorageStatus status = vgemm_diagonal_pair(lean_get_external_data(arena),
        left, (VStorageLayout){left_offset,left_rows,left_columns,left_leading,left_transposed},
        right, (VStorageLayout){right_offset,right_rows,right_columns,right_leading,right_transposed},
        output, (VStorageLayout){output_offset,output_rows,output_columns,output_leading,output_transposed},
        scratch, (VStorageLayout){scratch_offset,scratch_rows,scratch_columns,scratch_leading,scratch_transposed},
        (VDiagonal){lean_sarray_cptr(diagonal),lean_sarray_size(diagonal),uniform}, conjugate_left, conjugate_right, NULL);
    if (status == VS_OK) return vastitas_io_unit_success();
    return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string(vstorage_error(status))));
}
