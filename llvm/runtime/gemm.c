#include "storage_abi.h"
#include "gemm.h"

/* The checked LLVM opcode flattens each view and coefficient into i64 words.
 * Narrow only after validating the fields used by the host C ABI. */
int32_t vq_storage_gemm(VStorageArena *arena, uint64_t element,
        uint64_t left, uint64_t left_offset, uint64_t left_rows, uint64_t left_columns,
        uint64_t left_leading, uint64_t left_transposed, uint64_t conjugate_left,
        uint64_t right, uint64_t right_offset, uint64_t right_rows, uint64_t right_columns,
        uint64_t right_leading, uint64_t right_transposed, uint64_t conjugate_right,
        uint64_t output, uint64_t output_offset, uint64_t rows, uint64_t columns, uint64_t leading, uint64_t output_transposed,
        uint64_t mode,
        uint64_t alpha_kind, uint64_t alpha_scalar, uint64_t alpha_real, uint64_t alpha_imaginary,
        uint64_t alpha_allocation, uint64_t alpha_offset,
        uint64_t beta_kind, uint64_t beta_scalar, uint64_t beta_real, uint64_t beta_imaginary,
        uint64_t beta_allocation, uint64_t beta_offset) {
    if (left > UINT32_MAX || right > UINT32_MAX || output > UINT32_MAX ||
        alpha_allocation > UINT32_MAX || beta_allocation > UINT32_MAX) return checked(VS_HANDLE);
    if (left_transposed > 1 || right_transposed > 1 || output_transposed != 0) return checked(VS_LAYOUT);
    if (element > VS_COMPLEX_F32 || alpha_scalar > VS_COMPLEX_F32 || beta_scalar > VS_COMPLEX_F32)
        return checked(VS_SCALAR);
    if (conjugate_left > 1 || conjugate_right > 1 || mode > VGEMM_ACCUMULATE ||
        alpha_kind > VGEMM_VIEW || beta_kind > VGEMM_VIEW) return checked(VS_OPERATION);
    const VGemmCoefficient alpha = {(VGemmCoefficientKind)alpha_kind, (uint8_t)alpha_scalar,
                                    alpha_real, alpha_imaginary, (uint32_t)alpha_allocation, alpha_offset};
    const VGemmCoefficient beta = {(VGemmCoefficientKind)beta_kind, (uint8_t)beta_scalar,
                                   beta_real, beta_imaginary, (uint32_t)beta_allocation, beta_offset};
    return checked(vgemm_execute_scaled_as(arena, (int)element,
        (uint32_t)left, view(left_offset, left_rows, left_columns, left_leading, left_transposed), (uint8_t)conjugate_left,
        (uint32_t)right, view(right_offset, right_rows, right_columns, right_leading, right_transposed), (uint8_t)conjugate_right,
        (uint32_t)output, view(output_offset, rows, columns, leading, output_transposed), (VGemmMode)mode, alpha, beta, NULL));
}

int32_t vq_storage_diagonal_pair(VStorageArena *arena, uint64_t element,
        uint64_t left, uint64_t l_offset, uint64_t l_rows, uint64_t l_cols, uint64_t l_ld, uint64_t l_transposed,
        uint64_t right, uint64_t r_offset, uint64_t r_rows, uint64_t r_cols, uint64_t r_ld, uint64_t r_transposed,
        uint64_t output, uint64_t o_offset, uint64_t o_rows, uint64_t o_cols, uint64_t o_ld, uint64_t o_transposed,
        uint64_t scratch, uint64_t s_offset, uint64_t s_rows, uint64_t s_cols, uint64_t s_ld, uint64_t s_transposed,
        uint64_t conj_left, uint64_t conj_right, const uint8_t *data, uint64_t bytes, uint64_t uniform) {
    if (left > UINT32_MAX || right > UINT32_MAX || output > UINT32_MAX || scratch > UINT32_MAX)
        return checked(VS_HANDLE);
    if (l_transposed > 1 || r_transposed > 1 || o_transposed || s_transposed || conj_left > 1 || conj_right > 1)
        return checked(VS_OPERATION);
    const VStorageLayout l = view(l_offset, l_rows, l_cols, l_ld, l_transposed);
    VDiagonal diagonal;
    VStorageStatus status = diagonal_element(arena, element, (uint32_t)left, l);
    if (status != VS_OK) return checked(status);
    status = diagonal_descriptor(data, bytes, uniform, &diagonal);
    if (status != VS_OK) return checked(status);
    return checked(vgemm_diagonal_pair(arena, (uint32_t)left, l,
        (uint32_t)right, view(r_offset, r_rows, r_cols, r_ld, r_transposed),
        (uint32_t)output, view(o_offset, o_rows, o_cols, o_ld, 0),
        (uint32_t)scratch, view(s_offset, s_rows, s_cols, s_ld, 0),
        diagonal, (uint8_t)conj_left, (uint8_t)conj_right, NULL));
}
