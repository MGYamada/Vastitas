#ifndef VASTITAS_GEMM_H
#define VASTITAS_GEMM_H

#include "storage.h"

/* Internal numerical adapter, not public source/wire authority. Callers must
 * supply independently checked mathematical types and read/write/init rights.
 * Complex storage is two adjacent binary64 components. The compatibility
 * entry uses alpha=1 and beta=0 (overwrite) or 1 (accumulate). */
typedef enum { VGEMM_OVERWRITE, VGEMM_ACCUMULATE } VGemmMode;
typedef struct { uint64_t kernel_calls, written_bytes; } VGemmReport;
typedef enum { VGEMM_DEFAULT, VGEMM_LITERAL, VGEMM_VIEW } VGemmCoefficientKind;
typedef struct {
    VGemmCoefficientKind kind;
    uint8_t scalar;
    uint64_t real, imaginary;
    uint32_t allocation;
    uint64_t offset;
} VGemmCoefficient;

const char *vgemm_configuration(void);
VStorageStatus vgemm_backend_check(void);
VStorageStatus vgemm_execute(VStorageArena *arena,
    uint32_t left, VStorageLayout left_view, uint8_t left_conjugate,
    uint32_t right, VStorageLayout right_view, uint8_t right_conjugate,
    uint32_t output, VStorageLayout output_view, VGemmMode mode, VGemmReport *report);

/* Views read exactly one live scalar before any output write. They must be
 * initialized by the checked caller and physically disjoint from output.
 * Overwrite requires default beta and never reads previous output contents. */
VStorageStatus vgemm_execute_scaled(VStorageArena *arena,
    uint32_t left, VStorageLayout left_view, uint8_t left_conjugate,
    uint32_t right, VStorageLayout right_view, uint8_t right_conjugate,
    uint32_t output, VStorageLayout output_view, VGemmMode mode,
    VGemmCoefficient alpha, VGemmCoefficient beta, VGemmReport *report);

#endif
