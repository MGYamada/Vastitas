#ifndef VASTITAS_GEMM_H
#define VASTITAS_GEMM_H

#include "storage.h"

/* Internal numerical adapter, not public source/wire authority. Callers must
 * supply independently checked mathematical types and read/write/init rights.
 * This initial NativeFast profile fixes alpha=1 and beta=0 (overwrite) or 1
 * (accumulate). Complex storage is two adjacent binary64 components. */
typedef enum { VGEMM_OVERWRITE, VGEMM_ACCUMULATE } VGemmMode;
typedef struct { uint64_t kernel_calls, written_bytes; } VGemmReport;

const char *vgemm_configuration(void);
VStorageStatus vgemm_backend_check(void);
VStorageStatus vgemm_execute(VStorageArena *arena,
    uint32_t left, VStorageLayout left_view, uint8_t left_conjugate,
    uint32_t right, VStorageLayout right_view, uint8_t right_conjugate,
    uint32_t output, VStorageLayout output_view, VGemmMode mode, VGemmReport *report);

#endif
