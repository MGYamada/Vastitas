/* Differential-test entry for the production one-cell GEMM adapter. Each
 * fixture supplies alpha, beta, the old cell, then pairs of input cells.
 * Every component crosses this boundary as an unsigned bit pattern. */
#include "gemm.h"
#include <assert.h>
#include <inttypes.h>
#include <stdio.h>
#include <string.h>

static void check_dot_cell(uint8_t scalar, uint8_t conjugate_left, uint8_t conjugate_right,
                           uint64_t n, const uint64_t *words, uint64_t result[2]) {
    const unsigned bytes = vstorage_element_bytes(scalar);
    const VStorageLayout row = {0, 1, n, 1, 0}, col = {0, n, 1, n ? n : 1, 0};
    const VStorageLayout cell = {0, 1, 1, 1, 0};
    const VGemmCoefficient alpha = {VGEMM_LITERAL, scalar, words[0], words[1], 0, 0};
    const VGemmCoefficient beta = {VGEMM_LITERAL, scalar, words[2], words[3], 0, 0};
    VStorageArena *arena = vstorage_new((2 * n + 1) * bytes);
    assert(arena != NULL);
    assert(vstorage_allocate(arena, 0, scalar, n) == VS_OK);
    assert(vstorage_allocate(arena, 1, scalar, n) == VS_OK);
    assert(vstorage_allocate(arena, 2, scalar, 1) == VS_OK);
    assert(vstorage_store(arena, 2, cell, 0, 0, scalar, words[4], words[5]) == VS_OK);
    for (uint64_t i = 0; i < n; ++i) {
        const uint64_t *p = words + 6 + 4 * i;
        assert(vstorage_store(arena, 0, row, 0, i, scalar, p[0], p[1]) == VS_OK);
        assert(vstorage_store(arena, 1, col, i, 0, scalar, p[2], p[3]) == VS_OK);
    }
    VGemmReport report;
    assert(vgemm_execute_scaled_as(arena, scalar, 0, row, conjugate_left, 1, col, conjugate_right,
                                   2, cell, VGEMM_ACCUMULATE, alpha, beta, &report) == VS_OK);
    assert(report.kernel_calls == (n != 0));
    VStorageDense output;
    assert(vstorage_prepare_dense(arena, 2, cell, &output) == VS_OK);
    for (unsigned i = 0; i < 1u + vstorage_is_complex(scalar); ++i) {
        if (vstorage_component_bytes(scalar) == 4) {
            uint32_t value;
            memcpy(&value, (const uint8_t *)output.data + 4 * i, sizeof(value));
            result[i] = value;
        } else {
            memcpy(&result[i], (const uint8_t *)output.data + 8 * i, sizeof(result[i]));
        }
    }
    vstorage_delete(arena);
}

int main(void) {
    enum { max_terms = 4 };
    unsigned tag, cl, cr, n;
    int fields;
    while ((fields = scanf("%u%u%u%u", &tag, &cl, &cr, &n)) != EOF) {
        if (fields != 4 || tag > VS_COMPLEX_F32 || cl > 1 || cr > 1 || n > max_terms) return 1;
        uint64_t words[6 + 4 * max_terms], result[2] = {0};
        for (unsigned i = 0; i < 6 + 4*n; ++i)
            if (scanf("%" SCNu64, &words[i]) != 1) return 1;
        check_dot_cell((uint8_t)tag, (uint8_t)cl, (uint8_t)cr, n, words, result);
        printf("%" PRIu64, result[0]);
        if (vstorage_is_complex((uint8_t)tag)) printf(" %" PRIu64, result[1]);
        putchar('\n');
    }
    return ferror(stdin) ? 1 : 0;
}
