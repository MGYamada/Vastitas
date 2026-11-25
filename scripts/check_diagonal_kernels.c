/* Replay the Lean diagonalScale and adjointCell results through the arena ABI. */
#include "diagonal.h"
#include <assert.h>
#include <inttypes.h>
#include <stdio.h>
#include <string.h>

static VDiagonal weight(uint8_t bytes[8], int64_t integer, unsigned uniform) {
    double value = (double)integer;
    uint64_t bits;
    memcpy(&bits, &value, sizeof(bits));
    for (unsigned i = 0; i < 8; ++i) bytes[i] = (uint8_t)(bits >> (8*i));
    return (VDiagonal){bytes, 8, (uint8_t)uniform};
}

static int agrees(uint64_t actual, uint64_t expected, uint8_t tag) {
    const int single = vstorage_component_bytes(tag) == 4;
    const uint64_t magnitude = single ? UINT32_MAX >> 1 : UINT64_MAX >> 1;
    const uint64_t inf = single ? UINT32_C(0x7f800000) : UINT64_C(0x7ff0000000000000);
    return actual == expected || ((actual & magnitude) > inf && (expected & magnitude) > inf);
}

static int expect(VStorageArena *arena, unsigned id, VStorageLayout out,
                  uint8_t tag, uint64_t re, uint64_t im) {
    uint64_t observed[2];
    VStorageStatus rc = vstorage_expect_observed(arena, id, out, 0, 0, tag, re, im, observed);
    return rc == VS_OK || (rc == VS_EXPECT && agrees(observed[0], re, tag) &&
                            agrees(observed[1], im, tag));
}

int main(void) {
    unsigned tag, conjugate, transpose, source_uniform, target_uniform;
    int64_t source, target;
    uint64_t re, im, sr, si, ar, ai;
    unsigned counts[4] = {0};
    int n;
    while ((n = scanf("%u%u%u%u%u%" SCNd64 "%" SCNd64 "%" SCNu64 "%" SCNu64
                      "%" SCNu64 "%" SCNu64 "%" SCNu64 "%" SCNu64, &tag, &conjugate,
                      &transpose, &source_uniform, &target_uniform, &source, &target,
                      &re, &im, &sr, &si, &ar, &ai)) != EOF) {
        if (n != 13 || tag > VS_COMPLEX_F32 || conjugate > 1 || transpose > 1 ||
            source_uniform > 1 || target_uniform > 1) return 1;
        VStorageArena *arena = vstorage_new(512);
        assert(arena);
        for (unsigned id = 0; id < 3; ++id) assert(vstorage_allocate(arena, id, tag, 3) == VS_OK);
        VStorageLayout in = {vstorage_element_bytes(tag), 1, 1, 3, transpose};
        VStorageLayout out = {vstorage_element_bytes(tag), 1, 1, 2, 0};
        uint8_t s[8], t[8];
        VDiagonal sw = weight(s, source, source_uniform), tw = weight(t, target, target_uniform);
        assert(vstorage_store(arena, 0, in, 0, 0, tag, re, im) == VS_OK);
        assert(vdiagonal_scale(arena, 0, in, 1, out, tw, conjugate) == VS_OK);
        assert(vdiagonal_adjoint(arena, 0, in, 2, out, sw, tw, conjugate) == VS_OK);
        int ok = expect(arena, 1, out, tag, sr, si) && expect(arena, 2, out, tag, ar, ai);
        vstorage_delete(arena);
        if (!ok) {
            fprintf(stderr, "diagonal bits differ for representation %u, row %u\n", tag, counts[tag]);
            return 1;
        }
        ++counts[tag];
    }
    if (ferror(stdin)) return 1;
    for (unsigned i = 0; i < 4; ++i) if (!counts[i]) return 1;
    printf("Diagonal scale and adjoint matched Lean for %u cells across four representations\n",
           counts[0] + counts[1] + counts[2] + counts[3]);
    return 0;
}
