/* Observe explicit byte-copy operations in a private translation unit. This
 * checks block coalescing, not generated instruction counts or elapsed time. */
#include <assert.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

static int observing;
static size_t expected_copy_bytes, copy_calls, copied_bytes;

static void *observed_memcpy(void *target, const void *source, size_t bytes) {
    if (observing) {
        assert(bytes == expected_copy_bytes);
        ++copy_calls;
        copied_bytes += bytes;
    }
    return memcpy(target, source, bytes);
}

/* Some SDKs expose the real memcpy above through a fortified macro. */
#undef memcpy
#define memcpy observed_memcpy
#include "storage.c"
#undef memcpy

int main(void) {
    /* Explicit physical shapes/groupings keep the expectations independent
     * of the production permutation and stride decoder. */
    const struct {
        uint64_t d[3], from, to, rows, columns, target_rows, target_columns;
        size_t block_elements[2], calls[2];
    } cases[] = {
        {{2,3,4},48,42,6,4,8,3,{2,2},{12,12}},    /* common axis 0 */
        {{2,3,4},46,34,6,4,12,2,{3,3},{8,8}},    /* common axis 1 */
        {{2,3,4},38,32,8,3,12,2,{4,4},{6,6}},    /* common axis 2 */
        {{2,3,4},48,46,6,4,6,4,{1,1},{24,24}},   /* no common contiguous axis */
        {{2,1,4},46,42,2,4,8,1,{1,1},{8,8}},     /* unit first axis uses cell path */
        {{2,1,4},48,46,2,4,2,4,{2,2},{4,4}},     /* different orders, unit strides */
        {{7,2,1},48,42,14,1,7,2,{7,1},{2,14}},   /* fixed 56-byte / cell path */
        {{8,2,1},48,42,16,1,8,2,{8,1},{2,16}},   /* fixed 64-byte / cell path */
        {{24,1,1},48,42,24,1,24,1,{1,1},{24,24}}, /* larger contiguous axis */
    };
    for (unsigned n = 0; n < sizeof(cases)/sizeof(cases[0]); ++n)
        for (uint8_t scalar = 0; scalar <= 1; ++scalar)
            for (unsigned shared = 0; shared <= 1; ++shared) {
                VStorageArena *arena = vstorage_new(8192);
                const uint64_t width = scalar ? 16 : 8;
                const uint32_t target = shared ? 0 : 1;
                assert(arena && vstorage_allocate(arena,0,scalar,256) == VS_OK);
                if (!shared) assert(vstorage_allocate(arena,1,scalar,256) == VS_OK);
                VStorageLayout whole = {0,256,1,256,0};
                assert(vstorage_fill(arena,0,whole,scalar,0,0) == VS_OK);
                VStorageLayout input = {width,cases[n].rows,cases[n].columns,cases[n].rows+2,0};
                VStorageLayout output = {(shared ? 128 : 3)*width,cases[n].target_rows,
                    cases[n].target_columns,cases[n].target_rows+3,0};
                expected_copy_bytes = cases[n].block_elements[scalar]*width;
                copy_calls = copied_bytes = 0;
                observing = 1;
                assert(vstorage_regroup3(arena,0,input,target,output,
                    cases[n].d[0],cases[n].d[1],cases[n].d[2],cases[n].from,cases[n].to) == VS_OK);
                observing = 0;
                assert(copy_calls == cases[n].calls[scalar]);
                assert(copied_bytes == cases[n].d[0]*cases[n].d[1]*cases[n].d[2]*width);
                /* Even an identity mapping must reject overlap before copying. */
                copy_calls = copied_bytes = 0;
                observing = 1;
                assert(vstorage_regroup3(arena,0,input,0,input,
                    cases[n].d[0],cases[n].d[1],cases[n].d[2],cases[n].from,cases[n].from) == VS_ALIAS);
                observing = 0;
                assert(copy_calls == 0 && copied_bytes == 0);
                vstorage_delete(arena);
            }
    puts("regroup3: exact block/cell copy events and rejection before copy passed");
    return 0;
}
