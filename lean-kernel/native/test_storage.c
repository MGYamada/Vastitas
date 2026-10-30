#include "storage.h"
#include <assert.h>
#include <limits.h>
#include <stdio.h>

static const uint64_t one = UINT64_C(0x3ff0000000000000);
static const uint64_t two = UINT64_C(0x4000000000000000);

static void assert_value(VStorageArena *a, uint32_t id, VStorageLayout view, uint8_t scalar,
                         uint64_t row, uint64_t column, uint64_t real, uint64_t imaginary) {
    assert(vstorage_expect(a,id,view,row,column,scalar,real,imaginary) == VS_OK);
}

static void layouts(uint8_t scalar) {
    VStorageArena *a = vstorage_new(4096);
    assert(a);
    assert(vstorage_allocate(a,0,scalar,16) == VS_OK);
    assert(vstorage_allocate(a,1,scalar,16) == VS_OK);
    VStorageLayout full = {0,16,1,16,0}, pad = {0,2,3,4,0};
    uint64_t imaginary = scalar ? UINT64_C(0x8000000000000000) : 0;
    assert(vstorage_fill(a,0,full,scalar,two,two) == VS_OK);
    assert(vstorage_fill(a,0,pad,scalar,one,imaginary) == VS_OK);
    for (uint64_t i = 0; i < 16; ++i) {
        uint64_t expected = i < 12 && i % 4 < 2 ? one : two;
        uint64_t im = i < 12 && i % 4 < 2 ? imaginary : two;
        assert_value(a,0,full,scalar,i,0,expected,im);
    }
    /* All four source/destination transpose combinations, unequal row/column
     * extents, padding, exact payloads, and repeated destination reuse. */
    for (uint8_t source_transpose = 0; source_transpose < 2; ++source_transpose) {
        pad.transposed = source_transpose;
        uint64_t rows = source_transpose ? 3 : 2, columns = source_transpose ? 2 : 3;
        for (uint64_t c = 0; c < columns; ++c)
            for (uint64_t r = 0; r < rows; ++r)
                assert(vstorage_store(a,0,pad,r,c,scalar,one + r + 7*c,imaginary + r + c) == VS_OK);
        for (uint8_t target_transpose = 0; target_transpose < 2; ++target_transpose) {
            VStorageLayout dest = {0, target_transpose ? columns : rows,
                target_transpose ? rows : columns, 4, target_transpose};
            assert(vstorage_fill(a,1,full,scalar,two,two) == VS_OK);
            assert(vstorage_copy(a,0,pad,1,dest) == VS_OK);
            for (uint64_t c = 0; c < columns; ++c)
                for (uint64_t r = 0; r < rows; ++r)
                    assert_value(a,1,dest,scalar,r,c,one+r+7*c,imaginary+r+c);
            for (uint64_t physical = 0; physical < 16; ++physical)
                if (physical / 4 >= dest.columns || physical % 4 >= dest.rows)
                    assert_value(a,1,full,scalar,physical,0,two,two);
        }
    }
    assert(vstorage_fill(a,1,full,scalar,one,imaginary) == VS_OK);
    VStorageStats before = vstorage_stats(a);
    VStorageLayout bad[] = {{1,1,1,1,0},{0,3,2,2,0},{0,8,8,8,0},
        {0,0,0,(uint64_t)INT32_MAX+1,0},{UINT64_MAX,1,1,1,0},{0,1,1,1,2}};
    for (unsigned i = 0; i < sizeof(bad)/sizeof(bad[0]); ++i) {
        assert(vstorage_fill(a,1,bad[i],scalar,two,two) != VS_OK);
        assert(vstorage_copy(a,0,pad,1,bad[i]) != VS_OK);
        for (uint64_t r = 0; r < 16; ++r) assert_value(a,1,full,scalar,r,0,one,imaginary);
        assert(vstorage_stats(a).written_bytes == before.written_bytes);
    }
    assert(vstorage_store(a,1,full,16,0,scalar,two,two) == VS_BOUNDS);
    assert(vstorage_fill(a,1,full,!scalar,two,two) == VS_SCALAR);
    assert(vstorage_stats(a).written_bytes == before.written_bytes);
    /* Empty views validate metadata without forming or aligning a data pointer. */
    VStorageLayout empty = {1,0,INT32_MAX,1,1};
    assert(vstorage_fill(a,1,empty,scalar,two,two) == VS_OK);
    assert(vstorage_copy(a,0,empty,1,empty) == VS_OK);
    assert(vstorage_stats(a).written_bytes == before.written_bytes);
    /* Payload operations preserve zeros, infinities and quiet/signaling NaNs;
     * they perform no floating-point arithmetic or implicit conjugation. */
    uint64_t bits[] = {0,UINT64_C(0x8000000000000000),UINT64_C(0x7ff0000000000000),
        UINT64_C(0xfff0000000000000),UINT64_C(0x7ff8000000000042),UINT64_C(0x7ff0000000000001)};
    for (unsigned i = 0; i < sizeof(bits)/sizeof(bits[0]); ++i) {
        assert(vstorage_fill(a,0,full,scalar,bits[i],bits[i]) == VS_OK);
        assert(vstorage_copy(a,0,full,1,full) == VS_OK);
        assert_value(a,1,full,scalar,0,0,bits[i],bits[i]);
    }
    assert(vstorage_drop(a,0) == VS_OK);
    assert(vstorage_fill(a,0,full,scalar,two,two) == VS_HANDLE);
    assert(vstorage_drop(a,0) == VS_HANDLE);
    assert(vstorage_allocate(a,0,scalar,16) == VS_HANDLE);
    vstorage_close(a);
    VStorageStats after = vstorage_stats(a);
    assert(after.data_allocations == 2 && after.data_frees == 2 && after.live_bytes == 0);
    assert(after.metadata_allocations == 2 && after.metadata_bytes > 0);
    vstorage_close(a);
    assert(vstorage_stats(a).data_frees == 2);
    vstorage_delete(a);
}

static void alias_and_failure(void) {
    VStorageArena *a = vstorage_new(128);
    assert(a);
    assert(vstorage_allocate(a,0,0,16) == VS_OK);
    VStorageLayout whole = {0,16,1,16,0}, first = {0,4,1,4,0}, next = {32,4,1,4,0}, overlap = {8,4,1,4,0};
    assert(vstorage_fill(a,0,whole,0,two,0) == VS_OK);
    assert(vstorage_fill(a,0,first,0,one,0) == VS_OK);
    uint64_t written = vstorage_stats(a).written_bytes;
    assert(vstorage_copy(a,0,first,0,overlap) == VS_ALIAS);
    assert(vstorage_stats(a).written_bytes == written);
    assert_value(a,0,whole,0,4,0,two,0);
    assert(vstorage_copy(a,0,first,0,first) == VS_OK);
    assert(vstorage_stats(a).written_bytes == written);
    assert(vstorage_copy(a,0,first,0,next) == VS_OK);
    for (uint64_t r = 0; r < 8; ++r) assert_value(a,0,whole,0,r,0,one,0);
    assert(vstorage_allocate(a,1,0,1) == VS_ALLOCATION);
    assert_value(a,0,whole,0,0,0,one,0);
    assert(vstorage_allocate(a,1,0,UINT64_MAX) == VS_OVERFLOW);
    assert(vstorage_allocate(a,4096,0,0) == VS_HANDLE);
    vstorage_close(a);
    assert(vstorage_stats(a).live_bytes == 0 && vstorage_stats(a).data_frees == 1);
    assert(vstorage_allocate(a,2,0,1) == VS_HANDLE);
    vstorage_delete(a);
    a = vstorage_new(0);
    assert(a && vstorage_allocate(a,0,0,0) == VS_OK);
    VStorageLayout empty = {0,0,3,1,0};
    assert(vstorage_fill(a,0,empty,0,one,0) == VS_OK);
    assert(vstorage_copy(a,0,empty,0,empty) == VS_OK);
    assert(vstorage_store(a,0,empty,0,0,0,one,0) == VS_BOUNDS);
    assert(vstorage_stats(a).data_allocations == 0);
    vstorage_delete(a);
}

int main(void) {
    layouts(0);
    layouts(1);
    alias_and_failure();
    puts("native storage preflight, layout, alias, payload, failure and cleanup checks passed");
    return 0;
}
