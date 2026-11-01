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

static void assert_stats(VStorageStats actual, VStorageStats expected) {
    assert(actual.data_allocations == expected.data_allocations && actual.data_frees == expected.data_frees);
    assert(actual.live_bytes == expected.live_bytes && actual.peak_bytes == expected.peak_bytes);
    assert(actual.written_bytes == expected.written_bytes && actual.copied_bytes == expected.copied_bytes);
    assert(actual.metadata_allocations == expected.metadata_allocations && actual.metadata_bytes == expected.metadata_bytes);
}

static uint64_t pack_payload(uint64_t index) {
    const uint64_t special[] = {0,UINT64_C(0x8000000000000000),
        UINT64_C(0x7ff0000000000000),UINT64_C(0xfff0000000000000),
        UINT64_C(0x7ff8000000000042),UINT64_C(0x7ff0000000000001)};
    return index < 6 ? special[index] : one + index;
}

static void pack_layouts(uint8_t scalar, int same_allocation) {
    const uint64_t i = 2, k = 3, j = 4, count = 128, width = scalar ? 16 : 8;
    const uint64_t target_offset = same_allocation ? 56 : 2;
    const uint32_t target = same_allocation ? 0 : 1;
    VStorageLayout whole = {0,count,1,count,0};
    VStorageLayout input = {width,i,k*j,4,0}, output = {target_offset*width,i*j,k,11,0};
    VStorageArena *a = vstorage_new(8192);
    assert(a && vstorage_allocate(a,0,scalar,count) == VS_OK);
    assert(vstorage_fill(a,0,whole,scalar,two,two) == VS_OK);
    if (!same_allocation) {
        assert(vstorage_allocate(a,1,scalar,count) == VS_OK);
        assert(vstorage_fill(a,1,whole,scalar,two,two) == VS_OK);
    }
    for (uint64_t column = 0; column < k*j; ++column)
        for (uint64_t x = 0; x < i; ++x) {
            uint64_t index = x+i*column;
            assert(vstorage_store(a,0,input,x,column,scalar,
                pack_payload(index),pack_payload(23-index)) == VS_OK);
        }
    VStorageStats before = vstorage_stats(a);
    /* Reusing the exact destination adds no allocation or implicit reset. */
    for (uint64_t repetition = 1; repetition <= 2; ++repetition) {
        assert(vstorage_pack3(a,0,input,target,output,i,k,j) == VS_OK);
        VStorageStats expected = before;
        expected.written_bytes += repetition*i*k*j*width;
        expected.copied_bytes += repetition*i*k*j*width;
        assert_stats(vstorage_stats(a),expected);
        for (uint64_t physical = 0; physical < count; ++physical) {
            uint64_t rel = physical >= target_offset ? physical-target_offset : UINT64_MAX;
            uint64_t row = rel % output.leading, z = rel / output.leading;
            int destination_cell = physical >= target_offset && row < i*j && z < k;
            uint64_t source_rel = physical >= 1 ? physical-1 : UINT64_MAX;
            int source_cell = physical >= 1 && source_rel % input.leading < i &&
                source_rel / input.leading < k*j;
            uint64_t re = two, im = two;
            if (destination_cell) {
                uint64_t index = row%i + i*(z + k*(row/i));
                re = pack_payload(index); im = pack_payload(23-index);
            } else if (same_allocation && source_cell) {
                uint64_t index = source_rel%input.leading + i*(source_rel/input.leading);
                re = pack_payload(index); im = pack_payload(23-index);
            }
            assert_value(a,target,whole,scalar,physical,0,re,im);
            if (!same_allocation) {
                uint64_t index = source_rel%input.leading + i*(source_rel/input.leading);
                assert_value(a,0,whole,scalar,physical,0,
                    source_cell ? pack_payload(index) : two,
                    source_cell ? pack_payload(23-index) : two);
            }
        }
    }
    vstorage_close(a);
    VStorageStats after = vstorage_stats(a);
    assert(after.live_bytes == 0 && after.data_allocations == after.data_frees);
    vstorage_delete(a);
}

static void pack_failures(void) {
    VStorageArena *a = vstorage_new(8192);
    VStorageLayout whole = {0,128,1,128,0};
    VStorageLayout input = {8,2,12,4,0}, output = {16,8,3,11,0};
    assert(a && vstorage_allocate(a,0,0,128) == VS_OK);
    assert(vstorage_allocate(a,1,0,128) == VS_OK);
    assert(vstorage_allocate(a,2,1,128) == VS_OK);
    assert(vstorage_fill(a,0,whole,0,one,0) == VS_OK);
    assert(vstorage_fill(a,1,whole,0,two,0) == VS_OK);
    assert(vstorage_fill(a,2,whole,1,two,two) == VS_OK);
    VStorageStats before = vstorage_stats(a);
    struct Failure {
        uint32_t source; VStorageLayout input;
        uint32_t target; VStorageLayout output;
        uint64_t i, k, j; VStorageStatus status;
    } failures[] = {
        {0,input,1,output,1,3,4,VS_SHAPE},
        {0,input,1,output,2,2,6,VS_SHAPE},
        {0,input,1,output,2,3,0,VS_SHAPE},
        {0,input,1,output,(uint64_t)INT32_MAX+1,3,4,VS_LAYOUT},
        {0,input,1,output,2,UINT64_MAX,4,VS_LAYOUT},
        {0,input,1,output,2,3,UINT64_MAX,VS_LAYOUT},
        {0,{8,2,12,4,1},1,output,2,3,4,VS_OPERATION},
        {0,input,1,{16,8,3,11,1},2,3,4,VS_OPERATION},
        {0,{8,2,12,4,2},1,output,2,3,4,VS_LAYOUT},
        {0,{8,2,12,1,0},1,output,2,3,4,VS_LAYOUT},
        {0,input,1,{16,8,3,7,0},2,3,4,VS_LAYOUT},
        {0,{UINT64_MAX,2,12,4,0},1,output,2,3,4,VS_LAYOUT},
        {0,input,1,{1024,8,3,11,0},2,3,4,VS_LAYOUT},
        {0,{1,2,12,4,0},1,output,2,3,4,VS_LAYOUT},
        {0,input,1,{1,8,3,11,0},2,3,4,VS_LAYOUT},
        {0,input,2,output,2,3,4,VS_SCALAR},
        {4095,input,1,output,2,3,4,VS_HANDLE},
        {0,input,4095,output,2,3,4,VS_HANDLE},
        {0,input,0,output,2,3,4,VS_ALIAS},
        /* Even an exact identity and disjoint logical cells in overlapping
         * padding envelopes must be rejected before any write. */
        {0,{0,2,3,2,0},0,{0,2,3,2,0},2,3,1,VS_ALIAS},
        {0,{0,1,2,4,0},0,{8,2,1,2,0},1,1,2,VS_ALIAS},
        {0,{0,INT32_MAX,INT32_MAX,INT32_MAX,0},1,output,
            INT32_MAX,INT32_MAX,1,VS_OVERFLOW}
    };
    for (unsigned n = 0; n < sizeof(failures)/sizeof(failures[0]); ++n) {
        struct Failure f = failures[n];
        assert(vstorage_pack3(a,f.source,f.input,f.target,f.output,f.i,f.k,f.j) == f.status);
        assert_stats(vstorage_stats(a),before);
        for (uint64_t row = 0; row < 128; ++row) {
            assert_value(a,0,whole,0,row,0,one,0);
            assert_value(a,1,whole,0,row,0,two,0);
            assert_value(a,2,whole,1,row,0,two,two);
        }
    }
    /* Saturate the existing write-accounting seam to verify failure before
     * the first packed byte, without impossible-size physical allocations. */
    uint64_t remaining = UINT64_MAX-before.written_bytes;
    assert(vstorage_prepare_write(a,remaining) == VS_OK);
    vstorage_record_write(a,remaining);
    before = vstorage_stats(a);
    assert(vstorage_pack3(a,0,input,1,output,2,3,4) == VS_OVERFLOW);
    assert_stats(vstorage_stats(a),before);
    for (uint64_t row = 0; row < 128; ++row) assert_value(a,1,whole,0,row,0,two,0);
    vstorage_close(a);
    assert(vstorage_stats(a).live_bytes == 0 && vstorage_stats(a).data_frees == 3);
    assert(vstorage_pack3(a,0,input,1,output,2,3,4) == VS_HANDLE);
    assert(vstorage_pack3(NULL,0,input,1,output,2,3,4) == VS_HANDLE);
    vstorage_delete(a);
}

static void pack_empty(uint8_t scalar) {
    VStorageArena *a = vstorage_new(64);
    assert(a && vstorage_allocate(a,0,scalar,0) == VS_OK);
    assert(vstorage_allocate(a,1,scalar,0) == VS_OK);
    assert(vstorage_allocate(a,2,!scalar,0) == VS_OK);
    const uint64_t axes[][3] = {{0,3,4},{2,0,4},{2,3,0}};
    VStorageStats before = vstorage_stats(a);
    for (unsigned n = 0; n < 3; ++n) {
        uint64_t i = axes[n][0], k = axes[n][1], j = axes[n][2];
        uint64_t output_rows = i*j;
        VStorageLayout input = {0,i,k*j,i ? i : 1,0};
        VStorageLayout output = {0,output_rows,k,output_rows ? output_rows : 1,0};
        assert(vstorage_pack3(a,0,input,1,output,i,k,j) == VS_OK);
        assert(vstorage_pack3(a,0,input,0,output,i,k,j) == VS_OK);
        assert(vstorage_pack3(a,0,input,2,output,i,k,j) == VS_SCALAR);
        assert(vstorage_pack3(a,0,input,1,output,i+1,k,j) == VS_SHAPE);
        assert(vstorage_pack3(a,0,input,1,output,UINT64_MAX,k,j) == VS_LAYOUT);
        assert(vstorage_pack3(a,0,input,4095,output,i,k,j) == VS_HANDLE);
        VStorageLayout bad = input; bad.leading = 0;
        assert(vstorage_pack3(a,0,bad,1,output,i,k,j) == VS_LAYOUT);
        bad = output; bad.offset = 1;
        assert(vstorage_pack3(a,0,input,1,bad,i,k,j) == VS_LAYOUT);
        bad = input; bad.transposed = 1;
        assert(vstorage_pack3(a,0,bad,1,output,i,k,j) == VS_OPERATION);
        bad = output; bad.leading = (uint64_t)INT32_MAX+1;
        assert(vstorage_pack3(a,0,input,1,bad,i,k,j) == VS_LAYOUT);
        assert_stats(vstorage_stats(a),before);
    }
    /* An empty descriptor need not align its in-capacity offset. */
    assert(vstorage_allocate(a,3,scalar,1) == VS_OK);
    assert(vstorage_allocate(a,4,scalar,1) == VS_OK);
    VStorageLayout input = {1,0,12,1,0}, output = {1,0,3,1,0};
    before = vstorage_stats(a);
    assert(vstorage_pack3(a,3,input,4,output,0,3,4) == VS_OK);
    assert_stats(vstorage_stats(a),before);
    vstorage_close(a);
    assert(vstorage_stats(a).live_bytes == 0 && vstorage_stats(a).data_frees == 2);
    vstorage_delete(a);
}

typedef struct { unsigned order[3], split; uint64_t code; } TestGrouping;
/* Explicit permutations keep the oracle independent of the production decoder. */
static const TestGrouping groupings[] = {
    {{0,1,2},1,21}, {{0,2,1},1,15}, {{1,0,2},1,19},
    {{1,2,0},1,7},  {{2,0,1},1,11}, {{2,1,0},1,5},
    {{0,1,2},2,48}, {{0,2,1},2,42}, {{1,0,2},2,46},
    {{1,2,0},2,34}, {{2,0,1},2,38}, {{2,1,0},2,32}
};

static VStorageLayout grouped_layout(TestGrouping g, const uint64_t d[3],
                                     uint64_t offset, uint64_t padding) {
    uint64_t rows = 1, columns = 1;
    for (unsigned n = 0; n < g.split; ++n) rows *= d[g.order[n]];
    for (unsigned n = g.split; n < 3; ++n) columns *= d[g.order[n]];
    return (VStorageLayout){offset,rows,columns,rows+padding,0};
}

/* Evaluate the specified nested coordinate flattening, not the implementation's
 * physical strides. This also supplies expectations for every padding cell. */
static uint64_t grouped_cell(TestGrouping g, const uint64_t d[3], const uint64_t x[3],
                             VStorageLayout view, uint64_t width) {
    uint64_t row = 0, column = 0;
    for (unsigned n = g.split; n > 0; --n) row = x[g.order[n-1]] + d[g.order[n-1]]*row;
    for (unsigned n = 3; n > g.split; --n) column = x[g.order[n-1]] + d[g.order[n-1]]*column;
    return view.offset/width + row + view.leading*column;
}

static void regroup_layouts(uint8_t scalar, int same_allocation, const uint64_t d[3],
                            uint64_t padding) {
    const uint64_t count = 256, width = scalar ? 16 : 8, volume = d[0]*d[1]*d[2];
    const uint32_t target = same_allocation ? 0 : 1;
    VStorageLayout whole = {0,count,1,count,0};
    for (unsigned from = 0; from < 12; ++from)
        for (unsigned to = 0; to < 12; ++to) {
            VStorageArena *a = vstorage_new(8192);
            assert(a && vstorage_allocate(a,0,scalar,count) == VS_OK);
            assert(vstorage_fill(a,0,whole,scalar,two,two) == VS_OK);
            if (!same_allocation) {
                assert(vstorage_allocate(a,1,scalar,count) == VS_OK);
                assert(vstorage_fill(a,1,whole,scalar,two,two) == VS_OK);
            }
            VStorageLayout input = grouped_layout(groupings[from],d,width,2*padding);
            VStorageLayout output = grouped_layout(groupings[to],d,(same_allocation ? 128 : 3)*width,3*padding);
            uint64_t expected_source[256][2], expected_target[256][2];
            for (unsigned cell = 0; cell < count; ++cell) {
                expected_source[cell][0] = expected_source[cell][1] = two;
                expected_target[cell][0] = expected_target[cell][1] = two;
            }
            for (uint64_t x2 = 0; x2 < d[2]; ++x2)
                for (uint64_t x1 = 0; x1 < d[1]; ++x1)
                    for (uint64_t x0 = 0; x0 < d[0]; ++x0) {
                        uint64_t x[3] = {x0,x1,x2}, index = x0 + d[0]*(x1+d[1]*x2);
                        uint64_t src = grouped_cell(groupings[from],d,x,input,width);
                        uint64_t dst = grouped_cell(groupings[to],d,x,output,width);
                        assert(src < count && dst < count);
                        uint64_t re = pack_payload(index), im = pack_payload(volume-1-index);
                        assert(vstorage_store(a,0,whole,src,0,scalar,re,im) == VS_OK);
                        expected_source[src][0] = re; expected_source[src][1] = im;
                        expected_target[dst][0] = re; expected_target[dst][1] = im;
                        if (same_allocation) {
                            expected_target[src][0] = re; expected_target[src][1] = im;
                        }
                    }
            VStorageStats before = vstorage_stats(a);
            for (uint64_t repetition = 1; repetition <= 2; ++repetition) {
                assert(vstorage_regroup3(a,0,input,target,output,d[0],d[1],d[2],
                    groupings[from].code,groupings[to].code) == VS_OK);
                VStorageStats expected = before;
                expected.written_bytes += repetition*volume*width;
                expected.copied_bytes += repetition*volume*width;
                assert_stats(vstorage_stats(a),expected);
                for (uint64_t cell = 0; cell < count; ++cell) {
                    assert_value(a,target,whole,scalar,cell,0,expected_target[cell][0],expected_target[cell][1]);
                    if (!same_allocation)
                        assert_value(a,0,whole,scalar,cell,0,expected_source[cell][0],expected_source[cell][1]);
                }
            }
            vstorage_close(a);
            assert(vstorage_stats(a).live_bytes == 0 &&
                vstorage_stats(a).data_allocations == vstorage_stats(a).data_frees);
            vstorage_delete(a);
        }
}

static void regroup_failures(uint8_t scalar) {
    const uint64_t width = scalar ? 16 : 8;
    VStorageArena *a = vstorage_new(16384);
    VStorageLayout whole = {0,128,1,128,0};
    VStorageLayout input = {width,2,12,4,0}, output = {2*width,8,3,11,0};
    assert(a && vstorage_allocate(a,0,scalar,128) == VS_OK);
    assert(vstorage_allocate(a,1,scalar,128) == VS_OK);
    assert(vstorage_allocate(a,2,!scalar,128) == VS_OK);
    assert(vstorage_fill(a,0,whole,scalar,one,one) == VS_OK);
    assert(vstorage_fill(a,1,whole,scalar,two,two) == VS_OK);
    assert(vstorage_fill(a,2,whole,!scalar,two,two) == VS_OK);
    VStorageStats before = vstorage_stats(a);
    struct Failure {
        uint32_t source; VStorageLayout input; uint32_t target; VStorageLayout output;
        uint64_t d0, d1, d2, from, to; VStorageStatus status;
    } failures[] = {
        {0,input,1,output,1,3,4,21,42,VS_SHAPE},
        {0,input,1,output,2,3,4,19,42,VS_SHAPE},
        {0,input,1,output,2,3,4,21,48,VS_SHAPE},
        {0,input,1,output,2,3,0,21,42,VS_SHAPE},
        {0,input,1,output,(uint64_t)INT32_MAX+1,3,4,21,42,VS_LAYOUT},
        {0,input,1,output,2,UINT64_MAX,4,21,42,VS_LAYOUT},
        {0,input,1,output,2,3,UINT64_MAX,21,42,VS_LAYOUT},
        {0,input,1,output,2,3,4,54,42,VS_OPERATION},
        {0,input,1,output,2,3,4,21,UINT64_MAX,VS_OPERATION},
        {0,{width,2,12,4,1},1,output,2,3,4,21,42,VS_OPERATION},
        {0,input,1,{2*width,8,3,11,1},2,3,4,21,42,VS_OPERATION},
        {0,{width,2,12,4,2},1,output,2,3,4,21,42,VS_LAYOUT},
        {0,{width,2,12,1,0},1,output,2,3,4,21,42,VS_LAYOUT},
        {0,input,1,{2*width,8,3,7,0},2,3,4,21,42,VS_LAYOUT},
        {0,input,1,{2*width,8,3,0,0},2,3,4,21,42,VS_LAYOUT},
        {0,{UINT64_MAX,2,12,4,0},1,output,2,3,4,21,42,VS_LAYOUT},
        {0,input,1,{128*width,8,3,11,0},2,3,4,21,42,VS_LAYOUT},
        {0,{1,2,12,4,0},1,output,2,3,4,21,42,VS_LAYOUT},
        {0,input,1,{1,8,3,11,0},2,3,4,21,42,VS_LAYOUT},
        {0,input,2,output,2,3,4,21,42,VS_SCALAR},
        {4095,input,1,output,2,3,4,21,42,VS_HANDLE},
        {0,input,4095,output,2,3,4,21,42,VS_HANDLE},
        {0,input,0,output,2,3,4,21,42,VS_ALIAS},
        {0,input,0,input,2,3,4,21,21,VS_ALIAS},
        /* Logically disjoint cells still have overlapping padding envelopes. */
        {0,{0,1,2,4,0},0,{width,2,1,2,0},1,1,2,21,42,VS_ALIAS},
        {0,input,1,output,INT32_MAX,INT32_MAX,INT32_MAX,21,42,VS_OVERFLOW},
        {0,input,1,output,INT32_MAX,INT32_MAX,1,21,42,VS_OVERFLOW},
        {0,{0,INT32_MAX,INT32_MAX,INT32_MAX,0},1,output,2,3,4,21,42,VS_OVERFLOW}
    };
    for (unsigned n = 0; n < sizeof(failures)/sizeof(failures[0]); ++n) {
        struct Failure f = failures[n];
        VStorageStatus actual = vstorage_regroup3(a,f.source,f.input,f.target,f.output,f.d0,f.d1,f.d2,f.from,f.to);
        if (actual != f.status) fprintf(stderr,"regroup failure %u scalar %u: expected %s, got %s\n",
            n,scalar,vstorage_error(f.status),vstorage_error(actual));
        assert(actual == f.status);
        assert_stats(vstorage_stats(a),before);
        for (uint64_t cell = 0; cell < 128; ++cell) {
            assert_value(a,0,whole,scalar,cell,0,one,one);
            assert_value(a,1,whole,scalar,cell,0,two,two);
            assert_value(a,2,whole,!scalar,cell,0,two,two);
        }
    }
    /* Every non-permutation in the full encoding range is invalid on either side. */
    for (uint64_t code = 0; code < 54; ++code) {
        int valid = 0;
        for (unsigned n = 0; n < 12; ++n) valid |= code == groupings[n].code;
        if (valid) continue;
        assert(vstorage_regroup3(a,0,input,1,output,2,3,4,code,42) == VS_OPERATION);
        assert(vstorage_regroup3(a,0,input,1,output,2,3,4,21,code) == VS_OPERATION);
        assert_stats(vstorage_stats(a),before);
    }
    uint64_t remaining = UINT64_MAX-before.written_bytes;
    assert(vstorage_prepare_write(a,remaining) == VS_OK);
    vstorage_record_write(a,remaining);
    before = vstorage_stats(a);
    assert(vstorage_regroup3(a,0,input,1,output,2,3,4,21,42) == VS_OVERFLOW);
    assert_stats(vstorage_stats(a),before);
    for (uint64_t cell = 0; cell < 128; ++cell) {
        assert_value(a,0,whole,scalar,cell,0,one,one);
        assert_value(a,1,whole,scalar,cell,0,two,two);
    }
    vstorage_close(a);
    assert(vstorage_stats(a).live_bytes == 0 && vstorage_stats(a).data_frees == 3);
    assert(vstorage_regroup3(a,0,input,1,output,2,3,4,21,42) == VS_HANDLE);
    assert(vstorage_regroup3(NULL,0,input,1,output,2,3,4,21,42) == VS_HANDLE);
    vstorage_delete(a);
}

static void regroup_empty(uint8_t scalar) {
    VStorageArena *a = vstorage_new(64);
    assert(a && vstorage_allocate(a,0,scalar,0) == VS_OK);
    assert(vstorage_allocate(a,1,scalar,0) == VS_OK);
    assert(vstorage_allocate(a,2,!scalar,0) == VS_OK);
    VStorageStats before = vstorage_stats(a);
    for (unsigned zero = 0; zero < 3; ++zero) {
        uint64_t d[3] = {2,3,4}; d[zero] = 0;
        for (unsigned from = 0; from < 12; ++from)
            for (unsigned to = 0; to < 12; ++to) {
                VStorageLayout input = grouped_layout(groupings[from],d,0,1);
                VStorageLayout output = grouped_layout(groupings[to],d,0,2);
                uint64_t f = groupings[from].code, t = groupings[to].code;
                assert(vstorage_regroup3(a,0,input,1,output,d[0],d[1],d[2],f,t) == VS_OK);
                assert(vstorage_regroup3(a,0,input,0,output,d[0],d[1],d[2],f,t) == VS_OK);
                assert(vstorage_regroup3(a,0,input,2,output,d[0],d[1],d[2],f,t) == VS_SCALAR);
                assert(vstorage_regroup3(a,0,input,1,output,d[0],d[1],d[2],54,t) == VS_OPERATION);
                assert(vstorage_regroup3(a,0,input,1,output,d[0],d[1],d[2],f,0) == VS_OPERATION);
                assert(vstorage_regroup3(a,0,input,4095,output,d[0],d[1],d[2],f,t) == VS_HANDLE);
                VStorageLayout bad = input; bad.leading = 0;
                assert(vstorage_regroup3(a,0,bad,1,output,d[0],d[1],d[2],f,t) == VS_LAYOUT);
                bad = output; bad.offset = 1;
                assert(vstorage_regroup3(a,0,input,1,bad,d[0],d[1],d[2],f,t) == VS_LAYOUT);
                bad = input; bad.transposed = 1;
                assert(vstorage_regroup3(a,0,bad,1,output,d[0],d[1],d[2],f,t) == VS_OPERATION);
                assert_stats(vstorage_stats(a),before);
            }
    }
    /* Zero volume does not waive dimensions, shape, or ungrouped extents. */
    VStorageLayout input = {0,0,12,1,0}, output = {0,0,3,1,0};
    assert(vstorage_regroup3(a,0,input,1,output,UINT64_MAX,3,4,21,42) == VS_LAYOUT);
    assert(vstorage_regroup3(a,0,input,1,output,0,3,5,21,42) == VS_SHAPE);
    assert(vstorage_regroup3(a,0,input,1,output,0,INT32_MAX,INT32_MAX,21,42) == VS_SHAPE);
    assert_stats(vstorage_stats(a),before);
    assert(vstorage_allocate(a,3,scalar,1) == VS_OK);
    assert(vstorage_allocate(a,4,scalar,1) == VS_OK);
    input.offset = output.offset = 1; /* In-capacity empty offset need not align. */
    before = vstorage_stats(a);
    assert(vstorage_regroup3(a,3,input,4,output,0,3,4,21,42) == VS_OK);
    assert_stats(vstorage_stats(a),before);
    vstorage_close(a);
    assert(vstorage_stats(a).live_bytes == 0 && vstorage_stats(a).data_frees == 2);
    vstorage_delete(a);
}

int main(void) {
    layouts(0);
    layouts(1);
    alias_and_failure();
    pack_layouts(0,0);
    pack_layouts(1,0);
    pack_layouts(0,1);
    pack_layouts(1,1);
    pack_failures();
    pack_empty(0);
    pack_empty(1);
    /* All common contiguous axes, unequal groupings, padded and unpadded views,
     * and singleton axes (including the neutral physical rank-two extent).
     * The coordinate oracle checks every source, destination and padding cell. */
    const uint64_t regroup_shapes[][3] = {
        {2,3,4}, {3,5,2}, {1,3,4}, {2,1,4}, {2,3,1},
        {1,1,4}, {2,1,1}, {1,3,1}, {1,1,1}, {7,2,1}, {8,2,1}, {24,1,1}
    };
    for (unsigned shape = 0; shape < sizeof(regroup_shapes)/sizeof(regroup_shapes[0]); ++shape)
        for (uint64_t padding = 0; padding <= 1; ++padding)
            for (uint8_t scalar = 0; scalar <= 1; ++scalar)
                for (int same_allocation = 0; same_allocation <= 1; ++same_allocation)
                    regroup_layouts(scalar,same_allocation,regroup_shapes[shape],padding);
    regroup_failures(0);
    regroup_failures(1);
    regroup_empty(0);
    regroup_empty(1);
    puts("native storage preflight, layout, alias, payload, pack3, all 144 regroup3 pairs, failure and cleanup checks passed");
    return 0;
}
