#include "gemm.h"
#include <assert.h>
#include <limits.h>
#include <math.h>
#include <stdio.h>
#include <string.h>

static uint64_t bits(double value) {
    uint64_t result;
    memcpy(&result, &value, sizeof(result));
    return result;
}
static VStorageLayout layout(uint64_t rows, uint64_t columns, int transpose, int padded) {
    uint64_t stored_rows = transpose ? columns : rows;
    return (VStorageLayout){padded ? 16 : 0, stored_rows,
        transpose ? rows : columns, (stored_rows ? stored_rows : 1) + (padded ? 2 : 0), (uint8_t)transpose};
}
static void allocate(VStorageArena *arena, uint32_t id, uint8_t scalar, VStorageLayout view) {
    assert(vstorage_allocate(arena, id, scalar, view.offset / (scalar ? 16 : 8) +
        view.leading * view.columns) == VS_OK);
}
static void put(VStorageArena *arena, uint32_t id, VStorageLayout view,
                uint64_t row, uint64_t column, uint8_t scalar, double real, double imaginary) {
    assert(vstorage_store(arena,id,view,row,column,scalar,bits(real),bits(imaginary)) == VS_OK);
}
static void expect(VStorageArena *arena, uint32_t id, VStorageLayout view,
                   uint64_t row, uint64_t column, double real, double imaginary) {
    VStorageDense actual;
    assert(vstorage_prepare_dense(arena,id,view,&actual) == VS_OK);
    uint64_t index = actual.transposed ? column + row * actual.leading : row + column * actual.leading;
    index *= actual.scalar ? 2 : 1;
    assert(actual.data[index] == real);
    if (actual.scalar) assert(actual.data[index+1] == imaginary);
}
static void cleanup(VStorageArena *arena) {
    vstorage_close(arena);
    VStorageStats stats = vstorage_stats(arena);
    assert(stats.live_bytes == 0 && stats.data_allocations == stats.data_frees);
    vstorage_delete(arena);
}

static void real_orientations(void) {
    const double left[2][3] = {{1,2,3},{4,5,6}};
    const double right[3][2] = {{7,8},{9,10},{11,12}};
    const double product[2][2] = {{58,64},{139,154}};
    for (int ta=0; ta<2; ++ta) for (int tb=0; tb<2; ++tb) for (int pad=0;pad<2;++pad) {
        VStorageArena *arena = vstorage_new(4096);
        assert(arena);
        VStorageLayout a=layout(2,3,ta,pad), b=layout(3,2,tb,pad), c=layout(2,2,0,pad);
        allocate(arena,0,0,a); allocate(arena,1,0,b); allocate(arena,2,0,c);
        for (int i=0;i<2;++i) for(int j=0;j<3;++j) put(arena,0,a,i,j,0,left[i][j],0);
        for (int i=0;i<3;++i) for(int j=0;j<2;++j) put(arena,1,b,i,j,0,right[i][j],0);
        VStorageStats before=vstorage_stats(arena);
        VGemmReport report={99,99};
        /* Output is malloc-backed and deliberately uninitialized. */
        assert(vgemm_execute(arena,0,a,0,1,b,0,2,c,VGEMM_OVERWRITE,&report)==VS_OK);
        assert(report.kernel_calls==1 && report.written_bytes==32);
        for(int i=0;i<2;++i) for(int j=0;j<2;++j) expect(arena,2,c,i,j,product[i][j],0);
        assert(vgemm_execute(arena,0,a,0,1,b,0,2,c,VGEMM_ACCUMULATE,&report)==VS_OK);
        for(int i=0;i<2;++i) for(int j=0;j<2;++j) expect(arena,2,c,i,j,2*product[i][j],0);
        for(int i=0;i<2;++i) for(int j=0;j<3;++j) expect(arena,0,a,i,j,left[i][j],0);
        for(int i=0;i<3;++i) for(int j=0;j<2;++j) expect(arena,1,b,i,j,right[i][j],0);
        VStorageStats after=vstorage_stats(arena);
        assert(after.data_allocations==before.data_allocations && after.copied_bytes==before.copied_bytes);
        assert(after.written_bytes==before.written_bytes+64 && after.peak_bytes==before.peak_bytes);
        cleanup(arena);
    }
}

static void complex_product(void) {
    const double left[2][3][2]={{{1,0},{0,1},{2,0}},{{0,0},{1,0},{0,-1}}};
    const double right[3][2][2]={{{1,0},{0,0}},{{2,0},{1,0}},{{0,0},{0,1}}};
    const double product[2][2][2]={{{1,2},{0,3}},{{2,0},{2,0}}};
    for(int ta=0;ta<2;++ta) for(int tb=0;tb<2;++tb) {
        VStorageArena *arena=vstorage_new(4096); assert(arena);
        VStorageLayout a=layout(2,3,ta,1),b=layout(3,2,tb,1),c=layout(2,2,0,1);
        allocate(arena,0,1,a); allocate(arena,1,1,b); allocate(arena,2,1,c);
        for(int i=0;i<2;++i) for(int j=0;j<3;++j) put(arena,0,a,i,j,1,left[i][j][0],left[i][j][1]);
        for(int i=0;i<3;++i) for(int j=0;j<2;++j) put(arena,1,b,i,j,1,right[i][j][0],right[i][j][1]);
        VGemmReport report;
        assert(vgemm_execute(arena,0,a,0,1,b,0,2,c,VGEMM_OVERWRITE,&report)==VS_OK);
        assert(report.kernel_calls==1 && report.written_bytes==64);
        for(int i=0;i<2;++i) for(int j=0;j<2;++j) expect(arena,2,c,i,j,product[i][j][0],product[i][j][1]);
        cleanup(arena);
    }
}

static void conjugation_and_nonfinite(void) {
    VStorageArena *arena=vstorage_new(4096); assert(arena);
    VStorageLayout one=layout(1,1,0,0),t=layout(1,1,1,0);
    for(uint32_t id=0;id<3;++id) allocate(arena,id,1,one);
    put(arena,0,one,0,0,1,0,1); put(arena,1,one,0,0,1,1,0);
    VGemmReport report;
    assert(vgemm_execute(arena,0,t,0,1,one,0,2,one,VGEMM_OVERWRITE,&report)==VS_OK);
    expect(arena,2,one,0,0,0,1);
    assert(vgemm_execute(arena,0,t,1,1,one,0,2,one,VGEMM_OVERWRITE,&report)==VS_OK);
    expect(arena,2,one,0,0,0,-1);
    assert(vgemm_execute(arena,1,one,0,0,t,1,2,one,VGEMM_OVERWRITE,&report)==VS_OK);
    expect(arena,2,one,0,0,0,-1);
    /* Read/read aliases are allowed; ordinary multiplication stays bilinear. */
    assert(vgemm_execute(arena,0,one,0,0,one,0,2,one,VGEMM_OVERWRITE,&report)==VS_OK);
    expect(arena,2,one,0,0,-1,0);
    /* Overwrite is independent of old output NaNs as well as uninitialized bytes. */
    put(arena,2,one,0,0,1,NAN,NAN);
    assert(vgemm_execute(arena,0,one,0,1,one,0,2,one,VGEMM_OVERWRITE,&report)==VS_OK);
    expect(arena,2,one,0,0,0,1);
    cleanup(arena);
}

static void degenerate(void) {
    VStorageArena *arena=vstorage_new(4096); assert(arena);
    VStorageLayout a=layout(2,0,0,0),b=layout(0,3,0,0),c=layout(2,3,0,0);
    for(uint8_t scalar=0;scalar<2;++scalar) {
        uint32_t base=scalar*3;
        allocate(arena,base,scalar,a); allocate(arena,base+1,scalar,b); allocate(arena,base+2,scalar,c);
        VGemmReport report;
        assert(vgemm_execute(arena,base,a,0,base+1,b,0,base+2,c,VGEMM_OVERWRITE,&report)==VS_OK);
        assert(report.kernel_calls==0 && report.written_bytes==6*(scalar?16:8));
        for(int i=0;i<2;++i) for(int j=0;j<3;++j) expect(arena,base+2,c,i,j,0,0);
        put(arena,base+2,c,0,0,scalar,7,scalar?2:0);
        assert(vgemm_execute(arena,base,a,0,base+1,b,0,base+2,c,VGEMM_ACCUMULATE,&report)==VS_OK);
        assert(report.kernel_calls==0 && report.written_bytes==0);
        expect(arena,base+2,c,0,0,7,scalar?2:0);
    }
    cleanup(arena);
    arena=vstorage_new(64); assert(arena);
    a=layout(0,2,0,0); b=layout(2,0,0,0); c=layout(0,0,0,0);
    allocate(arena,0,0,a); allocate(arena,1,0,b); allocate(arena,2,0,c);
    VGemmReport report;
    assert(vgemm_execute(arena,0,a,0,1,b,0,2,c,VGEMM_OVERWRITE,&report)==VS_OK);
    assert(report.kernel_calls==0 && report.written_bytes==0);
    cleanup(arena);
}

static void nonfinite_inputs(void) {
    VStorageArena *arena=vstorage_new(64); assert(arena);
    VStorageLayout one=layout(1,1,0,0);
    for(uint32_t id=0;id<3;++id) allocate(arena,id,0,one);
    put(arena,0,one,0,0,0,INFINITY,0); put(arena,1,one,0,0,0,2,0);
    assert(vgemm_execute(arena,0,one,0,1,one,0,2,one,VGEMM_OVERWRITE,NULL)==VS_OK);
    expect(arena,2,one,0,0,INFINITY,0);
    put(arena,0,one,0,0,0,NAN,0);
    assert(vgemm_execute(arena,0,one,0,1,one,0,2,one,VGEMM_OVERWRITE,NULL)==VS_OK);
    VStorageDense result;
    assert(vstorage_prepare_dense(arena,2,one,&result)==VS_OK && isnan(result.data[0]));
    cleanup(arena);
}

static void failures_preserve_output(void) {
    VStorageArena *arena=vstorage_new(4096); assert(arena);
    VStorageLayout one=layout(1,1,0,0);
    for(uint32_t id=0;id<3;++id) { allocate(arena,id,0,one); put(arena,id,one,0,0,0,3,0); }
    allocate(arena,3,1,one); put(arena,3,one,0,0,1,3,0);
    VGemmReport report={71,72};
    VStorageStats before=vstorage_stats(arena);
    VStorageLayout wrong=one; wrong.rows=2;
    assert(vgemm_execute(arena,0,wrong,0,1,one,0,2,one,VGEMM_OVERWRITE,&report)==VS_LAYOUT);
    wrong=one; wrong.leading=(uint64_t)INT32_MAX+1;
    assert(vgemm_execute(arena,0,wrong,0,1,one,0,2,one,VGEMM_OVERWRITE,&report)==VS_LAYOUT);
    wrong=one; wrong.offset=UINT64_MAX;
    assert(vgemm_execute(arena,0,wrong,0,1,one,0,2,one,VGEMM_OVERWRITE,&report)==VS_LAYOUT);
    wrong=one; wrong.rows=0;
    assert(vgemm_execute(arena,0,wrong,0,1,one,0,2,one,VGEMM_OVERWRITE,&report)==VS_SHAPE);
    assert(vgemm_execute(arena,0,one,0,1,one,0,0,one,VGEMM_OVERWRITE,&report)==VS_ALIAS);
    assert(vgemm_execute(arena,0,one,0,1,one,0,1,one,VGEMM_OVERWRITE,&report)==VS_ALIAS);
    assert(vgemm_execute(arena,0,one,1,1,one,0,2,one,VGEMM_OVERWRITE,&report)==VS_OPERATION);
    assert(vgemm_execute(arena,0,one,0,1,one,0,2,one,(VGemmMode)2,&report)==VS_OPERATION);
    assert(vgemm_execute(arena,0,one,0,3,one,0,2,one,VGEMM_OVERWRITE,&report)==VS_SCALAR);
    assert(vgemm_execute(arena,0,one,0,99,one,0,2,one,VGEMM_OVERWRITE,&report)==VS_HANDLE);
    assert(report.kernel_calls==71 && report.written_bytes==72);
    assert(vstorage_stats(arena).written_bytes==before.written_bytes);
    for(uint32_t id=0;id<3;++id) expect(arena,id,one,0,0,3,0);
    cleanup(arena);
    /* Disjoint views in one real allocation retain actual byte provenance. */
    arena=vstorage_new(64); assert(arena);
    assert(vstorage_allocate(arena,0,0,3)==VS_OK);
    VStorageLayout second=one,third=one; second.offset=8; third.offset=16;
    put(arena,0,one,0,0,0,2,0); put(arena,0,second,0,0,0,4,0);
    assert(vgemm_execute(arena,0,one,0,0,second,0,0,third,VGEMM_OVERWRITE,&report)==VS_OK);
    expect(arena,0,third,0,0,8,0);
    cleanup(arena);
}

int main(void) {
    assert(vgemm_backend_check()==VS_OK);
    real_orientations(); complex_product(); conjugation_and_nonfinite();
    degenerate(); nonfinite_inputs(); failures_preserve_output();
    puts(vgemm_configuration());
    puts("GEMM: real/complex layouts, T/C, reuse, empty dimensions and failure-before-write passed");
}
