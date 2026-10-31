#include "diagonal.h"
#include <assert.h>
#include <stdio.h>
#include <string.h>

static uint64_t bits(double value) { uint64_t result; memcpy(&result, &value, 8); return result; }
static void encode(uint8_t *output, double value) {
    uint64_t raw = bits(value);
    for (unsigned i = 0; i < 8; ++i) output[i] = (uint8_t)(raw >> (8*i));
}
static VStorageLayout layout(unsigned scalar, uint64_t rows, uint64_t columns, uint64_t leading, uint8_t transpose) {
    return (VStorageLayout){scalar ? 16 : 8,rows,columns,leading,transpose};
}
static void rectangles(unsigned scalar, unsigned transpose, uint8_t conjugate) {
    VStorageArena *arena = vstorage_new(4096); assert(arena);
    assert(vstorage_allocate(arena,0,(uint8_t)scalar,20)==VS_OK);
    assert(vstorage_allocate(arena,1,(uint8_t)scalar,20)==VS_OK);
    VStorageLayout input = transpose ? layout(scalar,2,3,4,1) : layout(scalar,3,2,4,0);
    VStorageLayout output = layout(scalar,2,3,3,0);
    for (uint64_t j=0;j<2;++j) for (uint64_t i=0;i<3;++i) {
        double value=(double)(1+2*i+j);
        assert(vstorage_store(arena,0,input,i,j,(uint8_t)scalar,bits(value),bits(value))==VS_OK);
    }
    uint8_t source[16],target[24];
    encode(source,2); encode(source+8,-4);
    encode(target,3); encode(target+8,5); encode(target+16,-2);
    VDiagonal v={source,sizeof(source),0}, w={target,sizeof(target),0};
    VStorageStats before=vstorage_stats(arena);
    assert(vdiagonal_adjoint(arena,0,input,1,output,v,w,conjugate)==VS_OK);
    double gv[2]={2,-4},gw[3]={3,5,-2};
    for (uint64_t j=0;j<3;++j) for (uint64_t i=0;i<2;++i) {
        double value=((double)(1+2*j+i)*gw[j])/gv[i];
        assert(vstorage_expect(arena,1,output,i,j,(uint8_t)scalar,bits(value),bits(conjugate?-value:value))==VS_OK);
    }
    VStorageStats after=vstorage_stats(arena);
    assert(after.data_allocations==before.data_allocations && after.copied_bytes==before.copied_bytes);
    assert(after.written_bytes-before.written_bytes==6*(scalar?16:8));
    /* A malformed last entry must fail before the first destination element. */
    encode(target+16,1.5);
    before=vstorage_stats(arena);
    assert(vdiagonal_adjoint(arena,0,input,1,output,v,w,conjugate)==VS_OPERATION);
    assert(vstorage_stats(arena).written_bytes==before.written_bytes);
    assert(vstorage_expect(arena,1,output,0,0,(uint8_t)scalar,bits(1.5),bits(conjugate?-1.5:1.5))==VS_OK);
    encode(target+16,-2);
    assert(vdiagonal_adjoint(arena,0,input,0,output,v,w,conjugate)==VS_ALIAS);
    vstorage_close(arena);
    after=vstorage_stats(arena); assert(after.data_allocations==after.data_frees && after.live_bytes==0);
    vstorage_delete(arena);
}
static void entries(void) {
    uint8_t bytes[8]; VDiagonal d={bytes,8,1};
    for (unsigned i=0;i<5;++i) {
        const double accepted[]={1,-1,9007199254740992.0,-9007199254740992.0,3};
        encode(bytes,accepted[i]); assert(vdiagonal_validate(d,400000)==VS_OK);
    }
    const uint64_t rejected[]={0,UINT64_C(0x8000000000000000),UINT64_C(0x7ff0000000000000),UINT64_C(0x7ff8000000000000),UINT64_C(0x3ff8000000000000),UINT64_C(0x4340000000000001)};
    for (unsigned i=0;i<sizeof(rejected)/sizeof(*rejected);++i) {
        for (unsigned j=0;j<8;++j) bytes[j]=(uint8_t)(rejected[i]>>(8*j));
        assert(vdiagonal_validate(d,1)==VS_OPERATION);
    }
    assert(vdiagonal_validate((VDiagonal){NULL,0,0},0)==VS_OK);
    assert(vdiagonal_validate((VDiagonal){NULL,0,1},0)==VS_SHAPE);
}
int main(void) {
    entries();
    for (unsigned scalar=0;scalar<2;++scalar) for (unsigned transpose=0;transpose<2;++transpose)
        for(uint8_t conjugate=0;conjugate<2;++conjugate) rectangles(scalar,transpose,conjugate);
    puts("Diagonal: exact bounded coefficients, real/complex padded/transposed adjoints, failure preservation and allocation-free writes passed");
    return 0;
}
