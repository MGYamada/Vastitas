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
/* The decoder before #566: eight single-byte loads and shifts per entry, with
 * the uniform test inside each access. Outputs must stay bit-identical to it. */
static uint64_t old_bits_at(VDiagonal diagonal, uint64_t index) {
    const uint8_t *data = diagonal.data + 8 * (diagonal.uniform ? 0 : index);
    uint64_t result = 0;
    for (unsigned i = 0; i < 8; ++i) result |= (uint64_t)data[i] << (8 * i);
    return result;
}
static double old_entry(VDiagonal diagonal, uint64_t index) {
    uint64_t raw = old_bits_at(diagonal, index); double value; memcpy(&value, &raw, 8); return value;
}
static uint64_t state = UINT64_C(0x9e3779b97f4a7c15);
static uint64_t next(void) { /* splitmix64: deterministic and host independent */
    uint64_t z = (state += UINT64_C(0x9e3779b97f4a7c15));
    z = (z ^ (z >> 30)) * UINT64_C(0xbf58476d1ce4e5b9);
    z = (z ^ (z >> 27)) * UINT64_C(0x94d049bb133111eb);
    return z ^ (z >> 31);
}
static double sample(void) {
    switch (next() % 16) {
    case 0: return 0.0;
    case 1: return -0.0;
    case 2: return 1.0 / 0.0;
    case 3: return -1.0 / 0.0;
    default: { /* finite, with varied exponents, signs and full significands */
        uint64_t raw = (next() & UINT64_C(0x800fffffffffffff)) | ((UINT64_C(983) + next() % 81) << 52);
        double value; memcpy(&value, &raw, 8); return value;
    }
    }
}
static double coefficient(void) { /* accepted entries: nonzero integers up to 2^53 */
    uint64_t magnitude = next() % 4 ? 1 + next() % 4096 : 1 + next() % (UINT64_C(1) << 53);
    return next() % 2 ? -(double)magnitude : (double)magnitude;
}
/* Unaligned tables exercise memcpy decoding at every byte offset. */
static VDiagonal table(uint8_t *storage, unsigned shift, uint64_t count, uint8_t uniform) {
    for (uint64_t i = 0; i < (uniform ? 1 : count); ++i) encode(storage + shift + 8*i, coefficient());
    return (VDiagonal){storage + shift, 8*(uniform ? 1 : count), uniform};
}
static void decoding(void) {
    uint8_t raw[8*64+8];
    for (unsigned i = 0; i < sizeof(raw); ++i) raw[i] = (uint8_t)next();
    for (unsigned shift = 0; shift < 8; ++shift) for (uint8_t uniform = 0; uniform < 2; ++uniform) {
        VDiagonal d = {raw + shift, uniform ? 8 : 8*64, uniform};
        for (uint64_t i = 0; i < 64; ++i) {
            assert(bits(vdiagonal_entry(d, i)) == old_bits_at(d, i));
            assert(bits(vdiagonal_entry(d, i)) == bits(old_entry(d, i)));
        }
    }
}
static void old_decoding_outputs(unsigned scalar, unsigned transpose, uint8_t conjugate,
                                 uint8_t source_uniform, uint8_t target_uniform, unsigned shift) {
    enum { M = 5, N = 7 };
    const uint64_t width = scalar ? 2 : 1;
    VStorageArena *arena = vstorage_new(1 << 16); assert(arena);
    for (uint32_t id = 0; id < 4; ++id) assert(vstorage_allocate(arena, id, (uint8_t)scalar, 64) == VS_OK);
    uint8_t source_bytes[8*N+8], target_bytes[8*M+8];
    VDiagonal source = table(source_bytes, shift, N, source_uniform);
    VDiagonal target = table(target_bytes, 7 - shift, M, target_uniform);
    assert(vdiagonal_validate(source, N) == VS_OK && vdiagonal_validate(target, M) == VS_OK);
    /* Adjoint: logical input is M-by-N with a padded leading dimension (layouts
     * name physical rows/columns); the output is N-by-M. */
    VStorageLayout input = transpose ? layout(scalar, N, M, N+2, 1) : layout(scalar, M, N, M+3, 0);
    VStorageLayout output = layout(scalar, N, M, N+1, 0);
    double re[M][N], im[M][N];
    for (uint64_t i = 0; i < M; ++i) for (uint64_t j = 0; j < N; ++j) {
        re[i][j] = sample(); im[i][j] = scalar ? sample() : 0.0;
        assert(vstorage_store(arena, 0, input, i, j, (uint8_t)scalar, bits(re[i][j]), bits(im[i][j])) == VS_OK);
    }
    assert(vdiagonal_adjoint(arena, 0, input, 1, output, source, target, conjugate) == VS_OK);
    for (uint64_t j = 0; j < M; ++j) for (uint64_t i = 0; i < N; ++i) {
        double tw = old_entry(target, j), sw = old_entry(source, i);
        double real = (re[j][i] * tw) / sw;
        double imaginary = ((conjugate ? -im[j][i] : im[j][i]) * tw) / sw;
        assert(vstorage_expect(arena, 1, output, i, j, (uint8_t)scalar, bits(real), scalar ? bits(imaginary) : 0) == VS_OK);
    }
    /* Scaling a column, contiguous or with an explicit physical stride. */
    VStorageLayout column = transpose ? (VStorageLayout){width*8, 1, N, 3, 1} : (VStorageLayout){width*8, N, 1, N, 0};
    VStorageLayout scaled = {width*8*2, N, 1, N, 0};
    double x[N], y[N];
    for (uint64_t i = 0; i < N; ++i) {
        x[i] = sample(); y[i] = scalar ? sample() : 0.0;
        assert(vstorage_store(arena, 2, column, i, 0, (uint8_t)scalar, bits(x[i]), bits(y[i])) == VS_OK);
    }
    assert(vdiagonal_scale(arena, 2, column, 3, scaled, source, conjugate) == VS_OK);
    for (uint64_t i = 0; i < N; ++i) {
        double w = old_entry(source, i);
        double real = x[i] * w, imaginary = (conjugate ? -y[i] : y[i]) * w;
        assert(vstorage_expect(arena, 3, scaled, i, 0, (uint8_t)scalar, bits(real), scalar ? bits(imaginary) : 0) == VS_OK);
    }
    vstorage_delete(arena);
}
int main(void) {
    entries();
    decoding();
    for (unsigned scalar=0;scalar<2;++scalar) for (unsigned transpose=0;transpose<2;++transpose)
        for (uint8_t conjugate=0;conjugate<2;++conjugate) for (uint8_t su=0;su<2;++su)
            for (uint8_t tu=0;tu<2;++tu) for (unsigned shift=0;shift<8;shift+=3)
                old_decoding_outputs(scalar,transpose,conjugate,su,tu,shift);
    for (unsigned scalar=0;scalar<2;++scalar) for (unsigned transpose=0;transpose<2;++transpose)
        for(uint8_t conjugate=0;conjugate<2;++conjugate) rectangles(scalar,transpose,conjugate);
    puts("Diagonal: exact bounded coefficients, unaligned whole-entry decoding bit-identical to bytewise decoding, real/complex padded/transposed adjoints and scaling, failure preservation and allocation-free writes passed");
    return 0;
}
