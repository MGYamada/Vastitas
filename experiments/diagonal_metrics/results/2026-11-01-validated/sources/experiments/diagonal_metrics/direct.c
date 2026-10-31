/* Separate translation unit, no LTO. Same algorithm/iteration order/backend,
 * ordinary prepared C pointers and exact pre-realized diagonal coefficients. */
#include "direct.h"
#include "gemm.h"
#include <cblas.h>

/* Matched checked-C scope for the fixed conjugate-left/nonconjugate-right
 * requests used here. Uses the same independent primitive validations before
 * any write. The prepared-C scope omits this complete preflight explicitly. */
VStorageStatus direct_preflight(VStorageArena *arena, unsigned pair,
    const VStorageLayout *layouts, VDiagonal source, VDiagonal target) {
    VStorageDense a,b,c,s;
    VStorageStatus status;
    if (layouts[0].transposed>1 || layouts[pair?3:1].transposed || (pair&&layouts[2].transposed)) return VS_OPERATION;
    if(pair && (status=vgemm_backend_check())!=VS_OK) return status;
    if((status=vstorage_prepare_dense(arena,0,layouts[0],&a))!=VS_OK ||
       (status=vstorage_prepare_dense(arena,1,layouts[1],&b))!=VS_OK) return status;
    if(a.scalar!=b.scalar) return VS_SCALAR;
    if(!pair) {
        if(a.columns!=b.rows || a.rows!=b.columns) return VS_SHAPE;
        if(vdiagonal_overlaps(&a,&b)) return VS_ALIAS;
        if((status=vdiagonal_validate(source,a.columns))!=VS_OK ||
           (status=vdiagonal_validate(target,a.rows))!=VS_OK) return status;
        return vstorage_prepare_write(arena,b.bytes);
    }
    if((status=vstorage_prepare_dense(arena,2,layouts[2],&s))!=VS_OK ||
       (status=vstorage_prepare_dense(arena,3,layouts[3],&c))!=VS_OK) return status;
    if(a.scalar!=s.scalar || a.scalar!=c.scalar) return VS_SCALAR;
    if(a.columns!=1 || b.columns!=1 || s.columns!=1 || a.rows!=s.rows || b.rows!=s.rows || c.rows!=1 || c.columns!=1) return VS_SHAPE;
    /* Fixed owners 0,1,2,3 are distinct; still check actual native envelopes. */
    if(vdiagonal_overlaps(&a,&c) || vdiagonal_overlaps(&b,&c)) return VS_ALIAS;
    if((status=vdiagonal_validate(source,s.rows))!=VS_OK) return status;
    if(s.bytes>UINT64_MAX-c.bytes) return VS_OVERFLOW;
    return vstorage_prepare_write(arena,s.bytes+c.bytes);
}
void direct_adjoint(const VStorageDense *a, const VStorageDense *b,
                    const double *source, const double *target, unsigned uniform) {
    unsigned width=a->scalar?2:1;
    for(uint64_t j=0;j<b->columns;++j) for(uint64_t i=0;i<b->rows;++i) {
        uint64_t from=(i*a->leading+j)*width, to=(j*b->leading+i)*width;
        double s=source[uniform?0:i],t=target[uniform?0:j];
        b->data[to]=(a->data[from]*t)/s;
        if(a->scalar) b->data[to+1]=(-a->data[from+1]*t)/s;
    }
}
void direct_pair(const VStorageDense *a, const VStorageDense *b,
                 const VStorageDense *scratch, const VStorageDense *out,
                 const double *weights, unsigned uniform) {
    unsigned width=a->scalar?2:1;
    for(uint64_t i=0;i<a->rows;++i) {
        scratch->data[width*i]=b->data[width*i]*weights[uniform?0:i];
        if(a->scalar) scratch->data[width*i+1]=b->data[width*i+1]*weights[uniform?0:i];
    }
    if(a->scalar) {
        const double one[2]={1,0},zero[2]={0,0};
        cblas_zgemm(CblasColMajor,CblasConjTrans,CblasNoTrans,1,1,(blasint)a->rows,
                    one,a->data,(blasint)a->leading,scratch->data,(blasint)scratch->leading,
                    zero,out->data,(blasint)out->leading);
    } else {
        cblas_dgemm(CblasColMajor,CblasTrans,CblasNoTrans,1,1,(blasint)a->rows,
                    1,a->data,(blasint)a->leading,scratch->data,(blasint)scratch->leading,
                    0,out->data,(blasint)out->leading);
    }
}
