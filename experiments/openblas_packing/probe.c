/* Paired backend-only D/Z CBLAS fixtures. Exact bounded integral arithmetic
 * checks both transformations, complete input/padding preservation and output.
 * This does not grant public source authority or measure operation timings. */
#include <assert.h>
#include <cblas.h>
#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#ifdef VPACK_DIAGNOSTIC
#include "../openblas_workspace/observer.h"
void vpack_dump(void);
#else
static void vobs_mark(unsigned phase) { (void)phase; }
static void vobs_dump(void) {}
static void vpack_dump(void) {}
#endif
extern void gotoblas_quit(void);
_Static_assert(sizeof(blasint) == 4 && sizeof(double) == 8, "LP64 binary64 profile");
typedef struct { int64_t r, i; } Z;
typedef struct { double *base, *data; size_t rows, cols, ld, components, words; } Matrix;
static const uint64_t padding = UINT64_C(0x7ff8123456789abc);
static uint64_t bits(double x) { uint64_t r; memcpy(&r,&x,8); return r; }
static Z input(unsigned which, size_t r, size_t c, unsigned scalar) {
    return (Z){(int)((r+2*c+which)%5)-2, scalar ? (int)((2*r+c+which)%3)-1 : 0};
}
static Z term(size_t r, size_t c, size_t k, unsigned scalar, unsigned ta, unsigned tb) {
    Z a=ta ? input(0,k,r,scalar) : input(0,r,k,scalar);
    Z b=tb ? input(1,c,k,scalar) : input(1,k,c,scalar);
    if (ta==2) a.i=-a.i;
    if (tb==2) b.i=-b.i;
    return (Z){a.r*b.r-a.i*b.i, a.r*b.i+a.i*b.r};
}
static Z product(size_t r, size_t c, size_t k, unsigned scalar, unsigned ta, unsigned tb, unsigned beta) {
    Z full={0,0}, tail={0,0}, old=input(2,r,c,scalar);
    for (size_t t=0;t<15;++t) {
        Z z=term(r,c,t,scalar,ta,tb);
        full.r+=z.r; full.i+=z.i;
        if(t<k%15) {tail.r+=z.r;tail.i+=z.i;}
    }
    return (Z){full.r*(int64_t)(k/15)+tail.r+beta*old.r,
               full.i*(int64_t)(k/15)+tail.i+beta*old.i};
}
static Matrix matrix(size_t rows, size_t cols, unsigned scalar, unsigned which) {
    Matrix a={.rows=rows,.cols=cols,.ld=rows+3,.components=scalar+1};
    a.words=a.ld*cols*a.components;
    a.base=malloc((a.words+64)*8); assert(a.base); a.data=a.base+32;
    double sentinel; memcpy(&sentinel,&padding,8);
    for(size_t i=0;i<a.words+64;++i) a.base[i]=sentinel;
    for(size_t j=0;j<cols;++j) for(size_t i=0;i<rows;++i) {
        Z z=input(which,i,j,scalar);
        a.data[(j*a.ld+i)*a.components]=(double)z.r;
        if(scalar) a.data[(j*a.ld+i)*a.components+1]=(double)z.i;
    }
    return a;
}
static uint64_t verify(Matrix a, unsigned which, size_t k, unsigned scalar, unsigned ta, unsigned tb, unsigned beta) {
    uint64_t hash=UINT64_C(1469598103934665603);
    for(size_t i=0;i<a.words+64;++i) {
        uint64_t want=padding, got=bits(a.base[i]);
        if(i>=32 && i<32+a.words) {
            size_t offset=i-32, c=offset/a.components/a.ld, r=offset/a.components%a.ld;
            if(r<a.rows) {
                Z z=which==2 ? product(r,c,k,scalar,ta,tb,beta) : input(which,r,c,scalar);
                double expected=(double)(offset%a.components ? z.i : z.r);
                assert(a.base[i]==expected);
                want=bits(expected);
                if(which==2 && a.base[i]==0.0) got=bits(0.0);
            }
        }
        assert(got==want);
        hash=(hash^got)*UINT64_C(1099511628211);
    }
    return hash;
}
int main(int argc, char **argv) {
    assert(argc==8 && openblas_get_num_threads()==1);
    unsigned scalar=(unsigned)strtoul(argv[1],NULL,10);
    size_t m=strtoul(argv[2],NULL,10), n=strtoul(argv[3],NULL,10), k=strtoul(argv[4],NULL,10);
    unsigned ta=(unsigned)strtoul(argv[5],NULL,10), tb=(unsigned)strtoul(argv[6],NULL,10);
    unsigned beta=(unsigned)strtoul(argv[7],NULL,10);
    assert(scalar<=1 && ta<=2 && tb<=2 && beta<=1 && m<=50000 && n<=50000 && k<=50000);
    Matrix a=matrix(ta?k:m,ta?m:k,scalar,0), b=matrix(tb?n:k,tb?k:n,scalar,1);
    Matrix c=matrix(m,n,scalar,2);
    const enum CBLAS_TRANSPOSE t[3]={CblasNoTrans,CblasTrans,CblasConjTrans};
    vobs_mark(10); vobs_mark(11);
    if(!scalar) cblas_dgemm(CblasColMajor,t[ta],t[tb],(blasint)m,(blasint)n,(blasint)k,
                            1,a.data,(blasint)a.ld,b.data,(blasint)b.ld,beta,c.data,(blasint)c.ld);
    else {
        const double alpha[2]={1,0}, betaz[2]={beta,0};
        cblas_zgemm(CblasColMajor,t[ta],t[tb],(blasint)m,(blasint)n,(blasint)k,
                    alpha,a.data,(blasint)a.ld,b.data,(blasint)b.ld,betaz,c.data,(blasint)c.ld);
    }
    vobs_mark(12);
    uint64_t hashes[3]={verify(a,0,k,scalar,ta,tb,beta),verify(b,1,k,scalar,ta,tb,beta),verify(c,2,k,scalar,ta,tb,beta)};
    printf("{\"kind\":\"gemm\",\"configuration\":\"%s\",\"scalar\":%u,\"m\":%zu,\"n\":%zu,\"k\":%zu,"
           "\"ta\":%u,\"tb\":%u,\"beta\":%u,\"checksums\":[\"%016" PRIx64 "\",\"%016" PRIx64 "\",\"%016" PRIx64 "\"],\"matrices\":[",
           openblas_get_config(),scalar,m,n,k,ta,tb,beta,hashes[0],hashes[1],hashes[2]);
    Matrix all[3]={a,b,c};
    for(size_t i=0;i<3;++i)
        printf("%s{\"address\":\"0x%" PRIxPTR "\",\"rows\":%zu,\"cols\":%zu,\"ld\":%zu}",
               i ? "," : "",(uintptr_t)all[i].data,all[i].rows,all[i].cols,all[i].ld);
    puts("]}");
    free(a.base); free(b.base); free(c.base);
    vobs_mark(18); gotoblas_quit(); vobs_mark(19); vobs_dump(); vpack_dump();
    return 0;
}
