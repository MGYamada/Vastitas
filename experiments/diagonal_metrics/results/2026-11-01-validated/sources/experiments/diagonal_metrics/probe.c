#define _POSIX_C_SOURCE 200809L
#include "direct.h"
#include "gemm.h"
#include <assert.h>
#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

static uint64_t clock_ns(void) {
    struct timespec t; assert(clock_gettime(CLOCK_MONOTONIC,&t)==0);
    return (uint64_t)t.tv_sec*UINT64_C(1000000000)+(uint64_t)t.tv_nsec;
}
static uint64_t bits(double x) { uint64_t r; memcpy(&r,&x,8); return r; }
static uint64_t hash(const VStorageDense *v) {
    uint64_t h=UINT64_C(1469598103934665603); unsigned width=v->scalar?2:1;
    for(uint64_t j=0;j<v->columns;++j) for(uint64_t i=0;i<v->rows;++i)
        for(unsigned k=0;k<width;++k) { h^=bits(v->data[width*(j*v->leading+i)+k]); h*=UINT64_C(1099511628211); }
    return h;
}
static void sample(unsigned checked,unsigned pair,unsigned scalar,uint64_t n,uint64_t m,unsigned uniform,
                   uint64_t repetitions,unsigned iteration,unsigned order,unsigned adapter) {
    VStorageArena *arena=vstorage_new(UINT64_C(1)<<30); assert(arena);
    unsigned count=pair?4:2; uint64_t width=scalar?16:8;
    VStorageLayout layouts[4]={{width,n,pair?1:m,n+2,0},{width,pair?n:m,pair?1:n,(pair?n:m)+2,0},
        {width,n,1,n+2,0},{width,1,1,2,0}};
    VStorageDense views[4];
    for(unsigned id=0;id<count;++id) {
        assert(vstorage_allocate(arena,id,(uint8_t)scalar,1+layouts[id].leading*layouts[id].columns)==VS_OK);
        assert(vstorage_prepare_dense(arena,id,layouts[id],views+id)==VS_OK);
        if(id==0 || (pair&&id==1))
            assert(vstorage_fill(arena,id,layouts[id],(uint8_t)scalar,bits(id?3:1),bits(id?-2:1))==VS_OK);
    }
    uint64_t max=n>m?n:m, entries=uniform?1:max;
    double *source=malloc(entries*8),*target=malloc(entries*8);
    uint8_t *sb=malloc(entries*8),*tb=malloc(entries*8); assert(source&&target&&sb&&tb);
    for(uint64_t i=0;i<entries;++i) {
        source[i]=(i%2)?-4:2; target[i]=(i%2)?-2:3;
        for(unsigned k=0;k<8;++k) { sb[8*i+k]=(uint8_t)(bits(source[i])>>(8*k)); tb[8*i+k]=(uint8_t)(bits(target[i])>>(8*k)); }
    }
    VDiagonal s={sb,(size_t)((uniform?1:(pair?n:m))*8),(uint8_t)uniform};
    VDiagonal t={tb,(size_t)((uniform?1:n)*8),(uint8_t)uniform};
    VStorageStats before=vstorage_stats(arena); uint64_t written=pair?(n+1)*width:n*m*width;
    uint64_t start=clock_ns();
    for(uint64_t r=0;r<repetitions;++r) {
        if(adapter) {
            if(pair) assert(vgemm_diagonal_pair(arena,0,layouts[0],1,layouts[1],3,layouts[3],2,layouts[2],s,1,0,NULL)==VS_OK);
            else assert(vdiagonal_adjoint(arena,0,layouts[0],1,layouts[1],s,t,1)==VS_OK);
        } else {
            if(checked) assert(direct_preflight(arena,pair,layouts,s,t)==VS_OK);
            if(pair) direct_pair(views,views+1,views+2,views+3,source,uniform);
            else direct_adjoint(views,views+1,source,target,uniform);
            if(pair) { vstorage_record_write(arena,n*width);vstorage_record_write(arena,width); }
            else vstorage_record_write(arena,written);
        }
    }
    uint64_t elapsed=clock_ns()-start;
    VStorageStats after=vstorage_stats(arena);
    assert(after.data_allocations==before.data_allocations && after.copied_bytes==before.copied_bytes);
    assert(after.written_bytes-before.written_bytes==repetitions*written);
    /* Independent post-timing coordinate reference, beyond matching hashes.
     * This workload uses bounded integers and exact binary fractions. */
    if(pair) {
        double total=0;
        for(uint64_t i=0;i<n;++i) {
            total+=source[i];
            assert(views[2].data[(scalar?2:1)*i]==3*source[i]);
            if(scalar) assert(views[2].data[2*i+1]==-2*source[i]);
        }
        assert(views[3].data[0]==(scalar?total:3*total));
        if(scalar) assert(views[3].data[1]==-5*total);
    } else {
        for(uint64_t j=0;j<n;++j) for(uint64_t i=0;i<m;++i) {
            uint64_t at=(scalar?2:1)*(j*views[1].leading+i);
            assert(views[1].data[at]==target[j]/source[i]);
            if(scalar) assert(views[1].data[at+1]==-target[j]/source[i]);
        }
    }
    uint64_t digest=hash(views+(pair?3:1)); if(pair) digest^=hash(views+2);
    printf("%s,%s,%u,%"PRIu64",%"PRIu64",%u,%u,%u,%s,%"PRIu64",%"PRIu64",%"PRIu64",%"PRIu64",%"PRIu64",%"PRIu64"\n",
        checked?"checked":"prepared",pair?"pair":"adjoint",scalar,n,m,uniform,iteration,order,adapter?"adapter":"c",repetitions,elapsed,
        digest,after.data_allocations-before.data_allocations,after.copied_bytes-before.copied_bytes,after.written_bytes-before.written_bytes);
    free(source);free(target);free(sb);free(tb);vstorage_delete(arena);
}
int main(int argc,char **argv) {
    assert(argc==6); unsigned pair=(unsigned)strtoul(argv[1],NULL,10),scalar=(unsigned)strtoul(argv[2],NULL,10);
    uint64_t n=strtoull(argv[3],NULL,10),m=strtoull(argv[4],NULL,10),reps=strtoull(argv[5],NULL,10);
    assert(pair<=1&&scalar<=1&&n>0&&m>0&&n<=4096&&m<=4096&&reps>0);
    assert(vgemm_backend_check()==VS_OK);
    for(unsigned checked=0;checked<2;++checked)
        for(unsigned iteration=0;iteration<11;++iteration) for(unsigned order=0;order<2;++order)
            sample(checked,pair,scalar,n,m,0,reps,iteration,order,(iteration+order)%2);
    return 0;
}
