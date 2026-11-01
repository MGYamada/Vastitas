/* Experiment-only copy of storage.c: no production API or runtime edits.
 * Poisoning and coordinate checks are correctness instrumentation, not costs
 * claimed for ordinary execution. Exact arena counters exclude those probes. */
#define _POSIX_C_SOURCE 200809L
#define vstorage_new storage_new_impl
#define vstorage_allocate storage_allocate_impl
#define vstorage_drop storage_drop_impl
#define vstorage_delete storage_delete_impl
#include "../../lean-kernel/native/storage.c"
#undef vstorage_new
#undef vstorage_allocate
#undef vstorage_drop
#undef vstorage_delete
#include "../../lean-kernel/numerical/gemm.h"
#include <cblas.h>
#include <math.h>
#include <stdio.h>
#include "profile.h"
#include "calls.h"

static uint64_t m,k,n,pad,capacity[3],repetitions,arenas,guards,narrowings;
static VStorageLayout views[3];
static VStorageArena *active;
static VStorageStats total,before,timed;
static unsigned scope;
static uint64_t checksum;
static uint64_t blas_calls;
static int reported=1;
static const uint64_t poison=UINT64_C(0x7ff8000000001357);
static void require(int yes) { if(!yes) { fputs("shape experiment contract failure\n",stderr); abort(); } }
static void ok(VStorageStatus s) { require(s==VS_OK); }
static uint64_t word(double x) { uint64_t w; memcpy(&w,&x,8); return w; }
static uint64_t max(uint64_t a,uint64_t b) { return a>b?a:b; }
void shape_dgemm(enum CBLAS_ORDER order,enum CBLAS_TRANSPOSE a,enum CBLAS_TRANSPOSE b,
    blasint mm,blasint nn,blasint kk,double alpha,const double *x,blasint lda,
    const double *y,blasint ldb,double beta,double *z,blasint ldc) {
    ++blas_calls;cblas_dgemm(order,a,b,mm,nn,kk,alpha,x,lda,y,ldb,beta,z,ldc);
}
void shape_zgemm(enum CBLAS_ORDER order,enum CBLAS_TRANSPOSE a,enum CBLAS_TRANSPOSE b,
    blasint mm,blasint nn,blasint kk,const void *alpha,const void *x,blasint lda,
    const void *y,blasint ldb,const void *beta,void *z,blasint ldc) {
    ++blas_calls;cblas_zgemm(order,a,b,mm,nn,kk,alpha,x,lda,y,ldb,beta,z,ldc);
}
static int checked_add(uint64_t a,uint64_t b,uint64_t *out) { if(a>UINT64_MAX-b)return 0; *out=a+b;return 1; }
static int checked_mul(uint64_t a,uint64_t b,uint64_t *out) { if(b&&a>UINT64_MAX/b)return 0; *out=a*b;return 1; }
static int valid_layout(uint64_t elements,VStorageLayout v) {
    uint64_t width=SCALAR?16:8;
    if(v.rows>INT32_MAX||v.columns>INT32_MAX||v.leading>INT32_MAX||!v.leading||v.leading<v.rows||elements>INT64_MAX/width)return 0;
    return !v.rows||!v.columns||(v.columns-1)*v.leading+v.rows<=elements;
}
static int configure_layouts(void) {
    uint64_t lda,ldb,ldc;
    if(!checked_add(TRANSPOSE?k:m,pad,&lda)||!checked_add(k,pad,&ldb)||!checked_add(m,pad,&ldc))return 0;
    views[0]=(VStorageLayout){0,TRANSPOSE?k:m,TRANSPOSE?m:k,lda,TRANSPOSE};
    views[1]=(VStorageLayout){0,k,n,ldb,0}; views[2]=(VStorageLayout){0,m,n,ldc,0};
    return checked_mul(lda,views[0].columns,&capacity[0])&&checked_mul(ldb,n,&capacity[1])&&checked_mul(ldc,n,&capacity[2]);
}
static void failure_cleanup(void) {
    if(!reported) {
        require(!active&&total.live_bytes==0&&total.data_allocations==total.data_frees);
        fprintf(stderr,"AUDIT_FAILURE_CLEANUP {\"arenas\":%llu,\"data_allocations\":%llu,\"data_frees\":%llu,\"live_bytes\":0}\n",(unsigned long long)arenas,(unsigned long long)total.data_allocations,(unsigned long long)total.data_frees);
    }
}
void bench_config(uint64_t mm,uint64_t kk,uint64_t nn,uint64_t pp) {
    static int initialized;
    if(!initialized) { require(atexit(failure_cleanup)==0); initialized=1; }
    require(!active);m=mm;k=kk;n=nn;pad=pp;
    /* Metadata only; failed scalar narrowing never uses these descriptors. */
    (void)configure_layouts();
}
VStorageArena *vstorage_new(uint64_t budget) { require(!active); active=storage_new_impl(budget); return active; }
VStorageStatus vstorage_allocate(VStorageArena *a,uint32_t id,uint8_t scalar,uint64_t count) {
    VStorageStatus s=storage_allocate_impl(a,id,scalar,count);
    if(s==VS_OK) { Buffer *b=lookup(a,id); for(uint64_t x=0;x<b->capacity/8;++x)memcpy(b->data+x,&poison,8); }
    return s;
}
static int verify(VStorageArena *a) {
    uint64_t hash=UINT64_C(1469598103934665603);
    for(unsigned id=0;id<3;++id) {
        Buffer *b=lookup(a,id); if(!b||b->capacity!=capacity[id]*(SCALAR?16:8))return 0;
        VStorageLayout v=views[id];
        for(uint64_t x=0;x<capacity[id];++x) {
            int logical=x/v.leading<v.columns&&x%v.leading<v.rows;
            for(unsigned part=0;part<=SCALAR;++part) {
                uint64_t got;memcpy(&got,b->data+x*(SCALAR+1)+part,8);
                uint64_t want=poison;
                if(logical) {
                    double value=id==0?1.0:id==1?(part?-1.0:2.0):(part?(double)k:(SCALAR?3.0:2.0)*(double)k);
                    want=word(value);
                }
                if(got!=want)return 0;
                hash=(hash^got)*UINT64_C(1099511628211);
            }
        }
    }
    checksum=hash;return 1;
}
VStorageStatus vstorage_drop(VStorageArena *a,uint32_t id) { return storage_drop_impl(a,id); }
void vstorage_delete(VStorageArena *a) {
    if(!a)return;vstorage_close(a);VStorageStats s=vstorage_stats(a);
    require(!s.live_bytes&&s.data_allocations==s.data_frees&&active==a);
    total.data_allocations+=s.data_allocations;total.data_frees+=s.data_frees;
    total.written_bytes+=s.written_bytes;total.copied_bytes+=s.copied_bytes;
    total.metadata_allocations+=s.metadata_allocations;total.metadata_bytes=max(total.metadata_bytes,s.metadata_bytes);
    total.peak_bytes=max(total.peak_bytes,s.peak_bytes);++arenas;active=NULL;storage_delete_impl(a);
}
void bench_guard(void) { ++guards; }
void bench_narrow(void) { ++narrowings; }
void bench_verify(VStorageArena *a) { require(verify(a)); }
void bench_begin(uint32_t s,uint64_t reps,uint8_t checking) {
    require(s<2&&reps&&reps<=1000000&&checking);scope=s;repetitions=reps;
    total=(VStorageStats){0};before=vstorage_stats(active);timed=(VStorageStats){0};
    arenas=guards=narrowings=checksum=blas_calls=0;reported=0;
}
void bench_stop(void) {
    if(!scope)timed=total;
    else { VStorageStats s=vstorage_stats(active);
        timed.data_allocations=s.data_allocations-before.data_allocations;
        timed.data_frees=s.data_frees-before.data_frees;
        timed.written_bytes=s.written_bytes-before.written_bytes;
        timed.copied_bytes=s.copied_bytes-before.copied_bytes;
        timed.metadata_allocations=s.metadata_allocations-before.metadata_allocations;
    }
}
/* Independent C preflight, same physical arena and backend contract. No call
 * to vgemm_execute and no copy/packing. Immutable A/B alias is legal; C must
 * be disjoint. Zero-inner overwrite writes zero without calling BLAS. */
static int overlaps(VStorageDense *a,VStorageDense *b) {
    return a->allocation==b->allocation&&a->start<a->end&&b->start<b->end&&a->start<b->end&&b->start<a->end;
}
static VStorageStatus c_product(VStorageArena *arena,VStorageLayout output) {
    VStorageStatus status=vgemm_backend_check();if(status!=VS_OK)return status;
    VStorageDense a,b,c;
    if((status=vstorage_prepare_dense(arena,0,views[0],&a))!=VS_OK||
       (status=vstorage_prepare_dense(arena,1,views[1],&b))!=VS_OK||
       (status=vstorage_prepare_dense(arena,2,output,&c))!=VS_OK)return status;
    if(a.scalar!=b.scalar||a.scalar!=c.scalar)return VS_SCALAR;
    if(a.columns!=b.rows||a.rows!=c.rows||b.columns!=c.columns)return VS_SHAPE;
    if(output.transposed)return VS_OPERATION;
    if(overlaps(&a,&c)||overlaps(&b,&c))return VS_ALIAS;
    if(c.bytes&&(status=vstorage_prepare_write(arena,c.bytes))!=VS_OK)return status;
    if(!c.rows||!c.columns)return VS_OK;
    if(!a.columns)return vstorage_fill(arena,2,output,SCALAR,0,0);
    if(SCALAR) {
        const double alpha[2]={1,0},beta[2]={0,0};
        shape_zgemm(CblasColMajor,TRANSPOSE?CblasTrans:CblasNoTrans,CblasNoTrans,(blasint)c.rows,(blasint)c.columns,(blasint)a.columns,alpha,a.data,(blasint)a.leading,b.data,(blasint)b.leading,beta,c.data,(blasint)c.leading);
    } else shape_dgemm(CblasColMajor,TRANSPOSE?CblasTrans:CblasNoTrans,CblasNoTrans,(blasint)c.rows,(blasint)c.columns,(blasint)a.columns,1,a.data,(blasint)a.leading,b.data,(blasint)b.leading,0,c.data,(blasint)c.leading);
    vstorage_record_write(arena,c.bytes);return VS_OK;
}
static VStorageArena *c_setup(void) {
    require(configure_layouts());VStorageArena *a=vstorage_new(INT64_MAX);require(a!=NULL);
    bench_guard();require(m<=INT32_MAX);bench_guard();require(k<=INT32_MAX);bench_guard();require(n<=INT32_MAX);
    for(unsigned id=0;id<3;++id) { bench_guard();require(valid_layout(capacity[id],views[id]));ok(vstorage_allocate(a,id,SCALAR,capacity[id])); }
    ok(vstorage_fill(a,0,views[0],SCALAR,word(1),SCALAR?word(1):0));
    ok(vstorage_fill(a,1,views[1],SCALAR,word(2),SCALAR?word(-1):0));return a;
}
static void cleanup(VStorageArena *a) { for(unsigned id=0;id<3;++id)ok(vstorage_drop(a,id));vstorage_close(a);vstorage_delete(a); }
void bench_c_run(uint32_t s,uint64_t reps,uint8_t checking) {
    VStorageArena *a=s?c_setup():NULL;bench_begin(s,reps,checking);
    for(uint64_t i=0;i<reps;++i) { if(!s)a=c_setup();ok(c_product(a,views[2]));ok(c_product(a,views[2]));if(!s){bench_verify(a);cleanup(a);} }
    bench_stop();if(s){bench_verify(a);cleanup(a);}
}
void bench_report(void) {
    uint64_t width=SCALAR?16:8,cycles=scope?1:repetitions,peak=width*(capacity[0]+capacity[1]+capacity[2]);
    uint64_t init=width*(m*k+k*n),writes=2*width*m*n*repetitions,allocs=(capacity[0]!=0)+(capacity[1]!=0)+(capacity[2]!=0);
    require(!active&&arenas==cycles&&total.data_allocations==allocs*cycles&&total.data_frees==allocs*cycles);
    require(total.metadata_allocations==2*cycles&&total.peak_bytes==peak&&!total.copied_bytes);
    require(total.written_bytes==init*cycles+writes&&guards==(scope?0:6*repetitions));
    require(!narrowings||narrowings==(scope?0:9*repetitions));
    require(blas_calls==(m&&k&&n?2*repetitions:0));
    require(timed.data_allocations==(scope?0:allocs*cycles)&&timed.written_bytes==(scope?writes:total.written_bytes));
    reported=1;
    printf("{\"m\":%llu,\"k\":%llu,\"n\":%llu,\"pad\":%llu,\"repetitions\":%llu,\"checksum\":\"%016llx\",\"data_allocations\":%llu,\"data_frees\":%llu,\"live_bytes\":0,\"peak_data_bytes\":%llu,\"written_bytes\":%llu,\"copied_bytes\":%llu,\"metadata_allocations\":%llu,\"peak_metadata_bytes\":%llu,\"scope_data_allocations\":%llu,\"scope_data_frees\":%llu,\"scope_written_bytes\":%llu,\"scope_metadata_allocations\":%llu,\"scope_guards\":%llu,\"scope_nat_narrowings\":%llu,\"blas_calls\":%llu}\n",
    (unsigned long long)m,(unsigned long long)k,(unsigned long long)n,(unsigned long long)pad,(unsigned long long)repetitions,(unsigned long long)checksum,(unsigned long long)total.data_allocations,(unsigned long long)total.data_frees,(unsigned long long)peak,(unsigned long long)total.written_bytes,(unsigned long long)total.copied_bytes,(unsigned long long)total.metadata_allocations,(unsigned long long)total.metadata_bytes,(unsigned long long)timed.data_allocations,(unsigned long long)timed.data_frees,(unsigned long long)timed.written_bytes,(unsigned long long)timed.metadata_allocations,(unsigned long long)guards,(unsigned long long)narrowings,(unsigned long long)blas_calls);
}
#ifdef BENCH_STANDALONE
int main(void) {
    require(vgemm_backend_check()==VS_OK);fprintf(stderr,"backend=%s; parallel=%d; threads=%d\n",vgemm_configuration(),openblas_get_parallel(),openblas_get_num_threads());
    const uint64_t cases[][4]={{2,3,4,0},{3,5,2,2},{17,13,19,3},{0,3,4,1},{2,0,4,1},{2,3,0,1}};
    for(unsigned x=0;x<6;++x) {
        bench_config(cases[x][0],cases[x][1],cases[x][2],cases[x][3]);
        VStorageArena *a=c_setup();ok(c_product(a,views[2]));require(verify(a));uint64_t hash=checksum;
        VStorageLayout bad=views[2];bad.leading=0;VStorageStats saved=vstorage_stats(a);
        require(c_product(a,bad)!=VS_OK);require(vgemm_execute(a,0,views[0],0,1,views[1],0,2,bad,VGEMM_OVERWRITE,NULL)!=VS_OK);
        require(vstorage_stats(a).written_bytes==saved.written_bytes&&verify(a)&&checksum==hash);
        a->stats.written_bytes=UINT64_MAX;
        if(m&&n) {
            require(c_product(a,views[2])==VS_OVERFLOW);
            require(vgemm_execute(a,0,views[0],0,1,views[1],0,2,views[2],VGEMM_OVERWRITE,NULL)==VS_OVERFLOW);
            require(a->stats.written_bytes==UINT64_MAX&&verify(a)&&checksum==hash);
        }
        a->stats.written_bytes=saved.written_bytes;
        if(capacity[2]) { uint64_t old;memcpy(&old,lookup(a,2)->data,8);uint64_t corrupt=word(42);memcpy(lookup(a,2)->data,&corrupt,8);require(!verify(a));memcpy(lookup(a,2)->data,&old,8); }
        ok(vgemm_execute(a,0,views[0],0,1,views[1],0,2,views[2],VGEMM_OVERWRITE,NULL));
        require(verify(a)&&checksum==hash);cleanup(a);
        for(unsigned s=0;s<2;++s) { bench_c_run(s,3,1);bench_report(); }
    }
    fputs("coordinate, padding, source, zero axes, corruption, preflight preservation and costs passed\n",stderr);return 0;
}
#endif
