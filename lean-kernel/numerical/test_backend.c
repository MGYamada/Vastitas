#include "gemm.h"
#include <assert.h>
#include <pthread.h>
#include <stdatomic.h>
#include <stdio.h>
#include <string.h>
#include <sys/wait.h>
#include <unistd.h>

#ifdef VGEMM_TEST_BACKEND
static char good_configuration[]="OpenBLAS 0.3.34 SINGLE_THREADED";
static char *configuration=good_configuration;
static int parallel;
static atomic_uint configuration_calls, parallel_calls;
char *vgemm_test_config(void) {
    atomic_fetch_add(&configuration_calls,1);
    return configuration;
}
int vgemm_test_parallel(void) {
    atomic_fetch_add(&parallel_calls,1);
    return parallel;
}

static void rejected_backend(void) {
    const char *original=configuration;
    VStorageArena *arena=vstorage_new(64); assert(arena);
    VStorageLayout one={0,1,1,1,0};
    for(uint32_t id=0;id<4;++id) {
        assert(vstorage_allocate(arena,id,0,1)==VS_OK);
        assert(vstorage_fill(arena,id,one,0,0x4008000000000000ULL,0)==VS_OK);
    }
    VGemmReport report={19,23};
    uint8_t weight[8]={0,0,0,0,0,0,0,0x40}; /* exactly 2 */
    VDiagonal diagonal={weight,sizeof(weight),1};
    uint64_t written=vstorage_stats(arena).written_bytes;
    for(unsigned repeat=0;repeat<3;++repeat) {
        assert(vgemm_execute(arena,0,one,0,1,one,0,2,one,VGEMM_OVERWRITE,&report)==VS_ABI);
        assert(vgemm_diagonal_pair(arena,0,one,1,one,2,one,3,one,diagonal,0,0,&report)==VS_ABI);
        /* A cached failure cannot be retried into success by changing the
         * mock provider. Real linked-backend identity is process-lifetime. */
        configuration=good_configuration; parallel=0;
    }
    const char *snapshot=vgemm_configuration();
    if(original && strlen(original)<256) assert(snapshot && snapshot!=original && strcmp(snapshot,original)==0);
    else assert(snapshot==NULL);
    assert(atomic_load(&configuration_calls)==1 && atomic_load(&parallel_calls)<=1);
    assert(report.kernel_calls==19 && report.written_bytes==23);
    assert(vstorage_expect(arena,2,one,0,0,0,0x4008000000000000ULL,0)==VS_OK);
    assert(vstorage_expect(arena,3,one,0,0,0,0x4008000000000000ULL,0)==VS_OK);
    assert(vstorage_stats(arena).written_bytes==written);
    vstorage_delete(arena);
}

static void fresh_process_rejections(void) {
    char oversized[300];
    memset(oversized,'x',sizeof(oversized));
    memcpy(oversized,"OpenBLAS 0.3.34 ",16);
    oversized[sizeof(oversized)-1]=0;
    struct { char *configuration; int parallel; } bad[]={
        {NULL,0},{"OpenBLAS 0.3.33 SINGLE_THREADED",0},
        {"OpenBLAS 0.3.340 SINGLE_THREADED",0},
        {"OpenBLAS 0.3.34 USE64BITINT SINGLE_THREADED",0},
        {"unrelated BLAS 0.3.34",0},{good_configuration,1},
        {good_configuration,2},{oversized,0}
    };
    /* Fork only before any threads or backend initialization. Each case gets
     * a fresh once cell; no production reset hook is needed. */
    for(unsigned i=0;i<sizeof(bad)/sizeof(bad[0]);++i) {
        pid_t child=fork(); assert(child>=0);
        if(child==0) {
            configuration=bad[i].configuration; parallel=bad[i].parallel;
            rejected_backend();
            _exit(0);
        }
        int status=0;
        assert(waitpid(child,&status,0)==child && WIFEXITED(status) && WEXITSTATUS(status)==0);
    }
    assert(atomic_load(&configuration_calls)==0);
    puts("GEMM: eight fresh-process backend failures stay cached and preserve output/scratch/report");
}
#endif

enum { WORKERS=16, REPETITIONS=1000 };
static pthread_mutex_t gate=PTHREAD_MUTEX_INITIALIZER;
static pthread_cond_t condition=PTHREAD_COND_INITIALIZER;
static unsigned ready;
static int start;

static void *worker(void *argument) {
    const unsigned ordinal=*(const unsigned *)argument;
    VStorageArena *arena=vstorage_new(64); assert(arena);
    VStorageLayout one={0,1,1,1,0};
    for(uint32_t id=0;id<3;++id) {
        assert(vstorage_allocate(arena,id,0,1)==VS_OK);
        if(id<2) assert(vstorage_fill(arena,id,one,0,0x4008000000000000ULL,0)==VS_OK);
    }
    assert(pthread_mutex_lock(&gate)==0);
    ++ready;
    assert(pthread_cond_broadcast(&condition)==0);
    while(!start) assert(pthread_cond_wait(&condition,&gate)==0);
    assert(pthread_mutex_unlock(&gate)==0);
    if(ordinal%2) assert(vgemm_backend_check()==VS_OK);
    for(unsigned i=0;i<REPETITIONS;++i) {
        /* These paths race for first initialization, then reuse its result. */
        const char *config=vgemm_configuration();
        assert(config && strncmp(config,"OpenBLAS 0.3.34 ",16)==0);
        assert(vgemm_backend_check()==VS_OK);
        VGemmReport report={0,0};
        assert(vgemm_execute(arena,0,one,0,1,one,0,2,one,VGEMM_OVERWRITE,&report)==VS_OK);
        assert(report.kernel_calls==1 && report.written_bytes==8);
        assert(vstorage_expect(arena,2,one,0,0,0,0x4022000000000000ULL,0)==VS_OK); /* 9 */
    }
    vstorage_delete(arena);
    return NULL;
}

int main(void) {
#ifdef VGEMM_TEST_BACKEND
    fresh_process_rejections();
#endif
    pthread_t workers[WORKERS];
    unsigned ordinals[WORKERS];
    for(unsigned i=0;i<WORKERS;++i) {
        ordinals[i]=i;
        assert(pthread_create(&workers[i],NULL,worker,&ordinals[i])==0);
    }
    assert(pthread_mutex_lock(&gate)==0);
    while(ready!=WORKERS) assert(pthread_cond_wait(&condition,&gate)==0);
    start=1;
    assert(pthread_cond_broadcast(&condition)==0);
    assert(pthread_mutex_unlock(&gate)==0);
    for(unsigned i=0;i<WORKERS;++i) assert(pthread_join(workers[i],NULL)==0);
#ifdef VGEMM_TEST_BACKEND
    assert(atomic_load(&configuration_calls)==1 && atomic_load(&parallel_calls)==1);
    const char *snapshot=vgemm_configuration();
    assert(snapshot!=good_configuration && strcmp(snapshot,good_configuration)==0);
    good_configuration[0]='x';
    assert(strncmp(snapshot,"OpenBLAS 0.3.34 ",16)==0 && vgemm_backend_check()==VS_OK);
    assert(atomic_load(&configuration_calls)==1 && atomic_load(&parallel_calls)==1);
#endif
    puts("GEMM: cold concurrent checks, immutable configuration and 16000 independent-arena products passed");
    return 0;
}
