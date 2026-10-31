#include "gemm.h"
#include <assert.h>
#include <stdio.h>

static char *configuration;
static int parallel;
char *vgemm_test_config(void) { return configuration; }
int vgemm_test_parallel(void) { return parallel; }

int main(void) {
    VStorageArena *arena=vstorage_new(64); assert(arena);
    VStorageLayout one={0,1,1,1,0};
    for(uint32_t id=0;id<4;++id) {
        assert(vstorage_allocate(arena,id,0,1)==VS_OK);
        assert(vstorage_fill(arena,id,one,0,0x4008000000000000ULL,0)==VS_OK);
    }
    const char *bad[]={NULL,"OpenBLAS 0.3.33 SINGLE_THREADED","OpenBLAS 0.3.340 SINGLE_THREADED",
        "OpenBLAS 0.3.34 USE64BITINT SINGLE_THREADED","unrelated BLAS 0.3.34"};
    VGemmReport report={19,23};
    uint8_t weight[8]={0,0,0,0,0,0,0,0x40}; /* exactly 2 */
    VDiagonal diagonal={weight,sizeof(weight),1};
    uint64_t written=vstorage_stats(arena).written_bytes;
    for(unsigned i=0;i<sizeof(bad)/sizeof(bad[0]);++i) {
        configuration=(char *)bad[i]; parallel=0;
        assert(vgemm_execute(arena,0,one,0,1,one,0,2,one,VGEMM_OVERWRITE,&report)==VS_ABI);
        assert(vgemm_diagonal_pair(arena,0,one,1,one,2,one,3,one,diagonal,0,0,&report)==VS_ABI);
    }
    configuration="OpenBLAS 0.3.34 USE_LOCKING";
    for(parallel=1;parallel<=2;++parallel) {
        assert(vgemm_execute(arena,0,one,0,1,one,0,2,one,VGEMM_OVERWRITE,&report)==VS_ABI);
        assert(vgemm_diagonal_pair(arena,0,one,1,one,2,one,3,one,diagonal,0,0,&report)==VS_ABI);
    }
    assert(report.kernel_calls==19 && report.written_bytes==23);
    assert(vstorage_expect(arena,2,one,0,0,0,0x4008000000000000ULL,0)==VS_OK);
    assert(vstorage_expect(arena,3,one,0,0,0,0x4008000000000000ULL,0)==VS_OK);
    assert(vstorage_stats(arena).written_bytes==written);
    vstorage_delete(arena);
    puts("GEMM: linked-library version/integer ABI/threading mismatch rejected before output write");
}
