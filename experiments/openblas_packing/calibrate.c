/* Check the actual unchanged packing kernels, positive dimensions and tails.
 * The harness is also sanitized; upstream objects are not recompiled with it. */
#include <assert.h>
#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

_Static_assert(sizeof(long) == 8 && sizeof(double) == 8, "64-bit ABI only");
typedef int (*Copy)(long, long, double *, long, double *);
#define DECL(name) extern int name(long, long, double *, long, double *)
#if VP_D_M != VP_D_N
DECL(dgemm_incopy); DECL(dgemm_itcopy);
#endif
DECL(dgemm_oncopy); DECL(dgemm_otcopy);
DECL(zgemm_oncopy); DECL(zgemm_otcopy);
#if VP_Z_M != VP_Z_N
DECL(zgemm_incopy); DECL(zgemm_itcopy);
#endif
typedef struct { const char *name; Copy call; size_t width, components; int transpose; } Kernel;
static const Kernel kernels[] = {
#if VP_D_M != VP_D_N
    {"dgemm_incopy", dgemm_incopy, VP_D_M, 1, 0},
    {"dgemm_itcopy", dgemm_itcopy, VP_D_M, 1, 1},
#endif
    {"dgemm_oncopy", dgemm_oncopy, VP_D_N, 1, 0},
    {"dgemm_otcopy", dgemm_otcopy, VP_D_N, 1, 1},
    {"zgemm_oncopy", zgemm_oncopy, VP_Z_N, 2, 0},
    {"zgemm_otcopy", zgemm_otcopy, VP_Z_N, 2, 1},
#if VP_Z_M != VP_Z_N
    {"zgemm_incopy", zgemm_incopy, VP_Z_M, 2, 0},
    {"zgemm_itcopy", zgemm_itcopy, VP_Z_M, 2, 1},
#endif
};
static const uint64_t sentinel = UINT64_C(0x7ff8123456789abc);
static uint64_t bits(double value) { uint64_t result; memcpy(&result, &value, sizeof(result)); return result; }

static size_t check(const Kernel *k, size_t m, size_t n, size_t pad) {
    const size_t rows = k->transpose ? n : m, cols = k->transpose ? m : n;
    const size_t lda = rows + pad, input_words = lda * cols * k->components;
    const size_t output_words = m * n * k->components, guard = 32;
    double *input = malloc((input_words + 2 * guard) * sizeof(double));
    double *saved = malloc((input_words + 2 * guard) * sizeof(double));
    double *output = malloc((output_words + 2 * guard) * sizeof(double));
    assert(input && saved && output);
    double marker; memcpy(&marker, &sentinel, sizeof(marker));
    for (size_t i = 0; i < input_words + 2 * guard; ++i) input[i] = marker;
    for (size_t i = 0; i < output_words + 2 * guard; ++i) output[i] = marker;
    for (size_t col = 0; col < cols; ++col)
        for (size_t row = 0; row < rows; ++row)
            for (size_t c = 0; c < k->components; ++c) {
                double value = (double)(1 + col * 1000000 + row * 4 + c);
                input[guard + (col * lda + row) * k->components + c] = value;
            }
    memcpy(saved, input, (input_words + 2 * guard) * sizeof(uint64_t));
    int result = k->call((long)m, (long)n, input + guard, (long)lda, output + guard);
    assert(result == 0);
    assert(memcmp(saved, input, (input_words + 2 * guard) * sizeof(uint64_t)) == 0);
    for (size_t i = 0; i < guard; ++i) {
        assert(bits(output[i]) == sentinel);
        assert(bits(output[guard + output_words + i]) == sentinel);
    }
    size_t cursor = 0;
    for (size_t col = 0; col < n;) {
        size_t width = k->width;
        while (width > n - col) width /= 2;
        for (size_t row = 0; row < m; ++row)
            for (size_t j = 0; j < width; ++j)
                for (size_t c = 0; c < k->components; ++c) {
                    size_t at = k->transpose ? col + j + row * lda : row + (col + j) * lda;
                    if (bits(output[guard + cursor]) != bits(input[guard + at * k->components + c])) {
                        fprintf(stderr, "%s m=%zu n=%zu pad=%zu output=%zu differs\n", k->name, m, n, pad, cursor);
                        abort();
                    }
                    ++cursor;
                }
        col += width;
    }
    assert(cursor == output_words);
    free(output); free(saved); free(input);
    return output_words;
}

int main(int argc, char **argv) {
    if (argc != 1) {
        assert(argc == 5);
        size_t m=strtoul(argv[2],NULL,10), n=strtoul(argv[3],NULL,10), lda=strtoul(argv[4],NULL,10);
        assert(m>0 && n>0 && m<=50000 && n<=50000 && lda<=50003);
        const Kernel *kernel=NULL;
        for(size_t i=0;i<sizeof(kernels)/sizeof(kernels[0]);++i)
            if(strcmp(argv[1],kernels[i].name)==0) kernel=&kernels[i];
        assert(kernel);
        const size_t rows=kernel->transpose ? n : m, cols=kernel->transpose ? m : n;
        assert(lda>=rows && lda*cols*kernel->components<=16*1024*1024);
        size_t words=check(kernel,m,n,lda-rows);
        printf("{\"kind\":\"observed_kernel_footprint\",\"kernel\":\"%s\",\"m\":%zu,\"n\":%zu,"
               "\"lda\":%zu,\"checked_input_words\":%zu,\"checked_output_words\":%zu}\n",
               kernel->name,m,n,lda,lda*cols*kernel->components,words);
        return 0;
    }
    const size_t sizes[] = {1,2,3,4,5,7,8,9,15,16,17,31,32,33,63,64,65,127,128,129,255,256,257};
    uint64_t cases = 0, words = 0;
    for (size_t k = 0; k < sizeof(kernels) / sizeof(kernels[0]); ++k)
        for (size_t a = 0; a < sizeof(sizes) / sizeof(sizes[0]); ++a)
            for (size_t b = 0; b < sizeof(sizes) / sizeof(sizes[0]); ++b)
                for (size_t p = 0; p < 2; ++p) {
                    words += check(&kernels[k], sizes[a], sizes[b], p * 3);
                    ++cases;
                }
    printf("{\"kind\":\"kernel_calibration\",\"cases\":%" PRIu64 ",\"checked_output_words\":%" PRIu64 ",\"kernels\":[", cases, words);
    for (size_t i = 0; i < sizeof(kernels)/sizeof(kernels[0]); ++i)
        printf("%s{\"name\":\"%s\",\"width\":%zu,\"components\":%zu,\"transpose\":%d}",
               i ? "," : "", kernels[i].name, kernels[i].width, kernels[i].components, kernels[i].transpose);
    puts("]}");
    return 0;
}
