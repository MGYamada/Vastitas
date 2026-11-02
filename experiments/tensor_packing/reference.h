/* Independent coordinate oracle shared by the arena and standalone C probes.
 * Requires only fixture data and the bit-preserving word helper, no runtime. */
#ifndef VASTITAS_BENCH_REFERENCE_H
#define VASTITAS_BENCH_REFERENCE_H

typedef struct { long double r, i; } Z;
static Z z(const double *v) { return (Z){v[0], v[1]}; }
static Z plus(Z a, Z b) { return (Z){a.r+b.r, a.i+b.i}; }
static Z times(Z a, Z b) { return (Z){a.r*b.r-a.i*b.i, a.r*b.i+a.i*b.r}; }
static Z entry(unsigned id, uint64_t r, uint64_t c) {
    for (unsigned p = 0; p < 2; ++p)
        if (patches[id][p].row == r && patches[id][p].col == c) return z(patches[id][p].value);
    return z(values[id]);
}
/* Direct coordinate contraction oracle. Never reads packed storage or BLAS. */
static Z product(uint64_t r, uint64_t c) {
    uint64_t x = r % dim_i, y = r / dim_i;
    Z result = {0,0};
    for (uint64_t z = 0; z < dim_k; ++z)
        result = plus(result,times(entry(0,x,z+dim_k*y),entry(1,z,c)));
    return result;
}
static int verify_data(const double *const data[], uint64_t reps, uint64_t *hash_out) {
    (void)reps;
    uint64_t hash = UINT64_C(1469598103934665603);
    for (unsigned id = 0; id < 4; ++id) {
        const double *buffer = data[id];
        if (!buffer) return 0;
        uint64_t offset = views[id].offset / (scalar ? 16 : 8);
        for (uint64_t index = 0; index < elements[id]; ++index) {
            uint64_t rel = index >= offset ? index-offset : UINT64_MAX;
            uint64_t r = rel % views[id].leading, c = rel / views[id].leading;
            int logical = index >= offset && r < views[id].rows && c < views[id].columns;
            Z want = !logical ? z(sentinel) : id < 2 ? entry(id,r,c) : id == 2 ? entry(0,r%dim_i,c+dim_k*(r/dim_i)) : product(r,c);
            for (unsigned part = 0; part <= scalar; ++part) {
                double got = buffer[index*(scalar+1)+part];
                long double target = part ? want.i : want.r;
                if (!isfinite(got)) return 0;
                if (!logical || id < 3) {
                    if (word(got) != word((double)target)) return 0;
                } else {
                    long double tol = 32 * DBL_EPSILON * (dim_k+1) * fmaxl(1,fabsl(target));
                    if (fabsl((long double)got-target) > tol) return 0;
                }
                hash = (hash ^ word(got)) * UINT64_C(1099511628211);
            }
        }
    }
    *hash_out = hash;
    return 1;
}

#endif
