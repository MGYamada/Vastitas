/* Independent coordinate oracle shared by the arena and standalone C probes.
 * Requires only fixture data and the bit-preserving word helper, no runtime. */
#ifndef VASTITAS_BENCH_REFERENCE_H
#define VASTITAS_BENCH_REFERENCE_H

typedef struct { long double r, i; } Z;
static Z z(const double *v) { return (Z){v[0], v[1]}; }
static Z plus(Z a, Z b) { return (Z){a.r+b.r, a.i+b.i}; }
static Z minus(Z a, Z b) { return (Z){a.r-b.r, a.i-b.i}; }
static Z times(Z a, Z b) { return (Z){a.r*b.r-a.i*b.i, a.r*b.i+a.i*b.r}; }
static Z divide(Z a, Z b) {
    long double d = b.r*b.r+b.i*b.i;
    return (Z){(a.r*b.r+a.i*b.i)/d, (a.i*b.r-a.r*b.i)/d};
}
static Z power(Z x, uint64_t n) {
    Z result = {1,0};
    for (; n; n >>= 1, x = times(x,x)) if (n & 1) result = times(result,x);
    return result;
}
static Z entry(unsigned id, uint64_t r, uint64_t c) {
    for (unsigned p = 0; p < 2; ++p)
        if (patches[id][p].row == r && patches[id][p].col == c) return z(patches[id][p].value);
    return z(values[id]);
}
/* Independent rank-one + sparse-update identity, not BLAS/index-loop reuse. */
static Z product(uint64_t r, uint64_t c) {
    Z a = z(values[0]), b = z(values[1]);
    Z result = times((Z){views[0].columns,0}, times(a,b));
    for (unsigned p = 0; p < 2; ++p) {
        const Patch *x = &patches[0][p], *y = &patches[1][p];
        if (x->row == r) result = plus(result, times(minus(z(x->value),a),b));
        if (y->col == c) result = plus(result, times(a,minus(z(y->value),b)));
        for (unsigned q = 0; q < 2; ++q) {
            y = &patches[1][q];
            if (x->row == r && y->col == c && x->col == y->row)
                result = plus(result, times(minus(z(x->value),a),minus(z(y->value),b)));
        }
    }
    return result;
}
static Z expected(uint64_t r, uint64_t c, uint64_t reps) {
    Z ab = times(z(alpha),product(r,c)), one = {1,0};
    if (!accumulate) return ab;
    Z bn = power(z(beta),reps);
    return plus(times(ab,divide(minus(one,bn),minus(one,z(beta)))),times(bn,z(values[2])));
}
static int verify_data(const double *const data[], uint64_t reps, uint64_t *hash_out) {
    uint64_t hash = UINT64_C(1469598103934665603);
    for (unsigned id = 0; id < 3; ++id) {
        const double *buffer = data[id];
        if (!buffer) return 0;
        uint64_t offset = views[id].offset / (scalar ? 16 : 8);
        for (uint64_t index = 0; index < elements[id]; ++index) {
            uint64_t rel = index >= offset ? index-offset : UINT64_MAX;
            uint64_t r = rel % views[id].leading, c = rel / views[id].leading;
            int logical = index >= offset && r < views[id].rows && c < views[id].columns;
            Z want = !logical ? z(sentinel) : id < 2 ? entry(id,r,c) : expected(r,c,reps);
            for (unsigned part = 0; part <= scalar; ++part) {
                double got = buffer[index*(scalar+1)+part];
                long double target = part ? want.i : want.r;
                if (!isfinite(got)) return 0;
                if (!logical || id < 2) {
                    if (word(got) != word((double)target)) return 0;
                } else {
                    long double tol = 32 * DBL_EPSILON * (views[0].columns+1) * fmaxl(1,fabsl(target));
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
