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
/* Coordinate oracle uses only fixture inputs, never packed storage or BLAS.
 * Sparse corrections avoid a k-by-j reference loop per output coordinate. */
static Z minus(Z a, Z b) { return (Z){a.r-b.r,a.i-b.i}; }
static Z middle(uint64_t x, uint64_t y, uint64_t col) {
    Z t = z(values[0]), a = z(values[1]);
    Z result = times((Z){dim_k,0},times(t,a));
    for (unsigned p = 0; p < 2; ++p) {
        const Patch *v = &patches[1][p];
        if (v->col == col) result = plus(result,times(t,minus(z(v->value),a)));
    }
    for (unsigned p = 0; p < 2; ++p) {
        const Patch *v = &patches[0][p];
        if (v->row == x && v->col/dim_k == y)
            result = plus(result,times(minus(z(v->value),t),entry(1,v->col%dim_k,col)));
    }
    return result;
}
static Z product(uint64_t row, uint64_t col) {
    uint64_t x = row%dim_i, a = row/dim_i;
    Z result = {0,0};
    for (uint64_t y = 0; y < dim_j; ++y) result = plus(result,times(middle(x,y,a),entry(2,y,col)));
    return result;
}
static int logical_cell(unsigned view, uint64_t index, uint64_t *row, uint64_t *column) {
    uint64_t offset = views[view].offset/(scalar ? 16 : 8);
    if (index < offset) return 0;
    uint64_t relative = index-offset;
    *row = relative%views[view].leading; *column = relative/views[view].leading;
    return *row < views[view].rows && *column < views[view].columns;
}
static int verify_data(const double *const data[], uint64_t reps, uint64_t *hash_out) {
    (void)reps;
    uint64_t hash = UINT64_C(1469598103934665603);
    for (unsigned id = 0; id < 6; ++id) {
        const double *buffer = data[id];
        if (!buffer) return 0;
        for (uint64_t index = 0; index < elements[id]; ++index) {
            uint64_t r=0,c=0;
            Z want = z(sentinel);
            int arithmetic = 0;
            if (id == 3) {
                /* Second regroup overwrites only its own cells. All first-pack
                 * cells outside that footprint survive, including in padding. */
                if (logical_cell(6,index,&r,&c)) { want = middle(r%dim_i,c,r/dim_i); arithmetic = 1; }
                else if (logical_cell(3,index,&r,&c)) want = entry(0,r%dim_i,c+dim_k*(r/dim_i));
            } else if (logical_cell(id,index,&r,&c)) {
                if (id < 3) want = entry(id,r,c);
                else { want = id == 4 ? middle(r%dim_i,r/dim_i,c) : product(r,c); arithmetic = 1; }
            }
            for (unsigned part = 0; part <= scalar; ++part) {
                double got = buffer[index*(scalar+1)+part];
                long double target = part ? want.i : want.r;
                if (!isfinite(got)) return 0;
                if (!arithmetic) { if (word(got) != word((double)target)) return 0; }
                else {
                    long double tol = 64*DBL_EPSILON*(dim_k+1)*(dim_j+1)*fmaxl(1,fabsl(target));
                    if (fabsl((long double)got-target) > tol) return 0;
                }
                hash = (hash ^ word(got))*UINT64_C(1099511628211);
            }
        }
    }
    *hash_out = hash;
    return 1;
}

#endif
