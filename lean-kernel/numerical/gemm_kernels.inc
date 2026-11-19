/* Instantiated at each component precision. The same preflight and arithmetic
 * graph are used for real and interleaved complex storage at that precision. */
static VStorageStatus LOCAL(coefficient)(VStorageArena *arena, VGemmCoefficient input,
        const VStorageDense *output, COMPONENT fallback, COMPONENT value[2]) {
    value[0] = fallback;
    value[1] = 0.0;
    if (input.kind == VGEMM_DEFAULT) return VS_OK;
    if (input.kind == VGEMM_LITERAL) {
        if (input.scalar != output->scalar) return VS_SCALAR;
        WORD real = (WORD)input.real, imaginary = (WORD)input.imaginary;
        if ((uint64_t)real != input.real || (vstorage_is_complex(input.scalar) && (uint64_t)imaginary != input.imaginary))
            return VS_SCALAR;
        memcpy(&value[0], &real, sizeof(real));
        if (vstorage_is_complex(input.scalar)) memcpy(&value[1], &imaginary, sizeof(imaginary));
        return VS_OK;
    }
    if (input.kind != VGEMM_VIEW) return VS_OPERATION;
    VStorageDense source;
    VStorageStatus status = vstorage_prepare_dense(arena, input.allocation,
        (VStorageLayout){input.offset, 1, 1, 1, 0}, &source);
    if (status != VS_OK) return status;
    if (source.scalar != output->scalar) return VS_SCALAR;
    if (overlaps(&source, output)) return VS_ALIAS;
    memcpy(value, source.data, vstorage_element_bytes(source.scalar));
    return VS_OK;
}

/* Fused 1-by-1 output: c := beta*c + alpha*sum_p op(a_p) op(b_p) for a 1-by-k
 * row a and k-by-1 column b, k >= 1, replacing a level-3 BLAS call with M = N = 1.
 * The order is fixed and host independent: the sum starts at +0 and adds each
 * product in increasing p; every product, difference and sum is separately
 * rounded (no FMA contraction; GCC keeps ISO C11 mode off and clang obeys the
 * pragma). The pinned BLAS kernels may instead use FMA and their own order, so
 * results can differ from the former call in the last bits. Zero beta reads no
 * old output, one beta preserves it, and zero alpha reads neither input, as in
 * the pinned level-3 driver; an alpha of one is applied exactly. */
static void LOCAL(dot_update)(const VStorageDense *a, uint8_t conjugate_a,
                       const VStorageDense *b, uint8_t conjugate_b,
                       const VStorageDense *c, const COMPONENT alpha[2], const COMPONENT beta[2]) {
#if defined(__clang__)
#pragma STDC FP_CONTRACT OFF
#endif
    const int is_complex = vstorage_is_complex(c->scalar);
    const int beta_zero = beta[0] == 0.0 && beta[1] == 0.0, beta_one = beta[0] == 1.0 && beta[1] == 0.0;
    const int alpha_zero = alpha[0] == 0.0 && alpha[1] == 0.0, alpha_one = alpha[0] == 1.0 && alpha[1] == 0.0;
    COMPONENT *out = c->data;
    COMPONENT base[2] = {0.0, 0.0};
    if (beta_one) {
        base[0] = out[0];
        if (is_complex) base[1] = out[1];
    } else if (!beta_zero) {
        if (!is_complex) base[0] = beta[0] * out[0];
        else {
            COMPONENT rr = beta[0] * out[0], ii = beta[1] * out[1];
            COMPONENT ri = beta[0] * out[1], ir = beta[1] * out[0];
            base[0] = rr - ii;
            base[1] = ri + ir;
        }
    }
    if (alpha_zero) {
        out[0] = base[0];
        if (is_complex) out[1] = base[1];
        return;
    }
    const COMPONENT *x = a->data, *y = b->data;
    const uint64_t k = a->columns, sx = vector_step(a, 1), sy = vector_step(b, 0);
    COMPONENT sum[2] = {0.0, 0.0};
    if (!is_complex) {
        for (uint64_t p = 0; p < k; ++p) {
            COMPONENT product = x[p * sx] * y[p * sy];
            sum[0] = sum[0] + product;
        }
    } else {
        for (uint64_t p = 0; p < k; ++p) {
            const COMPONENT *u = x + p * sx, *v = y + p * sy;
            COMPONENT ur = u[0], ui = conjugate_a ? -u[1] : u[1];
            COMPONENT vr = v[0], vi = conjugate_b ? -v[1] : v[1];
            COMPONENT rr = ur * vr, ii = ui * vi, ri = ur * vi, ir = ui * vr;
            COMPONENT re = rr - ii, im = ri + ir;
            sum[0] = sum[0] + re;
            sum[1] = sum[1] + im;
        }
    }
    COMPONENT scaled[2] = {sum[0], sum[1]};
    if (!alpha_one) {
        if (!is_complex) scaled[0] = alpha[0] * sum[0];
        else {
            COMPONENT rr = alpha[0] * sum[0], ii = alpha[1] * sum[1];
            COMPONENT ri = alpha[0] * sum[1], ir = alpha[1] * sum[0];
            scaled[0] = rr - ii;
            scaled[1] = ri + ir;
        }
    }
    out[0] = base[0] + scaled[0];
    if (is_complex) out[1] = base[1] + scaled[1];
}

static VStorageStatus LOCAL(update)(VStorageArena *arena, uint32_t output, VStorageLayout output_view,
        const VStorageDense a, const VStorageDense b, const VStorageDense c,
        uint8_t left_conjugate, uint8_t right_conjugate, VGemmMode mode,
        VGemmCoefficient alpha_input, VGemmCoefficient beta_input, VGemmReport *report) {
    VStorageStatus status;
    COMPONENT alpha[2], beta[2];
    if ((status = LOCAL(coefficient)(arena, alpha_input, &c, 1.0, alpha)) != VS_OK ||
        (status = LOCAL(coefficient)(arena, beta_input, &c,
            mode == VGEMM_OVERWRITE ? 0.0 : 1.0, beta)) != VS_OK) return status;
    const int beta_one = beta[0] == 1.0 && beta[1] == 0.0;
    /* All physical shape/stride/bounds/LP64 checks precede the first write.
     * Initialization and nominal endpoint/frame/metric checks belong to the
     * actual checked source plan; matching dimensions cannot establish them. */
    if (c.bytes && (a.columns || !beta_one) &&
        (status = vstorage_prepare_write(arena, c.bytes)) != VS_OK) return status;
    VGemmReport result = {0, 0};
    if (c.rows && c.columns) {
        if (!a.columns) {
            /* For the empty product the defined degenerate operation is beta*C,
             * independent of alpha. Zero beta does not read old C, including
             * NaN/uninitialized overwrite destinations; one beta does no write. */
            if (beta[0] == 0.0 && beta[1] == 0.0) {
                status = vstorage_fill(arena, output, output_view, c.scalar, 0, 0);
                if (status != VS_OK) return status;
                result.written_bytes = c.bytes;
            } else if (!beta_one) {
                COMPONENT *data = c.data;
                for (uint64_t j = 0; j < c.columns; ++j) {
                    for (uint64_t i = 0; i < c.rows; ++i) {
                        uint64_t index = i + j * c.leading;
                        if (!vstorage_is_complex(c.scalar)) data[index] *= beta[0];
                        else {
                            COMPONENT real = data[2 * index], imaginary = data[2 * index + 1];
                            data[2 * index] = beta[0] * real - beta[1] * imaginary;
                            data[2 * index + 1] = beta[0] * imaginary + beta[1] * real;
                        }
                    }
                }
                vstorage_record_write(arena, c.bytes);
                result.written_bytes = c.bytes;
            }
        } else if (c.rows == 1 && c.columns == 1) {
            /* A scalar result needs no GEMM driver, packing or BLAS workspace.
             * It still counts as the operation's one kernel call. */
            LOCAL(dot_update)(&a, left_conjugate, &b, right_conjugate, &c, alpha, beta);
            vstorage_record_write(arena, c.bytes);
            result = (VGemmReport){1, c.bytes};
        } else {
            /* No scan, implicit packing, defensive copy or temporary output.
             * A and B may alias; C was independently checked against each. */
            enum CBLAS_TRANSPOSE ta = operation(&a, left_conjugate);
            enum CBLAS_TRANSPOSE tb = operation(&b, right_conjugate);
            if (!vstorage_is_complex(a.scalar)) {
                REAL_GEMM(CblasColMajor, ta, tb, (blasint)c.rows, (blasint)c.columns,
                    (blasint)a.columns, alpha[0], a.data, (blasint)a.leading, b.data,
                    (blasint)b.leading, beta[0], c.data, (blasint)c.leading);
            } else {
                COMPLEX_GEMM(CblasColMajor, ta, tb, (blasint)c.rows, (blasint)c.columns,
                    (blasint)a.columns, alpha, a.data, (blasint)a.leading, b.data,
                    (blasint)b.leading, beta, c.data, (blasint)c.leading);
            }
            vstorage_record_write(arena, c.bytes);
            result = (VGemmReport){1, c.bytes};
        }
    }
    if (report) *report = result;
    return VS_OK;
}
