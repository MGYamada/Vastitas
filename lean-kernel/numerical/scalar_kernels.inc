/* Included once per component width by scalar.c. All arithmetic, including
 * the two reciprocal scale factors, stays in the selected precision. */
static SCALAR FN(unpack)(WORD bits) {
    SCALAR value;
    memcpy(&value, &bits, sizeof(value));
    return value;
}

static WORD FN(pack)(SCALAR value) {
    WORD bits;
    memcpy(&bits, &value, sizeof(bits));
    return bits;
}

static SCALAR FN(divide)(SCALAR x, SCALAR y) {
    return y == (SCALAR)0 ? x * y : x / y;
}

WORD FN(rdiv)(WORD x, WORD y) {
    return FN(pack)(FN(divide)(FN(unpack)(x), FN(unpack)(y)));
}

void FN(cdiv)(const WORD x[2], const WORD y[2], WORD out[2]) {
    SCALAR a = FN(unpack)(x[0]), b = FN(unpack)(x[1]);
    SCALAR c = FN(unpack)(y[0]), d = FN(unpack)(y[1]);
    SCALAR s = FN(unpack)(y[0] & ~SIGN_MASK) + FN(unpack)(y[1] & ~SIGN_MASK);
    SCALAR t = FN(divide)((SCALAR)1, s);
    SCALAR A = a * t, B = b * t, C = c * t, D = d * t;
    SCALAR v = C * C + D * D;
    SCALAR u = FN(divide)((SCALAR)1, v);
    SCALAR re = (A * C + B * D) * u;
    SCALAR im = (B * C - A * D) * u;
    out[0] = FN(pack)(re);
    out[1] = FN(pack)(im);
}

void FN(cinv)(const WORD x[2], WORD out[2]) {
    const WORD one[2] = { ONE_BITS, 0 };
    FN(cdiv)(one, x, out);
}

#undef SCALAR
#undef WORD
#undef FN
#undef SIGN_MASK
#undef ONE_BITS
