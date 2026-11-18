#!/usr/bin/env python3
"""Compare Lean's integer/rational model with the native F32/F64 quotient adapters."""
import ctypes as ct
from pathlib import Path
import random
import subprocess
import tempfile

import float_reference as reference

ROOT = Path(__file__).resolve().parents[1]


def inputs(width):
    frac = {32: 23, 64: 52}[width]
    sign = 1 << (width - 1)
    unit = 1 << frac
    bias = sign // (2 * unit) - 1
    one, inf = bias * unit, sign - unit
    special = [0, sign, 1, sign + 1, unit - 1, unit, one, sign + one, one + 1,
               (bias + 1) * unit, inf - 1, inf, sign + inf, inf + 17,
               sign + inf + unit // 2 + 23]
    for i, a in enumerate(special):
        for j, b in enumerate(special):
            yield width, a, b, special[(i + j) % len(special)], special[(i - j) % len(special)]
    for c in [0, sign, 1, inf, inf + 17]:
        for d in [0, sign, 1, inf, inf + 17]:
            yield width, one, sign + one, c, d
    # Include midpoint cases with even and odd retained significands and the
    # transition from the largest subnormal to the smallest normal.
    for a, b in [(one, (bias - frac - 1) * unit), (one + 1, (bias - frac - 1) * unit),
                 (unit, one - 1), (1, (bias + 1) * unit)]:
        yield width, a, b, a, b
    rng = random.Random(758 + width)
    for _ in range(80):
        yield width, *(rng.getrandbits(width) for _ in range(4))
    for _ in range(80):
        yield width, *((rng.randrange(2) * sign + (rng.randrange(-7, 8) + bias) * unit
                        + rng.randrange(unit)) for _ in range(4))


def compare_bits(width, actual, expected):
    frac = {32: 23, 64: 52}[width]
    sign = 1 << (width - 1)
    inf = sign - (1 << frac)
    # NativeFast's arithmetic NaN payload is unspecified. Signed zeros,
    # subnormals and infinities have an exact bit comparison.
    if actual != expected and not (actual % sign > inf and expected % sign > inf):
        raise ValueError(f"0x{actual:x} != 0x{expected:x}")


def check_boundaries(width, a, b, values):
    fraction = {32: 23, 64: 52}[width]
    unit, sign = 1 << fraction, 1 << (width - 1)
    bias = sign // (2 * unit) - 1
    one, inf = bias * unit, sign - unit
    midpoint = (bias - fraction - 1) * unit
    # Independent bit-level answers. Underflow is tested after rounding, so
    # a midpoint that rounds up to minimum normal is inexact without underflow.
    checks = {
        (one, midpoint): (0, one, 16),
        (one + 1, midpoint): (0, one + 2, 16),
        (unit, one - 1): (4, unit, 16),
        (1, (bias + 1) * unit): (6, 0, 8 | 16),
        (inf - 1, (bias + 1) * unit): (4, inf, 4 | 16),
        (inf + 17, sign + inf + unit // 2 + 23): (0, inf + unit // 2 + 17, 1),
        (sign + inf + unit // 2 + 23, inf + 17): (0, sign + inf + unit // 2 + 23, 1),
        (one, sign): (6, sign + inf, 2),
        (sign + one, sign): (8, 0, 0),
        (inf, 0): (8, inf + unit // 2, 1),
    }
    if (a, b) in checks:
        pos, bits, flags = checks[a, b]
        if values[pos:pos + 2] != [bits, flags]:
            raise ValueError(f"boundary bits/flags {values[pos:pos+2]} != {[bits, flags]}")


def complex64_reference(x, y):
    # The strict reference selects exact NaN bits and accumulates local flags
    # for each node. The native adapter exposes only its two output words.
    flags = reference.Flags.NONE

    def step(op, a, b):
        nonlocal flags
        result = op(a, b)
        flags |= result.flags
        return result.value

    one = reference.F64(0x3ff0000000000000)

    def reciprocal(v):
        return step(reference.mul if v.is_zero else reference.div, one, v)

    a, b = x
    c, d = y
    t = reciprocal(step(reference.add, reference.F64(c.bits & ~reference.SIGN),
                        reference.F64(d.bits & ~reference.SIGN)))
    a, b, c, d = [step(reference.mul, component, t) for component in (a, b, c, d)]
    u = reciprocal(step(reference.add, step(reference.mul, c, c), step(reference.mul, d, d)))
    real_sum = step(reference.add, step(reference.mul, a, c), step(reference.mul, b, d))
    real = step(reference.mul, real_sum, u)
    imag_diff = step(reference.sub, step(reference.mul, b, c), step(reference.mul, a, d))
    imag = step(reference.mul, imag_diff, u)
    return [real.bits, imag.bits, int(flags)]


def verify(lib, case, values):
    width, a, b, c, d = case
    if len(values) != 16:
        raise ValueError("malformed Lean row")
    check_boundaries(width, a, b, values)
    word = ct.c_uint32 if width == 32 else ct.c_uint64
    pair = word * 2
    def function(op, types, result):
        fn = getattr(lib, f"vfloat{width}_{op}")
        fn.argtypes, fn.restype = types, result
        return fn
    rd = function("rdiv", [word, word], word)
    cd = function("cdiv", [ct.POINTER(word)] * 3, None)
    inv = function("cinv", [ct.POINTER(word)] * 2, None)
    compare_bits(width, rd(a, b), values[8])
    # Outputs may alias either input; calculate both components before writing.
    x, y = pair(a, b), pair(c, d)
    cd(x, y, x)
    inv(y, y)
    for actual, expected in zip([*x, *y], [*values[10:12], *values[13:15]], strict=True):
        compare_bits(width, actual, expected)
    if width == 64:
        x, y = reference.F64(a), reference.F64(b)
        ops = [reference.add, reference.sub, reference.mul, reference.div,
               reference.mul if y.is_zero else reference.div]
        for i, op in enumerate(ops):
            r = op(x, y)
            if [r.value.bits, int(r.flags)] != values[i * 2:i * 2 + 2]:
                raise ValueError(f"{op.__name__} differs from the binary64 Fraction reference")
        denominator = (reference.F64(c), reference.F64(d))
        for pos, numerator in [(10, (x, y)), (13, (reference.F64(0x3ff0000000000000), reference.zero()))]:
            if complex64_reference(numerator, denominator) != values[pos:pos + 3]:
                raise ValueError("complex quotient bits or flags differ from the binary64 Fraction reference")


def main():
    rows = list(inputs(32)) + list(inputs(64))
    with tempfile.TemporaryDirectory() as temp:
        directory = Path(temp)
        inputs_file = directory / "bits"
        inputs_file.write_text("".join(" ".join(map(str, row)) + "\n" for row in rows))
        library = directory / "quotient.so"
        subprocess.run(["cc", "-std=c11", "-O3", "-fPIC", "-shared", "-Wall", "-Wextra", "-Werror",
                        "-fno-fast-math", "-ffp-contract=off", str(ROOT / "lean-kernel/numerical/scalar.c"),
                        "-o", str(library)], check=True)
        lib = ct.CDLL(str(library))
        run = subprocess.run(["lake", "env", "lean", "--run", str(ROOT / "scripts/check_float_kernels.lean"),
                              str(inputs_file)], cwd=ROOT / "lean", text=True, stdout=subprocess.PIPE, check=True)
        for case, line in zip(rows, run.stdout.splitlines(), strict=True):
            try:
                verify(lib, case, list(map(int, line.split())))
            except ValueError as error:
                raise SystemExit(f"input {case}: {error}") from error
    print(f"{len(rows)} input tuples agreed on real quotient, complex quotient and inverse across both widths")


if __name__ == "__main__":
    main()
