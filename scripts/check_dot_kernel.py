#!/usr/bin/env python3
"""Compare fixed-order 1-by-k dot updates in the production C adapter with Lean."""

import argparse
from fractions import Fraction
from itertools import product
import os
from pathlib import Path
import random
import shlex
import subprocess
import tempfile

from check_float_kernels import ROOT, compare_bits
import float_reference as fp


def fixtures(tag):
    kind = fp.F32 if tag >= 2 else fp.F64
    width = 32 if tag >= 2 else 64
    complex_cell = tag % 2 == 1
    frac = 23 if width == 32 else 52
    sign = 1 << (width - 1)
    inf = sign - (1 << frac)
    one = fp.from_fraction(Fraction(1), kind=kind).value.bits
    def cell(re, im=0):
        return (re, im if complex_cell else 0)
    unit, zero = cell(one), cell(0)
    signed_zero = cell(sign, sign)
    nan = cell(inf + 13, sign + inf + 17)
    old = cell(one | sign, one)
    special = [zero, signed_zero, unit, old, nan, cell(inf, 1), cell(1, sign + 1),
               cell(inf - 1, inf - 1)]
    conj = list(product((0, 1), repeat=2)) if complex_cell else [(0, 0)]
    # Empty, zero-alpha, zero-beta, unit, and general paths. An exact copy
    # of the old cell must preserve a signaling NaN's payload.
    for alpha, beta in product([zero, signed_zero, unit, old, nan], repeat=2):
        for pairs in [[], [(nan, unit)], [(special[6], special[7]), (old, unit)]]:
            yield 0, 0, alpha, beta, nan, pairs
    # Reordering the three additions or contracting the last product into an
    # FMA produces a distinct result for the chosen component width.
    large = fp.from_fraction(Fraction(1 << (frac + 1)), kind=kind).value.bits
    delta = Fraction(1, 1 << (frac // 2 + 2))
    above, below = [fp.from_fraction(1 + x, kind=kind).value.bits for x in (delta, -delta)]
    yield 0, 0, unit, zero, nan, [(cell(v), unit) for v in (large, one, large | sign)]
    yield 0, 0, unit, zero, nan, [(cell(one | sign), unit), (cell(above), cell(below))]
    rng = random.Random(7580 + tag)
    for i in range(64):
        def random_cell():
            if i % 2:
                return cell(rng.getrandbits(width), rng.getrandbits(width))
            return rng.choice(special)
        pairs = [(random_cell(), random_cell()) for _ in range(1 + i % 4)]
        for cl, cr in conj:
            yield cl, cr, unit if i % 3 == 0 else old, zero if i % 3 == 0 else old, old, pairs


def check(prefix):
    native = ROOT / "lean-kernel/native"
    numerical = ROOT / "lean-kernel/numerical"
    cases = [(tag, *case) for tag in range(4) for case in fixtures(tag)]
    with tempfile.TemporaryDirectory(prefix="vastitas-dot-") as temporary:
        work = Path(temporary)
        path = work / "rows"
        rows = []
        for tag, cl, cr, alpha, beta, old, pairs in cases:
            words = [*alpha, *beta, *old, *(v for left, right in pairs for v in (*left, *right))]
            rows.append([tag, cl, cr, len(pairs), *words])
        path.write_text("".join(" ".join(map(str, row)) + "\n" for row in rows))
        probe = work / "dot"
        subprocess.run([*shlex.split(os.environ.get("CC", "cc")), "-std=c11", "-O3",
                        "-Wall", "-Wextra", "-Werror", "-fno-fast-math", "-ffp-contract=off",
                        f"-I{native}", f"-I{numerical}", f"-I{prefix / 'include'}",
                        ROOT / "scripts/check_dot_kernel.c", native / "storage.c", native / "diagonal.c",
                        numerical / "gemm.c", prefix / "lib/libopenblas.a", "-lm", "-lpthread", "-o", probe],
                       check=True)
        with path.open() as source:
            native_run = subprocess.run([probe], stdin=source, text=True, check=True, stdout=subprocess.PIPE)
        lean = subprocess.run(["lake", "env", "lean", "--run", ROOT / "scripts/check_dot_kernel.lean", path],
                              cwd=ROOT / "lean", text=True, check=True, stdout=subprocess.PIPE)
        results = zip(rows, native_run.stdout.splitlines(), lean.stdout.splitlines(), strict=True)
        for index, (row, output, line) in enumerate(results):
            tag, _, _, count, *words = row
            width = 64 if tag < 2 else 32
            if len(output.split()) != 1 + tag % 2:
                raise ValueError(f"row {index}: incorrect number of native components")
            # A beta of one and an empty product or zero alpha copies the old
            # cell, including a signaling NaN's payload and sign.
            one = 0x3F800000 if width == 32 else 0x3FF0000000000000
            magnitude = (1 << (width - 1)) - 1
            preserve = (count == 0 or all(v & magnitude == 0 for v in words[:2])) and (
                words[2] == one and words[3] & magnitude == 0)
            for part, (actual, expected) in enumerate(zip(map(int, output.split()), map(int, line.split()), strict=True)):
                if preserve and (actual != words[4 + part] or expected != actual):
                    raise ValueError(f"row {index}: unit-beta copy changed input bits")
                try:
                    compare_bits(width, actual, expected)
                except ValueError as err:
                    raise ValueError(f"row {index}, part {part}, operands {row}: {err}") from err
    print(f"{len(cases)} one-cell dot updates matched Lean across F32/F64 and RR/CC")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--prefix", type=Path, required=True)
    check(parser.parse_args().prefix.resolve())
