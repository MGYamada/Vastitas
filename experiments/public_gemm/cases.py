"""Finite public-source fixtures and an independently constructed C baseline plan."""
import itertools
import importlib.util
import json
from pathlib import Path
import random
import re
import struct

ROOT = Path(__file__).resolve().parents[2]
_cleanup_spec = importlib.util.spec_from_file_location('gemm_cleanup', ROOT/'experiments/native_cleanup.py')
cleanup_envelope = importlib.util.module_from_spec(_cleanup_spec)
_cleanup_spec.loader.exec_module(cleanup_envelope)


def bits(x):
    return struct.unpack("<Q", struct.pack("<d", x))[0]


def cases(smoke=False):
    sizes = [("tiny", 2, 3, 4), ("small", 17, 13, 19)]
    if not smoke:
        sizes += [("bulk", 384, 320, 256)]
    result = []
    for (size, m, n, k), scalar, pad, accumulate in itertools.product(sizes, range(2), range(2), range(2)):
        result.append(dict(case=f"{size}-{'complex' if scalar else 'f64'}-p{pad}-{'accumulate' if accumulate else 'overwrite'}",
                           m=m, n=n, k=k, scalar=scalar, pad=pad, accumulate=accumulate))
    random.Random(20261031).shuffle(result)
    return result


def spec(c):
    m, n, k, scalar, pad = (c[x] for x in ("m", "n", "k", "scalar", "pad"))
    width = 16 if scalar else 8
    dims = [(m, k), (k, n), (m, n)]
    layouts = [(width * (i + 1) * pad, r, s, r + (i + 2) * pad, False)
               for i, (r, s) in enumerate(dims)]
    elements = [(i + 1) * pad + ld * cols + 3 * pad
                for i, (_, _, cols, ld, _) in enumerate(layouts)]
    values = [(0.125, 0.25 * scalar), (-0.25, 0.125 * scalar), (0.75, -0.125 * scalar)]
    # Distinct corners break the constant-matrix symmetry, with O(1) source size.
    patches = [[(0, 0, (1.0, -0.5 * scalar)), (m - 1, k - 1, (-0.5, 0.75 * scalar))],
               [(0, n - 1, (0.5, 0.25 * scalar)), (k - 1, 0, (-0.75, -0.5 * scalar))]]
    alpha = (0.75, -0.5) if scalar else (1.5, 0.0)
    beta = ((0.5, 0.25 * scalar) if c["accumulate"] else (0.0, 0.0))
    return dict(layouts=layouts, elements=elements, values=values, patches=patches,
                alpha=alpha, beta=beta, width=width, sentinel=(-7.0, 3.0 * scalar))


def literal(value, scalar):
    a, b = map(bits, value)
    return f"complex_bits({a}, {b})" if scalar else f"f64_bits({a})"


def layout(value):
    return "layout(" + ", ".join(str(v).lower() for v in value) + ")"


def source(c):
    s, scalar = spec(c), c["scalar"]
    profile = "ComplexSmooth" if scalar else "RealSmooth"
    kind = "Complex<F64>" if scalar else "F64"
    lines = ["pub resource fn product() -> Unit {",
             f"space u = linear(super::profiles::{profile}, {c['n']});",
             f"space v = linear(super::profiles::{profile}, {c['k']});",
             f"space w = linear(super::profiles::{profile}, {c['m']});",
             "basis bu = basis(u); basis bv = basis(v); basis bw = basis(w);"]
    for i, name in enumerate("abc"):
        count, view = s["elements"][i], s["layouts"][i]
        lines += [f"allocate {name}: {kind}[{count}];",
                  f"borrow all_{name} = write({name}, layout(0, {count}, 1, {count}, false));",
                  f"fill(all_{name}, {literal(s['sentinel'], scalar)});", f"release(all_{name});"]
        if i < 2 or c["accumulate"]:
            lines += [f"borrow init_{name} = write({name}, {layout(view)});",
                      f"fill(init_{name}, {literal(s['values'][i], scalar)});"]
            if i < 2:
                for r, col, value in s["patches"][i]:
                    lines += [f"store(init_{name}, {r}, {col}, {literal(value, scalar)});"]
            lines += [f"release(init_{name});"]
    for name, mode, view in zip("abc", ["read", "read", "read_write" if c["accumulate"] else "write"], s["layouts"]):
        lines += [f"borrow loan_{name} = {mode}({name}, {layout(view)});"]
    lines += ["map left = view(loan_a, bv, bw);", "map right = view(loan_b, bu, bv);",
              "map destination = view(loan_c, bu, bw);"]
    coeff = f", alpha={literal(s['alpha'], scalar)}"
    if c["accumulate"]:
        coeff += f", beta={literal(s['beta'], scalar)}"
    lines += [f"gemm(left, right, destination, {'accumulate' if c['accumulate'] else 'overwrite'}, NativeFast{coeff});",
              "release(loan_c); release(loan_b); release(loan_a);",
              "drop(c); drop(b); drop(a);", "value { () }", "}"]
    return "\n".join(lines) + "\n"


def write_package(c, out):
    (out / "src/product").mkdir(parents=True)
    (out / "src/profiles").mkdir()
    (out / "Vastitas.toml").write_text('[package]\nname = "gemm_bench"\nversion = "0.1.0"\nroot = "src/main.vast"\n')
    (out / "src/main.vast").write_text('mod profiles;\nmod product;\nresource fn main() -> Int {\ncall product::product() -> ();\nvalue { 0 }\n}\n')
    (out / "src/profiles/mod.vast").write_text((ROOT / "examples/packages/numerical/src/profiles/mod.vast").read_text())
    (out / "src/product/mod.vast").write_text(source(c))


def c_header(c, layout_type="VStorageLayout"):
    s = spec(c)
    def view(v):
        return "{" + ",".join(str(int(x)) for x in v) + "}"
    def pair(v):
        return "{" + ",".join(float(x).hex() for x in v) + "}"
    def patch(v):
        return "{" + ",".join("{%d,%d,%s}" % (r, col, pair(val)) for r, col, val in v) + "}"
    return f'''/* Generated from cases.json, not translated from the emitted runtime. */
static const unsigned scalar = {c['scalar']}, accumulate = {c['accumulate']};
static const {layout_type} views[3] = {{{','.join(map(view, s['layouts']))}}};
static const uint64_t elements[3] = {{{','.join(map(str, s['elements']))}}};
static const double values[3][2] = {{{','.join(map(pair, s['values']))}}};
static const double sentinel[2] = {pair(s['sentinel'])};
static const double alpha[2] = {pair(s['alpha'])}, beta[2] = {pair(s['beta'])};
typedef struct {{ uint64_t row, col; double value[2]; }} Patch;
static const Patch patches[2][2] = {{{','.join(map(patch, s['patches']))}}};
'''


def split_generated(text):
    """Fail closed if codegen no longer has the audited straight-line shape."""
    marker = "def main : IO Unit := do\n"
    if text.count(marker) != 1:
        raise ValueError("unexpected generated main")
    preamble, body = text.split(marker)
    lines = body.splitlines()
    if lines[0] != f"  let arena ← newArena {2**63-1}" or lines[1] != "  try":
        raise ValueError("unexpected arena envelope")
    _, lines = cleanup_envelope.split(lines, 'arena')
    if not re.fullmatch(r"    IO.println \(VastitasGenerated\.[A-Za-z0-9_]+\)", lines[-1]):
        raise ValueError("unexpected pure return display")
    operations = lines[2:-1]
    allowed = r"    (allocate|fill|store|drop|VastitasGemmNative\.gemmScaled) arena [0-9a-z ]+"
    if not all(re.fullmatch(allowed, line) for line in operations):
        raise ValueError("unsupported generated instruction")
    indices = [i for i, line in enumerate(operations) if "gemmScaled" in line]
    if len(indices) != 1:
        raise ValueError("expected exactly one explicit-coefficient GEMM")
    i = indices[0]
    setup, gemm, cleanup = operations[:i], operations[i], operations[i+1:]
    if cleanup != ["    drop arena 2", "    drop arena 1", "    drop arena 0"]:
        raise ValueError("unexpected allocation/drop mapping")
    if sum("allocate arena" in x for x in setup) != 3:
        raise ValueError("unexpected setup")
    return preamble, lines[0], setup, gemm, cleanup


def driver(generated):
    preamble, arena, setup, gemm, cleanup = split_generated(generated)
    def block(lines, indent):
        return "\n".join(" " * indent + x.strip() for x in lines)
    # The sole removed operation is terminal printing of the constant pure result.
    # Every resource instruction, operand and cleanup style is preserved.
    wrapped = preamble + '''
@[extern "bench_begin_lean"] opaque benchBegin (scope : UInt32) (reps : UInt64) (verify : Bool) : IO Unit
@[extern "bench_stop_lean"] opaque benchStop : IO Unit
@[extern "bench_report_lean"] opaque benchReport : IO Unit
@[extern "bench_c_run_lean"] opaque benchCRun (scope : UInt32) (reps : UInt64) (verify : Bool) : IO Unit
@[extern "bench_verify_lean"] opaque benchVerify (arena : @& Arena) (reps : UInt64) : IO Unit

@[noinline] def generatedOnce : IO Unit := do
''' + arena + '\n  try\n' + block(setup + [gemm] + cleanup, 4) + '''
    pure ()
  finally
    close arena

def main (args : List String) : IO Unit := do
  let impl := args[0]!
  let scope := args[1]!.toNat!
  let reps := args[2]!.toNat!
  let verify := args[3]! == "1"
  -- Identical untimed backend/Lean warmup in every fresh process, on both sides.
  generatedOnce
  if impl == "c" then
    benchCRun scope.toUInt32 reps.toUInt64 verify
  else if scope == 0 then
    benchBegin 0 reps.toUInt64 verify
    for _ in [:reps] do generatedOnce
    benchStop
  else
''' + '  ' + arena + '\n    try\n' + block(setup, 6) + '''
      benchBegin scope.toUInt32 reps.toUInt64 verify
      for _ in [:reps] do
''' + block([gemm], 8) + '''
      benchStop
      benchVerify arena reps.toUInt64
''' + block(cleanup, 6) + '''
    finally
      close arena
  benchReport
'''
    return cleanup_envelope.preserve(generated, wrapped)
