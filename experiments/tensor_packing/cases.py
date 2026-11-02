"""Finite source fixtures: T[i,k,j] B[k,l] -> C[i,j,l], explicit pack + GEMM."""
import itertools
import importlib.util
from pathlib import Path
import random
import re
import struct

ROOT = Path(__file__).resolve().parents[2]
_cleanup_spec = importlib.util.spec_from_file_location('tensor_cleanup', ROOT/'experiments/native_cleanup.py')
cleanup_envelope = importlib.util.module_from_spec(_cleanup_spec)
_cleanup_spec.loader.exec_module(cleanup_envelope)


def bits(x):
    return struct.unpack("<Q", struct.pack("<d", x))[0]


def cases(smoke=False):
    sizes = [("tiny", 2, 3, 4, 5)]
    if not smoke:
        sizes += [("small", 7, 11, 5, 13), ("bulk", 32, 48, 24, 40)]
    result = [dict(case=f"{size}-{'complex' if scalar else 'f64'}-p{pad}",
                   i=i, k=k, j=j, l=l, scalar=scalar, pad=pad)
              for (size, i, k, j, l), scalar, pad in itertools.product(sizes, range(2), range(2))]
    random.Random(20261031).shuffle(result)
    return result


def spec(c):
    i, k, j, l, scalar, pad = (c[x] for x in ("i", "k", "j", "l", "scalar", "pad"))
    width = 16 if scalar else 8
    dims = [(i, k*j), (k, l), (i*j, k), (i*j, l)]
    layouts = [(width*(n+1)*pad, r, col, r+(n+2)*pad, False)
               for n, (r, col) in enumerate(dims)]
    elements = [(n+1)*pad + ld*col + 3*pad for n, (_, _, col, ld, _) in enumerate(layouts)]
    values = [(0.125, 0.25*scalar), (-0.25, 0.125*scalar)]
    # Off-corner z=1,y=0 patch distinguishes pack3 from an unchanged flat copy.
    # Sparse corrections keep source/checker work bounded as dimensions grow.
    patches = [[(0, 0, (1.0, -0.5*scalar)), (i-1, 1, (-0.5, 0.75*scalar))],
               [(0, l-1, (0.5, 0.25*scalar)), (k-1, 0, (-0.75, -0.5*scalar))]]
    return dict(layouts=layouts, elements=elements, values=values, patches=patches,
                width=width, sentinel=(-7.0, 3.0*scalar))


def literal(value, scalar):
    a, b = map(bits, value)
    return f"complex_bits({a}, {b})" if scalar else f"f64_bits({a})"


def layout(value):
    return "layout(" + ", ".join(str(v).lower() for v in value) + ")"


def source(c):
    s, scalar = spec(c), c["scalar"]
    profile = "ComplexSmooth" if scalar else "RealSmooth"
    kind = "Complex<F64>" if scalar else "F64"
    lines = ["pub resource fn product() -> Unit {"]
    for name, axis in zip("uvwx", ("i", "k", "j", "l")):
        lines += [f"space {name} = linear(super::profiles::{profile}, {c[axis]}); basis b{name} = basis({name});"]
    lines += ["space vd = dual(v); basis bvd = derived(bv, vd);",
              "space xd = dual(x); basis bxd = derived(bx, xd);"]
    for n, name in enumerate(("original", "right", "scratch", "result")):
        count, view = s["elements"][n], s["layouts"][n]
        lines += [f"allocate {name}: {kind}[{count}];",
                  f"borrow all_{name} = write({name}, layout(0, {count}, 1, {count}, false));",
                  f"fill(all_{name}, {literal(s['sentinel'], scalar)});", f"release(all_{name});"]
        if n < 2:
            lines += [f"borrow init_{name} = write({name}, {layout(view)});",
                      f"fill(init_{name}, {literal(s['values'][n], scalar)});"]
            for r, col, value in s["patches"][n]:
                lines += [f"store(init_{name}, {r}, {col}, {literal(value, scalar)});"]
            lines += [f"release(init_{name});"]
    for name, mode, view in zip(("original", "right", "scratch", "result"),
                                ("read", "read", "write", "write"), s["layouts"]):
        lines += [f"borrow loan_{name} = {mode}({name}, {layout(view)});"]
    lines += ["tensor t = view3(loan_original, bu, bvd, bw, axes(0, 1, 2), 1);",
              "tensor destination = view3(loan_scratch, bu, bvd, bw, axes(0, 2, 1), 2);",
              "pack3(t, destination);", "release(loan_scratch);",
              f"borrow packed_read = read(scratch, {layout(s['layouts'][2])});",
              "tensor packed = view3(packed_read, bu, bvd, bw, axes(0, 2, 1), 2);",
              "tensor b = view2(loan_right, bv, bxd);",
              "tensor c = view3(loan_result, bu, bw, bxd, axes(0, 1, 2), 2);",
              "contract3(packed, b, c, NativeFast);",
              "release(loan_result); release(packed_read); release(loan_right); release(loan_original);",
              "drop(result); drop(scratch); drop(right); drop(original);", "value { () }", "}"]
    return "\n".join(lines) + "\n"


def write_package(c, out):
    (out / "src/product").mkdir(parents=True)
    (out / "src/profiles").mkdir()
    (out / "Vastitas.toml").write_text('[package]\nname = "tensor_bench"\nversion = "0.1.0"\nroot = "src/main.vast"\n')
    (out / "src/main.vast").write_text('mod profiles;\nmod product;\nresource fn main() -> Int {\ncall product::product() -> ();\nvalue { 0 }\n}\n')
    (out / "src/profiles/mod.vast").write_text((ROOT / "examples/packages/tensor-packing/src/profiles/mod.vast").read_text())
    (out / "src/product/mod.vast").write_text(source(c))


def c_header(c, layout_type="VStorageLayout"):
    s = spec(c)
    def view(v): return "{" + ",".join(str(int(x)) for x in v) + "}"
    def pair(v): return "{" + ",".join(float(x).hex() for x in v) + "}"
    def patch(v): return "{" + ",".join("{%d,%d,%s}" % (r, col, pair(val)) for r, col, val in v) + "}"
    return f'''/* Independently constructed from cases.json, not emitted instructions. */
static const unsigned scalar = {c['scalar']};
static const uint64_t dim_i = {c['i']}, dim_k = {c['k']}, dim_j = {c['j']};
static const {layout_type} views[4] = {{{','.join(map(view, s['layouts']))}}};
static const uint64_t elements[4] = {{{','.join(map(str, s['elements']))}}};
static const double values[2][2] = {{{','.join(map(pair, s['values']))}}};
static const double sentinel[2] = {pair(s['sentinel'])};
static const double alpha[2] = {{1,0}}, beta[2] = {{0,0}};
typedef struct {{ uint64_t row, col; double value[2]; }} Patch;
static const Patch patches[2][2] = {{{','.join(map(patch, s['patches']))}}};
'''


def split_generated(text):
    """Fail closed unless the actual returned program has the reviewed envelope."""
    marker = "def main : IO Unit := do\n"
    if text.count(marker) != 1:
        raise ValueError("unexpected generated main")
    preamble, body = text.split(marker)
    lines = body.splitlines()
    if lines[:2] != [f"  let arena ← newArena {2**63-1}", "  try"]:
        raise ValueError("unexpected arena envelope")
    _, lines = cleanup_envelope.split(lines, 'arena')
    if not re.fullmatch(r"    IO.println \(VastitasGenerated\.[A-Za-z0-9_]+\)", lines[-1]):
        raise ValueError("unexpected pure return display")
    operations = lines[2:-1]
    allowed = r"    (allocate|fill|store|drop|pack3|VastitasGemmNative\.gemm) arena [0-9a-z ]+"
    if not all(re.fullmatch(allowed, line) for line in operations):
        raise ValueError("unsupported generated instruction")
    indices = [n for n, line in enumerate(operations) if "pack3 arena" in line]
    if len(indices) != 1:
        raise ValueError("expected exactly one pack3")
    n = indices[0]
    setup, operation, cleanup = operations[:n], operations[n:n+2], operations[n+2:]
    if len(operation) != 2 or not operation[1].startswith("    VastitasGemmNative.gemm arena "):
        raise ValueError("expected pack3 then one GEMM")
    if any("gemm" in x or "drop" in x for x in setup):
        raise ValueError("unexpected setup operation")
    if cleanup != [f"    drop arena {n}" for n in (3, 2, 1, 0)]:
        raise ValueError("unexpected allocation/drop mapping")
    if sum("allocate arena" in x for x in setup) != 4:
        raise ValueError("unexpected allocation count")
    return preamble, lines[0], setup, operation, cleanup


def driver(generated):
    preamble, arena, setup, operation, cleanup = split_generated(generated)
    def block(lines, indent): return "\n".join(" "*indent + x.strip() for x in lines)
    # Only terminal printing is removed. All resource instructions stay verbatim.
    wrapped = preamble + '''
@[extern "bench_begin_lean"] opaque benchBegin (scope : UInt32) (reps : UInt64) (verify : Bool) : IO Unit
@[extern "bench_stop_lean"] opaque benchStop : IO Unit
@[extern "bench_report_lean"] opaque benchReport : IO Unit
@[extern "bench_c_run_lean"] opaque benchCRun (scope : UInt32) (reps : UInt64) (verify : Bool) : IO Unit
@[extern "bench_verify_lean"] opaque benchVerify (arena : @& Arena) (reps : UInt64) : IO Unit

@[noinline] def generatedOnce : IO Unit := do
''' + arena + '\n  try\n' + block(setup + operation + cleanup, 4) + '''
    pure ()
  finally
    close arena

def main (args : List String) : IO Unit := do
  let impl := args[0]!
  let scope := args[1]!.toNat!
  let reps := args[2]!.toNat!
  let verify := args[3]! == "1"
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
''' + block(operation, 8) + '''
      benchStop
      benchVerify arena reps.toUInt64
''' + block(cleanup, 6) + '''
    finally
      close arena
  benchReport
'''
    return cleanup_envelope.preserve(generated, wrapped)
