"""Actual public runtime-shape fixtures and a fail-closed emitted-code wrapper."""
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent


def source(scalar, transpose, twice=False):
    profile = "ComplexSmooth" if scalar else "RealSmooth"
    kind = "Complex<F64>" if scalar else "F64"
    a = "complex_bits(4607182418800017408, 4607182418800017408)" if scalar else "f64_bits(4607182418800017408)"
    b = "complex_bits(4611686018427387904, 13830554455654793216)" if scalar else "f64_bits(4611686018427387904)"
    rows, cols = ("k", "m") if transpose else ("m", "k")
    header = f"m: Nat, k: Nat, n: Nat, u: RuntimeSpace<profiles::{profile}, m>, v: RuntimeSpace<profiles::{profile}, k>, w: RuntimeSpace<profiles::{profile}, n>, bu: RuntimeBasis<u>, bv: RuntimeBasis<v>, bw: RuntimeBasis<w>, left: RuntimeMap<bv, bu, read>, right: RuntimeMap<bw, bv, read>, output: RuntimeMap<bw, bu, write> initializes"
    tail = """
    let other_m: Nat = value { 3 };
    let other_k: Nat = value { 5 };
    let other_n: Nat = value { 2 };
    let other_pad: Nat = value { 2 };
    call run(other_m, other_k, other_n, other_pad) -> ();
""" if twice else ""
    return f"""mod profiles;
resource fn multiply({header}) -> Unit {{
    runtime_gemm(left, right, output, overwrite, NativeFast);
    value {{ () }}
}}
resource fn run(m: Nat, k: Nat, n: Nat, pad: Nat) -> Unit {{
    let lda: Nat = value {{ {rows} + pad }};
    let ldb: Nat = value {{ k + pad }};
    let ldc: Nat = value {{ m + pad }};
    let cap_a: Nat = value {{ lda * {cols} }};
    let cap_b: Nat = value {{ ldb * n }};
    let cap_c: Nat = value {{ ldc * n }};
    runtime_space u = linear(profiles::{profile}, m);
    runtime_space v = linear(profiles::{profile}, k);
    runtime_space w = linear(profiles::{profile}, n);
    runtime_basis bu = basis(u); runtime_basis bv = basis(v); runtime_basis bw = basis(w);
    runtime_allocate data_a: {kind}[cap_a] runtime_layout({rows}, {cols}, lda, {str(bool(transpose)).lower()});
    runtime_allocate data_b: {kind}[cap_b] runtime_layout(k, n, ldb, false);
    runtime_allocate data_c: {kind}[cap_c] runtime_layout(m, n, ldc, false);
    runtime_borrow ia = write(data_a); runtime_fill(ia, {a}); runtime_release(ia);
    runtime_borrow ib = write(data_b); runtime_fill(ib, {b}); runtime_release(ib);
    runtime_borrow a = read(data_a); runtime_borrow b = read(data_b); runtime_borrow c = write(data_c);
    runtime_map left = view(a, bv, bu); runtime_map right = view(b, bw, bv); runtime_map output = view(c, bw, bu);
    call multiply(m, k, n, u, v, w, bu, bv, bw, left, right, output) -> ();
    call multiply(m, k, n, u, v, w, bu, bv, bw, left, right, output) -> ();
    runtime_release(c); runtime_release(b); runtime_release(a);
    runtime_drop(data_a); runtime_drop(data_b); runtime_drop(data_c);
    value {{ () }}
}}
resource fn main() -> Int {{
    let m: Nat = value {{ 2 }}; let k: Nat = value {{ 3 }};
    let n: Nat = value {{ 4 }}; let pad: Nat = value {{ 0 }};
    call run(m, k, n, pad) -> ();
{tail}    value {{ 0 }}
}}
"""


def write_package(path, scalar, transpose, twice=False):
    (path / "src/profiles").mkdir(parents=True)
    (path / "Vastitas.toml").write_text('[package]\nname = "runtime_shape_bench"\nversion = "0.1.0"\nroot = "src/main.vast"\n')
    (path / "src/main.vast").write_text(source(scalar, transpose, twice))
    (path / "src/profiles/mod.vast").write_text((ROOT / "examples/packages/numerical/src/profiles/mod.vast").read_text())


def shapes():
    return [("tiny", 2, 3, 4, 0), ("padded", 3, 5, 2, 2),
            ("modest", 17, 13, 19, 3), ("zero_m", 0, 3, 4, 1),
            ("zero_k", 2, 0, 4, 1), ("zero_n", 2, 3, 0, 1)]


def split_generated(text):
    marker = "def main : IO Unit := do\n"
    if text.count(marker) != 1:
        raise ValueError("unexpected main")
    preamble, body = text.split(marker)
    lines = body.splitlines()
    if lines[:2] != ["  let shapeArena ← newArena 9223372036854775807", "  try"] or lines[-2:] != ["  finally", "    close shapeArena"]:
        raise ValueError("unexpected runtime-only arena envelope")
    if not re.fullmatch(r"    IO.println \(VastitasGenerated\.f_[0-9]+(?: resourceValue_[0-9]+)*\)", lines[-3]):
        raise ValueError("unexpected terminal return")
    operations = lines[2:-3]
    first = operations[:4]
    if not all(re.fullmatch(r"    let resourceValue_[0-9]+ := VastitasGenerated\.f_[0-9]+(?: resourceValue_[0-9]+)*", x) for x in first):
        raise ValueError("initial four scalar bindings changed")
    for i, name in enumerate(("m", "k", "n", "pad")):
        operations[i] = first[i].split(":=")[0] + ":= " + name
    allowed = ("    let resourceValue_", "    let runtimeExtent_", "    unless ", "      throw ",
               "    allocate shapeArena ", "    fill shapeArena ", "    drop shapeArena ", "    VastitasGemmNative.gemm shapeArena ")
    if not all(x.startswith(allowed) for x in operations):
        raise ValueError("unrecognized emitted operation")
    if sum(x.startswith("    allocate ") for x in operations) != 3 or sum(x.startswith("    fill ") for x in operations) != 2:
        raise ValueError("allocation/fill schedule changed")
    gemms = [i for i, x in enumerate(operations) if x.startswith("    VastitasGemmNative.gemm ")]
    if len(gemms) != 2 or operations[gemms[0]] != operations[gemms[1]]:
        raise ValueError("expected two identical destination-reusing GEMMs")
    # The call-boundary guards begin after the second fill. All remaining call
    # scalar computations, narrowing and guards stay inside each reused pair.
    cut = max(i for i,x in enumerate(operations) if x.startswith("    fill ")) + 1
    end = next(i for i,x in enumerate(operations) if x.startswith("    drop "))
    setup, operation, cleanup = operations[:cut], operations[cut:end], operations[end:]
    if [x for x in cleanup if x.startswith("    drop ")] != [f"    drop shapeArena {i}" for i in range(3)]:
        raise ValueError("drop order changed")
    return preamble, setup, operation, cleanup


def driver(text):
    preamble, setup, operation, cleanup = split_generated(text)
    def block(lines, indent):
        out = []
        for line in lines:
            if line.startswith("    unless "):
                out.append(" " * indent + "benchGuard")
            if " ← runtimeExtent" in line:
                out.append(" " * indent + "benchNarrow")
            out.append(" " * (indent-4) + line)
        return "\n".join(out)
    # Ordinary uninstrumented public executable is built separately. Only the
    # four input scalar definitions are parameterized; all emitted operations
    # and guards remain verbatim in these two explicit benchmark scopes.
    return preamble + '''
@[extern "shape_begin"] opaque benchBegin (scope : UInt32) (reps : UInt64) (verify : Bool) : IO Unit
@[extern "shape_stop"] opaque benchStop : IO Unit
@[extern "shape_report"] opaque benchReport : IO Unit
@[extern "shape_config"] opaque benchConfig (m k n pad : UInt64) : IO Unit
@[extern "shape_guard"] opaque benchGuard : IO Unit
@[extern "shape_narrow"] opaque benchNarrow : IO Unit
@[extern "shape_verify"] opaque benchVerify (arena : @& Arena) : IO Unit
@[extern "shape_c_run"] opaque benchC (scope : UInt32) (reps : UInt64) (verify : Bool) : IO Unit

@[noinline] def generatedOnce (m k n pad : Nat) : IO Unit := do
  let shapeArena ← newArena 9223372036854775807
  try
''' + block(setup+operation,4) + '''
    benchVerify shapeArena
''' + block(cleanup,4) + '''
  finally
    close shapeArena

@[noinline] def generatedReuse (m k n pad reps : Nat) (verify : Bool) : IO Unit := do
  let shapeArena ← newArena 9223372036854775807
  try
''' + block(setup,4) + '''
    benchBegin 1 reps.toUInt64 verify
    for _ in [:reps] do
''' + block(operation,6) + '''
    benchStop
    benchVerify shapeArena
''' + block(cleanup,4) + '''
  finally
    close shapeArena

def main (args : List String) : IO Unit := do
  let implementation := args[0]!
  let scope := args[1]!.toNat!
  let reps := args[2]!.toNat!
  let verify := args[3]! == "1"
  let mut rest := args.drop 4
  while !rest.isEmpty do
    let m := rest[0]!.toNat!; let k := rest[1]!.toNat!
    let n := rest[2]!.toNat!; let pad := rest[3]!.toNat!
    rest := rest.drop 4
    benchConfig m.toUInt64 k.toUInt64 n.toUInt64 pad.toUInt64
    if implementation == "c" then
      benchC scope.toUInt32 reps.toUInt64 verify
    else if scope == 0 then
      benchBegin 0 reps.toUInt64 verify
      for _ in [:reps] do generatedOnce m k n pad
      benchStop
    else
      generatedReuse m k n pad reps verify
    benchReport
'''
