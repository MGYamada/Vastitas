"""Bounded public T[i,k,j] A[k,a] B[j,b] -> C[i,a,b] two-edge tree fixtures."""
import itertools
import importlib.util
from pathlib import Path
import random
import re
import struct

ROOT = Path(__file__).resolve().parents[2]
_cleanup_spec = importlib.util.spec_from_file_location('tree_cleanup', ROOT/'experiments/native_cleanup.py')
cleanup_envelope = importlib.util.module_from_spec(_cleanup_spec)
_cleanup_spec.loader.exec_module(cleanup_envelope)


def bits(x):
    return struct.unpack("<Q", struct.pack("<d", x))[0]


def cases(smoke=False):
    sizes = [("tiny", 2, 3, 4, 5, 6)]
    if not smoke:
        sizes += [("small", 7, 17, 5, 11, 13), ("bulk", 24, 40, 32, 48, 56)]
    result = [dict(case=f"{size}-{'complex' if scalar else 'f64'}-p{pad}",
                   i=i, k=k, j=j, a=a, b=b, scalar=scalar, pad=pad)
              for (size,i,k,j,a,b),scalar,pad in itertools.product(sizes,range(2),range(2))]
    random.Random(20261101).shuffle(result)
    return result


def spec(c):
    i,k,j,a,b,scalar,pad = (c[x] for x in ("i","k","j","a","b","scalar","pad"))
    width = 16 if scalar else 8
    # 0=T,1=A,2=B,3=first scratch,4=middle,5=C,6=second scratch.
    dims = [(i,k*j),(k,a),(j,b),(i*j,k),(i*j,a),(i*a,b),(i*a,j)]
    layouts = [(width*(n+1)*pad,r,col,r+(n+2)*pad,False) for n,(r,col) in enumerate(dims)]
    capacity = [(n+1)*pad+ld*col+3*pad for n,(_,_,col,ld,_) in enumerate(layouts)]
    elements = capacity[:6]
    elements[3] = max(capacity[3],capacity[6])
    values = [(0.125,0.25*scalar),(-0.25,0.125*scalar),(0.5,-0.25*scalar)]
    patches = [[(0,0,(1.0,-0.5*scalar)),(i-1,1,(-0.5,0.75*scalar))],
               [(0,a-1,(0.5,0.25*scalar)),(k-1,0,(-0.75,-0.5*scalar))],
               [(j-1,0,(-0.25,0.5*scalar)),(0,b-1,(0.75,-0.75*scalar))]]
    return dict(layouts=layouts,elements=elements,values=values,patches=patches,
                width=width,sentinel=(-7.0,3.0*scalar))


def entry(s,id,row,col):
    return complex(*next((v for r,c,v in s["patches"][id] if (r,c)==(row,col)),s["values"][id]))


def middle(c,s,x,y,a):
    return sum((entry(s,0,x,z+c["k"]*y)*entry(s,1,z,a) for z in range(c["k"])),0j)


def product(c,s,row,col):
    x,a = row % c["i"], row // c["i"]
    return sum((middle(c,s,x,y,a)*entry(s,2,y,col) for y in range(c["j"])),0j)


def anchors(c,s):
    return [(0,0),(c["i"]-1,c["b"]-1),(c["i"]*c["a"]-1,0)]


def literal(value,scalar):
    a,b = map(bits,value)
    return f"complex_bits({a}, {b})" if scalar else f"f64_bits({a})"


def layout(value):
    return "layout("+", ".join(str(v).lower() for v in value)+")"


def source(c):
    s,scalar = spec(c),c["scalar"]
    profile = "ComplexSmooth" if scalar else "RealSmooth"
    kind = "Complex<F64>" if scalar else "F64"
    lines = ["pub resource fn product() -> Unit {"]
    for name,axis in zip("uvwab",("i","k","j","a","b")):
        lines += [f"space {name} = linear(super::profiles::{profile}, {c[axis]}); basis b{name} = basis({name});"]
    for name in "vwab":
        lines += [f"space {name}d = dual({name}); basis b{name}d = derived(b{name}, {name}d);"]
    names = ("original","matrix_a","matrix_b","scratch","middle","result")
    for n,name in enumerate(names):
        count = s["elements"][n]
        lines += [f"allocate {name}: {kind}[{count}];",
                  f"borrow all_{name} = write({name}, layout(0, {count}, 1, {count}, false));",
                  f"fill(all_{name}, {literal(s['sentinel'],scalar)});",f"release(all_{name});"]
        if n < 3:
            lines += [f"borrow init_{name} = write({name}, {layout(s['layouts'][n])});",
                      f"fill(init_{name}, {literal(s['values'][n],scalar)});"]
            for r,col,value in s["patches"][n]:
                lines += [f"store(init_{name}, {r}, {col}, {literal(value,scalar)});"]
            lines += [f"release(init_{name});"]
    for n,name in enumerate(names[:3]):
        lines += [f"borrow loan_{name} = read({name}, {layout(s['layouts'][n])});"]
    v = [layout(x) for x in s["layouts"]]
    lines += [f"borrow output = write(result, {v[5]});",
        "tensor t = view3(loan_original, bu, bvd, bwd, axes(0,1,2), 1);",
        "tensor right_a = view2(loan_matrix_a, bv, bad);",
        "tensor right_b = view2(loan_matrix_b, bw, bbd);",
        "tensor c = view3(output, bu, bad, bbd, axes(0,1,2), 2);",
        "contract_tree(c, NativeFast) {",
        "occurrence t = t; occurrence a = right_a; occurrence b = right_b;",
        "edge ev = (t[1], a[0]); edge ew = (t[2], b[0]);",
        "boundary(t[0], a[1], b[1]); plan {",
        f"borrow packed_write = write(scratch, {v[3]});",
        "tensor first_pack = view3(packed_write, bu, bvd, bwd, axes(0,2,1), 2);",
        "regroup(t, first_pack); release(packed_write);",
        f"borrow packed_read = read(scratch, {v[3]});",
        "tensor first_read = view3(packed_read, bu, bvd, bwd, axes(0,2,1), 2); rebind(t, first_read);",
        f"borrow middle_write = write(middle, {v[4]});",
        "tensor intermediate = view3(middle_write, bu, bwd, bad, axes(0,1,2), 2);",
        "join ta = (ev, t, a, intermediate); release(middle_write); release(packed_read);",
        f"borrow middle_read = read(middle, {v[4]});",
        "tensor intermediate_read = view3(middle_read, bu, bwd, bad, axes(0,1,2), 2); rebind(ta, intermediate_read);",
        f"borrow repacked_write = write(scratch, {v[6]});",
        "tensor second_pack = view3(repacked_write, bu, bwd, bad, axes(0,2,1), 2);",
        "regroup(ta, second_pack); release(repacked_write); release(middle_read);",
        f"borrow repacked_read = read(scratch, {v[6]});",
        "tensor second_read = view3(repacked_read, bu, bwd, bad, axes(0,2,1), 2); rebind(ta, second_read);",
        "join done = (ew, ta, b, c); release(repacked_read); } }",
        "release(output);",f"borrow checked = read(result, {v[5]});"]
    for row,col in anchors(c,s):
        value = product(c,s,row,col)
        lines += [f"expect(checked, {row}, {col}, {literal((value.real,value.imag),scalar)});"]
    lines += ["release(checked); release(loan_matrix_b); release(loan_matrix_a); release(loan_original);",
              "drop(result); drop(middle); drop(scratch); drop(matrix_b); drop(matrix_a); drop(original);",
              "value { () }", "}"]
    return "\n".join(lines)+"\n"


def write_package(c,out):
    (out/"src/product").mkdir(parents=True)
    (out/"src/profiles").mkdir()
    (out/"Vastitas.toml").write_text('[package]\nname = "tree_bench"\nversion = "0.1.0"\nroot = "src/main.vast"\n')
    (out/"src/main.vast").write_text('mod profiles; mod product; resource fn main() -> Int { call product::product() -> (); value { 0 } }\n')
    (out/"src/profiles/mod.vast").write_text((ROOT/"examples/packages/contraction-tree/src/profiles/mod.vast").read_text())
    (out/"src/product/mod.vast").write_text(source(c))


def c_header(c):
    s = spec(c)
    def view(v): return "{"+",".join(str(int(x)) for x in v)+"}"
    def pair(v): return "{"+",".join(float(x).hex() for x in v)+"}"
    def patch(v): return "{"+",".join("{%d,%d,%s}" % (r,col,pair(val)) for r,col,val in v)+"}"
    expected = [(r,col,(product(c,s,r,col).real,product(c,s,r,col).imag)) for r,col in anchors(c,s)]
    return f'''/* Fixture data independently constructed from cases.json. */
static const unsigned scalar = {c['scalar']};
static const uint64_t dim_i={c['i']}, dim_k={c['k']}, dim_j={c['j']}, dim_a={c['a']};
static const VStorageLayout views[7] = {{{','.join(map(view,s['layouts']))}}};
static const uint64_t elements[6] = {{{','.join(map(str,s['elements']))}}};
static const double values[3][2] = {{{','.join(map(pair,s['values']))}}};
static const double sentinel[2] = {pair(s['sentinel'])};
static const double alpha[2] = {{1,0}}, beta[2] = {{0,0}};
typedef struct {{ uint64_t row, col; double value[2]; }} Patch;
static const Patch patches[3][2] = {{{','.join(map(patch,s['patches']))}}};
static const Patch expected[3] = {patch(expected)};
'''


def split_generated(text):
    marker = "def main : IO Unit := do\n"
    if text.count(marker) != 1: raise ValueError("unexpected generated main")
    preamble,body = text.split(marker)
    lines = body.splitlines()
    if lines[:2] != [f"  let arena ← newArena {2**63-1}","  try"]: raise ValueError("unexpected arena envelope")
    _, lines = cleanup_envelope.split(lines, 'arena')
    if not re.fullmatch(r"    IO.println \(VastitasGenerated\.[A-Za-z0-9_]+\)",lines[-1]): raise ValueError("unexpected display")
    operations = lines[2:-1]
    allowed = r"    (allocate|fill|store|expect|drop|pack3|regroup3|VastitasGemmNative\.gemm) arena [0-9a-z ]+"
    if not all(re.fullmatch(allowed,x) for x in operations): raise ValueError("unsupported instruction")
    indices = [n for n,x in enumerate(operations) if "pack3 arena" in x]
    if len(indices)!=1: raise ValueError("expected one optimized pack3")
    n=indices[0]
    setup,operation,cleanup = operations[:n],operations[n:n+4],operations[n+4:]
    prefixes = ["pack3", "VastitasGemmNative.gemm", "regroup3", "VastitasGemmNative.gemm"]
    if len(operation)!=4 or any(not x.startswith(f"    {p} arena ") for x,p in zip(operation,prefixes)): raise ValueError("unexpected two-edge order")
    if any(not re.match(r"    (allocate|fill|store) arena ",x) for x in setup): raise ValueError("unexpected setup")
    if sum("allocate arena" in x for x in setup)!=6: raise ValueError("expected six allocations")
    if len(cleanup)!=9 or any(not x.startswith("    expect arena 5 ") for x in cleanup[:3]) or cleanup[3:]!=[f"    drop arena {n}" for n in range(5,-1,-1)]: raise ValueError("unexpected checks/drop mapping")
    return preamble,lines[0],setup,operation,cleanup


def driver(generated):
    preamble, arena, setup, operation, cleanup = split_generated(generated)
    def block(lines, indent): return "\n".join(" "*indent + x.strip() for x in lines)
    # Lifecycle preserves every resource instruction; reused scopes hoist setup/cleanup.
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
