#!/usr/bin/env python3
"""Execute actual checked internal GEMM schedules through the optional Lean FFI.

Also executes closed fixtures through the nominal resource-function checker.
Neither fixture entry point is a public source GEMM interface.
"""
import argparse
import copy
import itertools
import json
import os
from pathlib import Path
import re
import shutil
import struct
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]


def scalar_fixture(conjugate, inner=1, empty=False):
    steps = []
    def action(op, **fields):
        steps.append({"kind": "action", "action": {"op": op, **fields}})
    for owner, rows, columns, transposed in [(0, inner, 0 if empty else 1, True),
                                            (1, inner, 1, False), (2, 0 if empty else 1, 1, False)]:
        layout = dict(offset=0, rows=rows, columns=columns, leading=max(rows, 1), transposed=transposed)
        action("allocate", owner=owner, scalar="complex_f64", elements=rows * columns)
        action("borrow", name=owner+10, source={"kind": "owner", "name": owner}, layout=layout, access="write")
        if owner != 2:
            action("fill", loan=owner+10, value=dict(kind="complex_f64", real=0 if owner == 0 else 4607182418800017408,
                                                    imaginary=4607182418800017408 if owner == 0 else 0))
            action("release", loan=owner+10)
            action("borrow", name=owner+20, source={"kind": "owner", "name": owner}, layout=layout, access="read")
    action("gemm", left=20, right=21, output=12, conjugate_left=conjugate,
           conjugate_right=False, mode="overwrite", policy="native_fast")
    action("release", loan=12)
    output = dict(offset=0, rows=0 if empty else 1, columns=1, leading=1, transposed=False)
    action("borrow", name=22, source={"kind": "owner", "name": 2}, layout=output, access="read")
    if not empty:
        imaginary = (13830554455654793216 if conjugate else 4607182418800017408) if inner else 0
        action("expect", loan=22, row=0, column=0, value=dict(kind="complex_f64", real=0, imaginary=imaginary))
    for name in [20, 21, 22]: action("release", loan=name)
    for name in [0, 1, 2]: action("drop", owner=name)
    return {"statements": steps}


def orientation_fixture():
    """All N/T/R/C pairs, with rectangular padded views and scaled reuse."""
    left = [[1+2j, 3+5j, 7+11j], [13+17j, 19+23j, 29+31j]]
    right = [[37+41j, 43+47j], [53+59j, 61+67j], [71+73j, 79+83j]]
    steps = []

    def action(op, **fields):
        steps.append({"kind": "action", "action": {"op": op, **fields}})

    def literal(value):
        def bits(x):
            return struct.unpack("<Q", struct.pack("<d", x))[0]
        return dict(kind="complex_f64", real=bits(value.real), imaginary=bits(value.imag))

    for case, (ta, tb, ca, cb) in enumerate(itertools.product([False, True], repeat=4)):
        base = 40 * case
        layouts = []
        for owner, (rows, columns, transpose) in enumerate([(2, 3, ta), (3, 2, tb), (2, 2, False)]):
            if transpose:
                rows, columns = columns, rows
            layout = dict(offset=16, rows=rows, columns=columns, leading=rows+2, transposed=transpose)
            layouts.append(layout)
            action("allocate", owner=base+owner, scalar="complex_f64", elements=1+(rows+2)*columns)
            action("borrow", name=base+10+owner, source=dict(kind="owner", name=base+owner),
                   layout=layout, access="write")
            if owner < 2:
                matrix = left if owner == 0 else right
                for i, row in enumerate(matrix):
                    for j, value in enumerate(row):
                        action("store", loan=base+10+owner, row=i, column=j, value=literal(value))
                action("release", loan=base+10+owner)
                action("borrow", name=base+20+owner, source=dict(kind="owner", name=base+owner),
                       layout=layout, access="read")
        request = dict(left=base+20, right=base+21, output=base+12, conjugate_left=ca,
                       conjugate_right=cb, mode="overwrite", policy="native_fast")
        action("gemm", **request)
        product = [[sum((a.conjugate() if ca else a) * (b.conjugate() if cb else b)
                        for a, b in zip(row, column)) for column in zip(*right)] for row in left]
        action("release", loan=base+12)
        action("borrow", name=base+22, source=dict(kind="owner", name=base+2), layout=layouts[2], access="read_write")
        for i, row in enumerate(product):
            for j, value in enumerate(row):
                action("expect", loan=base+22, row=i, column=j, value=literal(value))
        # Coefficients are not conjugated with the operands: (2+3i)P+(1-i)P.
        request.update(output=base+22, mode="accumulate",
                       alpha=dict(kind="literal", value=literal(2+3j)),
                       beta=dict(kind="literal", value=literal(1-1j)))
        action("gemm", **request)
        for i, row in enumerate(product):
            for j, value in enumerate(row):
                action("expect", loan=base+22, row=i, column=j, value=literal((3+2j)*value))
        for name in [20, 21, 22]:
            action("release", loan=base+name)
        for owner in range(3):
            action("drop", owner=base+owner)
    return {"statements": steps}


def run(command, *, cwd=ROOT, success=True, env=None):
    result = subprocess.run([str(x) for x in command], cwd=cwd, env=env, capture_output=True, text=True)
    if (result.returncode == 0) != success:
        raise RuntimeError(f"{command}\n{result.stdout}\n{result.stderr}")
    return result


def check(prefix, lean_cc=None):
    prefix = prefix.resolve()
    run(["lake", "-d", "lean-kernel", "build", "storage-native-fixture", "numerical-native-fixture"])
    emitter = ROOT / "lean-kernel/.lake/build/bin/storage-native-fixture"
    numerical_emitter = ROOT / "lean-kernel/.lake/build/bin/numerical-native-fixture"
    fixture = json.loads((ROOT / "tests/fixtures/storage-gemm.json").read_text())
    # Host-built BLAS may reference newer libc symbols than Lean's portable
    # bundled linker libraries. Select the matching host compiler/linker for
    # numerical consumers only; the independent kernel retains its own build.
    native_env = os.environ.copy()
    package_options = ""
    if lean_cc is not None:
        native_env["LEAN_CC"] = lean_cc
        # Keep Lean's matching C++ ABI/support libraries while using the host
        # libc. Its portable libc lives in lib/glibc, which is NOT added here.
        lean_root = Path(run(["lean", "--print-prefix"]).stdout.strip())
        package_options = f' where\n  moreLinkArgs := #["-L", {json.dumps(str(lean_root / "lib"))}]'
    with tempfile.TemporaryDirectory(prefix="vastitas-checked-gemm-") as directory:
        work = Path(directory)
        for package in ("native", "numerical"):
            shutil.copytree(ROOT / "lean-kernel" / package, work / package,
                            ignore=shutil.ignore_patterns(".lake"))
        (work / "lean-toolchain").write_text((ROOT / "lean-kernel/lean-toolchain").read_text())
        (work / "lakefile.lean").write_text(
            f'import Lake\nopen Lake DSL\npackage checked_gemm{package_options}\n'
            'require vastitas_gemm_native from "./numerical" with\n'
            f'  NameMap.empty.insert `openblas {json.dumps(str(prefix))}\n'
            'lean_exe fixture where root := `Main\n')
        path = work / "input.json"
        for name, budget, failure in [
                ("products", 256, None),
                ("assertion_failure", 256, "E_NATIVE_EXPECT"),
                ("allocation_failure", 128, "E_NATIVE_ALLOCATION")]:
            source = copy.deepcopy(fixture)
            if name == "assertion_failure":
                first = next(s["action"] for s in source["statements"] if s["action"]["op"] == "expect")
                first["value"]["bits"] = 0
            path.write_text(json.dumps(source))
            run([emitter, path, work / "Main.lean", budget])
            generated = (work / "Main.lean").read_text()
            assert generated.count("VastitasGemmNative.gemm arena") == 4
            assert "import VastitasGemmNative" in generated
            assert "borrow " not in generated
            assert "fill arena" not in generated
            run(["lake", "build", "fixture"], cwd=work, env=native_env)
            result = run([work / ".lake/build/bin/fixture"], cwd=work, success=failure is None)
            if failure:
                assert failure in result.stderr, result
            match = re.search(r"#\[([\d, ]+)\]", result.stdout)
            assert match, result
            counters = [int(x) for x in match[1].split(",")]
            assert counters[0] == counters[1] and counters[2] == 0 and counters[5] == 0, counters
            if name == "products":
                assert counters[:6] == [6, 6, 0, 256, 480, 0], counters
            elif name == "allocation_failure":
                assert counters[:6] == [4, 4, 0, 128, 256, 0], counters
            print(f"checked GEMM {name}: allocations/frees/live/peak/written/copied={counters[:6]}")
        for name, source in [("transpose", scalar_fixture(False)), ("conjugate_transpose", scalar_fixture(True)),
                             ("zero_inner", scalar_fixture(False, inner=0)), ("empty_output", scalar_fixture(False, empty=True))]:
            path.write_text(json.dumps(source))
            run([emitter, path, work / "Main.lean", 256])
            run(["lake", "build", "fixture"], cwd=work, env=native_env)
            result = run([work / ".lake/build/bin/fixture"], cwd=work)
            match = re.search(r"#\[([\d, ]+)\]", result.stdout)
            assert match, result
            counters = [int(x) for x in match[1].split(",")]
            assert counters[0] == counters[1] and counters[2] == 0 and counters[5] == 0, counters
            print(f"checked GEMM {name}: bits and cleanup passed")
        path.write_text(json.dumps(orientation_fixture()))
        run([emitter, path, work / "Main.lean", 1024])
        generated = (work / "Main.lean").read_text()
        assert generated.count("VastitasGemmNative.gemm arena") == 16
        assert generated.count("VastitasGemmNative.gemmScaled arena") == 16
        run(["lake", "build", "fixture"], cwd=work, env=native_env)
        result = run([work / ".lake/build/bin/fixture"], cwd=work)
        match = re.search(r"#\[([\d, ]+)\]", result.stdout)
        assert match, result
        counters = [int(x) for x in match[1].split(",")]
        assert counters[:3] == [48, 48, 0] and counters[4:6] == [5120, 0], counters
        print("checked GEMM all 16 N/T/R/C pairs: rectangular bits, explicit coefficients, destination reuse and cleanup passed")
        for kind, peak in [("real", 128), ("complex", 256)]:
            run([numerical_emitter, kind, work / "Main.lean"])
            generated = (work / "Main.lean").read_text()
            assert generated.count("VastitasGemmNative.gemm arena") == 1
            run(["lake", "build", "fixture"], cwd=work, env=native_env)
            result = run([work / ".lake/build/bin/fixture"], cwd=work)
            match = re.search(r"#\[([\d, ]+)\]", result.stdout)
            assert match, result
            counters = [int(x) for x in match[1].split(",")]
            assert counters[:6] == [3, 3, 0, peak, peak, 0], counters
            print(f"nominal {kind} product: checked objects/bases, exact bits and destination reuse passed")
        # Each raw action is rejected before code generation; no native output
        # file may be produced on an initialization/mode/policy/alias failure.
        first_gemm = next(i for i, s in enumerate(fixture["statements"]) if s["action"]["op"] == "gemm")
        for name, value in [("mode", "accumulate"), ("policy", "exact"),
                            ("left", 12), ("output", 20), ("conjugate_left", 2)]:
            source = copy.deepcopy(fixture)
            source["statements"][first_gemm]["action"][name] = value
            path.write_text(json.dumps(source))
            output = work / f"rejected-{name}.lean"
            result = run([emitter, path, output, 256], success=False)
            assert "resource component rejected" in result.stderr and not output.exists(), result
        # Exercise the header dependency in a real downstream linked build.
        objects = [work / "numerical/.lake/build" / name for name in ("gemm.o", "ffi.o")]
        before = [p.stat().st_mtime_ns for p in objects]
        header = work / "numerical/gemm.h"
        header.write_text(header.read_text() + "\n/* header dependency regression */\n")
        run(["lake", "build", "fixture"], cwd=work, env=native_env)
        assert all(p.stat().st_mtime_ns != old for p, old in zip(objects, before))
    print("Checked raw and nominal GEMM/native FFI passed; public source integration remains separate.")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--prefix", type=Path, required=True)
    parser.add_argument("--lean-cc", help="native consumer compiler executable, e.g. cc for host Linux libc")
    args = parser.parse_args()
    check(args.prefix, args.lean_cc)
