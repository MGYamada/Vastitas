#!/usr/bin/env python3
"""Correctness/cost-only actual emitted runtime shapes versus checked direct CBLAS."""
import argparse
import datetime as dt
import importlib.util
import json
import os
from pathlib import Path
import platform
import shutil
import sys

from cases import HERE, ROOT, driver, shapes, split_generated, write_package

# Reuse only bounded command logging/capture/hash utilities. No tensor fixture,
# transformation, arithmetic or timing result is reused.
_spec = importlib.util.spec_from_file_location("tree_runner", ROOT / "experiments/contraction_trees/run.py")
_module = importlib.util.module_from_spec(_spec)
sys.path.insert(0, str(ROOT / "experiments/contraction_trees"))
# The imported module names cases; supply its own module during import.
_saved = sys.modules.pop("cases")
try:
    _spec.loader.exec_module(_module)
finally:
    sys.modules["cases"] = _saved
    sys.path.pop(0)
Runner, dump, sha, capture_wire, verify_inputs = (_module.Runner, _module.dump, _module.sha, _module.capture_wire, _module.verify_inputs)
FLAGS = ["-std=c11", "-O3", "-fno-lto", "-Wall", "-Wextra", "-Werror"]


def pair(a, b):
    # C receives uint64 extents and checks arithmetic; it has no Lean Nat boxing
    # or narrowing. This explicitly reported boundary difference is not hidden.
    if a.keys() != b.keys() or any(a[k] != b[k] for k in a if k != "scope_nat_narrowings"):
        raise ValueError(f"output/cost mismatch: {a} != {b}")


def profile(path, scalar, transpose):
    (path / "profile.h").write_text(f"#define SCALAR {scalar}\n#define TRANSPOSE {transpose}\n")


def instrument_gemm(path):
    path.write_text('#include "calls.h"\n#define cblas_dgemm shape_dgemm\n#define cblas_zgemm shape_zgemm\n' + (ROOT / "lean-kernel/numerical/gemm.c").read_text())


def native(runner, path, scalar, transpose, prefix, cc, sanitize, no_lsan):
    path.mkdir(parents=True)
    profile(path, scalar, transpose)
    instrument_gemm(path / "gemm.c")
    flags = FLAGS if not sanitize else ["-std=c11", "-O1", "-g", "-Wall", "-Wextra", "-Werror", "-fsanitize=address,undefined", "-fno-sanitize-recover=all", "-fno-omit-frame-pointer"]
    if sanitize and sys.platform.startswith("linux"):
        flags += ["-fno-pie", "-no-pie"]
    exe = path / "native"
    runner.run([cc, *flags, "-DBENCH_STANDALONE", "-I", path, "-I", HERE, "-I", ROOT / "lean-kernel/numerical", "-I", prefix / "include", "-I", ROOT / "lean-kernel/native", HERE / "probe.c", ROOT / "lean-kernel/native/diagonal.c", path / "gemm.c", prefix / "lib/libopenblas.a", "-lm", "-lpthread", "-o", exe], phase="native_compile")
    env = dict(runner.env)
    if no_lsan:
        env["ASAN_OPTIONS"] = env.get("ASAN_OPTIONS", "") + ":detect_leaks=0"
    result = runner.run([exe], env=env, phase="sanitizer" if sanitize else "native_validation")
    rows = [json.loads(line) for line in result["stdout"].splitlines()]
    if len(rows) != 12:
        raise ValueError("missing native rows")
    return dict(scalar=scalar, transpose=transpose, sanitizer=sanitize, rows=rows)


def private_runtime(work, scalar, transpose):
    for name in ("native", "numerical"):
        shutil.copytree(ROOT / "lean-kernel" / name, work / name, ignore=shutil.ignore_patterns(".lake"))
    profile(work / "native", scalar, transpose)
    instrument_gemm(work / "numerical/gemm.c")
    shutil.copyfile(HERE / "calls.h", work / "numerical/calls.h")
    shutil.copyfile(HERE / "calls.h", work / "native/calls.h")
    (work / "native/storage.c").write_text(f'#include {json.dumps(str(HERE / "probe.c"))}\n')
    with (work / "native/ffi.c").open("a") as stream:
        stream.write("\n" + (HERE / "ffi.c").read_text())
    p = work / "native/lakefile.lean"
    p.write_text(p.read_text().replace('"-std=c11", "-O3"', '"-std=c11", "-O3", "-fno-lto", ' + json.dumps("-I" + str(work / "native")) + ", " + json.dumps("-I" + str(work / "include"))))


def build(runner, work, scalar, transpose, args, lean_root):
    # This unmodified executable has two real source call sites and four GEMMs.
    canonical = work / "public"
    write_package(canonical, scalar, transpose, twice=True)
    for mode in ("check", "build"):
        command = [args.frontend, mode, "--manifest-path", canonical / "Vastitas.toml"]
        if mode == "build":
            command += ["--openblas-prefix", args.prefix, "--native-cc", args.cc, "-o", work / "canonical"]
        runner.run(command, phase="public_" + mode)
    result = runner.run([work / "canonical"], phase="public_execution")
    if result["stdout"].strip() != "0":
        raise ValueError("public result mismatch")
    public_wire = capture_wire(runner, args.frontend, canonical)
    response = json.loads(runner.run([args.kernel, "emit"], input=public_wire, phase="public_emit")["stdout"])
    if not response.get("ok") or response["lean_source"].count("    VastitasGemmNative.gemm ") != 4:
        raise ValueError("public multiple-call expansion changed")
    dump(work / "public-response.json", response)
    # The parameterized experimental wrapper is a distinct retained emission.
    write_package(work / "wrapper-source", scalar, transpose)
    wire = capture_wire(runner, args.frontend, work / "wrapper-source")
    result = json.loads(runner.run([args.kernel, "check"], input=wire, phase="wrapper_source_check")["stdout"])
    if not result.get("ok"):
        raise ValueError(result)
    response = json.loads(runner.run([args.kernel, "emit"], input=wire, phase="wrapper_source_emit")["stdout"])
    if not response.get("ok") or not response.get("numerical_runtime"):
        raise ValueError(response)
    dump(work / "response.json", response)
    generated = response["lean_source"]
    (work / "Generated.lean").write_text(generated)
    (work / "Main.lean").write_text(driver(generated))
    _, setup, operation, cleanup = split_generated(generated)
    audit = dict(setup=setup, operation=operation, cleanup=cleanup,
                 guards=sum("    unless " in x for x in setup+operation),
                 narrowings=sum(" ← runtimeExtentNat " in x for x in setup+operation))
    if (audit["guards"], audit["narrowings"]) != (6, 9):
        raise ValueError("guard/narrowing contract changed")
    dump(work / "transformation.json", audit)
    private_runtime(work, scalar, transpose)
    (work / "include").symlink_to(args.prefix / "include", target_is_directory=True)
    shutil.copyfile(ROOT / "lean-kernel/lean-toolchain", work / "lean-toolchain")
    (work / "lakefile.lean").write_text(f'''import Lake
open Lake DSL
package runtime_shape_audit where
  moreLinkArgs := #["-fno-lto", "-L", {json.dumps(str(lean_root / 'lib'))}]
require vastitas_kernel from {json.dumps(str(ROOT / 'lean-kernel'))}
require vastitas_gemm_native from "./numerical" with
  NameMap.empty.insert `openblas {json.dumps(str(args.prefix))}
lean_exe audit where
  root := `Main
  moreLeancArgs := #["-O3", "-fno-lto"]
''')
    runner.run(["lake", "build", "audit"], cwd=work, env=dict(runner.env, LEAN_CC=args.cc), phase="wrapper_compile")
    exe = work / ".lake/build/bin/audit"
    runner.run(["nm", exe], phase="symbols", stdout_path=work / "symbols.txt")
    return exe


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--prefix", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--frontend", type=Path, default=ROOT / "target/debug/vastitas")
    parser.add_argument("--kernel", type=Path, default=ROOT / "lean-kernel/.lake/build/bin/vastitas-kernel")
    parser.add_argument("--cc", default="cc")
    parser.add_argument("--no-leak-sanitizer", action="store_true")
    args = parser.parse_args()
    if sys.platform == "darwin" and not args.no_leak_sanitizer:
        parser.error("Apple ASan lacks LSan; pass --no-leak-sanitizer explicitly")
    for name in ("prefix", "output", "frontend", "kernel"):
        setattr(args, name, getattr(args, name).resolve())
    args.output.mkdir(parents=True, exist_ok=False)
    env = dict(os.environ, OPENBLAS_NUM_THREADS="1", OMP_NUM_THREADS="1", GOTO_NUM_THREADS="1", VASTITAS_KERNEL=str(args.kernel), VASTITAS_KERNEL_ROOT=str(ROOT / "lean-kernel"))
    runner = Runner(args.output, env)
    info = dict(started=dt.datetime.now(dt.timezone.utc).isoformat(), argv=sys.argv, platform=platform.platform(),
                performance="not measured; instrumented correctness/cost only", source_sha256={},
                lsan="explicitly unavailable" if args.no_leak_sanitizer else "enabled", commands={})
    for name, command in {"git":["git","rev-parse","HEAD"],"dirty":["git","status","--short"],"lean":["lean","--version"],"cc":[args.cc,"--version"]}.items():
        info["commands"][name] = runner.run(command, phase="environment")
    for rel in ("experiments/runtime_shapes", "experiments/native_cleanup.py", "experiments/contraction_trees/run.py", "experiments/contraction_trees/cases.py", "experiments/storage_copy/run.py", "lean-kernel/native", "lean-kernel/numerical", "src/storage.rs", "src/frontend/resource_parser.rs", "lean-kernel/VastitasKernel/ResourceSource.lean", "lean-kernel/VastitasKernel/ResourceCodegen.lean", "lean-kernel/VastitasKernel/StorageCodegen.lean", "lean-kernel/VastitasKernel/ResourceProtocol.lean", "lean-kernel/VastitasKernel/StorageFunctions.lean"):
        path = ROOT / rel
        files = [path] if path.is_file() else path.rglob("*")
        for f in files:
            if f.is_file() and not any(p in f.parts for p in (".lake", "__pycache__", "results")):
                key = str(f.relative_to(ROOT)); info["source_sha256"][key] = sha(f)
                target = args.output / "source" / key; target.parent.mkdir(parents=True, exist_ok=True); shutil.copyfile(f, target)
    for f in (ROOT / "lean-kernel/VastitasKernel").glob("StorageShape*.lean"):
        key = str(f.relative_to(ROOT)); info["source_sha256"][key] = sha(f)
        target = args.output / "source" / key; target.parent.mkdir(parents=True, exist_ok=True); shutil.copyfile(f, target)
    for f in (args.frontend,args.kernel,args.prefix / "lib/libopenblas.a",args.prefix / "include/cblas.h",args.prefix / "include/openblas_config.h"):
        info["source_sha256"][str(f)] = sha(f)
    dump(args.output / "environment.json", info)
    lean_root = Path(runner.run(["lean", "--print-prefix"])["stdout"].strip())
    records, validation, failures = [], [], []
    try:
        for scalar in (0,1):
            for transpose in (0,1):
                name = f"{'complex' if scalar else 'real'}-{'transpose' if transpose else 'normal'}"
                work = args.output / name; work.mkdir()
                for sanitize in (False,True):
                    validation.append(native(runner,work / ("sanitized" if sanitize else "native-test"),scalar,transpose,args.prefix,args.cc,sanitize,args.no_leak_sanitizer))
                    dump(args.output / "native-validation.json",validation)
                exe=build(runner,work,scalar,transpose,args,lean_root)
                dimensions=[str(v) for c in shapes() for v in c[1:]]
                for scope in (0,1):
                    for reps in (1,3,7):
                        found={}
                        for implementation in ("generated","c"):
                            result=runner.run([exe,implementation,scope,reps,1,*dimensions],phase="coordinate_cost_validation")
                            rows=[json.loads(line) for line in result["stdout"].splitlines()]
                            if len(rows)!=len(shapes()):raise ValueError("missing dynamic shapes in one process")
                            found[implementation]=rows
                            records += [dict(profile=name,scope=scope,implementation=implementation,**row) for row in rows]
                        for a,b in zip(found["generated"],found["c"]):pair(a,b)
                        dump(args.output / "records.json",records)
                for dims in ((2147483648,3,4,1),(2**64,3,4,1),(2,3,4,2**63)):
                    result=runner.run([exe,"generated",0,1,1,*dims],required=False,phase="narrowing_failure_cleanup")
                    if not result["returncode"] or result["stdout"] or "E_RUNTIME_" not in result["stderr"] or "AUDIT_FAILURE_CLEANUP" not in result["stderr"]:
                        raise ValueError(f"failure did not preserve clean exit: {result}")
                    failures.append(dict(profile=name,dimensions=dims,**result));dump(args.output / "failure-validation.json",failures)
                print(f"{name}: public + emitted multiple shapes, native/sanitizers, output/cost/cleanup passed",flush=True)
        verify_inputs(info["source_sha256"])
        info["inputs_unchanged"]=True
        dump(args.output / "status.json",dict(status="passed",records=len(records),native=len(validation),failures=len(failures),performance="not measured"))
    except Exception as error:
        dump(args.output / "status.json",dict(status="failed",reason=str(error),performance="not measured"));raise
    finally:
        info["finished"]=dt.datetime.now(dt.timezone.utc).isoformat();dump(args.output / "environment.json",info)


if __name__ == "__main__":
    main()
