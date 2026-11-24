#!/usr/bin/env python3
"""Opt-in LLVM/native ABI qualification; not compiler or proof acceptance."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import shlex
import shutil
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
LLVM_VERSION = "23.1.4"
LEAN_VERSION = "4.35.0"
LEAN_COMMIT = "eb6cafb7290e8bd5f2937522d8d804f58f02bafc"
BLAS_VERSION = "0.3.34"


def digest(path):
    with Path(path).open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def capture(command, *, env=None, cwd=None):
    result = subprocess.run(command, env=env, cwd=cwd, capture_output=True, text=True)
    if result.returncode:
        raise ValueError(f"{Path(command[0]).name} failed with exit {result.returncode}")
    return result.stdout.strip()


def validate_version(value, expected, name):
    if value.strip() != expected:
        raise ValueError(f"expected {name} {expected}, found {value.strip()!r}")


def environment(llvm, target):
    allowed = ("PATH", "HOME", "CARGO_HOME", "RUSTUP_HOME", "TMPDIR", "LANG", "LC_ALL",
               "SDKROOT", "DEVELOPER_DIR", "MACOSX_DEPLOYMENT_TARGET", "LIBRARY_PATH",
               "CARGO_TARGET_AARCH64_APPLE_DARWIN_LINKER")
    env = {key: os.environ[key] for key in allowed if key in os.environ}
    env.update(LLVM_SYS_231_PREFIX=str(llvm), CARGO_TARGET_DIR=str(target))
    return env


def linux_runtime_libraries(lean, work):
    """Give the host linker the pinned Lean archives while it uses its own libc."""
    directory = work / "lean-runtime-libs"
    directory.mkdir()
    for name in ("libc++.a", "libc++abi.a", "libunwind.a", "libuv.a", "libgmp.a"):
        (directory / name).symlink_to((lean / "lib" / name).resolve(strict=True))
    return directory


def emitter_comparison(lean, extra_needles=None):
    """Identify the pinned upstream comparison source and its relevant gaps."""
    relative = "src/lean/Lean/Compiler/IR/EmitLLVM.lean"
    path = lean / relative
    source = path.read_text()
    needles = {
        "abi_and_untested_notice": "our CI for LLVM is dysfunctional",
        "fixed_size_t": "def size_tType",
        "case_default": "def ensureHasDefault'",
        "case_tag_width": "buildZext builder tag",
        "case_switch": "buildSwitch builder tag",
        "join_point_lowering": "by generating SSA phi nodes",
        "executable_main": "def emitMainFn (",
        "main_status": "let retv ← callLeanUnboxUint32",
        "inbounds_gep": "buildInBoundsGEP",
        "bitcode_output": "writeBitcodeToFile",
    }
    needles.update(extra_needles or {})
    observations = {}
    for name, needle in needles.items():
        lines = [number for number, text in enumerate(source.splitlines(), 1) if needle in text]
        observations[name] = {"matched_lines": lines, "needle": needle}
    return {"source": relative, "sha256": digest(path), "observations": observations,
            "role": "comparison only; not a correctness oracle", "executed": False}


def generated_ir(template, triple, layout):
    if not re.fullmatch(r"[A-Za-z0-9_.:-]+", triple):
        raise ValueError("invalid target triple")
    if not re.fullmatch(r"[A-Za-z0-9_.:-]+", layout):
        raise ValueError("invalid target data layout")
    result = template.replace("@TRIPLE@", triple).replace("@LAYOUT@", layout)
    if "@TRIPLE@" in result or "@LAYOUT@" in result:
        raise ValueError("unexpanded LLVM fixture")
    return result.encode()


def run(args):
    llvm, lean, blas = (path.resolve() for path in (args.llvm_prefix, args.lean_prefix, args.openblas_prefix))
    output = args.output.resolve()
    if output.exists() and any(output.iterdir()):
        raise ValueError("output directory must be empty")
    output.mkdir(parents=True, exist_ok=True)
    report = {
        "schema": 1, "status": "blocked", "scope": "foreign LLVM/native feasibility spike",
        "proof_status": "Not claimed", "public_source_admission": False,
        "host": {"system": platform.system(), "release": platform.release(), "machine": platform.machine()},
        "llvm_sys": "231.0.1", "llvm_link_mode": args.link_mode,
        "phases": {}, "negative_cases": {},
    }
    target = args.target_dir.resolve() if args.target_dir else output / "target"
    report["cargo_target_preexisting"] = target.exists()
    env = environment(llvm, target)

    def measured(label, command, cwd=None, expect_success=True):
        result_file = output / f"{label}.measure.json"
        result = subprocess.run([sys.executable, str(HERE / "measure.py"), str(result_file), "--",
                                 *map(str, command)], env=env, cwd=cwd, capture_output=True, text=True)
        report["phases"][label] = json.loads(result_file.read_text())
        if expect_success is not None and expect_success != (result.returncode == 0):
            # No absolute paths, environment values or machine-local logs in the report.
            report["phases"][label]["diagnostic"] = result.stderr[-4096:]
            raise ValueError(f"{label}: unexpected exit status {result.returncode}")
        return result

    try:
        llvm_config = llvm / "bin/llvm-config"
        version = capture([str(llvm_config), "--version"], env=env)
        validate_version(version, LLVM_VERSION, "LLVM")
        report["llvm"] = {"version": version, "llvm_config_sha256": digest(llvm_config)}
        library_paths = shlex.split(capture([str(llvm_config), "--libfiles", f"--link-{args.link_mode}"], env=env))
        report["llvm"]["libraries"] = [{"name": Path(path).name, "sha256": digest(path),
                                         "bytes": Path(path).stat().st_size} for path in library_paths]
        system_libraries = shlex.split(capture([str(llvm_config), "--system-libs", f"--link-{args.link_mode}"], env=env))
        report["llvm"]["system_libraries"] = [
            {"name": Path(value).name, "sha256": digest(value)} if Path(value).is_absolute()
            else {"flag": value} for value in system_libraries]
        report["inputs"] = {name: digest(HERE / name) for name in (
            "Cargo.toml", "Cargo.lock", "src/main.rs", "shim.c", "RuntimeProbe.lean", "program.ll.in",
            "Comparison.lean", "FamilyComparison.lean", "OppositeComparison.lean", "StructuredLookupComparison.lean",
            "GemmComparison.lean", "run.py", "measure.py")}
        predicate_source = Path("llvm/fixtures/ComparisonMethodControl.lean")
        report["inputs"][str(predicate_source)] = digest(ROOT / predicate_source)
        family_source = Path("tests/fixtures/FamilyComparison.vast")
        report["inputs"][str(family_source)] = digest(ROOT / family_source)
        adapter = Path("src/driver/llvm_backend.rs")
        report["inputs"][str(adapter)] = digest(ROOT / adapter)
        report["rust"] = capture(["rustc", "--version"], env=env)
        report["c_compiler"] = capture(["cc", "--version"], env=env).splitlines()[0]
        lean_bin = lean / "bin/lean"
        lean_version = capture([str(lean_bin), "--version"], env=env)
        if not re.search(r"version 4\.35\.0\b", lean_version) or LEAN_COMMIT not in lean_version:
            raise ValueError("Lean toolchain version or commit differs from pin")
        report["lean"] = {"version": LEAN_VERSION, "commit": LEAN_COMMIT,
                          "binary_sha256": digest(lean_bin), "leanc_sha256": digest(lean / "bin/leanc"),
                          "header_sha256": digest(lean / "include/lean/lean.h")}
        runtime_libraries = sorted((lean / "lib").glob("*.a")) + sorted((lean / "lib/lean").glob("*.a"))
        report["lean"]["runtime_archives"] = [{"name": str(path.relative_to(lean)), "sha256": digest(path)}
                                              for path in runtime_libraries]
        archive = blas / "lib/libopenblas.a"
        report["openblas"] = {"version": BLAS_VERSION, "archive_sha256": digest(archive),
                              "header_sha256": digest(blas / "include/cblas.h")}
        report["emitter_comparison"] = emitter_comparison(lean, {"external_call": "def emitSimpleExternalCall"})
        features = json.loads(capture([str(lean_bin), "--features"], env=env))
        report["emitter_comparison"]["toolchain_features"] = features
        suites = report["emitter_comparison"]["fixtures"] = {}
        with tempfile.TemporaryDirectory(prefix="vastitas-lean-llvm-") as temporary:
            comparison = Path(temporary)
            fixtures = {name: HERE / (name + ".lean") for name in
                        ("Comparison", "FamilyComparison", "OppositeComparison", "StructuredLookupComparison", "GemmComparison")}
            fixtures["IntegerPredicateComparison"] = ROOT / predicate_source
            for stem, fixture in fixtures.items():
                suite = suites[stem] = {"emitted": False, "disassembled": False}
                source = stem + ".lean"
                shutil.copyfile(fixture, comparison / source)
                if stem == "FamilyComparison":
                    measured("lean_family_results", [lean_bin, "--run", source], comparison)
                    suite["reference_results_checked"] = True
                if stem == "GemmComparison":
                    result = measured("lean_gemm_coefficients", [lean_bin, "--run", source], comparison)
                    suite["reference_component_bits"] = result.stdout.strip()
                if stem == "OppositeComparison":
                    result = measured("lean_opposite_results", [lean_bin, "--run", source],
                                      comparison, expect_success=None)
                    if result.returncode != 42:
                        raise ValueError("opposite S3 comparison did not return 42")
                    suite["reference_exit_status"] = result.returncode
                if stem == "StructuredLookupComparison":
                    for method, arguments, expected in [("selected", [], 42), ("fallback", ["fallback"], 7)]:
                        result = measured(f"lean_lookup_{method}", [lean_bin, "--run", source, *arguments],
                                          comparison, expect_success=None)
                        if result.returncode != expected:
                            raise ValueError(f"structured lookup {method} returned {result.returncode}, expected {expected}")
                        suite[f"{method}_exit_status"] = result.returncode
                if "LLVM" not in features:
                    suite["execution_gap"] = "pinned Lean binary reports no LLVM feature"
                    continue
                report["emitter_comparison"]["executed"] = True
                bitcode = output / (stem + ".bc")
                compared = measured(stem + "_emission", [lean_bin, "-b", bitcode, source],
                                    comparison, expect_success=None)
                if compared.returncode or not bitcode.is_file():
                    suite["execution_gap"] = "pinned Lean LLVM emission failed"
                    continue
                suite["emitted"] = True
                ir = output / (stem + ".ll")
                disassembled = measured(stem + "_disassembly", [llvm / "bin/llvm-dis", bitcode, "-o", ir],
                                        expect_success=None)
                if disassembled.returncode or not ir.is_file():
                    suite["execution_gap"] = "upstream bitcode disassembly failed"
                    continue
                suite.update(disassembled=True, output_sha256=digest(ir))
        cargo = ["cargo", "build", "--locked", "--manifest-path", str(HERE / "Cargo.toml"),
                 "--jobs", "1", "--no-default-features", "--features", f"llvm-{args.link_mode}"]
        if not args.allow_cargo_downloads:
            cargo.append("--offline")
        measured("backend_build", cargo, cwd=ROOT)
        backend = target / "debug/vastitas-llvm-qualification"
        described = capture([str(backend), "describe"], env=env)
        description = dict(line.split("=", 1) for line in described.splitlines())
        validate_version(description["llvm"], LLVM_VERSION, "linked LLVM")
        report["target"] = {"triple": description["triple"], "data_layout": description["layout"],
                            "cpu": "generic", "features": "", "optimization": "none", "relocation": "PIC"}
        template = (HERE / "program.ll.in").read_text()
        data = generated_ir(template, description["triple"], description["layout"])
        authorized, handoff, object_path = (output / name for name in ("authorized.ll", "handoff.ll", "program.o"))
        authorized.write_bytes(data)
        handoff.write_bytes(data)
        measured("llvm_object", [backend, "emit", authorized, handoff, object_path])
        report["llvm"]["input_sha256"] = digest(handoff)
        report["llvm"]["input_bytes"] = len(data)

        # LLVM receives exactly the compared immutable buffer. No hash-only authorization.
        mutated = output / "mutated.ll"
        mutated.write_bytes(data + b"\n")
        rejected = output / "rejected.o"
        result = measured("reject_changed_bytes", [backend, "emit", authorized, mutated, rejected], expect_success=False)
        if rejected.exists() or "complete LLVM byte comparison failed" not in result.stderr:
            raise ValueError("modified byte fixture did not fail before object generation")
        report["negative_cases"]["changed_bytes"] = "rejected before LLVM parsing"
        malformed = output / "malformed.ll"
        malformed.write_bytes(b"not LLVM IR\n")
        measured("reject_parser", [backend, "emit", malformed, malformed, rejected], expect_success=False)
        if rejected.exists():
            raise ValueError("parser failure created an object")
        report["negative_cases"]["malformed_ir"] = "rejected"
        wrong_layout = output / "wrong-layout.ll"
        wrong_layout.write_bytes(data.replace(description["layout"].encode(), b"e-p:32:32"))
        measured("reject_layout", [backend, "emit", wrong_layout, wrong_layout, rejected], expect_success=False)
        if rejected.exists():
            raise ValueError("layout failure created an object")
        report["negative_cases"]["wrong_layout"] = "rejected"

        with tempfile.TemporaryDirectory(prefix="vastitas-llvm-runtime-") as temporary:
            work = Path(temporary)
            runtime_source = ROOT / "lean-kernel/VastitasKernel/IndexedRuntime.lean"
            shutil.copyfile(runtime_source, work / "IndexedRuntime.lean")
            shutil.copyfile(HERE / "RuntimeProbe.lean", work / "RuntimeProbe.lean")
            report["lean"]["indexed_runtime_source_sha256"] = digest(runtime_source)
            env["LEAN_PATH"] = str(work)
            measured("runtime_lean", [lean_bin, "-o", "IndexedRuntime.olean", "-c", "IndexedRuntime.c", "IndexedRuntime.lean"], work)
            measured("probe_lean", [lean_bin, "-o", "RuntimeProbe.olean", "-c", "RuntimeProbe.c", "RuntimeProbe.lean"], work)
            leanc = lean / "bin/leanc"
            sdk = ["-isysroot", capture(["xcrun", "--show-sdk-path"], env=env)] if sys.platform == "darwin" else []
            measured("runtime_c", [leanc, *sdk, "-c", "-O2", "IndexedRuntime.c", "-o", "IndexedRuntime.o"], work)
            measured("probe_c", [leanc, *sdk, "-c", "-O2", "RuntimeProbe.c", "-o", "RuntimeProbe.o"], work)
            measured("shim_c", ["cc", *sdk, "-c", "-std=c11", "-O2", "-Wall", "-Wextra", "-Werror",
                                 "-I" + str(lean / "include"), "-I" + str(blas / "include"),
                                 HERE / "shim.c", "-o", "shim.o"], work)
            family = "FamilyComparison"
            shutil.copyfile(HERE / f"{family}.lean", work / f"{family}.lean")
            measured("family_lean_c", [lean_bin, "-c", f"{family}.c", f"{family}.lean"], work)
            # The executable entry is the LLVM fixture. Only link the reference
            # evaluator and its initialization from this generated translation.
            measured("family_reference_object", [leanc, *sdk, "-O2", "-Dmain=vq_reference_main",
                                                  "-Drun_main=vq_reference_run_main", "-c",
                                                  f"{family}.c", "-o", "family.o"], work)
            report["emitter_comparison"]["fixtures"][family]["reference_c_sha256"] = digest(work / f"{family}.c")
            library = output / "libqualification_runtime.a"
            measured("runtime_archive", [lean / "bin/llvm-ar", "rcs", library,
                                           "IndexedRuntime.o", "RuntimeProbe.o", "shim.o", "family.o"], work)
            executable = output / "program"
            system_libs = [] if sys.platform == "darwin" else ["-lm", "-lpthread"]
            if sys.platform.startswith("linux"):
                # OpenBLAS was built against the host libc. Use its linker
                # driver with leanc's runtime flags and the host sysroot.
                directory = linux_runtime_libraries(lean, work)
                system_libs.insert(0, "-L" + str(directory))
                report["lean"]["linux_link_archives"] = sorted(p.name for p in directory.iterdir())
                env["LEAN_CC"] = "cc"
                report["native_link_driver"] = report["c_compiler"]
            measured("link", [leanc, *sdk, object_path, library, archive, *system_libs, "-o", executable], work)
            result = measured("execute", [executable])
            if not result.stdout.startswith("openblas=OpenBLAS 0.3.34 "):
                raise ValueError("missing executed OpenBLAS profile")
            report["openblas"]["runtime_configuration"] = result.stdout.strip().removeprefix("openblas=")
        report["artifacts"] = {name: {"bytes": (output / name).stat().st_size, "sha256": digest(output / name)}
                               for name in ("program.o", "libqualification_runtime.a", "program")}
        report["backend_binary_bytes"] = backend.stat().st_size
        report["build_tree_bytes"] = sum(path.stat().st_size for path in target.rglob("*") if path.is_file() and not path.is_symlink())
        report["checks"] = ["big_nat_square", "int_euclidean_division", "division_by_zero", "nat_monus",
                            "indexed_runtime", "sgemm", "dgemm", "cgemm", "zgemm", "branch_phi",
                            "family_llvm_vs_lean_c_both_branches_small_and_big",
                            "mixed_division_both_orders_against_lean_c"]
        report["status"] = "passed"
        return 0
    except (ValueError, OSError, KeyError) as error:
        report["status"] = "blocked"
        report["failure"] = str(error)
        return 1
    finally:
        # Prefixes are command inputs, not evidence. Keep records portable.
        text = json.dumps(report, indent=2, sort_keys=True)
        for value, replacement in ((str(llvm), "<LLVM_PREFIX>"), (str(lean), "<LEAN_PREFIX>"),
                                   (str(blas), "<OPENBLAS_PREFIX>"), (str(output), "<OUTPUT>"),
                                   (str(ROOT), "<REPOSITORY>")):
            text = text.replace(value, replacement)
        text = text.replace(str(Path.home()), "<HOME>")
        (output / "report.json").write_text(text + "\n")
        print(f"LLVM qualification: {report['status']}")
        if "failure" in report:
            print(report["failure"], file=sys.stderr)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--llvm-prefix", type=Path, required=True)
    parser.add_argument("--lean-prefix", type=Path, required=True)
    parser.add_argument("--openblas-prefix", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--target-dir", type=Path)
    parser.add_argument("--link-mode", choices=("static", "dynamic"), default="static")
    parser.add_argument("--allow-cargo-downloads", action="store_true")
    args = parser.parse_args()
    if platform.system() not in ("Darwin", "Linux"):
        parser.error("only macOS and Linux are qualified")
    try:
        raise SystemExit(run(args))
    except ValueError as error:
        parser.error(str(error))


if __name__ == "__main__":
    main()
