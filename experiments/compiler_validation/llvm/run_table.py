#!/usr/bin/env python3
"""Qualify the canonical unary table module for the native host."""
import argparse
import json
from pathlib import Path
import shutil
import subprocess
import tempfile

from run import HERE, ROOT, LEAN_COMMIT, capture, digest, emitter_comparison


def native_results(work, backend, module, inputs, symbol="vq_lookup"):
    if symbol not in {"vq_lookup", "vq_forward"}:
        raise ValueError(f"unexpected foreign function {symbol}")
    readback = work / "readback.ll"
    shutil.copyfile(module, readback)
    obj = work / "table.o"
    capture([backend, "emit", module, readback, obj])
    probe = work / "probe.c"
    probe.write_text('#include <inttypes.h>\n#include <stdio.h>\n'
                     f'extern uint32_t {symbol}(uint32_t);\n'
                     'int main(void) {\n'
                     '  uint32_t i;\n'
                     f'  while (scanf("%" SCNu32, &i) == 1) printf("%" PRIu32 "\\n", {symbol}(i));\n'
                     '  return !feof(stdin);\n}\n')
    exe = work / "table"
    capture(["cc", "-std=c11", "-Wall", "-Wextra", "-Werror", probe, obj, "-o", exe])
    result = subprocess.run([exe], input="\n".join(map(str, inputs)) + "\n",
                            text=True, capture_output=True, check=True)
    return result.stdout.strip(), obj.stat().st_size


def check_changed_handoff(backend, original, changed, rejected):
    attempt = subprocess.run([backend, "emit", original, changed, rejected],
                             capture_output=True, text=True)
    if (attempt.returncode == 0 or rejected.exists() or
            "complete LLVM byte comparison failed" not in attempt.stderr):
        raise ValueError(f"{changed.name}: expected byte mismatch before object emission")


def mutations(rows, original):
    """The expected raw LLVM result is separate from canonical byte admission."""
    def replace(old, new):
        if old not in original:
            raise ValueError(f"missing canonical fixture marker {old!r}")
        return original.replace(old, new, 1)

    yield "trailing-comment", original + b"; extra\n", True
    yield "undefined-default-block", replace(b"label %miss [", b"label %void ["), False
    if rows == 0:
        yield "changed-miss-value", replace(b"  ret i32 -1", b"  ret i32 -2"), True
    else:
        yield "retargeted-edge", replace(b"label %k0000\n", b"label %k0001\n"), True
        yield "duplicate-case", replace(b"i32 u0x0000, label", b"i32 u0x0001, label"), False
        yield "out-of-range-output", replace(b"ret i32 u0x0FFF", b"ret i32 u0x1000"), True
        wrong_count = replace(b"; rows 1000", b"; rows 1001")
        yield "wrong-row-count", wrong_count, True
        extra_case = wrong_count.replace(b"  ]\nmiss:", b"    i32 u0x1000, label %k1000\n  ]\nmiss:", 1)
        extra_case = extra_case.removesuffix(b"}\n") + b"k1000:\n  ret i32 u0x0000\n}\n"
        if extra_case.count(b"    i32 u0x") != 4097 or extra_case.count(b"  ret i32 u0x") != 4097:
            raise ValueError("expected exactly 4097 cases and 4097 output blocks")
        yield "4097-complete-cases", extra_case, True


def check_boundaries(work, backend, lean_command, machine):
    fixture = HERE / "TableBoundary.lean"
    inputs = [*range(4097), 0xFFFFFFFF]
    cases = []
    for rows in (0, 4096):
        case = work / f"boundary-{rows}"
        case.mkdir()
        module = case / "table.ll"
        model = capture([*lean_command, fixture, "generate", str(rows), machine["triple"],
                         machine["layout"], module], cwd=ROOT)
        native, obj_bytes = native_results(case, backend, module, inputs)
        expected = [str(4095 - i if i < rows else 0xFFFFFFFF) for i in inputs]
        if native != model or native.splitlines() != expected:
            raise ValueError(f"{rows} rows: boundary native or modeled results differ")

        altered = []
        raw_llvm = {}
        for name, data, accepted in mutations(rows, module.read_bytes()):
            changed = case / f"{name}.ll"
            changed.write_bytes(data)
            altered.append(changed)
            check_changed_handoff(backend, module, changed, case / f"{name}-handoff.o")
            obj = case / f"{name}-raw.o"
            raw = subprocess.run([backend, "emit", changed, changed, obj], capture_output=True)
            if (raw.returncode == 0) != accepted or obj.is_file() != accepted:
                raise ValueError(f"{name}: unexpected raw LLVM result")
            raw_llvm[name] = "accepted" if accepted else "rejected"
        capture([*lean_command, fixture, "reject", *altered], cwd=ROOT)
        cases.append({"rows": rows, "module_bytes": module.stat().st_size,
                      "module_sha256": digest(module), "object_bytes": obj_bytes,
                      "matched_inputs": len(inputs), "parser_and_handoff_rejected": list(raw_llvm),
                      "raw_llvm": raw_llvm})
    return {"fixture_sha256": digest(fixture), "inputs": "0..4096 and UINT32_MAX", "cases": cases}


def check_specialization(frontend, manifest, source, lean_command, machine, work):
    """All changed libraries pass public Core checking before specialization."""
    original = source.read_text()
    call = "finite::lookup::<image>(x)"
    if original.count(call) != 1:
        raise ValueError("expected one public lookup site in the source fixture")
    cases = [
        ("wrong-owner", original, "image"),
        ("private-function", original.replace("pub fn pick(", "fn pick("), "pick"),
        ("constant-body", original.replace(call, "Output::high"), "pick"),
        ("second-function", original + "\nfn extra(x: Input<>) -> Output<> { Output::high }\n", "pick"),
    ]
    try:
        for label, text, name in cases:
            source.write_text(text)
            receipt = work / f"{label}.json"
            receipt.write_text(capture([frontend, "check", "--manifest-path", manifest,
                                        "--print-function-revision"], cwd=work))
            output = work / f"{label}.ll"
            args = [*lean_command, HERE / "TableProbe.lean", receipt, name, machine["triple"],
                    machine["layout"], output]
            failed = subprocess.run(args, cwd=ROOT, capture_output=True, text=True)
            if failed.returncode == 0 or output.exists() or "single direct, nominal unary lookup" not in failed.stderr:
                raise ValueError(f"{label}: expected specialization rejection before bytes")
    finally:
        source.write_text(original)
    return [label for label, _, _ in cases]


def run(frontend, backend, lean, llvm, save_ir, case="unary-table"):
    lean_bin = lean / "bin/lean"
    if LEAN_COMMIT not in capture([lean_bin, "--version"]):
        raise ValueError("unexpected Lean commit")
    machine = dict(line.split("=", 1) for line in capture([backend, "describe"]).splitlines())
    if capture([llvm / "bin/llvm-config", "--version"]) != "23.1.4":
        raise ValueError("expected LLVM 23.1.4")
    comparison = emitter_comparison(lean)
    features = json.loads(capture([lean_bin, "--features"]))
    if case == "closure-unit":
        fixture = ROOT / "llvm/fixtures/ClosureUnit.vast"
        reference = HERE / "ClosureUnitComparison.lean"
        main = HERE / "ClosureUnitMain.vast"
        package, function, expected = "closure_unit", "unitAt", [1, 2]
    else:
        fixture = HERE / "TableComparison.vast"
        reference = HERE / "TableComparison.lean"
        main = HERE / "TableMain.vast"
        package, function, expected = "table_fixture", "pick", [1, 0, 1]
    with tempfile.TemporaryDirectory(prefix="vastitas-unary-table-") as temp:
        work = Path(temp)
        library = work / "library"
        library.mkdir()
        source = library / "main.vast"
        shutil.copyfile(fixture, source)
        manifest = library / "Vastitas.toml"
        manifest.write_text(f'[package]\nname = "{package}"\nversion = "0.1.0"\n'
                            'edition = "2026"\nroot = "main.vast"\n')
        receipt = work / "revision.json"
        receipt.write_text(capture([frontend, "check", "--manifest-path", manifest,
                                    "--print-function-revision"], cwd=work))
        application = work / "app"
        application.mkdir()
        harness = application / "main.vast"
        shutil.copyfile(main, harness)
        app_manifest = application / "Vastitas.toml"
        app_manifest.write_text('[package]\nname = "table_app"\nversion = "0.1.0"\n'
                                'edition = "2026"\nroot = "main.vast"\n'
                                '[dependencies]\nlib = { path = "../library" }\n')
        capture([frontend, "build", "--manifest-path", app_manifest, "-o", work / "source-main"], cwd=work)
        capture([work / "source-main"])

        module = work / "table.ll"
        lean_command = [lean / "bin/lake", "-d", ROOT / "lean-kernel", "env", "lean", "--run"]
        model = capture([*lean_command, HERE / "TableProbe.lean", receipt, function, machine["triple"],
                         machine["layout"], module], cwd=ROOT)
        preview = subprocess.run([frontend, "check", "--manifest-path", manifest, "--llvm-preview",
                                  "--target-triple", machine["triple"], "--data-layout", machine["layout"]],
                                 cwd=ROOT, stdout=subprocess.PIPE, check=True).stdout
        if preview != module.read_bytes():
            raise ValueError("public output differs from replaying the checked revision")
        ordinals = [0, 1, 2, 3, 4095, 0xFFFFFFFF]
        native, _ = native_results(work, backend, module, ordinals)
        oracle = capture([lean_bin, "--run", reference])
        if native != model or native != oracle or list(map(int, native.splitlines())) != [
                expected[i] if i < len(expected) else 0xFFFFFFFF for i in ordinals]:
            raise ValueError("unexpected table results")

        original = module.read_bytes()
        marker = b"ret i32 u0x0001"
        if marker not in original:
            raise ValueError("expected canonical result block")
        changed = work / "modified-result.ll"
        changed.write_bytes(original.replace(marker, b"ret i32 u0x0000", 1))
        check_changed_handoff(backend, module, changed, work / "changed.o")
        extra = {}
        if case == "unary-table":
            extra["boundaries"] = check_boundaries(work, backend, lean_command, machine)
            extra["specialization_rejections"] = check_specialization(
                frontend, manifest, source, lean_command, machine, work)

        if "LLVM" in features:
            bitcode = work / "reference.bc"
            emitted = subprocess.run([lean_bin, "-b", bitcode, reference], capture_output=True)
            if emitted.returncode == 0 and bitcode.is_file():
                ll = work / "reference.ll"
                dis = subprocess.run([llvm / "bin/llvm-dis", bitcode, "-o", ll], capture_output=True)
                if dis.returncode == 0 and ll.is_file():
                    comparison.update(executed=True, disassembled_sha256=digest(ll),
                                      switch_lines=sum("switch " in line for line in ll.read_text().splitlines()))
                else:
                    comparison["execution_gap"] = "bitcode disassembly failed"
            else:
                comparison["execution_gap"] = "reference bitcode emission failed"
        else:
            comparison["execution_gap"] = "pinned Lean binary reports no LLVM feature"
        if save_ir:
            with save_ir.open("xb") as dest:
                dest.write(original)
        return {"status": "passed", "target": machine, "source_sha256": digest(source),
                "source_main_sha256": digest(harness), "source_function": function,
                "checked_stages": ["compiled Core", "MidIR optimization", "MidIR execution", "LLVM module bytes"],
                "reference_sha256": digest(reference), "emitter_comparison": comparison,
                "module_bytes": len(original), "module_sha256": digest(module),
                "ordinals": ordinals, "results": list(map(int, native.splitlines())),
                "changed_result_byte": "rejected before object emission", **extra}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--frontend", type=Path, required=True)
    parser.add_argument("--backend", type=Path, required=True)
    parser.add_argument("--lean-prefix", type=Path, required=True)
    parser.add_argument("--llvm-prefix", type=Path, required=True)
    parser.add_argument("--save-ir", type=Path, help="retain the verified module at a new path")
    parser.add_argument("--case", choices=("unary-table", "closure-unit"), default="unary-table")
    args = parser.parse_args()
    print(json.dumps(run(args.frontend.resolve(), args.backend.resolve(),
                         args.lean_prefix.resolve(), args.llvm_prefix.resolve(), args.save_ir, args.case), indent=2))
