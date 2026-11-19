#!/usr/bin/env python3
"""Qualify an actual two-function checked Core library and its complete LLVM bytes."""
import argparse
import json
from pathlib import Path
import subprocess
import tempfile

from run import HERE, ROOT, LEAN_COMMIT, capture, digest, emitter_comparison
from run_table import check_changed_handoff, native_results


def compare_emitter(lean, llvm, work, reference):
    result = emitter_comparison(lean)
    lines = (lean / result["source"]).read_text().splitlines()
    for name, needle in [("static_application", "def emitFullApp"), ("static_call", "buildCall2")]:
        result["observations"][name] = {"needle": needle, "matched_lines": [
            i for i, text in enumerate(lines, 1) if needle in text and
            (name == "static_application" or "(← getFunIdTy f) fv ys" in text)]}
        if not result["observations"][name]["matched_lines"]:
            raise ValueError(f"missing pinned emitter comparison point {name}")
    if "LLVM" not in json.loads(capture([lean / "bin/lean", "--features"])):
        result["execution_gap"] = "pinned Lean binary reports no LLVM feature"
    else:
        bc, ll = work / "reference.bc", work / "reference.ll"
        emission = subprocess.run([lean / "bin/lean", "-b", bc, reference], capture_output=True)
        if emission.returncode == 0 and bc.is_file():
            dis = subprocess.run([llvm / "bin/llvm-dis", bc, "-o", ll], capture_output=True)
            if dis.returncode == 0 and ll.is_file():
                result.update(executed=True, disassembled_sha256=digest(ll),
                              call_instructions=sum(" call " in line for line in ll.read_text().splitlines()))
            else:
                result["execution_gap"] = "reference bitcode disassembly failed"
        else:
            result["execution_gap"] = "reference bitcode emission failed"
    return result


def run(frontend, backend, lean, llvm, save_ir):
    if (LEAN_COMMIT not in capture([lean / "bin/lean", "--version"]) or
            capture([llvm / "bin/llvm-config", "--version"]) != "23.1.4"):
        raise ValueError("unexpected Lean or LLVM version")
    machine = dict(line.split("=", 1) for line in capture([backend, "describe"]).splitlines())
    if machine.get("llvm") != "23.1.4":
        raise ValueError("unexpected libLLVM version")
    lean_cmd = [lean / "bin/lake", "-d", ROOT / "lean-kernel", "env", "lean", "--run", HERE / "CallProbe.lean"]
    original = (HERE / "CallComparison.vast").read_text()
    ordinals = [0, 1, 2, 3, 4095, 0xFFFFFFFF]
    expected = [1, 0, 1, 0xFFFFFFFF, 0xFFFFFFFF, 0xFFFFFFFF]
    reference = HERE / "CallComparison.lean"
    with tempfile.TemporaryDirectory(prefix="vastitas-call-") as tmp:
        work = Path(tmp)
        package = work / "library"
        package.mkdir()
        source = package / "main.vast"
        source.write_text(original)
        manifest = package / "Vastitas.toml"
        manifest.write_text('[package]\nname = "call_fixture"\nversion = "0.1.0"\n'
                            'edition = "2026"\nroot = "main.vast"\n')
        def receipt(name):
            out = work / f"{name}.json"
            out.write_text(capture([frontend, "check", "--manifest-path", manifest, "--print-function-revision"], cwd=work))
            return out

        def probe(revision, callee, caller, output):
            return [*lean_cmd, revision, callee, caller, machine["triple"], machine["layout"], output]

        library = work / "library.ll"
        model = capture(probe(receipt("actual"), "pick", "forward", library), cwd=ROOT)
        if list(map(int, model.splitlines())) != expected or capture([lean / "bin/lean", "--run", reference]) != model:
            raise ValueError("unexpected modeled or Lean reference observations")
        app = work / "app"
        app.mkdir()
        harness = (HERE / "TableMain.vast").read_text().replace("pick", "forward")
        (app / "main.vast").write_text(harness)
        app_manifest = app / "Vastitas.toml"
        app_manifest.write_text('[package]\nname = "call_app"\nversion = "0.1.0"\n'
                                'edition = "2026"\nroot = "main.vast"\n[dependencies]\nlib = { path = "../library" }\n')
        capture([frontend, "build", "--manifest-path", app_manifest, "-o", work / "main"], cwd=work)
        capture([work / "main"])
        for sym in ("vq_lookup", "vq_forward"):
            directory = work / sym
            directory.mkdir()
            native, _ = native_results(directory, backend, library, ordinals, symbol=sym)
            if native != model:
                raise ValueError(f"unexpected native results through {sym}")
        negatives = [
            ("reversed-export-owners", original, "forward", "pick"),
            ("private-callee", original.replace("pub fn pick", "fn pick"), "pick", "forward"),
            ("different-operand", original.replace("{ pick(x) }", "{ pick(Input::first) }"), "pick", "forward"),
            ("different-caller-abi", original.replace("forward(x: Input<>", "forward(x: Output<>")
             .replace("{ pick(x) }", "{ pick(Input::first) }"), "pick", "forward"),
            ("bypassed-callee", original.replace("{ pick(x) }", "{ finite::lookup::<image>(x) }"), "pick", "forward"),
        ]
        for label, changed, callee, caller in negatives:
            source.write_text(changed)
            out = work / f"{label}.ll"
            attempt = subprocess.run(probe(receipt(label), callee, caller, out), cwd=ROOT, capture_output=True, text=True)
            if attempt.returncode == 0 or out.exists() or "two-function call specialization rejected" not in attempt.stderr:
                raise ValueError(f"unexpected accepted-source specialization result for {label}")
        data = library.read_bytes()
        head, lookup, forward = data.partition(b"define i32 @vq_lookup")
        first, marker, second = forward.partition(b"\ndefine i32 @vq_forward")
        if not lookup or not marker:
            raise ValueError("missing modeled functions")
        edits = {
            "redirect-to-caller": data.replace(b"call i32 @vq_lookup", b"call i32 @vq_forward"),
            "constant-operand": data.replace(b"call i32 @vq_lookup(i32 %tag)", b"call i32 @vq_lookup(i32 0)"),
            "wrong-return-abi": data.replace(b"define i32 @vq_forward", b"define i64 @vq_forward"),
            "changed-definition-order": head + marker + second + lookup + first,
            "trailing-bytes": data + b"\n",
        }
        rejected = []
        for name, buf in edits.items():
            changed = work / f"{name}.ll"
            if data == buf:
                raise ValueError(f"ineffective mutation {name}")
            changed.write_bytes(buf)
            check_changed_handoff(backend, library, changed, work / f"{name}.o")
            rejected.append(changed)
        capture([*lean_cmd, "reject", *rejected], cwd=ROOT)
        comparison = compare_emitter(lean, llvm, work, reference)
        if save_ir:
            with save_ir.open("xb") as out:
                out.write(data)
        return {"status": "passed", "target": machine, "source_sha256": digest(HERE / "CallComparison.vast"),
                "reference_sha256": digest(reference), "source_call": ["forward", "pick"],
                "foreign_call": ["vq_forward", "vq_lookup"], "module_sha256": digest(library),
                "module_bytes": len(data), "ordinals_each_export": ordinals, "results_each_export": expected,
                "specialization_rejections": [n[0] for n in negatives],
                "parser_and_handoff_rejections": list(edits), "emitter_comparison": comparison}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--frontend", type=Path, required=True)
    parser.add_argument("--backend", type=Path, required=True)
    parser.add_argument("--lean-prefix", type=Path, required=True)
    parser.add_argument("--llvm-prefix", type=Path, required=True)
    parser.add_argument("--save-ir", type=Path)
    args = parser.parse_args()
    print(json.dumps(run(args.frontend.resolve(), args.backend.resolve(),
                         args.lean_prefix.resolve(), args.llvm_prefix.resolve(), args.save_ir), indent=2))
