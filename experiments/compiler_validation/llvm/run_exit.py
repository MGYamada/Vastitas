#!/usr/bin/env python3
"""Qualify the public LLVM status preview, preserving the complete .ll bytes."""
import argparse
from dataclasses import dataclass
import hashlib
import json
import os
from pathlib import Path
import re
import shlex
import shutil
import subprocess
import tempfile
import time

from run import ROOT, LEAN_COMMIT, capture, digest, emitter_comparison

CORPUS_TARGET = ("arm64-apple-darwin27.2.0",
                 "e-m:o-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-n32:64-S128-Fn32")
LITERAL = -(2**128) - 1


@dataclass(frozen=True)
class Case:
    source: str
    lean_expression: str
    value: int
    operators: tuple[tuple[str, tuple[str, ...]], ...]
    package: str | None = None
    lean_prelude: str = ""


CASES = {
    "exit-status": Case("ExitStatus.vast", str(LITERAL), LITERAL, (("neg", ("Int",)),)),
    "folded-arithmetic": Case("FoldedArithmetic.vast", "Int.ediv (Int.ofNat 7) (-3) + 12", 10,
                              (("neg", ("Int",)), ("add", ("Int", "Int")), ("div", ("Nat", "Int")))),
    "assembled-bool": Case("AssembledBool.vast", "if selected true then 42 else 7", 42, (),
                           "assembled_bool", "@[noinline] def selected (b : Bool) : Bool := b\n\n"),
}


def prepare_case(work, case, source):
    if case.package is None:
        (work / case.source).write_bytes(source)
        return [case.source], None
    (work / "main.vast").write_bytes(source)
    manifest = work / "Vastitas.toml"
    manifest.write_text(f'[package]\nname = "{case.package}"\nversion = "0.1.0"\n'
                        'edition = "2026"\nroot = "main.vast"\n', encoding="utf-8")
    return ["--manifest-path", manifest], manifest


def checked_sites(receipt, case, text, manifest=None):
    wire = receipt["input"]
    if case.package is None:
        file, root, offset = case.source, "vastitas:compat:flat", 0
    else:
        file = root = str(manifest.resolve(strict=True))
        offset = manifest.stat().st_size + 1
    if (wire["file"], wire["version"], wire["root"], wire["root_source"]) != (
        file, 10, root, {"offset": offset, "text": text}
    ):
        raise ValueError("checked revision does not describe the physical fixture source")
    sites = receipt["pure"]["operator_sites"]
    for site in sites:
        identity = site["id"]
        if (site["core"], identity["module"], identity["package"]) != (
            0, ["operator"], {"source": "vastitas:compat:operators", "name": "std", "version": "2026.0.0"}
        ):
            raise ValueError("unexpected operator owner or Core function in checked revision")
    if tuple((site["id"]["name"], tuple(site["key"])) for site in sites) != case.operators:
        raise ValueError("fixture has different checked operations or argument keys")
    return sites


def checked_dispatch(receipt, case, manifest):
    root = str(manifest.resolve(strict=True))
    package = {"source": root, "name": case.package, "version": "0.1.0"}
    [source_package] = receipt["input"]["packages"]
    if (source_package["edition"] != "2026" or source_package["dependencies"] != []
            or any(source_package[k] != v for k, v in package.items())):
        raise ValueError("unexpected assembled package identity")

    def owner(name):
        return {"module": [], "name": name, "package": package}

    families = receipt["families"]
    if len(families) != 2 or {f["id"]["name"] for f in families} != {"main", "choose"}:
        raise ValueError("expected main and the assembled choose family")
    if any(f["id"] != owner(f["id"]["name"]) for f in families):
        raise ValueError("function revision has the wrong family owner")
    main = next(f["definition"] for f in families if f["id"]["name"] == "main")
    [row] = next(f["dispatch"] for f in families if f["id"]["name"] == "choose")
    selected = row["selected"]
    # The fixture's single dispatch key is the kernel's Bool classifier.
    if (row["key"], selected["ordinal"], selected["origin"]) != (
        [2], 1, {"contribution": owner("winner"), "index": 0}
    ):
        raise ValueError("expected contributed method 1 from winner on the Bool key")
    pure = receipt["pure"]
    [call] = pure["dispatch_calls"]
    target = {"definition": selected["definition"], "core": call["core"]}
    if (call != {"caller": main, "caller_targets": [], "id": owner("choose"), "key": row["key"],
                 "method": selected["ordinal"], **target}
            or pure["calls"] != [{"caller": main, "caller_targets": [], "targets": [], **target}]):
        raise ValueError("emitted call does not select the assembled method")
    symbols = pure["symbols"]
    definitions = set()
    for symbol in symbols:
        key = symbol["specialization"]
        if (not isinstance(key, dict) or set(key) != {"definition", "targets"} or key["targets"] != []
                or type(key["definition"]) is not int or key["definition"] < 0):
            raise ValueError("expected a concrete specialization for each Core symbol")
        definitions.add(key["definition"])
    if (len(symbols) != 3 or sorted(s["core"] for s in symbols) != [0, 1, 2]
            or sorted(s["id"]["name"] for s in symbols) != ["choose", "choose", "main"]
            or any(s["id"] != owner(s["id"]["name"]) for s in symbols) or len(definitions) != 3):
        raise ValueError("expected three distinct real Core symbols and specializations")
    winner = next((s for s in symbols if s["core"] == call["core"]), None)
    caller = next(s for s in symbols if s["id"] == owner("main"))
    if (winner is None or winner["id"] != owner("choose") or winner["specialization"]["definition"] != selected["definition"]
            or caller["specialization"]["definition"] != main):
        raise ValueError("Core symbol does not match the assembled call")
    # Keep portable symbol facts. The complete replayed revision includes a
    # canonical, machine-local manifest path and stays in the temporary build.
    return {"package": case.package, "edition": "2026", "family": "choose", "method": selected["ordinal"],
            "key": row["key"], "contribution": "winner", "selected_core": call["core"], "caller_core": caller["core"],
            "symbols": [{"function": s["id"]["name"], "core": s["core"], "specialization": s["specialization"]}
                        for s in symbols]}


def archive_set(config):
    paths = [Path(p) for p in shlex.split(capture([config, "--link-static", "--libfiles"]))]
    records = sorted((p.name, digest(p)) for p in paths)
    if not records:
        raise ValueError("missing expected LLVM static archives")
    manifest = json.dumps(records, separators=(",", ":")).encode()
    return {"count": len(records), "sorted_name_digest_pairs_sha256": hashlib.sha256(manifest).hexdigest()}


def dependencies(program, triple):
    if "darwin" in triple:
        lines = capture(["otool", "-L", program]).splitlines()[1:]
        names = [Path(line.strip().split(" (")[0]).name for line in lines]
    else:
        names = re.findall(r"\(NEEDED\).*?\[([^\]]+)\]", capture(["readelf", "-d", program]))
    if any(re.search("openblas|liblean|libllvm", s, re.I) for s in names):
        raise ValueError("unexpected private runtime in the pure executable")
    return names


def run(frontend, adapter, llvm, lean, cc, name="exit-status"):
    case = CASES[name]
    fixture = ROOT / "llvm/fixtures" / case.source
    corpus = ROOT / "llvm/src" / (name + ".ll")
    status = case.value % 256
    kernel = ROOT / "lean-kernel/.lake/build/bin/vastitas-kernel"
    env = dict(os.environ, VASTITAS_KERNEL=str(kernel), VASTITAS_KERNEL_ROOT=str(ROOT / "lean-kernel"))
    env["PATH"] = str(lean / "bin") + os.pathsep + env["PATH"]
    machine = dict(line.split("=", 1) for line in capture([adapter, "describe"]).splitlines())
    config = llvm / "bin/llvm-config"
    if capture([config, "--version"]) != "23.1.4" or machine["llvm"] != "23.1.4":
        raise ValueError("expected LLVM 23.1.4 in the prefix and linked adapter")
    lean_bin = lean / "bin/lean"
    if LEAN_COMMIT not in capture([lean_bin, "--version"]):
        raise ValueError("expected the pinned Lean compiler")
    target = (machine["triple"], machine["layout"])
    timings = {}

    with tempfile.TemporaryDirectory(prefix="vastitas-exit-preview-") as temporary:
        work = Path(temporary)
        source_bytes = fixture.read_bytes()
        input_args, manifest = prepare_case(work, case, source_bytes)
        def phase(name, args, status=0):
            start = time.monotonic()
            result = subprocess.run(args, env=env, cwd=work, capture_output=True)
            timings[name] = round(time.monotonic() - start, 6)
            if result.returncode != status:
                raise ValueError(f"{name}: got status {result.returncode}, expected {status}: "
                                 + result.stderr.decode(errors="replace"))
            return result.stdout

        revision = phase("capture_function_revision", [frontend, "check", *input_args, "--print-function-revision"])
        evidence = json.loads(revision)
        sites = checked_sites(evidence, case, source_bytes.decode(), manifest)
        dispatch = checked_dispatch(evidence, case, manifest) if manifest is not None else None
        receipt = work / "revision.json"
        receipt.write_bytes(revision)
        require_revision = ["--expect-function-revision", receipt]

        def check(header):
            return [frontend, "check", *input_args, *require_revision, "--llvm-preview",
                    "--target-triple", header[0], "--data-layout", header[1]]

        checked = phase("check_host_complete_bytes", check(target))
        pinned = checked if target == CORPUS_TARGET else phase("check_corpus_complete_bytes", check(CORPUS_TARGET))
        if pinned != corpus.read_bytes():
            raise ValueError("checked output differs from the retained corpus bytes")
        handoff = work / "status.ll"
        handoff.write_bytes(checked)

        # Time in-process parsing and object emission together, then the linker
        # alone, independently of the end-to-end public build measurement.
        obj = work / "status.o"
        phase("adapter_read_compare_parse_verify_emit", [adapter, "emit", handoff, handoff, obj])
        control = work / "object-control"
        phase("system_link_control", [cc, obj, "-o", control])
        program = work / "installed"
        program.write_bytes(b"previous output")
        phase("public_build_check_emit_link_install",
              [frontend, "build", *input_args, *require_revision, "--llvm-preview", "--native-cc", cc, "-o", program])
        phase("installed_program", [program], status)
        phase("control_program", [control], status)

        lean_control = work / "lean-control"
        phase("default_lean_c_build", [frontend, "build", *input_args, *require_revision, "-o", lean_control])
        phase("default_lean_c_program", [lean_control], status)
        needles = {"numeric_literal": "def emitNumLit (", "static_application": "def emitFullApp ("}
        if dispatch is not None:
            needles.update(conditional="def emitCase (", jump="def emitJmp (",
                           join_argument="emitLhsSlotStore builder p.x xv")
        comparison = emitter_comparison(lean, needles)
        if any(not observation["matched_lines"] for observation in comparison["observations"].values()):
            raise ValueError("pinned upstream emitter comparison source is incomplete")
        reference = work / "Reference.lean"
        reference.write_text(case.lean_prelude + "def main : IO UInt32 :=\n"
                             f"  pure ((({case.lean_expression} : Int) % 256).toNat.toUInt32)\n")
        phase("lean_reference_result", [lean_bin, "--run", reference], status)
        features = json.loads(capture([lean_bin, "--features"]))
        if "LLVM" in features:
            bc = work / "reference.bc"
            ref_ll = work / "reference.ll"
            emitted = subprocess.run([lean_bin, "-b", bc, reference], cwd=work, capture_output=True)
            if emitted.returncode != 0 or not bc.is_file():
                comparison["execution_gap"] = "upstream bitcode emission failed"
            elif subprocess.run([llvm / "bin/llvm-dis", bc, "-o", ref_ll], capture_output=True).returncode:
                comparison["execution_gap"] = "upstream bitcode disassembly failed"
            else:
                comparison.update(executed=True, disassembled_sha256=digest(ref_ll))
        else:
            comparison["execution_gap"] = "pinned Lean binary reports no LLVM feature"
        return {
            "status": "passed", "source": str(fixture.relative_to(ROOT)),
            "source_sha256": digest(fixture), "source_value": str(case.value),
            "replayed_revision_sha256": digest(receipt), "checked_operator_sites": sites,
            **({"checked_dispatch": dispatch, "root_source_offset": evidence["input"]["root_source"]["offset"],
                "lean_reference_prelude": case.lean_prelude.strip()} if dispatch is not None else {}),
            "default_lean_c_exit_code": status, "lean_reference_expression": case.lean_expression,
            "modeled_mod_256": status, "native_exit_code": status, "lean_reference_exit_code": status,
            "target": machine, "abi": "i32 main()", "cpu": "generic", "features": "",
            "optimization": "none", "relocation": "PIC", "runtime_inputs": "system startup and C runtime",
            "llvm_sys": "231.0.1", "llvm_link": "static", "llvm_config_sha256": digest(config),
            "llvm_prefix_static_archives": archive_set(config),
            "installed_dynamic_libraries": dependencies(program, machine["triple"]),
            "compiler_sha256": digest(frontend), "adapter_sha256": digest(adapter),
            "adapter_source_sha256": digest(ROOT / "src/driver/llvm_backend.rs"),
            "cargo_lock_sha256": digest(ROOT / "Cargo.lock"), "kernel_sha256": digest(kernel),
            "link_driver": {"name": cc.name, "sha256": digest(cc),
                            "version": capture([cc, "--version"]).splitlines()[0]},
            "host_llvm_bytes": len(checked), "host_llvm_sha256": hashlib.sha256(checked).hexdigest(),
            "corpus_target_equals_host": target == CORPUS_TARGET,
            "corpus_compared_byte_for_byte": str(corpus.relative_to(ROOT)),
            "corpus_sha256": digest(corpus), "object_bytes": obj.stat().st_size,
            "executable_bytes": program.stat().st_size, "emitter_comparison": comparison,
            "wall_seconds_single_invocation": timings,
        }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--frontend", type=Path, required=True)
    parser.add_argument("--case", choices=CASES, default="exit-status")
    parser.add_argument("--backend", type=Path, required=True)
    parser.add_argument("--llvm-prefix", type=Path, required=True)
    parser.add_argument("--lean-prefix", type=Path, required=True)
    parser.add_argument("--cc", default="cc", help="host linker driver")
    args = parser.parse_args()
    cc = shutil.which(args.cc)
    if cc is None:
        parser.error("host linker driver unavailable")
    report = run(args.frontend.resolve(), args.backend.resolve(), args.llvm_prefix.resolve(),
                 args.lean_prefix.resolve(), Path(cc).absolute(), args.case)
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
