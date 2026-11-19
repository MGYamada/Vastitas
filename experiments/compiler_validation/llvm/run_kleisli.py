#!/usr/bin/env python3
"""Qualify the complete optional Kleisli package on the pinned host toolchain."""
import argparse
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile
import time

from run import HERE, ROOT, LEAN_COMMIT, capture, digest
from run_call import compare_emitter
from run_exit import dependencies
from run_table import check_changed_handoff


FIXTURE = ROOT / "examples/packages/finite-kleisli"
SOURCE = FIXTURE / "src/main.vast"
MANIFEST = FIXTURE / "Vastitas.toml"
REFERENCE = HERE / "KleisliComparison.lean"


def phases(work, env):
    times = {}

    def run(name, args, status=0):
        start = time.monotonic()
        result = subprocess.run(args, cwd=work, env=env, capture_output=True)
        times[name] = round(time.monotonic() - start, 6)
        if result.returncode != status:
            raise ValueError(f"{name} exited {result.returncode}, expected {status}: "
                             + result.stderr.decode(errors="replace"))
        return result.stdout

    return times, run


def once(text, old, new):
    if text.count(old) != 1:
        raise ValueError(f"expected one occurrence of {old!r}")
    return text.replace(old, new, 1)


def changes(original):
    # Mutate concrete instruction operands, without depending on source/core symbol numbering.
    phi = re.search(rb"^  %\w+ = phi i32 \[ %\w+ , (%\w+) \] , \[ %\w+ , (%\w+) \]$", original, re.M)
    branch = re.search(rb"^  br i1 %v\w+ , label (%b\d+) , label (%b\d+)$", original, re.M)
    comparison = re.search(rb"^  %v\w+ = icmp eq i32 [^\n]+$", original, re.M)
    if not phi or not branch or not comparison:
        raise ValueError("expected the entry comparison, conditional branch, and exit phi")
    return {
        "truncated": ("rejected", original[:-1]),
        "duplicate-phi-predecessor": ("rejected", once(original, phi[0], phi[0].replace(phi[2], phi[1]))),
        "comparison-reversed": ("different", once(original, comparison[0], comparison[0].replace(b" eq ", b" ne "))),
        "branch-reversed": ("different", once(original, branch[0], branch[0][:branch.start(1)-branch.start()]
            + branch[2] + b" , label " + branch[1])),
    }


def source_variant(work, text):
    # Keep manifests and checked authorities intact. Only the root body changes.
    pkg = work / "examples/packages/finite-kleisli"
    (pkg / "src").mkdir(parents=True)
    shutil.copyfile(MANIFEST, pkg / "Vastitas.toml")
    for dep in ("stdlib", "monad"):
        (work / dep).symlink_to(ROOT / dep, target_is_directory=True)
    path = pkg / "src/main.vast"
    path.write_bytes(text)
    return pkg / "Vastitas.toml", path


def extended_source(original):
    text = once(original, b"    let lifted =", b"""    let extended = monad::kleisli::extend::<Triple, Obj::lo, Obj::hi>(C::up);
    let lifted =""")
    return once(text, b"mappedUp(C::up) == C::rightId { 0 }",
                b"mappedUp(C::up) == C::rightId && extended == C::rightId { 42 }")


def extension_evidence(module, linkage):
    focused = linkage["focused_function"]
    owner, symbol, ops = focused["owner"], focused["local_symbol"], focused["operations"]
    if (owner["package"], owner["module"], owner["name"]) != ("vastitas_monad", ["kleisli"], "extend"):
        raise ValueError("extension is not the selected optional package function")
    [selection] = [r for r in linkage["retained"] if r["local_symbol"] == symbol]
    indices = selection["indices"]
    if (indices[0]["monad"]["name"], [i["object"] for i in indices[1:]]) != ("M", ["lo", "hi"]):
        raise ValueError("the triple did not specialize to M, lo, hi")
    edges = next(row["callees"] for row in linkage["calls"] if row["caller"] == linkage["local_entry"])
    if symbol not in edges:
        raise ValueError("entry does not call the checked extension")
    if [op["opcode"] for op in ops] != ["finite.ordinal.v1", "finite.lookup.ordinal.v1", "finite.lookup.ordinal.v1"]:
        raise ValueError("extension did not retain the multiplication component, action and composition")
    component, action, composition = ops
    sites = [(op["table"]["name"], op["authority"]["name"], op["operands"]) for op in (action, composition)]
    if component["operands"] or sites != [("closeArr", "M", [[0, 0]]), ("comp", "C", [[0, 1], [0, 2]])]:
        raise ValueError("extension uses different maps or operand order")
    source = module.read_text("ascii")
    action_fn, compose_fn = f"t{symbol}_0_2", f"t{symbol}_0_3"
    body = f"""define internal i32 @f{symbol} ( i32 %v0_0 ) {{
b0:
  %v0_1 = add i32 0 , 0
  %v0_2 = call i32 @{action_fn} ( i32 %v0_0 )
  %v0_3 = call i32 @{compose_fn} ( i32 %v0_1 , i32 %v0_2 )
  ret i32 %v0_3
}}"""
    if source.count(body) != 1:
        raise ValueError("actual LLVM calls do not implement the checked MidIR extension")
    for name in (action_fn, compose_fn):
        helper = re.search(rf"^define internal i32 @{name} \([^{{]+\) \{{\n(.*?)^\}}$", source, re.M | re.S)
        if not helper or "switch i32" not in helper[1] or "ret i32 4294967295" not in helper[1]:
            raise ValueError("missing finite-table helper or miss sentinel")
    return {"specialization": selection, "function": focused, "entry_calls": edges,
            "action_helper": action_fn, "composition_helper": compose_fn, "llvm_body": body.splitlines()}


def emitter(lean, llvm, work):
    comparison = compare_emitter(lean, llvm, work, REFERENCE)
    source = (lean / comparison["source"]).read_text().splitlines()
    for key, needle in {"conditional": "def emitCase (", "jump": "def emitJmp (",
                        "static_argument_load": "let yv ← LLVM.buildLoad2 builder yty yslot",
                        "static_result_store": "LLVM.buildStore builder zv zslot",
                        "case_switch": "LLVM.buildSwitch builder tag defaultBB",
                        "join": "def emitJDecl (", "join_argument_store": "emitLhsSlotStore builder p.x xv"}.items():
        lines = [i for i, line in enumerate(source, 1) if needle in line]
        if not lines:
            raise ValueError(f"missing pinned upstream {key}")
        comparison["observations"][key] = {"needle": needle, "matched_lines": lines}
    comparison["features"] = json.loads(capture([lean / "bin/lean", "--features"]))
    if comparison["executed"]:
        llvm_ir = (work / "reference.ll").read_text()
        comparison["disassembled_instructions"] = {
            k: len(re.findall(pattern, llvm_ir, re.M)) for k, pattern in {
                "direct_calls": r"\bcall\b[^\n]*@", "switches": r"\bswitch i\d+",
                "conditional_branches": r"\bbr i1 ", "phi": r" = phi ",
            }.items()
        }
    return comparison


def qualify(frontend, backend, lean, llvm, cc):
    lean_version = capture([lean / "bin/lean", "--version"])
    machine = dict(s.split("=", 1) for s in capture([backend, "describe"]).splitlines())
    if LEAN_COMMIT not in lean_version or machine["llvm"] != "23.1.4" or capture([
            llvm / "bin/llvm-config", "--version"]) != machine["llvm"]:
        raise ValueError("expected the pinned Lean commit and LLVM library/prefix")
    env = dict(os.environ, VASTITAS_KERNEL=str(ROOT / "lean-kernel/.lake/build/bin/vastitas-kernel"),
               VASTITAS_KERNEL_ROOT=str(ROOT / "lean-kernel"))
    env["PATH"] = str(lean / "bin") + os.pathsep + env["PATH"]
    target = ["--target-triple", machine["triple"], "--data-layout", machine["layout"]]
    with tempfile.TemporaryDirectory(prefix="vastitas-kleisli-") as tmp:
        work = Path(tmp)
        timings, run = phases(work, env)
        def build_case(name, manifest, status, focus=None):
            flags = ["--manifest-path", manifest]
            receipt = work / f"{name}-revision.json"
            revision = run(f"{name}_revision", [frontend, "check", *flags, "--print-function-revision"])
            receipt.write_bytes(revision)
            expect = [*flags, "--expect-function-revision", receipt]
            module = work / f"{name}.ll"
            module.write_bytes(run(f"{name}_check", [frontend, "check", *expect, "--llvm-preview", *target]))
            native, lean_c = work / name, work / f"{name}-lean-c"
            run(f"{name}_public_native_build", [frontend, "build", *expect, "--llvm-preview",
                                                "--native-cc", cc, "-o", native])
            run(f"{name}_public_native_execute", [native], status)
            run(f"{name}_lean_c_build", [frontend, "build", *expect, "-o", lean_c])
            run(f"{name}_lean_c_execute", [lean_c], status)
            linkage = json.loads(run(f"{name}_source_revision_midir_bytes", [
                lean/"bin/lake", "-d", ROOT/"lean-kernel", "env", "lean", "--run",
                HERE/"KleisliPackageProbe.lean", receipt, manifest.parent/"src/main.vast", module,
                *([focus] if focus else [])]))
            if linkage["core_and_midir_integer"] != status or linkage["modeled_exit"] != status:
                raise ValueError("the checked entry observations differ from the expected closure result")
            return module, native, linkage

        module, native, linkage = build_case("original", MANIFEST, 0)
        source = SOURCE.read_bytes()
        alt_manifest, alt_source = source_variant(work/"alternate-tree", once(source, b"if u == C::up", b"if u != C::up"))
        alt, _, _ = build_case("alternate", alt_manifest, 1)
        ext_manifest, ext_source = source_variant(work/"extended-tree", extended_source(source))
        extension, _, ext_linkage = build_case("extension", ext_manifest, 42, "extend")
        ext_evidence = extension_evidence(extension, ext_linkage)
        original = module.read_bytes()
        if original == alt.read_bytes():
            raise ValueError("different source comparisons yielded identical modules")
        instructions = {name: len(re.findall(pattern, original, re.M)) for name, pattern in {
            "specializations": rb"^define internal i(?:1|32) @f\d+ ",
            "lookup_helpers": rb"^define internal i32 @t\d+_\d+_\d+ ",
            "calls_to_specializations_including_main_wrapper": rb" = call i(?:1|32) @f\d+ ",
            "lookup_calls": rb" = call i32 @t",
            "equality": rb" = icmp eq ", "and_including_table_guards": rb" = and i1 ", "phi": rb" = phi ",
            "switches": rb"^  switch ", "branches": rb"^  br i1 ",
        }.items()}
        if instructions["specializations"] != 6 or not all(instructions.values()):
            raise ValueError("package lowered without its complete call and control-flow structure")
        # Additional host control exercises the exact same shared in-process adapter.
        handoff, obj, exe = work/"handoff.ll", work/"original.o", work/"control"
        shutil.copyfile(module, handoff)
        run("adapter_read_compare_parse_verify_object", [backend, "emit", module, handoff, obj])
        run("host_link", [cc, obj, "-o", exe])
        run("host_execute", [exe])
        ext_copy, ext_obj, ext_exe = work/"extension-handoff.ll", work/"extension.o", work/"extension-control"
        shutil.copyfile(extension, ext_copy)
        run("extension_adapter_object", [backend, "emit", extension, ext_copy, ext_obj])
        run("extension_control_link", [cc, ext_obj, "-o", ext_exe])
        run("extension_control_execute", [ext_exe], 42)
        probe = [lean/"bin/lake", "-d", ROOT/"lean-kernel", "env", "lean", "--run", HERE/"KleisliProbe.lean", module]
        mutations = {}
        for name, (kind, data) in changes(original).items():
            modified = work / (name + ".ll")
            modified.write_bytes(data)
            check_changed_handoff(backend, module, modified, work/(name + "-rejected.o"))
            probe.extend([kind, modified])
            mutations[name] = {"canonical_model": kind, "original_handoff": "rejected"}
            if kind == "different":
                changed_obj, changed_exe = work/(name + ".o"), work/name
                run(name + "_control_object", [backend, "emit", modified, modified, changed_obj])
                run(name + "_control_link", [cc, changed_obj, "-o", changed_exe])
                run(name + "_control_execute", [changed_exe], 1)
                mutations[name]["independent_host_control_status"] = 1
        probe.extend(["different", alt])
        run("lean_model_bytes_and_mutations", probe)
        run("independent_closure_reference", [lean/"bin/lean", "--run", REFERENCE])
        run("independent_extension_reference", [lean/"bin/lean", "--run", REFERENCE, "extend"], 42)
        return {"status": "passed", "target": machine, "llvm_sys": "231.0.1", "lean_commit": LEAN_COMMIT,
                "source": str(SOURCE.relative_to(ROOT)), "source_sha256": digest(SOURCE),
                "kleisli_library_sha256": digest(ROOT/"monad/src/kleisli/mod.vast"),
                "complete_llvm": {"bytes": len(original), "sha256": digest(module), "instructions": instructions},
                "object_bytes": obj.stat().st_size, "dependencies": dependencies(native, machine["triple"]),
                "source_linkage": linkage,
                "original": {"expected": 0, "model": 0, "lean_c": 0, "public_native": 0, "host_control": 0},
                "alternate": {"source_change": "u != C::up", "source_sha256": digest(alt_source),
                              "llvm_sha256": digest(alt), "model": 1, "lean_c": 1, "public_native": 1},
                "extension": {"source_call": "monad::kleisli::extend::<Triple, Obj::lo, Obj::hi>(C::up)",
                              "source_sha256": digest(ext_source), "llvm_sha256": digest(extension),
                              "llvm_bytes": extension.stat().st_size, "object_bytes": ext_obj.stat().st_size,
                              "model": ext_linkage["modeled_exit"], "core_and_midir_integer": ext_linkage["core_and_midir_integer"],
                              "lean_c": 42, "public_native": 42, "host_control": 42, "lean_reference": 42,
                              **ext_evidence},
                "mutations": mutations, "reference_sha256": digest(REFERENCE),
                "emitter_comparison": emitter(lean, llvm, work), "seconds": timings}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    for flag in ("--frontend", "--backend", "--lean-prefix", "--llvm-prefix"):
        parser.add_argument(flag, type=Path, required=True)
    parser.add_argument("--cc", default="cc")
    args = parser.parse_args()
    print(json.dumps(qualify(args.frontend.resolve(), args.backend.resolve(), args.lean_prefix.resolve(),
                             args.llvm_prefix.resolve(), args.cc), indent=2))
