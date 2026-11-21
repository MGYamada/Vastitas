#!/usr/bin/env python3
"""Replay closed kernel proofs over an actual protocol-10 request and saved LLVM bytes."""
import argparse
import hashlib
import importlib.util
import json
import os
import re
from pathlib import Path
import shutil
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
DEFAULT_SOURCE = ROOT / "llvm/fixtures/ExitStatus.vast"
DEFAULT_LL = ROOT / "llvm/src/exit-status.ll"
TARGET_REPORT = HERE.parent / "llvm/results/macos-arm64/unary-table.json"
REDUCTION = HERE.parent / "reduction/run.py"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def load_reduction():
    spec = importlib.util.spec_from_file_location("reduction_measure", REDUCTION)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def proof_environment(prefix, *module_paths):
    # leanchecker and leanexport also look up the sysroot when started outside
    # a Lake package. Use the toolchain whose binaries run this proof.
    return {**os.environ, "LEAN_SYSROOT": str(prefix), "LEAN_NUM_THREADS": "1",
            "LEAN_PATH": os.pathsep.join(map(str, module_paths))}


def digest(data):
    return hashlib.sha256(data).hexdigest()


def lean_string(text):
    # Raw source includes line endings. Use Lean escapes and preserve the
    # distinction between a literal backslash and a control character.
    out = ['"']
    for ch in text:
        code = ord(ch)
        if 0xd800 <= code <= 0xdfff:
            raise ValueError("surrogate in a wire string")
        if code < 32 or code == 127:
            out.append(f"\\u{code:04x}")
        elif ch in ('"', '\\'):
            out.append('\\' + ch)
        else:
            out.append(ch)
    return ''.join(out) + '"'


def json_term(value):
    if value is None:
        return ".null"
    if type(value) is bool:
        return ".bool " + str(value).lower()
    if type(value) is int:
        return f"(toJson ({value} : Int))"
    if type(value) is str:
        return ".str " + lean_string(value)
    if type(value) is list:
        return ".arr #[" + ", ".join(map(json_term, value)) + "]"
    if type(value) is dict:
        return "(Json.mkObj [" + ", ".join(
            "(" + lean_string(key) + ", " + json_term(value[key]) + ")" for key in sorted(value)) + "])"
    raise ValueError(f"unsupported protocol-10 JSON type {type(value).__name__}")


def inputs(wire, target, physical, data, value):
    (package,) = wire["packages"]
    package_owner = ", ".join(lean_string(package[k]) for k in ("source", "name", "version"))
    # The wire value and all file bytes appear in the theorem environment.
    return f"""import Current
set_option autoImplicit false
namespace VastitasQualification.ExitFixture
open Lean VastitasKernel VastitasKernel.LLVM
def wire : Json := {json_term(wire)}
def sourceBytes : List UInt8 := {list(physical)}
def owner : Namespace.Owner := ⟨⟨⟨{package_owner}⟩, []⟩, "main"⟩
def target : TargetHeader :=
  ⟨⟨{lean_string(target['triple'])}.toUTF8.data.toList, by decide⟩,
   ⟨{lean_string(target['layout'])}.toUTF8.data.toList, by decide⟩⟩
def bytes : List UInt8 := {list(data)}
def value : Int := {value}
end VastitasQualification.ExitFixture
"""


OPEN = """import Inputs
open Lean VastitasKernel VastitasKernel.LLVM
open VastitasQualification.OfficialExit VastitasQualification.ExitFixture
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
"""
PROOFS = {
    "Wire": ("wireChecked", "(ResourceSource.Wire.check wire true).isOk = true", "cbv"),
    "Linked": ("linked", "Observes wire target bytes value", "apply of_validate\n  cbv"),
}


ENDPOINTS = [("Decoded", "decoded"), ("Printed", "printed"), ("Facts", "endpoints")]
STAGED = [
    ("PhysicalScan", "scannedEntry"), ("PhysicalDeclaration", "replayedDeclaration"),
    ("PhysicalReplay", "physicalEditsOfLayout"),
    ("Source", "source_and_envelope"), ("NamespaceGates", "namespace_gates"),
    ("NamespaceValidation", "declarationsFromLower"),
    ("Admission", "wire_of_parts"), ("Lexical", "wire_of_pass"),
]
DECLARATIONS = [
    ("CompatibilityLookup", "shortcut"), ("CompatibilityRows", "rowNames"),
    ("SchemeBodies", "schemeBodies"), ("SmoothBodies", "smoothBodies"),
    ("SharedBodies", "sharedBodies"), ("DeclarationFold", "bodyFold"),
    ("DeclarationPasses", "exportResolved"), ("DeclarationLowering", "loweredAndAudited"),
    ("DeclarationAcceptance", "acceptedDeclarations"),
]
AUTHORITY = [("AuthorityAssembly", "actualAssembly"), ("AuthorityPreparation", "acceptedPurePreparation")]
WIRE = [
    ("CompilerInputs", "prepared"), ("FunctionLowering", "checkedLower"),
    ("PassValidation", "passValid"), ("ModuleTyping", "moduleTyped"), ("ModuleAudit", "coreChecked"),
    ("PassAcceptance", "passes"), ("PureProgram", "actualPureProgram"), ("PublicWire", "wireAccepted"),
]
ARTIFACT = [
    ("ResourceRecord", "request_data"), ("RevisionBound", "boundedRevision"),
    ("LinkedMid", "opt"), ("SignedArtifact", "actualExit"), ("PrintedArtifact", "completeText"),
    ("PublicArtifact", "observesArtifact"),
]
STAGED_OPEN = """import Lexical
import NamespaceValidation
open Lean VastitasKernel VastitasQualification.ExitFixture VastitasQualification.ExitAdmission
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
"""
STAGED_PROOFS = {
    "LowerDeclarations": (
        "loweredHeaders", "(Indexed.Source.lower headers).isOk = true", "cbv",
    ),
    "StagedWire": (
        "wireChecked", "(ResourceSource.Wire.check wire true).isOk = true",
        "apply wire_of_pass\n  cbv",
    ),
}


def snapshot_local_imports(work, paths, retained):
    """Keep local Lean declarations stable between elaboration and official replay."""
    result = []
    inventory = hashlib.sha256()
    for index, item in enumerate(paths.split(os.pathsep)):
        original = Path(item).resolve()
        if original.is_relative_to(ROOT):
            frozen = work / "imports" / str(index)
            source = retained / str(index) if retained else original
            shutil.copytree(source, frozen)
            # Length-prefix the relative module path and hash the exact olean bytes.
            for module in sorted(frozen.rglob("*")):
                if module.is_file() and (module.name.endswith(".olean") or ".olean." in module.name and not module.name.endswith(".hash")):
                    relative = f"{index}/{module.relative_to(frozen).as_posix()}".encode()
                    inventory.update(len(relative).to_bytes(8, "big"))
                    inventory.update(relative)
                    inventory.update(hashlib.sha256(module.read_bytes()).digest())
            result.append(str(frozen))
        else:
            result.append(str(original))
    return os.pathsep.join(result), inventory.hexdigest()


def revision_source(receipt):
    def tokens(value):
        if value is None:
            return [".null"]
        if type(value) is bool:
            return [".boolean " + str(value).lower()]
        if type(value) is int:
            return [f".number ({value}) 0"]
        if type(value) is str:
            return [".string " + lean_string(value)]
        if type(value) is list:
            return [f".array {len(value)}", *(token for elem in value for token in tokens(elem))]
        if type(value) is dict:
            result = [f".object {len(value)}"]
            for name in sorted(value):
                result.append(".key " + lean_string(name))
                result.extend(tokens(value[name]))
            return result
        raise ValueError("unsupported JSON number in the signed-literal revision")
    return ("import RevisionData\n\nnamespace VastitasQualification.ExitFixture\n"
            "/-- Every token of the fixture compiler's complete public revision. -/\n"
            "def expectedRevision : List RevisionToken := [\n  " + ",\n  ".join(tokens(receipt)) +
            "]\nend VastitasQualification.ExitFixture\n")


def live_fixture(args, *, bind_revision=False):
    """Compare the installed public compiler to each value of the retained closed theorem."""
    frontend = args.frontend.resolve()
    kernel = Path(os.environ.get("VASTITAS_KERNEL", ROOT / "lean-kernel/.lake/build/bin/vastitas-kernel")).resolve()
    source = args.source.resolve()
    data = args.module.read_bytes()
    physical = source.read_bytes()
    target = json.loads(TARGET_REPORT.read_bytes())["target"]
    binaries = [digest(path.read_bytes()) for path in (frontend, kernel)]
    env = {**os.environ, "VASTITAS_KERNEL": str(kernel)}

    def invoke(options):
        return subprocess.check_output([frontend, "check", source.name, *options], cwd=source.parent, env=env)

    def unique_fields(pairs):
        values = dict(pairs)
        if len(values) != len(pairs):
            raise ValueError("duplicate field in public revision")
        return values

    receipt = json.loads(invoke(["--print-function-revision"]), object_pairs_hook=unique_fields)
    if bind_revision and revision_source(receipt).encode() != (HERE / "ExpectedRevision.lean").read_bytes():
        raise ValueError("the complete public revision differs from the closed artifact")
    def canonical(value):
        return json.dumps(value, sort_keys=True, separators=(",", ":")).encode()

    wire = receipt["input"]
    emitted = invoke(["--llvm-preview", "--target-triple", target["triple"], "--data-layout", target["layout"]])
    body = inputs(wire, target, physical, emitted, args.value).encode()
    if emitted != data:
        raise ValueError("supplied LLVM bytes differ from the public compiler output")
    if wire["root_source"] != {"offset": 0, "text": physical.decode("utf-8")}:
        raise ValueError("public wire does not retain the complete source")
    if body != (HERE / "Inputs.lean").read_bytes():
        raise ValueError("live source, wire, target, emitted bytes or claimed value differs from Inputs.lean")
    if binaries != [digest(path.read_bytes()) for path in (frontend, kernel)]:
        raise ValueError("the public compiler binaries changed during capture")
    return {
        "attempt": "live-public-comparison", "status": "passed",
        "frontend_sha256": binaries[0], "kernel_sha256": binaries[1],
        "schema": receipt["schema"], "protocol": wire["version"], "owner": wire["root"], "file": wire["file"],
        "source_sha256": digest(physical), "source_byte_length": len(physical),
        "wire_sha256": digest(canonical(wire)), "full_revision_sha256": digest(canonical(receipt)),
        "lean_input_sha256": digest(body), "emitted_sha256": digest(emitted), "byte_length": len(emitted),
        "target_triple": target["triple"], "data_layout": target["layout"],
    }


def check(args):
    measure = load_reduction().measure
    if args.timeout <= 0 or args.memory <= 0:
        raise ValueError("positive resource bounds are required")
    source, ll = args.source.resolve(), args.module.resolve()
    target = json.loads(TARGET_REPORT.read_bytes())["target"]
    lean_prefix = Path(subprocess.check_output(["lake", "-d", "lean", "env", "lean", "--print-prefix"], cwd=ROOT, text=True).strip())
    lean = lean_prefix / "bin/lean"
    paths = subprocess.check_output(["lake", "-d", "lean", "env", "printenv", "LEAN_PATH"], cwd=ROOT, text=True).strip()
    frontend = args.frontend.resolve()
    revision = subprocess.check_output([frontend, "check", source.name, "--print-function-revision"], cwd=source.parent)
    wire = json.loads(revision)["input"]
    physical = source.read_bytes()
    if (wire["version"] != 10 or wire["file"] != source.name
            or wire["root"] != "vastitas:compat:flat"
            or wire["root_source"] != {"offset": 0, "text": physical.decode("utf-8")}):
        raise ValueError("expected the protected flat input and complete original UTF-8 source")
    data = ll.read_bytes()
    body = inputs(wire, target, physical, data, args.value)
    # Preserve the complete protected flat owner from the public frontend.
    if args.save_inputs:
        args.save_inputs.write_text(body)
    else:
        retained = HERE / "Inputs.lean"
        if source == DEFAULT_SOURCE and ll == DEFAULT_LL and retained.read_text() != body:
            raise ValueError("the retained input owner, wire or LLVM bytes differ")
    with tempfile.TemporaryDirectory(prefix="vastitas-official-exit-") as tmp:
        work = Path(tmp)
        if args.declarations:
            paths, import_digest = snapshot_local_imports(work, paths, args.import_snapshot)
        env = proof_environment(lean_prefix, work, *paths.split(os.pathsep))
        shutil.copyfile(HERE / "Current.lean", work / "Current.lean")
        (work / "Inputs.lean").write_text(body)
        phases = []
        def build(name, theorem=None):
            previous = {row["phase"]: row["status"] for row in phases}
            imports = re.findall(r"^import (\S+)$", (work / (name + ".lean")).read_text(), re.MULTILINE)
            failed = [dep for dep in imports if dep in previous and previous[dep] != "passed"]
            if failed:
                phases.append({"phase": name, "status": "skipped", "missing_imports": failed})
                return False
            command = [str(lean), "-M", str(args.memory), "-DwarningAsError=true", "--root", ".", "-o", name + ".olean", name + ".lean"]
            source_sha256 = digest((work / (name + ".lean")).read_bytes())
            result = measure(command, work, env, name, args.timeout)
            result["module_source_sha256"] = source_sha256
            if result["status"] != "passed":
                log = (work / (name + ".stdout")).read_text() + (work / (name + ".stderr")).read_text()
                if result["timed_out"]:
                    result["failure_kind"] = "wall-time-limit"
                elif "excessive memory consumption" in log:
                    result["failure_kind"] = "lean-memory-limit"
                elif "unsolved goals" in log:
                    result["failure_kind"] = "unsolved-goals"
                else:
                    result["failure_kind"] = "elaboration-error"
            if theorem:
                output = (work / (name + ".stdout")).read_text()
                label = f"'{theorem}' depends on axioms: ["
                if result["status"] == "passed":
                    if f"'{theorem}' does not depend on any axioms" in output.splitlines():
                        ax = set()
                    elif label in output:
                        names = output.split(label, 1)[1].split("]", 1)[0]
                        ax = {name.strip() for name in names.split(",") if name.strip()}
                    else:
                        raise ValueError(f"missing axiom audit for {theorem}")
                    if ax - ALLOWED:
                        raise ValueError(f"unexpected axioms for {theorem}: {sorted(ax - ALLOWED)}")
                    result["axioms"] = sorted(ax)
                result["theorem"] = theorem
            if result["status"] == "passed" and not (work / (name + ".olean")).is_file():
                raise ValueError(f"Lean did not produce {name}.olean")
            phases.append(result)
            return result["status"] == "passed"
        if not build("Current") or not build("Inputs"):
            raise RuntimeError("could not compile the generic proof or concrete input declarations")
        modules = ([(name, "VastitasQualification.ExitAdmission." + theorem) for name, theorem in STAGED]
                   if args.staged else ENDPOINTS)
        if args.declarations:
            modules.extend((name, "VastitasQualification.ExitAdmission." + theorem) for name, theorem in DECLARATIONS)
        if args.authority:
            modules.extend((name, "VastitasQualification.ExitAdmission." + theorem) for name, theorem in AUTHORITY)
        proofs = STAGED_PROOFS if args.staged else PROOFS
        if args.declarations:
            proofs = {"StagedWire": STAGED_PROOFS["StagedWire"]}
        prelude = STAGED_OPEN if args.staged else OPEN
        if args.authority:
            prelude = "import AuthorityPreparation\n" + prelude
            proofs = {"PreparedWire": (
                "wireChecked", "(ResourceSource.Wire.check wire true).isOk = true",
                "apply wire_of_pass\n  unfold passReady Indexed.AuthoritySource.checkProgram\n  rw [acceptedPurePreparation]\n  cbv",
            )}
        if args.wire:
            modules.extend((name, "VastitasQualification.ExitAdmission." + theorem) for name, theorem in WIRE)
            proofs = {}
        if args.artifact:
            modules.extend((name, "VastitasQualification.ExitAdmission." + theorem) for name, theorem in ARTIFACT)
        if args.provision_fast:
            modules.extend(ENDPOINTS)
        for name, theorem in modules:
            shutil.copyfile(HERE / (name + ".lean"), work / (name + ".lean"))
            build(name, theorem)
        for name, (theorem, statement, proof) in proofs.items():
            (work / (name + ".lean")).write_text(prelude + f"theorem {theorem} : {statement} := by\n  {proof}\n#print axioms {theorem}\n")
            build(name, theorem)
        status = {row["phase"]: row["status"] for row in phases}
        # leanchecker expects an explicit module name; imports and the pinned
        # toolchain remain the environment of this experiment.
        checker = lean_prefix / "bin/leanchecker"
        for name in list(status):
            if status[name] != "passed":
                continue
            phase = "official_" + name
            result = measure([str(checker), "-v", name], work, env, phase, args.timeout)
            if result["status"] == "passed":
                logs = (work / (phase + ".stdout")).read_text() + (work / (phase + ".stderr")).read_text()
                if f"replaying {name}" not in logs.splitlines():
                    raise ValueError(f"official checker did not identify module {name}")
            else:
                result["diagnostic"] = (work / (phase + ".stderr")).read_text(errors="replace")[:1200]
            phases.append(result)
            status[phase] = result["status"]
        authority_record = None
        if args.provision_fast and all(v == "passed" for v in status.values()):
            from fast_check import provision
            authority_record = provision(work, env, lean_prefix, args.provision_fast.resolve(), args.timeout, measure)
        return {
            "attempt": "public-artifact" if args.artifact else "public-wire" if args.wire else "authority-preparation" if args.authority else "protected-declarations" if args.declarations else "decomposed-wire" if args.staged else "endpoints-and-public-emission",
            "status": "passed" if all(v == "passed" for v in status.values()) else "incomplete",
            **({"provisioned_authority": authority_record} if authority_record is not None else {}),
            **({"local_olean_snapshot_sha256": import_digest} if args.declarations else {}),
            "source_sha256": digest(physical), "source_byte_length": len(physical), "bytes_sha256": digest(data),
            "wire_sha256": digest(json.dumps(wire, sort_keys=True, separators=(",", ":")).encode()),
            "lean_input_sha256": digest(body.encode()), "byte_length": len(data),
            "target_triple": target["triple"], "data_layout": target["layout"],
            "max_seconds_per_phase": args.timeout, "lean_memory_limit_mib": args.memory,
            "lean": subprocess.check_output([lean, "--version"], text=True).strip(),
            "phases": phases,
        }


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--provision-fast", type=Path, help="after successful Official replay, provision an independent complete export reference in a new directory")
    parser.add_argument("--compare-live", action="store_true", help="compare the current public source request and emitted bytes with the retained fixture")
    parser.add_argument("--artifact", action="store_true", help="replay the exact public emission, Core and MidIR observations, and saved bytes")
    parser.add_argument("--wire", action="store_true", help="replay the closed result of public Wire.check on the exact signed-literal fixture")
    parser.add_argument("--authority", action="store_true", help="apply the concrete authority preparation to the full public wire goal")
    parser.add_argument("--declarations", action="store_true", help="replay the actual compatibility declaration lowering and its validation gates")
    parser.add_argument("--staged", action="store_true", help="check the decomposed signed-literal admission and its remaining pass")
    parser.add_argument("--import-snapshot", type=Path, help="reuse a previously frozen set of local libraries, with the same numbered slots as the Lake environment")
    parser.add_argument("--frontend", type=Path, default=ROOT / "target/debug/vastitas")
    parser.add_argument("--source", type=Path, default=DEFAULT_SOURCE)
    parser.add_argument("--module", type=Path, default=DEFAULT_LL)
    parser.add_argument("--value", type=int, default=-(2**128 + 1))
    parser.add_argument("--timeout", type=float, default=60)
    parser.add_argument("--memory", type=int, default=1536)
    parser.add_argument("--save-inputs", type=Path)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    if args.compare_live and args.provision_fast:
        parser.error("choose live comparison or authority provisioning")
    args.artifact = args.artifact or bool(args.provision_fast)
    args.wire = args.wire or args.artifact
    args.authority = args.authority or args.wire
    args.declarations = args.declarations or args.authority
    args.staged = args.staged or args.declarations
    if args.compare_live:
        report = live_fixture(args, bind_revision=True)
        recorded = HERE / "results/macos-arm64-fast-provision.json"
        if recorded.is_file():
            report["qualified_local_olean_snapshot_sha256"] = json.loads(recorded.read_text())["local_olean_snapshot_sha256"]
        report["installed_declaration_closure_replayed_by_live_capture"] = False
    else:
        report = check(args)
    output = json.dumps(report, indent=2) + "\n"
    if args.output:
        args.output.write_text(output)
    else:
        print(output, end="")
    raise SystemExit(0 if report["status"] == "passed" else 1)
