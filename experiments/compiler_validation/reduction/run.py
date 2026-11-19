#!/usr/bin/env python3
"""Measure an isolated, kernel-reduced SSA lowering validation workload.

No production compiler acceptance or Fast/Official admission is established by
this experiment. Measurements bind generated source and the export bytes; the
exported axiom environment is inspected, not authenticated as a compiler bundle.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import shutil
import signal
import subprocess
import sys
import tempfile
import time


ROOT = Path(__file__).resolve().parents[3]
HERE = Path(__file__).resolve().parent
PIN = "leanprover/lean4:v4.35.0"
LEAN_COMMIT = "eb6cafb7290e8bd5f2937522d8d804f58f02bafc"
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
RECORD_KINDS = {"meta", "in", "il", "ie", "axiom", "def", "thm", "opaque", "quot", "inductive"}


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def operations(count: int) -> tuple[list[str], list[str]]:
    """Produce two separately serialized artifacts with backward SSA references."""
    if count < 4:
        raise ValueError("at least four operations are required")
    source = [".literal 42", ".literal 7"]
    target = [".constant 42", ".constant 7"]
    latest = 1
    for index in range(2, count):
        phase = (index - 2) % 4
        if phase == 0 and index + 1 < count:
            source.append(f".eq {latest} 0")
            target.append(f".call .natEq {latest} 0")
        elif phase == 1:
            source.append(f".select {index - 1} {latest} 0")
            target.append(f".select {index - 1} {latest} 0")
            latest = index
        else:
            op, call = ("add", "natAdd") if phase != 3 else ("mul", "natMul")
            source.append(f".{op} {latest} 1")
            target.append(f".call .{call} {latest} 1")
            latest = index
    return source, target


def fixture(count: int, chunk_size: int, proof: str) -> tuple[str, list[str]]:
    if count < 4 or chunk_size < 4 or proof not in {"decide", "rfl"}:
        raise ValueError("invalid workload or proof method")
    sizes = [chunk_size] * (count // chunk_size)
    if rest := count % chunk_size:
        if sizes and rest < 4:
            sizes[-1] += rest
        else:
            sizes.append(rest)
    if not sizes:
        sizes = [count]
    if min(sizes) < 4:
        raise ValueError("each chunk needs at least four operations")
    lines = [
        "import Model", "set_option maxRecDepth 200000",
        "set_option maxHeartbeats 8000000", "namespace ReductionFixture",
        "open ReductionSpike",
    ]
    targets: list[str] = []
    for index, size in enumerate(sizes):
        source, target = operations(size)
        for name, ty, values in (
            ("source", "SourceOp", source), ("target", "TargetOp", target),
            ("witness", "Nat", [str(i) for i in range(size)]),
        ):
            lines.append(f"def {name}{index} : List {ty} := [\n  " + ",\n  ".join(values) + "\n]")
        lines += [
            f"theorem accepted{index} : validate source{index} target{index} witness{index} = true := by {proof}",
            f"theorem refined{index} : executeTarget target{index} [] = executeSource source{index} [] :=",
            f"  accepted_refines source{index} target{index} witness{index} accepted{index}",
            f"theorem changedCall{index} : validate source{index}",
            f"    (target{index}.set {size - 1} (.constant 0)) witness{index} = false := by {proof}",
            f"theorem changedWitness{index} : validate source{index} target{index}",
            f"    (witness{index}.set {size - 1} 0) = false := by {proof}",
        ]
        targets.extend(f"ReductionFixture.{name}{index}" for name in
                       ("accepted", "refined", "changedCall", "changedWitness"))
    lines += [
        "theorem forwardReference : validate [.literal 0, .add 2 0]",
        "    [.constant 0, .call .natAdd 2 0] [0, 1] = false := by decide",
        "theorem wrongOperandType : validate [.literal 0, .eq 0 0, .add 1 0]",
        "    [.constant 0, .call .natEq 0 0, .call .natAdd 1 0] [0, 1, 2] = false := by decide",
        "end ReductionFixture",
    ]
    targets += ["ReductionFixture.forwardReference", "ReductionFixture.wrongOperandType"]
    return "\n".join(lines) + "\n", targets


def inspect_export(path: Path, targets: list[str]) -> dict:
    """Require the pinned format and every requested theorem, including negatives.

    nanoda checks referenced expressions/declarations. This structural precheck
    additionally prevents an empty or truncated-but-valid subset from counting
    as the requested workload. It does not authenticate the standard axioms.
    """
    names = {0: ""}
    declarations: dict[str, str] = {}
    axioms: list[str] = []
    metadata = None
    record_count = 0
    with path.open(encoding="utf-8") as stream:
        for line_number, line in enumerate(stream, 1):
            record_count += 1
            if not line.endswith("\n"):
                raise ValueError("export has an unterminated record")
            entry = json.loads(line)
            if not isinstance(entry, dict):
                raise ValueError("export record is not an object")
            if len(RECORD_KINDS.intersection(entry)) != 1:
                raise ValueError("unknown or ambiguous export record kind")
            if "meta" in entry:
                if metadata is not None or line_number != 1:
                    raise ValueError("export metadata is missing, repeated or displaced")
                metadata = entry["meta"]
            if "in" in entry:
                name_id = entry["in"]
                if name_id in names:
                    raise ValueError("duplicate exported name ID")
                node = entry.get("str", entry.get("num"))
                if not isinstance(node, dict) or node.get("pre") not in names:
                    raise ValueError("malformed exported name")
                parent = names[node["pre"]]
                component = node.get("str", node.get("i"))
                if isinstance(component, str) and "." in component:
                    raise ValueError("ambiguous dotted name component")
                names[name_id] = f"{parent}.{component}" if parent else str(component)
            nodes = []
            for kind in ("axiom", "def", "thm", "opaque", "quot"):
                node = entry.get(kind)
                if node is not None:
                    nodes.append((kind, node))
            if "inductive" in entry:
                block = entry["inductive"]
                if not isinstance(block, dict) or set(block) != {"types", "ctors", "recs"}:
                    raise ValueError("malformed inductive block")
                for kind in ("types", "ctors", "recs"):
                    if not isinstance(block[kind], list):
                        raise ValueError("malformed inductive declarations")
                    nodes.extend((kind, node) for node in block[kind])
            for kind, node in nodes:
                if not isinstance(node, dict) or "name" not in node:
                    raise ValueError("malformed declaration")
                if node.get("isUnsafe", False) or node.get("safety", "safe") != "safe":
                    raise ValueError("unsafe or partial declaration")
                if kind == "thm" and not {"type", "value"}.issubset(node):
                    raise ValueError("theorem missing its type or proof")
                name = names.get(node["name"])
                if name is None or name in declarations:
                    raise ValueError("missing or repeated declaration name")
                declarations[name] = kind
                if kind == "axiom":
                    axioms.append(name)
    if metadata != {
        "exporter": {"name": "lean4export", "version": "3.1.0"},
        "format": {"version": "3.1.0"},
        "lean": {"githash": LEAN_COMMIT, "version": "4.35.0"},
    }:
        raise ValueError("export metadata does not match the pinned Lean/exporter")
    missing = sorted(target for target in targets if declarations.get(target) != "thm")
    if missing:
        raise ValueError("missing requested theorem(s): " + ", ".join(missing))
    unexpected = sorted(set(axioms) - ALLOWED_AXIOMS)
    if unexpected:
        raise ValueError("unapproved axiom(s): " + ", ".join(unexpected))
    return {"sha256": digest(path), "bytes": path.stat().st_size,
            "records": record_count, "declarations": len(declarations),
            "target_theorems": targets, "axioms": sorted(axioms),
            "axiom_environment_authenticated": False}


def checked_count(output: str, errors: str, expected: int) -> int | None:
    match = re.fullmatch(r"Checked ([1-9][0-9]*) declarations with no errors\n", output)
    if match is None or errors.strip() or int(match.group(1)) != expected:
        return None
    return int(match.group(1))


def measure(command: list[str], cwd: Path, env: dict[str, str], name: str,
            timeout: float, stdout: Path | None = None, *, run_from: Path | None = None) -> dict:
    """wait4 measures this child, without platform timer/sandbox side effects."""
    output_path = stdout or cwd / f"{name}.stdout"
    error_path = cwd / f"{name}.stderr"
    started = time.monotonic()
    timed_out = False
    with output_path.open("wb") as output, error_path.open("wb") as error:
        child = subprocess.Popen(command, cwd=run_from or cwd, env=env, stdout=output, stderr=error,
                                 start_new_session=True)
        try:
            while True:
                pid, status, usage = os.wait4(child.pid, os.WNOHANG)
                if pid:
                    break
                if time.monotonic() - started >= timeout:
                    timed_out = True
                    os.killpg(child.pid, signal.SIGKILL)
                    _, status, usage = os.wait4(child.pid, 0)
                    break
                time.sleep(0.02)
        except BaseException:
            os.killpg(child.pid, signal.SIGKILL)
            _, status, _ = os.wait4(child.pid, 0)
            child.returncode = os.waitstatus_to_exitcode(status)
            raise
        child.returncode = os.waitstatus_to_exitcode(status)
    result = {
        "phase": name, "exit_code": child.returncode, "timed_out": timed_out,
        "wall_seconds": time.monotonic() - started,
        "user_seconds": usage.ru_utime, "system_seconds": usage.ru_stime,
        "peak_rss_bytes": usage.ru_maxrss * (1 if platform.system() == "Darwin" else 1024),
        "peak_rss_scope": "wait4 maximum resident set; not summed concurrent process memory",
    }
    # Logs stay temporary. The portable report contains no paths or user names.
    if child.returncode:
        result["status"] = "failed"
    else:
        result["status"] = "passed"
    return result


def toolchain() -> Path:
    if (ROOT / "lean-toolchain").read_text().strip() != PIN:
        raise ValueError("update the reviewed experiment pin with the repository toolchain")
    found = subprocess.run(["lean", "--print-prefix"], cwd=ROOT, capture_output=True, text=True, check=True)
    prefix = Path(found.stdout.strip()).resolve()
    version = subprocess.run([str(prefix / "bin/lean"), "--version"], capture_output=True,
                             text=True, check=True).stdout
    if "version 4.35.0" not in version or LEAN_COMMIT not in version:
        raise ValueError("Lean version/commit does not match the experiment pin")
    for executable in ("lean", "lake", "leanexport", "leanchecker", "nanoda_bin"):
        if not os.access(prefix / "bin" / executable, os.X_OK):
            raise ValueError(f"pinned toolchain is missing {executable}")
    nanoda = subprocess.run([str(prefix / "bin/nanoda_bin"), "--help"], capture_output=True,
                            text=True, check=True).stdout
    if not re.search(r"\bnanoda_bin 0\.4\.19\b", nanoda):
        raise ValueError("nanoda version does not match the experiment pin")
    return prefix


def run(args: argparse.Namespace) -> dict:
    prefix = toolchain()
    text, targets = fixture(args.operations, args.chunk_size, args.proof)
    report = {
        "schema_version": 1, "experiment": "compiler-validation-reduction",
        "scope": "isolated straight-line typed SSA and exact runtime-call lowering",
        "production_midir": False, "compiler_acceptance": False,
        "host": {"os": platform.system(), "release": platform.release(), "machine": platform.machine()},
        "toolchain": {"lean": PIN, "commit": LEAN_COMMIT, "nanoda": "0.4.19"},
        "workload": {"operations": args.operations, "chunk_size": args.chunk_size,
                     "proof_method": args.proof, "model_sha256": digest(HERE / "Model.lean"),
                     "fixture_sha256": hashlib.sha256(text.encode()).hexdigest()},
        "phases": [], "status": "failed",
    }
    with tempfile.TemporaryDirectory(prefix="vastitas-reduction-") as directory:
        work = Path(directory)
        shutil.copyfile(HERE / "Model.lean", work / "Model.lean")
        (work / "Fixture.lean").write_text(text)
        (work / "lean-toolchain").write_text(PIN + "\n")
        (work / "lakefile.toml").write_text(
            'name = "reduction_spike"\nversion = "0.0.0"\ndefaultTargets = ["Fixture"]\n'
            '[[lean_lib]]\nname = "Fixture"\nroots = ["Model", "Fixture"]\n')
        env = dict(os.environ, LEAN_NUM_THREADS="1", VASTITAS_REPLAY_THREADS="1",
                   VASTITAS_REPLAY_TIME="", PATH=str(prefix / "bin") + os.pathsep + os.environ["PATH"])
        # Fresh isolated directory, no project builds and no inherited Lean imports.
        env.pop("LEAN_PATH", None)
        steps = [
            ("elaboration", [str(prefix / "bin/lake"), "build", "Fixture"], None),
            ("official_replay", ["bash", str(ROOT / "scripts/replay_lean.sh"), str(work), "Fixture"], None),
            ("export", [str(prefix / "bin/lake"), "env", str(prefix / "bin/leanexport"),
                        "Fixture", "--", *targets], work / "proof.ndjson"),
        ]
        for name, command, output in steps:
            result = measure(command, work, env, name, args.timeout, output)
            report["phases"].append(result)
            print(f"{name}: {result['status']} ({result['wall_seconds']:.3f}s)", flush=True)
            if result["exit_code"]:
                report["blocker"] = f"{name} failed; no later verification is claimed"
                if args.logs:
                    sys.stderr.write((work / f"{name}.stderr").read_text(errors="replace"))
                    if output is None:
                        sys.stderr.write((work / f"{name}.stdout").read_text(errors="replace"))
                return report
        try:
            report["export"] = inspect_export(work / "proof.ndjson", targets)
        except (ValueError, KeyError, json.JSONDecodeError) as error:
            report["blocker"] = f"export inspection: {error}"
            return report
        policy = json.loads((ROOT / "config/nanoda-internal-audit.json").read_text())
        if (set(policy["permitted_axioms"]) != ALLOWED_AXIOMS
                or not policy["unpermitted_axiom_hard_error"] or policy["unsafe_permit_all_axioms"]):
            raise ValueError("nanoda policy no longer matches the reviewed experiment")
        policy["export_file_path"] = str(work / "proof.ndjson")
        (work / "nanoda.json").write_text(json.dumps(policy))
        result = measure([str(prefix / "bin/nanoda_bin"), str(work / "nanoda.json")],
                         work, env, "nanoda", args.timeout)
        output = (work / "nanoda.stdout").read_text(errors="replace")
        error_output = (work / "nanoda.stderr").read_text(errors="replace")
        count = checked_count(output, error_output, report["export"]["declarations"])
        if count is None:
            result["status"] = "failed"
        else:
            result["checked_declarations"] = count
        report["phases"].append(result)
        print(f"nanoda: {result['status']} ({result['wall_seconds']:.3f}s)", flush=True)
        if result["status"] != "passed":
            report["blocker"] = "nanoda did not report a complete successful audit"
            if args.logs:
                sys.stderr.write(error_output + output)
        else:
            report["status"] = "passed"
        return report


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--operations", type=int, default=1000)
    parser.add_argument("--chunk-size", type=int, default=1000)
    parser.add_argument("--proof", choices=("decide", "rfl"), default="decide")
    parser.add_argument("--timeout", type=float, default=300)
    parser.add_argument("--output", type=Path, default=ROOT / "target/compiler-validation/reduction.json")
    parser.add_argument("--logs", action="store_true", help="print temporary diagnostic logs on failure")
    args = parser.parse_args()
    if not 4 <= args.operations <= 4096 or not 4 <= args.chunk_size <= 4096 or args.timeout <= 0:
        parser.error("operations/chunk-size must be 4..4096; timeout must be positive")
    try:
        report = run(args)
    except (OSError, ValueError, subprocess.SubprocessError) as error:
        # Do not put OS exception text (which may contain local paths) in records.
        print(f"preflight failed: {type(error).__name__}", file=sys.stderr)
        if args.logs:
            print(error, file=sys.stderr)
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps({
            "schema_version": 1, "experiment": "compiler-validation-reduction",
            "status": "failed", "production_midir": False, "compiler_acceptance": False,
            "blocker": "preflight or measurement infrastructure failed",
            "error_type": type(error).__name__, "phases": [],
        }, indent=2) + "\n")
        return 2
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2) + "\n")
    return 0 if report["status"] == "passed" else 1


if __name__ == "__main__":
    raise SystemExit(main())
