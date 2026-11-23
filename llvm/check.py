#!/usr/bin/env python3
"""Compare public compiler output and closed Lean proofs with every retained LLVM file."""
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
from typing import NamedTuple

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
EXPERIMENT = ROOT / "experiments/compiler_validation/llvm"


class Sample(NamedTuple):
    name: str
    source: Path
    package: str | None
    target: str = "macos-arm64"


CASES = [
    Sample("exit-status", HERE / "fixtures/ExitStatus.vast", "exit_status"),
    Sample("folded-arithmetic", HERE / "fixtures/FoldedArithmetic.vast", "folded_arithmetic"),
    Sample("boxed-program", HERE / "fixtures/BoxedProgram.vast", "boxed_program"),
    Sample("ordered-calls", HERE / "fixtures/OrderedCalls.vast", "ordered_calls"),
    Sample("assembled-conversion", HERE / "fixtures/AssembledConversion.vast", "assembled_conversion"),
    Sample("boxed-pairs", HERE / "fixtures/BoxedPairs.vast", "boxed_pairs"),
    Sample("singleton-power", HERE / "fixtures/SingletonPower.vast", "singleton_power"),
    Sample("borrowed-operator", HERE / "fixtures/borrowed-operator/Vastitas.toml", None),
    Sample("uncalled-operator", HERE / "fixtures/uncalled-operator/Vastitas.toml", None),
    Sample("boxed-arithmetic", HERE / "fixtures/BoxedArithmetic.vast", "boxed_arithmetic"),
    Sample("assembled-bool", HERE / "fixtures/AssembledBool.vast", "assembled_bool"),
    Sample("structured-lookup", HERE / "fixtures/StructuredLookup.vast", "structured_lookup"),
    Sample("structured-lookup-linux-x86_64", HERE / "fixtures/StructuredLookup.vast", "structured_lookup", "linux-x86_64"),
    Sample("finite-projection", HERE / "fixtures/FiniteProjection.vast", "finite_projection"),
    Sample("static-selection", HERE / "fixtures/StaticSelection.vast", "static_selection"),
    Sample("literal-comparison", HERE / "fixtures/LiteralComparison.vast", "literal_comparison"),
    Sample("empty-lookup", HERE / "fixtures/EmptyLookup.vast", "empty_lookup"),
    Sample("closure-unit", HERE / "fixtures/ClosureUnit.vast", "closure_unit"),
    Sample("tensor-column", HERE / "fixtures/tensor-column/Vastitas.toml", None),
    Sample("gemm-coefficients", ROOT / "examples/packages/numerical/gemm-coefficients/Vastitas.toml", None),
    Sample("float-identity", ROOT / "examples/packages/float-identity/Vastitas.toml", None),
    Sample("float-complex-identity", ROOT / "examples/packages/float-complex-identity/Vastitas.toml", None),
    Sample("float32-identity", HERE / "fixtures/float32-identity/Vastitas.toml", None),
    Sample("float32-complex-identity", HERE / "fixtures/float32-complex-identity/Vastitas.toml", None),
    Sample("opposite-s3", HERE / "fixtures/opposite-s3/Vastitas.toml", None),
    Sample("finite-iso", HERE / "fixtures/finite-iso/Vastitas.toml", None),
    Sample("finite-kleisli", ROOT / "examples/packages/finite-kleisli/Vastitas.toml", None),
    Sample("kleisli-callback", HERE / "fixtures/kleisli-callback/Vastitas.toml", None),
    Sample("kleisli-forward", HERE / "fixtures/kleisli-forward/Vastitas.toml", None),
    Sample("kleisli-forward-linux-x86_64", HERE / "fixtures/kleisli-forward/Vastitas.toml", None, "linux-x86_64"),
    Sample("unary-table", EXPERIMENT / "TableComparison.vast", "table_fixture"),
    Sample("s3-composition", HERE / "fixtures/S3Composition.vast", "s3_composition"),
    Sample("static-call", EXPERIMENT / "CallComparison.vast", "call_fixture"),
]


def check_boxed_operators(command, target_args, expected, work):
    package = {"name": "std", "source": "vastitas:compat:operators", "version": "2026.0.0"}
    sites = [
        {"core": 0, "id": {"module": ["operator"], "name": name, "package": package},
         "key": key, "method": {"ordinal": ordinal, "result": result}}
        for name, key, ordinal, result in [
            ("sub", ["Nat", "Nat"], 0, "Nat"),
            ("div", ["Nat", "Int"], 1, "Int"),
            ("add", ["Int", "Int"], 1, "Int"),
        ]
    ]
    source = work / "main.vast"
    original = source.read_text(encoding="utf-8")
    alternate = original.replace("n - 5", "std::operator::sub(n, 5)").replace(
        "std::operator::div(remainder, divisor)", "remainder / divisor").replace(
        "q + q", "std::operator::add(q, q)")
    if alternate == original:
        raise ValueError("missing boxed arithmetic fixture operators")
    for spelling in [original, alternate]:
        source.write_text(spelling, encoding="utf-8")
        revision = json.loads(subprocess.check_output([*command, "--print-function-revision"], cwd=ROOT))
        if revision["pure"]["operator_sites"] != sites:
            raise ValueError("named calls and operators must select the same protected owners and ordered keys")
        if subprocess.check_output([*command, *target_args], cwd=ROOT) != expected:
            raise ValueError("changing the operator spelling changed the boxed LLVM library")

    revision["pure"]["operator_sites"][1]["method"]["ordinal"] = 2
    receipt = work / "swapped-division.json"
    receipt.write_text(json.dumps(revision), encoding="utf-8")
    forged = subprocess.run([*command, *target_args, "--expect-function-revision", receipt],
                            cwd=ROOT, capture_output=True)
    if forged.returncode == 0 or forged.stdout or b"E_FUNCTION_REVISION" not in forged.stderr:
        raise ValueError("mixed division produced LLVM with the reversed key's method ordinal")


def check_static_revision(command, target_args, expected, work):
    """Keep the two invoke specializations distinct even though their ABIs agree."""
    receipt = json.loads(subprocess.check_output([*command, "--print-function-revision"], cwd=ROOT))
    pure = receipt["pure"]
    invokes = [s["specialization"] for s in pure["symbols"] if s["id"]["name"] == "invoke"]
    if len(invokes) != 2 or invokes[0]["definition"] != invokes[1]["definition"] or invokes[0]["targets"] == invokes[1]["targets"]:
        raise ValueError("invoke needs two distinct static targets of the same source function")
    uses = pure["static_uses"]
    for key in invokes:
        if not any(site["caller"] == key and [site["target"]] == key["targets"] for site in uses):
            raise ValueError("no checked use of the static parameter by its own invoke specialization")
    path = work / "revision.json"
    replay = [*command, *target_args, "--expect-function-revision", path]
    path.write_text(json.dumps(receipt), encoding="utf-8")
    if subprocess.check_output(replay, cwd=ROOT) != expected:
        raise ValueError("the exact static selection revision did not reproduce the retained bytes")
    # Both callers exist in this very module and have the same ABI.
    next(site for site in uses if site["caller"] == invokes[0])["caller"] = invokes[1]
    path.write_text(json.dumps(receipt), encoding="utf-8")
    forged = subprocess.run(replay, cwd=ROOT, capture_output=True)
    if forged.returncode == 0 or forged.stdout or b"E_FUNCTION_REVISION" not in forged.stderr:
        raise ValueError("the compiler accepted a static use attributed to the other specialization")


def check_callback_revision(command, target_args, expected, work):
    receipt = json.loads(subprocess.check_output([*command, "--print-function-revision"], cwd=ROOT))
    pure = receipt["pure"]
    symbols = {s["id"]["name"]: s for s in pure["symbols"] if s["id"]["package"]["name"] == "kleisli_callback"}
    apply_key = symbols["applyArrow"]["specialization"]
    target = {"definition": symbols["next"]["specialization"]["definition"]}
    sites = [use for use in pure["static_uses"] if use["caller"] == apply_key]
    category = {**symbols["next"]["id"], "name": "C"}
    signature = {"params": [], "result": {"category": category, "source": "o", "target": "o"}}
    if apply_key["targets"] != [target] or not sites or any(
        use["target"] != target or use.get("signature") != signature for use in sites
    ):
        raise ValueError("the callable must retain its selected definition, category and endpoints")
    path = work / "callback-revision.json"
    replay = [*command, *target_args, "--expect-function-revision", path]
    path.write_text(json.dumps(receipt), encoding="utf-8")
    if subprocess.check_output(replay, cwd=ROOT) != expected:
        raise ValueError("the callable revision did not reproduce the retained module")
    hom = sites[0]["signature"]["result"]
    for field, forged in (("target", "other"), ("category", {**category, "module": ["other"]})):
        original = hom[field]
        hom[field] = forged
        path.write_text(json.dumps(receipt), encoding="utf-8")
        rejected = subprocess.run(replay, cwd=ROOT, capture_output=True)
        if rejected.returncode == 0 or rejected.stdout or b"E_FUNCTION_REVISION" not in rejected.stderr:
            raise ValueError(f"the compiler accepted a forged Hom {field}")
        hom[field] = original


def check_forward_revision(command, target_args, expected, work):
    receipt = json.loads(subprocess.check_output([*command, "--print-function-revision"], cwd=ROOT))
    pure = receipt["pure"]
    site, = pure["finite_forwards"]

    def symbol(package, name):
        matches = [s for s in pure["symbols"] if s["id"]["package"]["name"] == package and s["id"]["name"] == name]
        if len(matches) != 1:
            raise ValueError(f"expected one specialization of {package}::{name}, got {len(matches)}")
        return matches[0]

    caller = symbol("kleisli_forward", "applyArrow")["specialization"]
    producer = symbol("kleisli_callback", "next")
    method = symbol("vastitas_monad", "bind")
    category = {**producer["id"], "name": "C"}
    target = {"definition": producer["specialization"]["definition"]}
    signature = {"params": [], "result": {"category": category, "source": "o", "target": "o"}}
    indices = [{"monad": {**category, "name": "M"}}] + [{"category": category, "object": "o"}] * 3
    if (site["caller"] != caller or caller["targets"] != [target] or site["family"] != method["id"]
        or site["family"]["module"] != ["kleisli"] or site["definition"] != method["specialization"]["definition"]
        or site["finite_indices"] != indices or method["specialization"]["finite_indices"] != indices
        or site["targets"] != [None, {"signature": signature, "target": target}]):
        raise ValueError("the forwarding site lost its caller, selected method, Monad or producer")
    path = work / "forward-revision.json"
    replay = [*command, *target_args, "--expect-function-revision", path]
    path.write_text(json.dumps(receipt), encoding="utf-8")
    if subprocess.check_output(replay, cwd=ROOT) != expected:
        raise ValueError("the exact forwarding revision did not reproduce the retained bytes")
    for field, replacement in (("method", site["site"]), ("targets", list(reversed(site["targets"]))),
                               ("finite_indices", [{"monad": category}, *indices[1:]])):
        original = site[field]
        site[field] = replacement
        path.write_text(json.dumps(receipt), encoding="utf-8")
        rejected = subprocess.run(replay, cwd=ROOT, capture_output=True)
        if rejected.returncode == 0 or rejected.stdout or b"E_FUNCTION_REVISION" not in rejected.stderr:
            raise ValueError(f"the compiler accepted a forged forwarding {field}")
        site[field] = original


def preview_args(target):
    return ["--llvm-preview", "--target-triple", target["triple"], "--data-layout", target["layout"]]


def check_structured_targets(command, targets, work):
    """One source revision retains both method bodies under either target header."""
    path = work / "revision.json"
    path.write_bytes(subprocess.check_output([*command, "--print-function-revision"], cwd=ROOT))
    source = work / "main.vast"
    original = source.read_text(encoding="utf-8")
    for target, name in [("macos-arm64", "structured-lookup"), ("linux-x86_64", "structured-lookup-linux-x86_64")]:
        source.write_text(original, encoding="utf-8")
        preview = [*command, *preview_args(targets[target])]
        replay = [*preview, "--expect-function-revision", path]
        expected = (HERE / "src" / f"{name}.ll").read_bytes()
        if subprocess.check_output(replay, cwd=ROOT) != expected:
            raise ValueError(f"{target}: the same function revision did not reproduce the retained bytes")
        for old, new in [("!a || b", "!a && b"), ("!a && !b", "!a || !b")]:
            if original.count(old) != 1:
                raise ValueError(f"expected one method body containing {old}")
            source.write_text(original.replace(old, new), encoding="utf-8")
            if subprocess.check_output(preview, cwd=ROOT) == expected:
                raise ValueError(f"{target}: changing {old} did not change the emitted methods")
            rejected = subprocess.run(replay, cwd=ROOT, capture_output=True)
            if rejected.returncode == 0 or rejected.stdout or b"E_FUNCTION_REVISION" not in rejected.stderr:
                raise ValueError(f"{target}: a change to {old} did not invalidate the function revision")


def main():
    registered = {f"{sample.name}.ll" for sample in CASES}
    retained = {str(p.relative_to(HERE / "src")) for p in (HERE / "src").rglob("*.ll")}
    if retained != registered:
        raise SystemExit(f"LLVM corpus inventory differs: {sorted(retained ^ registered)}")
    targets = {
        "macos-arm64": json.loads((EXPERIMENT / "results/macos-arm64/unary-table.json").read_bytes())["target"],
        "linux-x86_64": {
            "triple": "x86_64-unknown-linux-gnu",
            "layout": "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128",
        },
    }
    subprocess.run([sys.executable, ROOT / "scripts/build_stdlib_package.py"], cwd=ROOT, check=True)
    subprocess.run(["lake", "-d", "lean-kernel", "build", "vastitas-kernel"], cwd=ROOT, check=True)
    subprocess.run(["lake", "-d", "lean", "build", "VastitasOracle.CallFunction", "VastitasOracle.ExitFunction",
                    "VastitasOracle.DispatchFunction", "VastitasOracle.BinaryFunction",
                    "VastitasKernel.LLVM.FiniteExecution", "VastitasOracle.StorageProgram"], cwd=ROOT, check=True)
    # The closed equalities reduce large terms. Elaborating one declaration
    # at a time avoids holding several kernel reductions in memory at once.
    print(f"Checking closed Lean proofs for {len(registered)} LLVM files", flush=True)
    subprocess.run(["lake", "-d", "lean", "env", "lean", "-j1", "-DwarningAsError=true", "--run",
                    HERE / "Corpus.lean", HERE / "src", *sorted(registered)],
                   cwd=ROOT, check=True)
    print("Lean corpus replay passed. Comparing the public compiler output.", flush=True)
    for name, source, package, target_name in CASES:
        target = targets[target_name]
        with tempfile.TemporaryDirectory(prefix="vastitas-llvm-corpus-") as tmp:
            work = Path(tmp)
            manifest = source
            if package is not None:
                shutil.copyfile(source, work / "main.vast")
                manifest = work / "Vastitas.toml"
                manifest.write_text(f'[package]\nname = "{package}"\nversion = "0.1.0"\n'
                                    'edition = "2026"\nroot = "main.vast"\n', encoding="utf-8")
            command = ["cargo", "run", "--locked", "--quiet", "--bin", "vastitas", "--",
                       "check", "--manifest-path", manifest]
            target_args = preview_args(target)
            fresh = subprocess.check_output([*command, *target_args], cwd=ROOT)
            expected = (HERE / "src" / f"{name}.ll").read_bytes()
            if fresh != expected:
                raise SystemExit(f"{name}: checked source produced different LLVM bytes")
            if name == "boxed-arithmetic":
                check_boxed_operators(command, target_args, expected, work)
            elif name == "static-selection":
                check_static_revision(command, target_args, expected, work)
            elif name == "structured-lookup-linux-x86_64":
                check_structured_targets(command, targets, work)
            elif name == "kleisli-callback":
                check_callback_revision(command, target_args, expected, work)
            elif source == HERE / "fixtures/kleisli-forward/Vastitas.toml":
                check_forward_revision(command, target_args, expected, work)
            print(f"{name}: {len(expected)} bytes matched")


if __name__ == "__main__":
    main()
