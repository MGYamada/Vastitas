#!/usr/bin/env python3
"""Validate the indexed examples/ corpus; optionally check/build/run its cases.

No compiler is needed for the default structural validation. Pass --run after
building the Rust CLI and Lean kernel; native stdout witnesses are also tested.
"""

import argparse
import re
import subprocess
import sys
import tempfile
import tomllib
from pathlib import Path, PurePosixPath


ROOT = Path(__file__).resolve().parents[1]
EXAMPLES = ROOT / "examples"
IDENTIFIER = re.compile(r"[a-z0-9-]+(?:\.[a-z0-9-]+)*\Z")
DIAGNOSTIC = re.compile(r"E_[A-Z0-9_]+\Z")
FIELDS = {"id", "kind", "path", "expect", "stdout", "diagnostic", "libraries", "covered_by"}


def relative_path(value, origin):
    if not isinstance(value, str) or not value:
        raise ValueError(f"{origin}: expected a nonempty relative path")
    path = PurePosixPath(value)
    if path.is_absolute() or path.as_posix() != value or any(
        segment in (".", "..") for segment in value.split("/")
    ):
        raise ValueError(f"{origin}: noncanonical or escaping path: {value}")
    return path


def load_cases(examples=EXAMPLES, repository=ROOT):
    """Return checked case dictionaries; reject omissions and ambiguous cases."""
    with (examples / "corpus.toml").open("rb") as handle:
        index = tomllib.load(handle)
    if set(index) != {"schema_version", "case"} or index["schema_version"] != 1:
        raise ValueError("corpus.toml: expected schema_version = 1 and [[case]] entries")
    cases = index["case"]
    if not isinstance(cases, list) or not cases:
        raise ValueError("corpus.toml: at least one case is required")

    names = set()
    paths = set()
    package_paths = set()
    loose_paths = set()
    for case in cases:
        if not isinstance(case, dict) or not {"id", "kind", "path", "expect"} <= set(case):
            raise ValueError(f"incomplete case: {case}")
        if set(case) - FIELDS:
            raise ValueError(f"{case['id']}: unknown fields: {sorted(set(case) - FIELDS)}")
        name = case["id"]
        if not isinstance(name, str) or not IDENTIFIER.fullmatch(name) or name in names:
            raise ValueError(f"invalid or duplicate case id: {name}")
        names.add(name)

        path = relative_path(case["path"], name)
        if path.as_posix() in paths:
            raise ValueError(f"{name}: duplicate path: {path}")
        paths.add(path.as_posix())
        file = examples.joinpath(*path.parts)
        if not file.is_file() or not file.resolve().is_relative_to(examples.resolve()):
            raise ValueError(f"{name}: missing or escaping file: {path}")

        kind, expect = case["kind"], case["expect"]
        if expect not in ("accept", "reject", "dependency"):
            raise ValueError(f"{name}: unknown expectation: {expect}")
        if kind == "source" and path.suffix == ".vast":
            if expect == "dependency":
                raise ValueError(f"{name}: only packages may be dependency fixtures")
            if expect == "accept" and path.parts[0] != "book":
                raise ValueError(f"{name}: accepted single-file sources belong under book/")
            if expect == "reject" and path.parts[0] != "reject":
                raise ValueError(f"{name}: rejected sources belong under reject/")
            loose_paths.add(path.as_posix())
        elif (kind == "package" and path.name == "Vastitas.toml" and
              ((expect in ("accept", "dependency") and path.parts[0] == "packages") or
               (expect == "reject" and path.parts[0] == "reject"))):
            package_paths.add(path.as_posix())
        else:
            raise ValueError(f"{name}: invalid kind, expectation or path: {path}")

        if expect == "reject":
            code = case.get("diagnostic")
            if not isinstance(code, str) or not DIAGNOSTIC.fullmatch(code):
                raise ValueError(f"{name}: rejected cases require an exact E_* diagnostic code")
        elif "diagnostic" in case:
            raise ValueError(f"{name}: accepted cases cannot claim a rejection code")
        if expect == "dependency":
            owner = case.get("covered_by")
            if not isinstance(owner, str) or not IDENTIFIER.fullmatch(owner):
                raise ValueError(f"{name}: dependency fixtures require a covering case ID")
        elif "covered_by" in case:
            raise ValueError(f"{name}: only dependency fixtures may declare covered_by")
        if "stdout" in case and (expect != "accept" or not isinstance(case["stdout"], str)):
            raise ValueError(f"{name}: stdout is an exact native witness for accepted cases only")
        libraries = case.get("libraries", [])
        if not isinstance(libraries, list) or (kind == "package" and libraries):
            raise ValueError(f"{name}: libraries must be a list for a source case")
        for lib in libraries:
            libpath = relative_path(lib, name)
            full = repository.joinpath(*libpath.parts)
            if libpath.suffix != ".vast" or not full.is_file() or not full.resolve().is_relative_to(repository.resolve()):
                raise ValueError(f"{name}: nonexistent or escaping library: {lib}")

    for source in examples.rglob("*.vast"):
        rel = source.relative_to(examples).as_posix()
        if rel in loose_paths:
            continue
        if rel.startswith(("packages/", "reject/")) and any(
            parent.relative_to(examples).as_posix() + "/Vastitas.toml" in package_paths
            for parent in source.parents if parent != examples and examples in parent.parents
        ):
            continue
        raise ValueError(f"unregistered Vastitas source: {rel}")
    manifests = {p.relative_to(examples).as_posix() for p in examples.rglob("Vastitas.toml")}
    if manifests != package_paths:
        raise ValueError(f"unregistered package manifests: {sorted(manifests ^ package_paths)}")

    # Check the manifest-relative dependency graph after corpus moves. This is
    # structural only: it never replaces the compiler's package checker.
    graph = {}
    for rel in package_paths:
        manifest = examples / rel
        with manifest.open("rb") as handle:
            data = tomllib.load(handle)
        dependencies = set()
        for dependency, desc in data.get("dependencies", {}).items():
            if isinstance(desc, dict) and "path" in desc:
                target = desc["path"]
                if not isinstance(target, str) or not target or Path(target).is_absolute():
                    raise ValueError(f"{rel}: invalid path dependency {dependency}")
                resolved = (manifest.parent / target).resolve()
                if not resolved.is_relative_to(repository.resolve()) or not (resolved / "Vastitas.toml").is_file():
                    raise ValueError(f"{rel}: broken path dependency {dependency} = {target}")
                dependencies.add((resolved / "Vastitas.toml").resolve())
        graph[manifest.resolve()] = dependencies

    # A dependency fixture is not promised to pass `check` in isolation: edit
    # authority, for example, can name a recipient outside its own closure.
    # Require a registered, accepted package whose dependency graph checks it.
    by_id = {case["id"]: case for case in cases}
    for case in cases:
        if case["expect"] != "dependency":
            continue
        owner = by_id.get(case["covered_by"])
        if owner is None or owner["kind"] != "package" or owner["expect"] != "accept":
            raise ValueError(f"{case['id']}: covered_by must name an accepted package case")
        target = (examples / case["path"]).resolve()
        root = (examples / owner["path"]).resolve()
        reachable = set()
        pending = list(graph.get(root, ()))
        while pending:
            manifest = pending.pop()
            if manifest in reachable:
                continue
            reachable.add(manifest)
            pending.extend(graph.get(manifest, ()))
        if target == root or target not in reachable:
            raise ValueError(f"{case['id']}: not in {owner['id']}'s dependency closure")
    return cases


def arguments(case):
    file = (EXAMPLES / case["path"]).relative_to(ROOT).as_posix()
    if case["kind"] == "package":
        return ["--manifest-path", file]
    args = [file]
    for library in case.get("libraries", []):
        args.extend(["--lib", library])
    return args


def first_diagnostic(stderr):
    """Use only the first diagnostic header, never codes quoted in notes."""
    for line in stderr.splitlines():
        if line.startswith("note: ") or ": note: " in line:
            continue
        starts = [0] + [match.end() for match in re.finditer(r": ", line)]
        for start in starts:
            match = re.match(r"(E_[A-Z0-9_]+): ", line[start:])
            if match:
                return match.group(1)
    return None


def execute(case, cli):
    """Check each case; build and run only cases with an exact stdout witness."""
    name = case["id"]
    args = arguments(case)
    result = subprocess.run([str(cli), "check", *args], cwd=ROOT, capture_output=True, timeout=180)
    diagnostic = result.stderr.decode("utf-8", errors="replace")
    if case["expect"] == "reject":
        code = case["diagnostic"]
        if result.returncode == 0 or first_diagnostic(diagnostic) != code:
            raise ValueError(f"{name}: expected rejection {code}, got exit {result.returncode}: {diagnostic[-2000:]}")
        return
    if result.returncode:
        raise ValueError(f"{name}: expected acceptance, got exit {result.returncode}: {diagnostic[-2000:]}")
    if "stdout" not in case:
        return
    with tempfile.TemporaryDirectory(prefix="vastitas-corpus-") as temporary:
        binary = Path(temporary) / "program"
        built = subprocess.run([str(cli), "build", *args, "-o", str(binary)],
                               cwd=ROOT, capture_output=True, timeout=300)
        if built.returncode:
            raise ValueError(f"{name}: build failed: {built.stderr.decode('utf-8', 'replace')[-2000:]}")
        run = subprocess.run([str(binary)], cwd=ROOT, capture_output=True, timeout=120)
        expected = case["stdout"].encode("utf-8")
        if run.returncode or run.stdout != expected:
            raise ValueError(f"{name}: expected exit 0/stdout {expected!r}, got exit {run.returncode}/stdout {run.stdout!r}: {run.stderr!r}")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--run", action="store_true", help="check each selected case and run its native witness")
    parser.add_argument("--cli", type=Path, default=ROOT / "target/debug/vastitas")
    parser.add_argument("--case", help="run only cases whose stable id contains this string")
    parser.add_argument("--list", action="store_true", help="list the indexed case ids")
    args = parser.parse_args()
    try:
        cases = load_cases()
        selected = [case for case in cases if args.case is None or args.case in case["id"]]
        if not selected:
            raise ValueError("no conformance cases matched --case")
        if args.list:
            for case in selected:
                print(f"{case['id']} ({case['expect']})")
        if args.run:
            cli = args.cli.resolve()
            if not cli.is_file():
                raise ValueError(f"compiler not found: {cli}; build the CLI and Lean kernel first")
            by_id = {case["id"]: case for case in cases}
            checked = set()
            for case in selected:
                checked_case = by_id[case["covered_by"]] if case["expect"] == "dependency" else case
                if checked_case["id"] not in checked:
                    execute(checked_case, cli)
                    checked.add(checked_case["id"])
                if case["expect"] == "dependency":
                    print(f"ok {case['id']} (covered by {checked_case['id']})")
                else:
                    print(f"ok {case['id']}")
        print(f"conformance corpus: {len(cases)} indexed cases, {len(selected)} selected")
    except (OSError, ValueError, subprocess.TimeoutExpired) as error:
        print(f"conformance corpus: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
