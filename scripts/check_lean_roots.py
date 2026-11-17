#!/usr/bin/env python3
"""Check that a build root of CI's Lean job reaches every kernel and oracle module.

`scripts/audit_axioms.lean` enumerates every Lean source module of
`lean-kernel/` and `lean/` and requires an `.olean` for each, but it does not
check that the `.olean` is current. A module that no build root of the CI job
"Lean proofs and axiom audit" reaches is never rebuilt there: a local audit
then counts a stale `.olean`, and a clean checkout fails (#533). This check
runs before any build and fails on such a module.

A build root is a library root or an executable root of a target that the job
builds with `lake -d lean-kernel build` or `lake -d lean build`, or a module of
`scripts/check_kernel_regressions.sh` when the job runs that script. A module
is reached when the import closure of a build root contains it; an import of
the oracle reaches kernel modules. The enumeration is that of the audit: it
skips `.lake`, hidden directories and nested Lake packages.
"""
import argparse
from pathlib import Path
import re
import sys
import tomllib

from check_boundaries import lean_imports

ROOT = Path(__file__).resolve().parents[1]
PACKAGES = ("lean-kernel", "lean")
WORKFLOW = Path(".github/workflows/ci.yml")
JOB = "Lean proofs and axiom audit"
REGRESSIONS = Path("scripts/check_kernel_regressions.sh")
_BUILD = re.compile(r"\blake -d (\S+) build\b([^\n;&|#]*)")
_JOB = re.compile(r"^  [A-Za-z0-9_-]+:\s*$", re.M)


def modules(root, package):
    """{module name: path} of the Lean sources of `package`, as the audit enumerates them."""
    base = root / package
    found = {}

    def walk(directory):
        for entry in sorted(directory.iterdir()):
            if entry.is_dir():
                if entry.name.startswith(".") or any(
                        (entry / name).exists() for name in ("lakefile.toml", "lakefile.lean")):
                    continue
                walk(entry)
            elif entry.suffix == ".lean" and entry.name != "lakefile.lean":
                found[".".join(entry.relative_to(base).with_suffix("").parts)] = entry

    walk(base)
    return found


def targets(root, package):
    """{target name: its root modules} of the libraries and executables of `package`, and its default targets."""
    config = tomllib.loads((root / package / "lakefile.toml").read_text(encoding="utf-8"))
    found = {}
    for library in config.get("lean_lib", []):
        if "globs" in library:
            raise ValueError(f"{package}/lakefile.toml: library {library['name']} uses globs, which this check does not read")
        found[library["name"]] = list(library.get("roots", [library["name"]]))
    for executable in config.get("lean_exe", []):
        found[executable["name"]] = [executable.get("root", executable["name"])]
    return found, list(config.get("defaultTargets", []))


def joined(text):
    """`text` with shell line continuations joined."""
    return re.sub(r"\\\n\s*", " ", text)


def job(root):
    """The text of the CI job named `JOB`."""
    text = (root / WORKFLOW).read_text(encoding="utf-8")
    starts = [match.start() for match in _JOB.finditer(text)]
    for start, end in zip(starts, starts[1:] + [len(text)]):
        block = text[start:end]
        if re.search(rf"^    name: {re.escape(JOB)}\s*$", block, re.M):
            return joined(block)
    raise ValueError(f"{WORKFLOW}: no job named {JOB!r}")


def build_roots(root, errors):
    """{package: root modules} that CI's Lean job builds, and the regression modules it runs."""
    text = job(root)
    roots = {package: set() for package in PACKAGES}
    commands = [(match.group(1), match.group(2).split()) for match in _BUILD.finditer(text)]
    if "bash scripts/check_kernel_regressions.sh" in text:
        script = joined((root / REGRESSIONS).read_text(encoding="utf-8"))
        commands += [(match.group(1), match.group(2).split()) for match in _BUILD.finditer(script)]
    for package, names in commands:
        if package not in PACKAGES:
            continue
        known, default = targets(root, package)
        for name in [name for name in names if not name.startswith("-")] or default:
            if name in known:
                roots[package].update(known[name])
            elif name in modules(root, package):
                roots[package].add(name)
            else:
                errors.append(f"{WORKFLOW}: `lake -d {package} build` names {name}, which is no target or module of {package}")
    return roots


def check(root=ROOT):
    """The modules of `lean-kernel/` and `lean/` that no build root of CI's Lean job reaches."""
    errors = []
    sources = {}
    for package in PACKAGES:
        for name, path in modules(root, package).items():
            if name in sources:
                errors.append(f"{path.relative_to(root)}: module {name} is also {sources[name].relative_to(root)}")
            sources[name] = path
    roots = build_roots(root, errors)
    reached = set()
    pending = [name for package in PACKAGES for name in roots[package]]
    while pending:
        name = pending.pop()
        if name in reached or name not in sources:
            continue
        reached.add(name)
        try:
            pending.extend(lean_imports(sources[name].read_text(encoding="utf-8")))
        except ValueError as error:
            errors.append(f"{sources[name].relative_to(root)}: cannot read the imports: {error}")
    for name, path in sorted(sources.items()):
        if name not in reached:
            errors.append(f"{path.relative_to(root)}: no build root of the CI job {JOB!r} reaches {name}")
    return errors, len(sources), sum(len(names) for names in roots.values())


def main():
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("--root", type=Path, default=ROOT, help="repository root (default: this checkout)")
    arguments = parser.parse_args()
    errors, count, roots = check(arguments.root.resolve())
    for error in errors:
        print(error, file=sys.stderr)
    if errors:
        return 1
    print(f"Lean build roots: {roots} roots of the CI job {JOB!r} reach all {count} modules of "
          f"{' and '.join(PACKAGES)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
