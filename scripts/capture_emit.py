#!/usr/bin/env python3
"""Capture, and compare, what the compiler emits for every example.

For each documented single-file example, every package manifest under
`examples/` and `stdlib/`, and every manifest under `tests/emit_corpus/`, the
script records:

- `wire.raw.json` and `wire.json`: the exact protocol request the frontend
  sends to the kernel (raw, and re-serialized for reading), captured with a
  stub backend (the pattern of `captured_wire` in `tests/common/mod.rs`);
- `cli.txt`: the exit code and output of `vastitas check` with the kernel under
  test;
- `check.json` and `emit.json`: the kernel's responses to that request in
  `check` and `emit` mode, without the build identity (`kernel`), which changes
  with every kernel edit, and `check.txt`/`emit.txt` with the kernel's exit code
  and standard error;
- `emit.lean`: the `lean_source` of the `emit` response, when there is one.

With `--kernel-fixtures`, it also records the generated modules of
`scripts/check_indexed_codegen.lean`.

The kernel rejects every package under `tests/emit_corpus/rejected/` on
purpose, so that the comparison covers the diagnostics of rejected primitive
calls; their `cli.txt` and `check.json` hold the message. With `E_ENDPOINT`,
the packages fail a family, a coefficient marker, a domain, a fixed index
(`flat`, `relative_coefficient`), a shared endpoint (`compose`, the seed of
`cotangent_backward`), an endpoint fixed by a declaration (`relative_pair`),
two equal applications (`same`), the index pattern (a covector in the point
slot of a pullback, which lists the operand types), and a family that
`relative_coefficient` and `relative_pair` report before the index pattern.
One package fails the operand shape (`E_TYPE`) and one the operand count
(`E_ARITY`). `tests/rejected_diagnostics.rs` also pins these `cli.txt` texts in
every `cargo test` run, against `tests/fixtures/rejected/`.

The checkout root is written as `<ROOT>` so captures from different
checkouts compare. `--compare BASELINE` reports every byte difference against
an earlier capture and exits 1 when there is one. A change that promises
byte-identical generated code, diagnostics and wire format runs this before
and after, each time with the binaries built from that tree:

    python3 scripts/capture_emit.py --out /tmp/baseline --kernel-fixtures   # on the base commit
    python3 scripts/capture_emit.py --out /tmp/after --kernel-fixtures --compare /tmp/baseline

Limits. `build` sends the kernel the same request as `check`, so `emit` on the
captured request is the kernel step of `build`; the emitted Lean is not
compiled or run here (the documented examples in `tests/examples.rs` do that).
Library packages without an entry point reject `emit` with `E_MAIN`, so their
primitives are lowered only through the packages that use them. No example
selects protocol 5 or 6; their fixtures live in `tests/`.
"""
import argparse
import difflib
import json
import os
import shutil
import stat
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
MARKER = ".capture_emit"
STDLIB_INT = "stdlib/src/arithmetic/int.vast"
STDLIB_NAT = "stdlib/src/arithmetic/nat.vast"
STDLIB_GENERIC = "stdlib/src/arithmetic/generic.vast"

# Single-file examples with the arguments their documentation gives
# (tests/examples.rs and docs/guide). Every other `examples/*.vast` is checked alone.
SINGLE_FILE = {
    "dispatch-arithmetic": ["--lib", STDLIB_INT, "--lib", STDLIB_NAT, "--lib", STDLIB_GENERIC],
    "promotion": ["--lib", STDLIB_INT, "--lib", STDLIB_NAT, "--lib", STDLIB_GENERIC],
    "stdlib-arithmetic": ["--lib", STDLIB_INT, "--lib", STDLIB_NAT],
}

STUB = """#!/usr/bin/env python3
import json, os, sys
request = sys.stdin.buffer.read()
with open(os.environ["VASTITAS_CAPTURE_WIRE"], "wb") as handle:
    handle.write(request)
version = json.loads(request).get("version", 0)
print(json.dumps({"version": version, "ok": False,
                  "diagnostics": [{"code": "E_CAPTURED", "message": "captured"}]}))
sys.exit(1)
"""


def corpus():
    """(name, arguments after `check`) for every input, in a stable order."""
    cases = []
    for example in sorted((ROOT / "examples").glob("*.vast")):
        cases.append((f"example/{example.stem}", [str(example.relative_to(ROOT))] + SINGLE_FILE.get(example.stem, [])))
    manifests = sorted(ROOT.glob("examples/**/Vastitas.toml")) + sorted(ROOT.glob("stdlib/**/Vastitas.toml"))
    manifests += sorted(ROOT.glob("tests/emit_corpus/**/Vastitas.toml"))
    for manifest in manifests:
        relative = manifest.relative_to(ROOT)
        if "stdlib/target" in str(relative):
            continue
        name = "package/" + str(relative.parent).replace("examples/packages/", "").replace("/", "__")
        cases.append((name, ["--manifest-path", str(relative)]))
    return cases


def normalize(text):
    return text.replace(str(ROOT), "<ROOT>")


def decoded(data):
    return normalize(data.decode("utf-8", "replace"))


def run(command, env=None, stdin=None):
    return subprocess.run(command, cwd=ROOT, env=env, input=stdin, capture_output=True, timeout=1800)


def process_text(result):
    return f"exit {result.returncode}\n--- stderr ---\n{decoded(result.stderr)}"


def capture_case(name, arguments, out, cli, kernel, stub, work):
    directory = out / name
    directory.mkdir(parents=True, exist_ok=True)
    for stale in directory.iterdir():
        stale.unlink()
    wire_path = work / f"{name.replace('/', '__')}.wire.json"
    wire_path.unlink(missing_ok=True)
    stub_env = dict(os.environ, VASTITAS_KERNEL=str(stub), VASTITAS_CAPTURE_WIRE=str(wire_path))
    captured = run([cli, "check", *arguments], env=stub_env)
    if b"E_CAPTURED" not in captured.stderr or not wire_path.exists():
        sys.exit(f"{name}: the capture stub was not reached; the frontend said:\n{process_text(captured)}")
    real = run([cli, "check", *arguments], env=dict(os.environ, VASTITAS_KERNEL=kernel))
    (directory / "cli.txt").write_text(
        f"exit {real.returncode}\n--- stdout ---\n{decoded(real.stdout)}--- stderr ---\n{decoded(real.stderr)}")
    wire = wire_path.read_bytes()
    (directory / "wire.raw.json").write_text(decoded(wire))
    (directory / "wire.json").write_text(normalize(json.dumps(json.loads(wire), indent=1, ensure_ascii=False)) + "\n")
    summary = []
    for mode in ("check", "emit"):
        result = run([kernel, mode], stdin=wire)
        try:
            response = json.loads(result.stdout)
        except ValueError:
            sys.exit(f"{name}: the kernel's {mode} output is not JSON:\n{process_text(result)}")
        (directory / f"{mode}.txt").write_text(process_text(result))
        if isinstance(response, dict):
            response.pop("kernel", None)
        (directory / f"{mode}.json").write_text(normalize(json.dumps(response, indent=1, ensure_ascii=False)) + "\n")
        summary.append(f"{mode}={'ok' if isinstance(response, dict) and response.get('ok') else 'rejected'}")
        if mode == "emit":
            source = response.get("lean_source") if isinstance(response, dict) else None
            if isinstance(source, str):
                (directory / "emit.lean").write_text(normalize(source))
                summary.append(f"{len(source)} bytes of Lean")
    return ", ".join(summary)


def capture_kernel_fixtures(out):
    """The generated modules of the kernel's own codegen fixtures."""
    kernel_dir = ROOT / "lean-kernel"
    modules = [
        "VastitasKernel.IndexedCoreRegression", "VastitasKernel.IndexedPackageSemanticRegression",
        "VastitasKernel.IndexedSourceRegression", "VastitasKernel.IndexedSourceTypeRegression",
        "VastitasKernel.IndexedSourceBodyRegression", "VastitasKernel.IndexedFunctionRegression",
        "VastitasKernel.IndexedDispatchRegression", "VastitasKernel.IndexedAuthorityRegression",
        "VastitasKernel.SmoothObjectRegression", "VastitasKernel.CotangentRegression",
        "VastitasKernel.MetricFormRegression", "VastitasKernel.IndexedCodegen"]
    subprocess.run(["lake", "build", *modules], cwd=kernel_dir, check=True)
    with tempfile.TemporaryDirectory() as work:
        subprocess.run(["lake", "env", "lean", "--run", str(ROOT / "scripts/check_indexed_codegen.lean"), work],
                       cwd=kernel_dir, check=True)
        directory = out / "kernel-fixtures"
        if directory.exists():
            shutil.rmtree(directory)
        directory.mkdir(parents=True)
        fixtures = sorted(Path(work).glob("*.lean"))
        for fixture in fixtures:
            (directory / fixture.name).write_text(normalize(fixture.read_text()))
        return len(fixtures)


def compare(baseline, out):
    """Every byte difference between two captures. Returns the number of differing paths."""
    differences = 0
    baseline_files = {path.relative_to(baseline) for path in baseline.rglob("*") if path.is_file()}
    out_files = {path.relative_to(out) for path in out.rglob("*") if path.is_file()}
    for missing in sorted(baseline_files - out_files):
        print(f"MISSING in the new capture: {missing}")
        differences += 1
    for extra in sorted(out_files - baseline_files):
        print(f"NEW (absent from the baseline): {extra}")
        differences += 1
    for path in sorted(baseline_files & out_files):
        before = (baseline / path).read_bytes()
        after = (out / path).read_bytes()
        if before == after:
            continue
        differences += 1
        print(f"DIFFERENT: {path}")
        diff = difflib.unified_diff(
            before.decode("utf-8", "replace").splitlines(), after.decode("utf-8", "replace").splitlines(),
            str(baseline / path), str(out / path), lineterm="", n=1)
        for index, line in enumerate(diff):
            if index >= 40:
                print("  ...")
                break
            print(f"  {line}")
    return differences


def prepare_output(out, only):
    """An empty capture directory, or an earlier capture to extend with `--only`."""
    home = Path.home().resolve()
    if out in (ROOT, home) or out in ROOT.parents or out in home.parents:
        sys.exit(f"refusing to capture into {out}")
    if out.exists() and not only:
        if not (out / MARKER).is_file():
            if any(out.iterdir()):
                sys.exit(f"{out} exists and is not an earlier capture; choose a new or empty directory")
        else:
            shutil.rmtree(out)
    out.mkdir(parents=True, exist_ok=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--out", required=True, type=Path,
                        help="directory for this capture; an earlier capture there is replaced")
    parser.add_argument("--compare", type=Path, help="an earlier capture to compare byte for byte")
    parser.add_argument("--cli", type=Path, default=ROOT / "target/debug/vastitas")
    parser.add_argument("--kernel", type=Path, default=ROOT / "lean-kernel/.lake/build/bin/vastitas-kernel")
    parser.add_argument("--kernel-fixtures", action="store_true",
                        help="also capture the generated modules of scripts/check_indexed_codegen.lean")
    parser.add_argument("--only", help="capture only the cases whose name contains this text, keeping the rest")
    args = parser.parse_args()
    cli, kernel = args.cli.resolve(), args.kernel.resolve()
    for binary in (cli, kernel):
        if not binary.is_file():
            sys.exit(f"missing {binary}: build it first (cargo build; lake -d lean-kernel build vastitas-kernel)")
    subprocess.run([sys.executable, str(ROOT / "scripts/build_stdlib_package.py")], cwd=ROOT, check=True)
    out = args.out.resolve()
    prepare_output(out, args.only)
    cases = [case for case in corpus() if not args.only or args.only in case[0]]
    if not cases:
        sys.exit(f"no case matches --only {args.only!r}")
    with tempfile.TemporaryDirectory() as work:
        work = Path(work)
        stub = work / "capture-kernel"
        stub.write_text(STUB)
        stub.chmod(stub.stat().st_mode | stat.S_IXUSR | stat.S_IXGRP | stat.S_IXOTH)
        for name, arguments in cases:
            print(f"{name}: {capture_case(name, arguments, out, str(cli), str(kernel), stub, work)}")
    print(f"captured {len(cases)} case(s)")
    if args.kernel_fixtures:
        print(f"kernel fixtures: {capture_kernel_fixtures(out)} generated modules")
    (out / MARKER).write_text("written by scripts/capture_emit.py\n")
    if args.compare:
        differences = compare(args.compare.resolve(), out)
        if differences:
            sys.exit(f"{differences} path(s) differ from {args.compare}")
        print(f"identical to {args.compare}: {sum(1 for path in out.rglob('*') if path.is_file())} files")


if __name__ == "__main__":
    main()
