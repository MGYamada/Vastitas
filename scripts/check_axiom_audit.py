#!/usr/bin/env python3
"""Exercise the real audit against isolated fixture packages, without native execution.

Run after building every kernel library, executable and the oracle:
lake -d lean env python3 scripts/check_axiom_audit.py
The deliberately invalid declarations exist only in temporary fixture packages.
Each fixture package has a `.lake/build/lib/lean` build directory on the Lean
search path, so the audit discovers its sources exactly as it discovers `lean/`
and `lean-kernel/`.
"""
import os
from pathlib import Path
import shutil
import subprocess
import tempfile


ROOT = Path(__file__).resolve().parents[1]
AUDIT = (ROOT / "scripts/audit_axioms.lean").read_text()
GROUPS = ("VastitasKernel", "VastitasOracle", "VastitasPromotion", "VastitasPublicTest",
          "VastitasStorageTest", "VastitasAlgebraTest", "Main")
ORACLE_BUILD = (ROOT / "lean/.lake/build/lib/lean").resolve()


def invoke(arguments, environment):
    return subprocess.run(
        ["lean", *map(str, arguments)], cwd=ROOT, env=environment,
        text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
        timeout=900, check=False,
    )


def project_overlay(build):
    # Lean selects a search directory for the top-level module component.
    # A fixture-only VastitasKernel/ would hide the real Core.olean. Link the
    # existing project libraries into a private overlay, never write into them.
    for entry in os.environ["LEAN_PATH"].split(os.pathsep):
        for group in GROUPS:
            for source in Path(entry).glob(group + "*"):
                destination = build / source.name
                if destination.exists():
                    continue
                if source.is_dir():
                    shutil.copytree(source, destination,
                                    copy_function=lambda a, b: os.symlink(Path(a).resolve(), b))
                else:
                    destination.symlink_to(source.resolve())


def fixture_source(package, module, declarations):
    source = package.joinpath(*module.split(".")).with_suffix(".lean")
    source.parent.mkdir(parents=True, exist_ok=True)
    if (ROOT / "lean-kernel").joinpath(*module.split(".")).with_suffix(".lean").exists() or \
            (ROOT / "lean").joinpath(*module.split(".")).with_suffix(".lean").exists():
        raise RuntimeError(f"fixture collides with an existing module: {module}")
    source.write_text("import Lean\nnamespace UnrelatedNamespace\n" +
                      declarations + "\nend UnrelatedNamespace\n")
    return source


def check(label, fixtures=(), expected=(), unbuilt=(), audit=AUDIT, without_oracle=False):
    """`fixtures` and `unbuilt` hold (module, declarations); `expected` holds the
    substrings of a rejection, or is empty for an accepted fixture."""
    with tempfile.TemporaryDirectory(prefix="vastitas-axiom-audit-") as directory:
        temporary = Path(directory)
        package = temporary / "package"
        build = package / ".lake/build/lib/lean"
        build.mkdir(parents=True)
        environment = dict(os.environ)
        entries = environment["LEAN_PATH"].split(os.pathsep)
        if without_oracle:
            entries = [entry for entry in entries if Path(entry).resolve() != ORACLE_BUILD]
        environment["LEAN_PATH"] = os.pathsep.join([str(build), *entries])
        project_overlay(build)
        for module, declarations in fixtures:
            source = fixture_source(package, module, declarations)
            target = build.joinpath(*module.split(".")).with_suffix(".olean")
            target.parent.mkdir(parents=True, exist_ok=True)
            compiled = invoke(["--root", package, "-o", target, source], environment)
            if compiled.returncode:
                raise RuntimeError(f"{label}: fixture failed to compile\n{compiled.stdout}")
        for module, declarations in unbuilt:
            fixture_source(package, module, declarations)
        probe = temporary / "AuditProbe.lean"
        probe.write_text(audit)
        result = invoke(["--root", temporary, probe], environment)
        if not expected:
            if result.returncode or "axiom audit passed" not in result.stdout:
                raise RuntimeError(f"{label}: valid fixture rejected\n{result.stdout}")
        elif not result.returncode or not all(text in result.stdout for text in expected):
            raise RuntimeError(f"{label}: expected rejection {expected!r}\n{result.stdout}")
        print(f"passed: {label}", flush=True)
        return 1


def main():
    if not os.environ.get("LEAN_PATH"):
        raise SystemExit("run with: lake -d lean env python3 scripts/check_axiom_audit.py")
    cases = 0
    cases += check("private declarations and proved csimp remain permitted",
                   [("VastitasKernel.AuditFixture", """
private def original (n : Nat) : Nat := n + 0
private def replacement (n : Nat) : Nat := n
@[csimp] private theorem equal : original = replacement := by
  funext n
  simp [original, replacement]
""")])
    for group in ("VastitasKernel", "VastitasOracle", "VastitasPromotion",
                  "VastitasPublicTest", "VastitasStorageTest", "VastitasAlgebraTest"):
        cases += check(f"unused private axiom in {group}",
                       [(f"{group}.AuditFixture", "private axiom hidden : False")],
                       ["unapproved axiom", "hidden"])
    cases += check("public declaration in an unrelated namespace",
                   [("VastitasKernel.AuditFixture", "axiom unrelated : False")],
                   ["unapproved axiom UnrelatedNamespace.unrelated"])
    cases += check("sorry in a theorem that nothing uses",
                   [("VastitasKernel.AuditFixture", "private theorem probe : False := sorry")],
                   ["unapproved axiom sorryAx"])
    cases += check("private extern substitution", [("VastitasKernel.AuditFixture", """
@[extern "vastitas_negative_audit_fixture"] private opaque external : Nat
""")], ["unlisted declarations", "extern", "external in VastitasKernel.AuditFixture"])
    cases += check("private implemented_by substitution", [("VastitasOracle.AuditFixture", """
private def replacement (n : Nat) : Nat := n + 1
@[implemented_by replacement] private def original (n : Nat) : Nat := n
""")], ["unlisted declarations", "implemented_by", "original in VastitasOracle.AuditFixture"])
    cases += check("private partial definition", [("VastitasKernel.AuditFixture", """
private partial def spin (n : Nat) : Nat := spin (n + 1)
""")], ["unlisted declarations", "partial", "spin in VastitasKernel.AuditFixture"])
    cases += check("partial definition named like a derived Repr", [("VastitasKernel.AuditFixture", """
partial def instReprProbe.repr (n : Nat) : Nat := instReprProbe.repr (n + 1)
""")], ["unlisted declarations", "partial UnrelatedNamespace.instReprProbe.repr"])
    cases += check("unsafe definition", [("VastitasStorageTest.AuditFixture", """
unsafe def coerce (n : Nat) : Nat := n + 1
""")], ["unlisted declarations", "unsafe UnrelatedNamespace.coerce"])
    cases += check("opaque constant", [("VastitasPromotion.AuditFixture", """
opaque hidden : Nat → Nat
""")], ["unlisted declarations", "opaque UnrelatedNamespace.hidden"])
    cases += check("total structural recursion remains permitted", [("VastitasKernel.AuditFixture", """
def count : List Nat → Nat
  | [] => 0
  | _ :: rest => count rest + 1
""")])
    cases += check("source module without a built object file", unbuilt=[
        ("VastitasKernel.AuditUnbuilt", "def unbuilt : Nat := 0")],
        expected=["source module VastitasKernel.AuditUnbuilt has no built .olean"])
    cases += check("source module outside the audited groups", unbuilt=[
        ("UnauditedLibrary.Probe", "def probe : Nat := 0")],
        expected=["source module UnauditedLibrary.Probe", "outside the audited module groups"])
    cases += check("oracle module not imported by the oracle root",
                   [("VastitasOracle.AuditOrphan", "def orphan : Nat := 0")],
                   ["oracle module VastitasOracle.AuditOrphan is not imported by the VastitasOracle root"])
    cases += check("oracle package missing from the search path", without_oracle=True,
                   expected=["required module group VastitasOracle has no source modules"])
    stale = AUDIT.replace(
        "def exceptions : Array Listed := #[\n",
        "def exceptions : Array Listed := #[\n"
        "  { module := `Main, name := `vastitasStaleProbe, kind := \"partial\", reason := \"stale\" },\n", 1)
    if stale == AUDIT:
        raise RuntimeError("could not insert the stale exception probe")
    cases += check("listed exception that no longer exists", audit=stale,
                   expected=["unused exception partial vastitasStaleProbe in Main"])
    print(f"axiom-audit coverage/provenance/substitution regressions passed: {cases} cases")


if __name__ == "__main__":
    main()
