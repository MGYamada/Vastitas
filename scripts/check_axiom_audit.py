#!/usr/bin/env python3
"""Exercise the real audit against isolated imported modules, without native execution.

Run after the oracle build: lake -d lean env python3 scripts/check_axiom_audit.py
The deliberately invalid declarations exist only in temporary negative fixtures.
"""
import os
from pathlib import Path
import shutil
import subprocess
import tempfile


ROOT = Path(__file__).resolve().parents[1]
AUDIT = (ROOT / "scripts/audit_axioms.lean").read_text()


def invoke(arguments, environment):
    return subprocess.run(
        ["lean", *map(str, arguments)], cwd=ROOT, env=environment,
        text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
        timeout=90, check=False,
    )


def project_overlay(temporary):
    # Lean selects a search directory for the top-level module component.
    # A fixture-only VastitasKernel/ would hide the real Core.olean. Link the
    # existing project libraries into a private overlay, never write into them.
    for entry in os.environ["LEAN_PATH"].split(os.pathsep):
        for group in ("VastitasKernel", "VastitasOracle", "VastitasPromotion"):
            for source in Path(entry).glob(group + "*"):
                destination = temporary / source.name
                if source.is_dir():
                    shutil.copytree(source, destination,
                                    copy_function=lambda a, b: os.symlink(Path(a).resolve(), b))
                else:
                    destination.symlink_to(source.resolve())


def check(label, module, declarations, expected=None):
    with tempfile.TemporaryDirectory(prefix="vastitas-axiom-audit-") as directory:
        temporary = Path(directory)
        environment = dict(os.environ)
        environment["LEAN_PATH"] = str(temporary) + os.pathsep + environment["LEAN_PATH"]
        if module:
            project_overlay(temporary)
            source = temporary.joinpath(*module.split(".")).with_suffix(".lean")
            source.parent.mkdir(parents=True, exist_ok=True)
            if source.exists() or source.with_suffix(".olean").exists():
                raise RuntimeError(f"fixture collides with an existing module: {module}")
            source.write_text("import Lean\nnamespace UnrelatedNamespace\n" +
                              declarations + "\nend UnrelatedNamespace\n")
            compiled = invoke(["--root", temporary, "-o", source.with_suffix(".olean"), source],
                              environment)
            if compiled.returncode:
                raise RuntimeError(f"{label}: fixture failed to compile\n{compiled.stdout}")
            audit = AUDIT.replace("import VastitasOracle\n",
                                  f"import VastitasOracle\nimport {module}\n", 1)
        else:
            # A missing project import must fail, even with no bad declaration.
            audit = AUDIT.replace("import VastitasOracle\n", "", 1)
        probe = temporary / "AuditProbe.lean"
        probe.write_text(audit)
        result = invoke(["--root", temporary, probe], environment)
        if expected is None:
            if result.returncode or "axiom audit passed" not in result.stdout:
                raise RuntimeError(f"{label}: valid fixture rejected\n{result.stdout}")
        elif not result.returncode or expected not in result.stdout:
            raise RuntimeError(f"{label}: expected rejection {expected!r}\n{result.stdout}")
        print(f"passed: {label}", flush=True)


def main():
    if not os.environ.get("LEAN_PATH"):
        raise SystemExit("run with: lake -d lean env python3 scripts/check_axiom_audit.py")
    check("private declarations and proved csimp remain permitted",
          "VastitasKernel.AuditFixture", """
private def original (n : Nat) : Nat := n + 0
private def replacement (n : Nat) : Nat := n
@[csimp] private theorem equal : original = replacement := by
  funext n
  simp [original, replacement]
""")
    for group in ("VastitasKernel", "VastitasOracle", "VastitasPromotion"):
        check(f"unused private axiom in {group}", f"{group}.AuditFixture",
              "private axiom hidden : False", "unapproved axiom")
    check("public declaration in an unrelated namespace", "VastitasKernel.AuditFixture",
          "axiom unrelated : False", "unapproved axiom")
    check("private extern substitution", "VastitasKernel.AuditFixture", """
@[extern "vastitas_negative_audit_fixture"] private opaque external : Nat
""", "unproved extern implementation")
    check("private implemented_by substitution", "VastitasOracle.AuditFixture", """
private def replacement (n : Nat) : Nat := n + 1
@[implemented_by replacement] private def original (n : Nat) : Nat := n
""", "unproved implemented_by substitution")
    check("missing required module group", None, "",
          "no declarations from required module group VastitasOracle")
    print("axiom-audit provenance/substitution regressions passed: 8 cases")


if __name__ == "__main__":
    main()
