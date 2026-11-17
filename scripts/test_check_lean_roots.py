"""The build-root reachability check of the kernel and oracle modules (#533)."""

from pathlib import Path
import tempfile
import textwrap
import unittest

import check_lean_roots

KERNEL = """\
name = "kernel"
defaultTargets = ["tool"]

[[lean_lib]]
name = "Kernel"

[[lean_lib]]
name = "Tests"
roots = ["Tests.Main"]

[[lean_exe]]
name = "tool"
root = "Main"
"""
ORACLE = """\
name = "oracle"

[[lean_lib]]
name = "Oracle"
"""
WORKFLOW = """\
name: CI
jobs:
  compiler:
    name: Native compiler
    steps:
      - run: lake -d lean-kernel build Kernel.Unbuilt
  oracle:
    name: Lean proofs and axiom audit
    steps:
      - name: Build the oracle
        run: lake -d lean build Oracle
      - name: Build the kernel
        run: |
          lake -d lean-kernel build Kernel Tests \\
            tool
          bash scripts/check_kernel_regressions.sh
      - name: An unrelated package
        run: lake -d .ci-tools/other build Unknown
  later:
    name: Something else
"""
REGRESSIONS = """\
#!/usr/bin/env bash
lake -d lean-kernel build \\
  Kernel.Regression
"""
SOURCES = {
    "lean-kernel/Kernel.lean": "import Kernel.A\n",
    "lean-kernel/Kernel/A.lean": "/-! A module. -/\nimport Lean.Data.Json\n",
    "lean-kernel/Kernel/Regression.lean": "import Kernel.A\n",
    "lean-kernel/Kernel/OracleOnly.lean": "def x := 1\n",
    "lean-kernel/Kernel/Unbuilt.lean": "def y := 1\n",
    "lean-kernel/Main.lean": "import Kernel\n",
    "lean-kernel/Tests/Main.lean": "import Kernel.A\n",
    "lean-kernel/native/lakefile.lean": "import Lake\n",
    "lean-kernel/native/Native.lean": "def z := 1\n",
    "lean-kernel/.lake/build/Stale.lean": "def w := 1\n",
    "lean/Oracle.lean": "import Oracle.B\n",
    "lean/Oracle/B.lean": "-- the oracle reaches a kernel module\nimport Kernel.OracleOnly\nimport Kernel.Unbuilt\n",
}


class CheckLeanRootsTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.root = Path(self.directory.name)
        files = dict(SOURCES)
        files.update({"lean-kernel/lakefile.toml": KERNEL, "lean/lakefile.toml": ORACLE,
                      ".github/workflows/ci.yml": WORKFLOW,
                      "scripts/check_kernel_regressions.sh": REGRESSIONS})
        for relative, text in files.items():
            self.write(relative, text)

    def tearDown(self):
        self.directory.cleanup()

    def write(self, relative, text):
        path = self.root / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text, encoding="utf-8")

    def errors(self):
        return check_lean_roots.check(self.root)[0]

    def test_the_repository_passes(self):
        errors, count, roots = check_lean_roots.check()
        self.assertEqual(errors, [])
        self.assertGreater(count, 300)
        self.assertGreater(roots, 50)

    def test_library_executable_regression_and_oracle_roots_reach_the_fixture(self):
        errors, count, _ = check_lean_roots.check(self.root)
        self.assertEqual(errors, [])
        # The nested package and `.lake` are not enumerated.
        self.assertEqual(count, 9)

    def test_an_orphaned_module_fails(self):
        self.write("lean-kernel/Kernel/Orphan.lean", "def o := 1\n")
        self.write("lean/Oracle/Orphan.lean", "import Kernel.A\n")
        self.assertEqual(self.errors(), [
            "lean-kernel/Kernel/Orphan.lean: no build root of the CI job 'Lean proofs and axiom audit' "
            "reaches Kernel.Orphan",
            "lean/Oracle/Orphan.lean: no build root of the CI job 'Lean proofs and axiom audit' "
            "reaches Oracle.Orphan"])

    def test_an_import_in_a_comment_reaches_nothing(self):
        self.write("lean-kernel/Kernel/Orphan.lean", "def o := 1\n")
        self.write("lean-kernel/Kernel.lean",
                   "/- import Kernel.Orphan -/\n-- import Kernel.Orphan\nimport Kernel.A\n")
        self.assertEqual(len(self.errors()), 1)

    def test_an_import_after_the_header_reaches_nothing(self):
        self.write("lean-kernel/Kernel/Orphan.lean", "def o := 1\n")
        self.write("lean-kernel/Kernel.lean", "import Kernel.A\ndef a := 1\n-- import Kernel.Orphan\n")
        self.assertEqual(len(self.errors()), 1)

    def test_only_the_lean_job_counts(self):
        # `Kernel.Unbuilt` is built by another job; only the oracle import reaches it.
        self.write("lean/Oracle/B.lean", "import Kernel.OracleOnly\n")
        self.assertEqual(self.errors(), [
            "lean-kernel/Kernel/Unbuilt.lean: no build root of the CI job 'Lean proofs and axiom audit' "
            "reaches Kernel.Unbuilt"])

    def test_the_regressions_count_only_when_the_job_runs_them(self):
        self.write(".github/workflows/ci.yml",
                   WORKFLOW.replace("          bash scripts/check_kernel_regressions.sh\n", ""))
        self.assertEqual(self.errors(), [
            "lean-kernel/Kernel/Regression.lean: no build root of the CI job 'Lean proofs and axiom audit' "
            "reaches Kernel.Regression"])

    def test_a_library_that_the_job_does_not_build_reaches_nothing(self):
        self.write(".github/workflows/ci.yml", WORKFLOW.replace("build Kernel Tests", "build Kernel"))
        self.assertEqual(self.errors(), [
            "lean-kernel/Tests/Main.lean: no build root of the CI job 'Lean proofs and axiom audit' "
            "reaches Tests.Main"])

    def test_a_build_without_targets_builds_the_default_targets(self):
        self.write(".github/workflows/ci.yml", WORKFLOW.replace(
            "lake -d lean-kernel build Kernel Tests \\\n            tool",
            "lake -d lean-kernel build Kernel Tests\n          lake -d lean-kernel build"))
        self.assertEqual(self.errors(), [])
        self.write("lean-kernel/lakefile.toml", KERNEL.replace('defaultTargets = ["tool"]\n', ""))
        self.assertEqual(self.errors(), [
            "lean-kernel/Main.lean: no build root of the CI job 'Lean proofs and axiom audit' reaches Main"])

    def test_an_unknown_target_fails(self):
        self.write(".github/workflows/ci.yml", WORKFLOW.replace("build Kernel Tests", "build Kernel Tset Tests"))
        self.assertEqual(self.errors(), [
            ".github/workflows/ci.yml: `lake -d lean-kernel build` names Tset, which is no target or module "
            "of lean-kernel"])

    def test_a_missing_job_fails(self):
        self.write(".github/workflows/ci.yml", WORKFLOW.replace("Lean proofs and axiom audit", "Proofs"))
        with self.assertRaises(ValueError):
            self.errors()

    def test_globs_are_refused(self):
        self.write("lean-kernel/lakefile.toml", KERNEL + textwrap.dedent("""
            [[lean_lib]]
            name = "Globbed"
            globs = ["Globbed.*"]
            """))
        with self.assertRaises(ValueError):
            self.errors()


if __name__ == "__main__":
    unittest.main()
