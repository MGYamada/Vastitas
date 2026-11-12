"""The capture's corpus, its handling of an example that the frontend rejects,
and the modules of its kernel fixtures.

These tests run without the compiler: a stand-in for the driver plays the
frontend, and no kernel is called.
"""
import stat
import sys
import tempfile
import unittest
from pathlib import Path

# `python3 -m unittest scripts/test_capture_emit.py` imports this file from the
# repository root, where `scripts/` is not on the module path.
sys.path.insert(0, str(Path(__file__).resolve().parent))

import capture_emit  # noqa: E402

REJECTING_FRONTEND = """#!/usr/bin/env python3
import sys
sys.stderr.write("{root}/main.vast:1:1: E_PARSE: stand-in rejection\\n")
sys.exit({code})
"""


class CorpusTests(unittest.TestCase):
    def test_only_the_rejected_examples_of_the_book_are_marked(self):
        cases = capture_emit.corpus()
        marked = [name for name, _, rejected in cases if rejected]
        self.assertIn("package/examples__reject__packages__unknown-manifest-key", marked)
        self.assertIn("reject/dispatch__literal-key", marked)
        for name, arguments, rejected in cases:
            if arguments[0] == "--manifest-path":
                expected = Path(arguments[1]).parent.parent == capture_emit.REJECTED_PACKAGES
            else:
                expected = capture_emit.REJECTED_EXAMPLES in Path(arguments[0]).parents
            self.assertEqual(rejected, expected, name)
        # A package nested in a rejected package is its dependency, an ordinary case.
        nested = [name for name, arguments, rejected in cases
                  if arguments[0] == "--manifest-path"
                  and capture_emit.REJECTED_PACKAGES in Path(arguments[1]).parents and not rejected]
        self.assertTrue(nested)

    def test_every_rejected_program_is_a_case_of_its_own(self):
        programs = sorted(
            path.relative_to(capture_emit.ROOT)
            for path in (capture_emit.ROOT / capture_emit.REJECTED_EXAMPLES).glob("**/*.vast")
            if capture_emit.REJECTED_PACKAGES not in path.relative_to(capture_emit.ROOT).parents)
        self.assertIn(Path("examples/reject/dispatch/literal-key.vast"), programs)
        cases = {name: arguments for name, arguments, _ in capture_emit.corpus() if name.startswith("reject/")}
        # A rejected program takes no library: one argument, the file.
        self.assertEqual(sorted(Path(arguments[0]) for arguments in cases.values()), programs)
        self.assertTrue(all(len(arguments) == 1 for arguments in cases.values()))
        self.assertEqual(cases["reject/dispatch__literal-key"], ["examples/reject/dispatch/literal-key.vast"])
        # The sources of a rejected package are captured through its manifest only.
        single_files = [arguments[0] for _, arguments, _ in capture_emit.corpus() if arguments[0] != "--manifest-path"]
        self.assertFalse([path for path in single_files if capture_emit.REJECTED_PACKAGES in Path(path).parents])


class KernelFixtureTests(unittest.TestCase):
    def test_the_fixture_build_names_every_import_of_the_codegen_check(self):
        source = (capture_emit.ROOT / "scripts/check_indexed_codegen.lean").read_text(encoding="utf-8")
        imports = [line.split()[1] for line in source.splitlines() if line.startswith("import ")]
        self.assertIn("VastitasKernel.ReverseCoreRegression", imports)
        self.assertEqual(sorted(capture_emit.KERNEL_FIXTURE_MODULES), sorted(imports))


class FrontendRejectionTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.work = Path(self.temp.name)
        self.out = self.work / "out"
        self.out.mkdir()

    def frontend(self, code):
        """A driver that rejects every input itself and never starts a kernel."""
        cli = self.work / f"frontend-{code}"
        cli.write_text(REJECTING_FRONTEND.format(root=capture_emit.ROOT, code=code))
        cli.chmod(cli.stat().st_mode | stat.S_IXUSR)
        return str(cli)

    def capture(self, code, rejected_example):
        return capture_emit.capture_case(
            "package/case", ["--manifest-path", "Vastitas.toml"], rejected_example,
            self.out, self.frontend(code), "no-kernel", self.work / "no-stub", self.work)

    def test_a_rejected_package_records_its_diagnostics_alone(self):
        self.assertEqual(self.capture(1, True), "frontend rejected")
        directory = self.out / "package/case"
        self.assertEqual([path.name for path in directory.iterdir()], ["cli.txt"])
        self.assertEqual(
            (directory / "cli.txt").read_text(),
            "exit 1\n--- stdout ---\n--- stderr ---\n<ROOT>/main.vast:1:1: E_PARSE: stand-in rejection\n")

    def test_an_ordinary_case_must_reach_the_kernel(self):
        with self.assertRaises(SystemExit) as stopped:
            self.capture(1, False)
        self.assertIn("the capture stub was not reached", str(stopped.exception))

    def test_a_frontend_rejection_must_end_with_exit_code_one(self):
        with self.assertRaises(SystemExit) as stopped:
            self.capture(101, True)
        self.assertIn("a frontend rejection ends with exit code 1", str(stopped.exception))


if __name__ == "__main__":
    unittest.main()
