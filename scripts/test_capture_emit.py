"""The capture's corpus and its handling of a package that the frontend rejects.

These tests run without the compiler: a stand-in for the driver plays the
frontend, and no kernel is called.
"""
import stat
import tempfile
import unittest
from pathlib import Path

import capture_emit

REJECTING_FRONTEND = """#!/usr/bin/env python3
import sys
sys.stderr.write("{root}/main.vast:1:1: E_PARSE: stand-in rejection\\n")
sys.exit({code})
"""


class CorpusTests(unittest.TestCase):
    def test_only_the_rejected_packages_of_the_book_are_marked(self):
        cases = capture_emit.corpus()
        marked = [name for name, _, rejected in cases if rejected]
        self.assertIn("package/examples__reject__packages__unknown-manifest-key", marked)
        for name, arguments, rejected in cases:
            manifest = Path(arguments[1]) if arguments[0] == "--manifest-path" else None
            expected = manifest is not None and manifest.parent.parent == capture_emit.REJECTED_PACKAGES
            self.assertEqual(rejected, expected, name)
        # A package nested in a rejected package is its dependency, an ordinary case.
        nested = [name for name, arguments, rejected in cases
                  if arguments[0] == "--manifest-path"
                  and capture_emit.REJECTED_PACKAGES in Path(arguments[1]).parents and not rejected]
        self.assertTrue(nested)


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
