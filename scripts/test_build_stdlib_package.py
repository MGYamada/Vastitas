"""Byte-preservation and generated-output lifecycle regressions."""
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

import build_stdlib_package as generator


class PackageGenerationTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        (self.root / "scripts").mkdir()
        self.script = self.root / "scripts/build_stdlib_package.py"
        shutil.copyfile(Path(generator.__file__), self.script)
        self.sources = self.root / "stdlib/src/arithmetic"
        self.sources.mkdir(parents=True)
        for name in ("int", "nat", "generic"):
            (self.sources / f"{name}.vast").write_bytes(b"// empty fixture\n")
        self.destination = self.root / "stdlib/target/package"

    def run_generator(self, *args, success=True):
        result = subprocess.run(
            [sys.executable, str(self.script), *args], capture_output=True
        )
        self.assertEqual(result.returncode == 0, success, result.stderr.decode())
        return result

    def test_preserves_all_non_lf_comment_separators_and_final_bytes(self):
        for separator in ("\r", "\v", "\f", "\x1c", "\x1d", "\x1e", "\x85", "\u2028", "\u2029"):
            for ending in ("", "\n", "\r\n"):
                with self.subTest(separator=repr(separator), ending=repr(ending)):
                    source = (
                        "fn f() -> Int {\r\n"
                        f"    5 // ignored{separator} + 100\n"
                        f"}}{ending}"
                    ).encode()
                    (self.sources / "int.vast").write_bytes(source)
                    self.run_generator()
                    actual = (self.destination / "arithmetic/integers.vast").read_bytes()
                    self.assertEqual(actual, generator.HEADER + b"pub " + source)
                    self.run_generator("--check")

    def test_check_detects_missing_changed_and_extra_files_without_writing(self):
        self.run_generator("--check", success=False)
        self.run_generator()
        original = {p: (p.read_bytes(), p.stat().st_mtime_ns) for p in self.destination.rglob("*.vast")}
        self.run_generator()
        self.run_generator("--check")
        self.assertEqual(original, {p: (p.read_bytes(), p.stat().st_mtime_ns) for p in original})
        changed = self.destination / "lib.vast"
        changed.write_bytes(b"// modified\r\n")
        self.run_generator("--check", success=False)
        self.assertEqual(changed.read_bytes(), b"// modified\r\n")
        self.run_generator()
        extra = self.destination / "arithmetic/obsolete.vast"
        extra.write_bytes(b"fn stale() -> Int { 0 }")
        keep = self.destination / "notes.txt"
        keep.write_bytes(b"keep")
        self.run_generator("--check", success=False)
        self.assertTrue(extra.exists())
        self.run_generator()
        self.assertFalse(extra.exists())
        self.assertEqual(keep.read_bytes(), b"keep")
        self.run_generator("--check")


if __name__ == "__main__":
    unittest.main()
