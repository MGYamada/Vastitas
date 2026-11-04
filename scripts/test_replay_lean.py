"""Regression checks for scripts/replay_lean.sh, the bounded leanchecker runner.

A fake `lake` on PATH records its arguments and LEAN_NUM_THREADS, so these tests
never run the real replay.
"""
import os
from pathlib import Path
import stat
import subprocess
import tempfile
import unittest

SCRIPT = Path(__file__).resolve().parent / "replay_lean.sh"


class ReplayLeanTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        root = Path(self.tmp.name)
        self.package = root / "pkg"
        self.package.mkdir()
        (self.package / "lakefile.toml").write_text('name = "pkg"\n')
        self.bin = root / "bin"
        self.bin.mkdir()
        self.record = root / "record.txt"
        fake = self.bin / "lake"
        fake.write_text(
            "#!/bin/sh\n"
            f'echo "threads=$LEAN_NUM_THREADS args=$*" > "{self.record}"\n'
            'exit "${FAKE_LAKE_STATUS:-0}"\n'
        )
        fake.chmod(fake.stat().st_mode | stat.S_IEXEC)

    def tearDown(self):
        self.tmp.cleanup()

    def run_script(self, *args, **env):
        environment = dict(os.environ)
        environment["PATH"] = f"{self.bin}{os.pathsep}{environment['PATH']}"
        environment.pop("VASTITAS_REPLAY_THREADS", None)
        environment.update(env)
        return subprocess.run(["bash", str(SCRIPT), *args], capture_output=True, text=True,
                              env=environment, check=False)

    def recorded(self):
        return self.record.read_text().strip() if self.record.exists() else None

    def test_defaults_to_one_thread_and_passes_modules(self):
        result = self.run_script(str(self.package), "-v", "VastitasBridge")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(self.recorded(), "threads=1 args=env leanchecker -v VastitasBridge")

    def test_thread_count_is_configurable(self):
        result = self.run_script(str(self.package), "VastitasOracle", "VastitasKernel",
                                 VASTITAS_REPLAY_THREADS="2")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(self.recorded(), "threads=2 args=env leanchecker VastitasOracle VastitasKernel")

    def test_rejects_a_missing_module_without_running_leanchecker(self):
        for args in ([str(self.package)], [str(self.package), "-v"], [str(self.package), "--help"]):
            result = self.run_script(*args)
            self.assertEqual(result.returncode, 2, args)
            self.assertIsNone(self.recorded(), args)

    def test_rejects_unknown_flags_and_bad_thread_counts(self):
        self.assertEqual(self.run_script(str(self.package), "--fresh", "M").returncode, 2)
        for threads in ("0", "two", "-1"):
            result = self.run_script(str(self.package), "M", VASTITAS_REPLAY_THREADS=threads)
            self.assertEqual(result.returncode, 2, threads)
        self.assertIsNone(self.recorded())

    def test_an_empty_thread_setting_means_the_default(self):
        result = self.run_script(str(self.package), "M", VASTITAS_REPLAY_THREADS="")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(self.recorded(), "threads=1 args=env leanchecker M")

    def test_rejects_a_directory_without_a_lakefile(self):
        result = self.run_script(self.tmp.name, "M")
        self.assertEqual(result.returncode, 2)
        self.assertIsNone(self.recorded())

    def test_a_failed_or_killed_replay_is_reported_unverified(self):
        result = self.run_script(str(self.package), "M", FAKE_LAKE_STATUS="137")
        self.assertEqual(result.returncode, 137)
        self.assertIn("not verified", result.stderr)


if __name__ == "__main__":
    unittest.main()
