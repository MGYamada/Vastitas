"""The OpenBLAS builder rejects installed archives outside the locked sequential LP64 profile."""
import os
import shutil
import subprocess
import tempfile
import unittest
from pathlib import Path

import build_openblas

PROVIDER = r"""
const char *openblas_get_config(void) { return CONFIGURATION; }
int openblas_get_parallel(void) { return PARALLEL; }
"""


@unittest.skipUnless(shutil.which("cc") and shutil.which("ar"), "requires a C compiler and archiver")
class ProfileCheckTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)

    def check(self, configuration, parallel=0):
        """Install a mock provider archive in a fresh prefix and inspect it."""
        prefix, work = self.root / f"prefix-{len(list(self.root.iterdir()))}", self.root / "work"
        (prefix / "include").mkdir(parents=True)
        (prefix / "lib").mkdir()
        work.mkdir(exist_ok=True)
        (prefix / "include/cblas.h").write_text(
            "const char *openblas_get_config(void);\nint openblas_get_parallel(void);\n")
        source, object_file = work / "provider.c", work / "provider.o"
        source.write_text(PROVIDER)
        literal = '"' + configuration.replace("\\", "\\\\").replace('"', '\\"') + '"'
        subprocess.run(["cc", "-std=c11", f"-DCONFIGURATION={literal}", f"-DPARALLEL={parallel}",
                        "-c", str(source), "-o", str(object_file)], check=True)
        subprocess.run(["ar", "rcs", str(prefix / "lib/libopenblas.a"), str(object_file)], check=True)
        return build_openblas.check_profile(prefix, work, dict(os.environ))

    def test_locked_sequential_lp64_profile_is_accepted(self):
        configuration = "OpenBLAS 0.3.34 NO_LAPACK NO_LAPACKE NO_AFFINITY USE_LOCKING HASWELL SINGLE_THREADED"
        self.assertEqual(self.check(configuration), configuration)

    def test_unlocked_sequential_profile_is_rejected(self):
        for configuration in ("OpenBLAS 0.3.34 NO_LAPACK NO_AFFINITY HASWELL SINGLE_THREADED",
                              "OpenBLAS 0.3.34 NO_USE_LOCKING HASWELL SINGLE_THREADED",
                              "OpenBLAS 0.3.34 USE_LOCKING_X HASWELL SINGLE_THREADED"):
            with self.subTest(configuration=configuration), self.assertRaisesRegex(ValueError, "locked LP64"):
                self.check(configuration)

    def test_other_profiles_are_rejected(self):
        for configuration, parallel in (
                ("OpenBLAS 0.3.34 USE_LOCKING HASWELL MAX_THREADS=4", 1),
                ("OpenBLAS 0.3.34 USE64BITINT USE_LOCKING HASWELL SINGLE_THREADED", 0),
                ("OpenBLAS 0.3.33 USE_LOCKING HASWELL SINGLE_THREADED", 0), ("", 0)):
            with self.subTest(configuration=configuration), self.assertRaisesRegex(ValueError, "locked LP64"):
                self.check(configuration, parallel)


if __name__ == "__main__":
    unittest.main()
