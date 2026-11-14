"""Run as programs the demonstrations of the reference models that the tests of their models do not run.

The book gives each as a command, `python3 scripts/demo_<model>_reference.py`.
The tests of some models import helpers from their demo but never run it.
Each demo here must run with the standard library alone and exit 0.
"""
import subprocess
import sys
import unittest
from pathlib import Path


SCRIPTS = Path(__file__).resolve().parent
DEMOS = ("demo_doctest_result_reference.py", "demo_float_reference.py", "demo_graph_reference.py",
         "demo_identifier_reference.py", "demo_incremental_reference.py", "demo_integral_reference.py",
         "demo_l2_tail_reference.py", "demo_rand_reference.py", "demo_reduction_reference.py",
         "demo_sparse_reference.py")


class DemoTests(unittest.TestCase):
    def test_each_demo_runs_without_site_packages(self):
        for demo in DEMOS:
            with self.subTest(demo=demo):
                result = subprocess.run([sys.executable, "-S", str(SCRIPTS / demo)],
                                        capture_output=True, text=True, timeout=300, check=False)
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertTrue(result.stdout.strip(), f"{demo} printed nothing")


if __name__ == "__main__":
    unittest.main()
