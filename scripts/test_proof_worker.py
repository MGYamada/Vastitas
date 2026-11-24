"""The local proof budget must work across processes, including parent exit."""
import fcntl
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

from proof_worker import proof_slot


class ProofWorkerTests(unittest.TestCase):
    def test_child_holds_slot_until_exit(self):
        # A different temporary directory keeps this test separate from live proofs.
        with tempfile.TemporaryDirectory() as directory, patch("proof_worker.LOCK_DIRECTORY", Path(directory)):
            path = Path(directory) / f"vastitas-proof-worker-{os.getuid()}.lock"
            with proof_slot() as slot:
                child = subprocess.Popen([sys.executable, "-c", "import sys; sys.stdin.buffer.read(1)"],
                                         pass_fds=(slot,), stdin=subprocess.PIPE)
            try:
                with path.open("rb") as observer:
                    with self.assertRaises(BlockingIOError):
                        fcntl.flock(observer, fcntl.LOCK_EX | fcntl.LOCK_NB)
                    child.communicate(b"x", timeout=5)
                    self.assertEqual(child.returncode, 0)
                    fcntl.flock(observer, fcntl.LOCK_EX | fcntl.LOCK_NB)
            finally:
                if child.poll() is None:
                    child.kill()
                    child.communicate()

    def test_unsafe_lock_file_is_rejected(self):
        with tempfile.TemporaryDirectory() as directory, patch("proof_worker.LOCK_DIRECTORY", Path(directory)):
            path = Path(directory) / f"vastitas-proof-worker-{os.getuid()}.lock"
            file = Path(directory) / "unrelated"
            file.write_text("keep")
            path.symlink_to(file)
            with self.assertRaises(OSError), proof_slot():
                self.fail("unexpected lock")
            self.assertEqual(file.read_text(), "keep")


if __name__ == "__main__":
    unittest.main()
