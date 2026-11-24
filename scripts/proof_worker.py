"""Share the memory budget of compiler-proof tests across local worktrees."""
from contextlib import contextmanager
import fcntl
import os
from pathlib import Path
import stat
import subprocess


# One slot even when different worktrees set their own TMPDIR.
LOCK_DIRECTORY = Path("/tmp")


@contextmanager
def proof_slot():
    # Keep one inode per user. Unlinking it after release would let another
    # process create a second lock while existing waiters still use the first.
    path = LOCK_DIRECTORY / f"vastitas-proof-worker-{os.getuid()}.lock"
    fd = os.open(path, os.O_CREAT | os.O_RDWR | os.O_NOFOLLOW | os.O_NONBLOCK, 0o600)
    try:
        info = os.fstat(fd)
        if not stat.S_ISREG(info.st_mode) or info.st_uid != os.getuid() or info.st_nlink != 1:
            raise OSError("invalid compiler-proof worker lock")
        fcntl.flock(fd, fcntl.LOCK_EX)
        yield fd
    finally:
        os.close(fd)


def run_proof_worker(command, **kwargs):
    env = dict(kwargs.pop("env", os.environ))
    env.setdefault("LEAN_NUM_THREADS", "1")
    with proof_slot() as fd:
        return subprocess.run(command, env=env, pass_fds=(fd,), **kwargs)
