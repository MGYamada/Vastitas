#!/usr/bin/env python3
"""Measure one command in a fresh process without retaining environment values."""
import json
from pathlib import Path
import resource
import subprocess
import sys
import time


def main():
    if len(sys.argv) < 4 or sys.argv[2] != "--":
        raise SystemExit("usage: measure.py RESULT.json -- COMMAND [ARG ...]")
    started = time.monotonic()
    result = subprocess.run(sys.argv[3:], check=False)
    usage = resource.getrusage(resource.RUSAGE_CHILDREN)
    Path(sys.argv[1]).write_text(json.dumps({
        "wall_seconds": time.monotonic() - started,
        "user_seconds": usage.ru_utime,
        "system_seconds": usage.ru_stime,
        "max_child_rss_bytes": int(usage.ru_maxrss * (1 if sys.platform == "darwin" else 1024)),
        "rss_scope": "maximum child-process high-water mark, not simultaneous tree RSS",
        "exit_code": result.returncode,
    }, sort_keys=True) + "\n")
    raise SystemExit(result.returncode if result.returncode >= 0 else 128 - result.returncode)


if __name__ == "__main__":
    main()
