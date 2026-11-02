#!/usr/bin/env python3
"""Enforce identical, bounded UTF-8 contributor guidance at the repository root."""
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
FILES = ("AGENTS.md", "CLAUDE.md")
MAX_LINES = 100
MAX_BYTES = 6_000


def check_docs(root: Path) -> list[str]:
    errors = []
    contents = {}
    for name in FILES:
        try:
            data = (root / name).read_bytes()
        except OSError as error:
            errors.append(f"{name}: cannot read file: {error}")
            continue
        contents[name] = data
        if len(data) > MAX_BYTES:
            errors.append(f"{name}: {len(data):,} UTF-8 bytes exceeds {MAX_BYTES:,}")
        try:
            lines = len(data.decode("utf-8").splitlines())
        except UnicodeDecodeError:
            errors.append(f"{name}: invalid UTF-8")
            continue
        if lines > MAX_LINES:
            errors.append(f"{name}: {lines} lines exceeds {MAX_LINES}")
    if len(contents) == len(FILES) and contents[FILES[0]] != contents[FILES[1]]:
        errors.append("AGENTS.md and CLAUDE.md must be byte-for-byte identical")
    return errors


def main() -> int:
    errors = check_docs(ROOT)
    if errors:
        print("\n".join(errors), file=sys.stderr)
        return 1
    print("AGENTS.md and CLAUDE.md: identical; each within 100 lines / 6,000 UTF-8 bytes")
    return 0


if __name__ == "__main__":
    sys.exit(main())
