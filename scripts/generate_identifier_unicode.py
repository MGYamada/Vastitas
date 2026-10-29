"""Regenerate the fixed Unicode 16.0.0 ranges from the vendored UCD file."""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().with_name("identifier_data")
SOURCE = ROOT / "DerivedCoreProperties-16.0.0.txt"
OUTPUT = ROOT / "unicode16_ranges.json"
SOURCE_SHA256 = "39d35161f2954497f69e08bdb9e701493f476a3d30222de20028feda36c1dabd"
PROPERTIES = ("XID_Start", "XID_Continue", "Default_Ignorable_Code_Point")


def generate() -> str:
    raw = SOURCE.read_bytes()
    if hashlib.sha256(raw).hexdigest() != SOURCE_SHA256:
        raise ValueError("UCD source hash mismatch")
    ranges: dict[str, list[list[int]]] = {prop: [] for prop in PROPERTIES}
    for line in raw.decode("utf-8").splitlines():
        fields = line.partition("#")[0].strip().split(";")
        if len(fields) != 2 or fields[1].strip() not in ranges:
            continue
        bounds = fields[0].strip().split("..")
        ranges[fields[1].strip()].append([int(bounds[0], 16), int(bounds[-1], 16)])
    for prop, entries in ranges.items():
        merged: list[list[int]] = []
        for lo, hi in sorted(entries):
            if merged and lo <= merged[-1][1]:
                raise ValueError(f"overlapping UCD ranges: {prop}")
            if merged and lo == merged[-1][1] + 1:
                merged[-1][1] = hi
            else:
                merged.append([lo, hi])
        ranges[prop] = merged
    return json.dumps({
        "unicode_version": "16.0.0",
        "source_url": "https://www.unicode.org/Public/16.0.0/ucd/DerivedCoreProperties.txt",
        "source_sha256": SOURCE_SHA256,
        "properties": ranges,
    }, ensure_ascii=True, indent=2) + "\n"


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    expected = generate()
    if args.check:
        if OUTPUT.read_text(encoding="utf-8") != expected:
            raise SystemExit("generated Unicode table differs")
        print("Unicode 16.0.0 ranges match the pinned UCD source")
    else:
        OUTPUT.write_text(expected, encoding="utf-8")
        print(OUTPUT.name)
