#!/usr/bin/env python3
"""Reparse the physical sources of four handwritten Lean wire regression suites."""
import json
from pathlib import Path
import subprocess
import tempfile
import tomllib

ROOT = Path(__file__).resolve().parents[1]
EXPORT = "scripts/export_indexed_regression_sources.lean"


def compare(expected, actual, field):
    if isinstance(expected, dict):
        if not isinstance(actual, dict) or actual.keys() != expected.keys():
            raise ValueError(f"{field}: different record fields")
        for key, value in expected.items():
            compare(value, actual[key], f"{field}.{key}")
    elif isinstance(expected, list):
        if not isinstance(actual, list) or len(actual) != len(expected):
            raise ValueError(f"{field}: different number of entries")
        for i, value in enumerate(expected):
            compare(value, actual[i], f"{field}[{i}]")
    elif actual != expected:
        raise ValueError(f"{field}: expected {expected!r}, got {actual!r}")


def check(request, directory):
    source = request["root_source"]
    manifest = directory / "Vastitas.toml"
    manifest.write_bytes(source["files"][0]["text"].encode())
    package = tomllib.loads(manifest.read_text(encoding="utf-8"))["package"]
    entry = directory / package["root"]
    entry.write_bytes(source["text"].encode() + b"\nfn main() -> Int { 0 }\n")
    revision = subprocess.check_output(
        ["cargo", "run", "--locked", "--quiet", "--bin", "vastitas", "--", "check",
         "--manifest-path", manifest, "--print-function-revision"], cwd=ROOT)
    fixture_root = request["packages"][0]["modules"][0]
    parsed_root = json.loads(revision)["input"]["packages"][0]["modules"][0]
    compare(fixture_root["span"], parsed_root["span"], f"{package['name']}.root.span")
    expected = fixture_root["indexed_declarations"]
    actual = parsed_root["indexed_declarations"]
    if not expected or any(d["span"]["end"] <= d["span"]["start"] for d in expected):
        raise ValueError(f"{package['name']}: missing physical declaration span")
    compare(expected, actual, package["name"])
    print(f"{package['name']}: {len(expected)} declarations match the public frontend")


def main():
    out = subprocess.check_output(["lake", "-d", "lean-kernel", "env", "lean", "--run", EXPORT], cwd=ROOT)
    for request in json.loads(out):
        with tempfile.TemporaryDirectory(prefix="vastitas-indexed-fixture-") as tmp:
            check(request, Path(tmp))


if __name__ == "__main__":
    main()
