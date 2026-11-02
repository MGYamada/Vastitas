#!/usr/bin/env python3
"""Validate all three standalone C baselines; this is not performance evidence."""
from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
PROFILES = ("public_gemm", "tensor_packing", "contraction_trees")


def load_profile(profile):
    directory = ROOT / "experiments" / profile
    previous = sys.modules.get("cases")
    try:
        spec = importlib.util.spec_from_file_location("cases", directory / "cases.py")
        cases = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(cases)
        sys.modules["cases"] = cases
        spec = importlib.util.spec_from_file_location(f"plain_baseline_{profile}", directory / "run.py")
        runner = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(runner)
        return cases, runner
    finally:
        if previous is None:
            sys.modules.pop("cases", None)
        else:
            sys.modules["cases"] = previous


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--prefix", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--cc", default="cc")
    parser.add_argument("--smoke", action="store_true")
    parser.add_argument("--no-leak-sanitizer", action="store_true")
    parser.add_argument("--valgrind", action="store_true")
    args = parser.parse_args()
    output, prefix = args.output.resolve(), args.prefix.resolve()
    output.mkdir(parents=True, exist_ok=False)
    environment = dict(os.environ, OPENBLAS_NUM_THREADS="1", OMP_NUM_THREADS="1", GOTO_NUM_THREADS="1")
    files = {Path(__file__).resolve(), ROOT / "scripts/native_sanitizers.py", ROOT / "experiments/native_cleanup.py",
             ROOT / "experiments/storage_copy/run.py"}
    for name in (*PROFILES, "plain_c"):
        files.update(path for path in (ROOT / "experiments" / name).iterdir()
                     if path.is_file() and path.suffix in {".c", ".h", ".py"})
    for name in ("native", "numerical"):
        files.update(path for path in (ROOT / "lean-kernel" / name).iterdir()
                     if path.is_file() and path.suffix in {".c", ".h"})
    hashes = {str(path.relative_to(ROOT)): digest(path) for path in sorted(files)}
    for name in hashes:
        destination = output / "inputs" / name
        destination.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(ROOT / name, destination)
    metadata = dict(performance="unmeasured; native diagnostic validation only", source_sha256=hashes,
                    git_head=subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip(),
                    git_status=subprocess.check_output(["git", "status", "--short"], cwd=ROOT, text=True),
                    openblas_sha256={name: digest(prefix / name) for name in
                                     ("lib/libopenblas.a", "include/cblas.h", "include/openblas_config.h")},
                    python=sys.version, compiler=args.cc,
                    compiler_version=subprocess.check_output([args.cc, "--version"], text=True),
                    leak_sanitizer=not args.no_leak_sanitizer,
                    valgrind=args.valgrind, records=[])
    (output / "validation.json").write_text(json.dumps(metadata, indent=2) + "\n")
    for profile in PROFILES:
        cases, module = load_profile(profile)
        runner = module.Runner(output, environment)
        # Append each profile to the shared command-provenance log.
        if (output / "commands.json").exists():
            runner.commands = json.loads((output / "commands.json").read_text())
        valgrind_done = False
        for case in cases.cases(args.smoke):
            work = output / "cases" / profile / case["case"]
            for sanitize in (False, True):
                tag = "sanitized" if sanitize else "optimized"
                arena = module.native_test(runner, case, work / f"arena-{tag}", prefix,
                                           [args.cc], sanitize, args.no_leak_sanitizer)
                plain = module.plain_c.native_test(runner, case, cases.c_header, profile,
                    work / f"plain-{tag}", prefix, [args.cc], arena["rows"],
                    sanitize=sanitize, no_lsan=args.no_leak_sanitizer)
                metadata["records"].append(dict(profile=profile, arena=arena, plain=plain))
                if args.valgrind and not sanitize and not valgrind_done and case["case"].startswith("tiny-") and case["scalar"] and case["pad"]:
                    runner.run(["valgrind", "--error-exitcode=99", "--leak-check=full",
                                "--errors-for-leak-kinds=definite,indirect", work / f"plain-{tag}/timing", "self-test"],
                               phase="plain_c_valgrind")
                    valgrind_done = True
            print(f"{profile}/{case['case']}: arena/plain output, costs, fatal sanitizers and cleanup passed", flush=True)
            (output / "validation.json").write_text(json.dumps(metadata, indent=2) + "\n")
        if args.valgrind and not valgrind_done:
            raise ValueError(f"missing {profile} Valgrind case")
    for name, expected in hashes.items():
        if digest(ROOT / name) != expected:
            raise ValueError(f"validation input changed during execution: {name}")
    metadata["status"] = "passed"
    (output / "validation.json").write_text(json.dumps(metadata, indent=2) + "\n")
    print(f"passed {len(metadata['records'])} optimized/sanitized arena/plain comparisons; no performance acceptance")


if __name__ == "__main__":
    main()
