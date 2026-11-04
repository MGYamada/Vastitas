#!/usr/bin/env python3
"""Observe actual package import-chain checking on identical source inputs.

Build the kernels and Rust CLI first. Runs alternate baseline/candidate order
after one accepted warmup for each workload and kernel. These are uncontrolled
compiler observations, not runtime performance acceptance or timing thresholds.
"""

import argparse
import hashlib
import json
import math
import os
from pathlib import Path
import platform
import statistics
import tempfile

from check_storage_scaling import observe  # Shared process-group deadline/cleanup.

ROOT = Path(__file__).resolve().parents[1]
CASES = ((250, 1), (500, 1), (1000, 1), (600, 300))


def source(imports, references):
    aliases = [f"use self::a{i + 1} as a{i};" for i in range(imports)]
    bindings = [f"let v{i} = a0(41);" for i in range(references)]
    return "\n".join(aliases + [f"fn a{imports}(x: Int) -> Int {{ x + 1 }}",
                                 "fn main() -> Int {"] + bindings +
                     [f"v{references - 1}", "}", ""])


def binary(path):
    path = path.resolve(strict=True)
    return dict(path=str(path), sha256=hashlib.sha256(path.read_bytes()).hexdigest())


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--compiler", type=Path, default=ROOT / "target/debug/vastitas")
    parser.add_argument("--kernel-root", type=Path, default=ROOT / "lean-kernel")
    parser.add_argument("--baseline-kernel-root", type=Path)
    # The driver rejects a kernel built from other sources (#550), so a baseline
    # kernel from another checkout runs with that checkout's own compiler.
    parser.add_argument("--baseline-compiler", type=Path)
    parser.add_argument("--runs", type=int, default=3)
    parser.add_argument("--timeout", type=float, default=60)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.runs < 1 or not math.isfinite(args.timeout) or args.timeout <= 0:
        parser.error("runs and timeout must be positive and finite")
    if args.baseline_compiler and not args.baseline_kernel_root:
        parser.error("--baseline-compiler requires --baseline-kernel-root")
    compiler = binary(args.compiler)
    kernels = {"candidate": binary(args.kernel_root / ".lake/build/bin/vastitas-kernel")}
    compilers = {"candidate": compiler}
    if args.baseline_kernel_root:
        kernels = {"baseline": binary(args.baseline_kernel_root / ".lake/build/bin/vastitas-kernel"),
                   **kernels}
        compilers = {"baseline": binary(args.baseline_compiler) if args.baseline_compiler
                     else compiler, **compilers}
    report = dict(host=platform.platform(), controlled_host=False, compiler=compiler,
                  compilers=compilers, kernels=kernels, runs=args.runs,
                  timeout_seconds=args.timeout, cases=[])
    accepted = True
    with tempfile.TemporaryDirectory(prefix="vastitas-namespace-scaling-") as directory:
        directory = Path(directory)
        manifest = directory / "Vastitas.toml"
        manifest.write_text("[package]\nname='namespace_scaling'\nversion='0.1.0'\n"
                            "root='main.vast'\n", encoding="utf-8")
        for imports, references in CASES:
            program = source(imports, references)
            (directory / "main.vast").write_text(program, encoding="utf-8")
            case = dict(imports=imports, references=references,
                        source_sha256=hashlib.sha256(program.encode()).hexdigest(),
                        warmups={}, samples={label: [] for label in kernels})
            report["cases"].append(case)
            def measure(label):
                command = [compilers[label]["path"], "check", "--manifest-path", str(manifest)]
                return observe(command, {**os.environ, "VASTITAS_KERNEL": kernels[label]["path"]},
                               args.timeout)

            def ok(result):
                return not result["timed_out"] and result["exit_code"] == 0

            case["warmups"] = {label: measure(label) for label in kernels}
            accepted = all(ok(result) for result in case["warmups"].values())
            if accepted:
                for run in range(args.runs):
                    order = list(kernels) if run % 2 == 0 else list(reversed(kernels))
                    for label in order:
                        result = measure(label)
                        case["samples"][label].append(result)
                        if not ok(result):
                            accepted = False
                            break
                    if not accepted:
                        break
            if accepted:
                case["median_seconds"] = {
                    label: statistics.median(sample["seconds"] for sample in samples)
                    for label, samples in case["samples"].items()}
            args.output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
            print(json.dumps(dict(imports=imports, references=references, accepted=accepted,
                                  median_seconds=case.get("median_seconds"))), flush=True)
            if not accepted:
                break
    return 0 if accepted else 1


if __name__ == "__main__":
    raise SystemExit(main())
