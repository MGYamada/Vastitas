#!/usr/bin/env python3
"""Check growing actual protocol-8 programs with a bounded observation deadline.

These are compiler scaling observations, not controlled-host runtime performance
acceptance. Build the kernel and Rust CLI first. Run the same generated sources
against each kernel root for a before/after comparison.
"""

import argparse
import hashlib
import json
import math
import os
from pathlib import Path
import platform
import signal
import subprocess
import tempfile
import time

ROOT = Path(__file__).resolve().parents[1]
SHAPES = ("allocate_drop", "read_loans", "write_children", "reborrow_chain", "wrapped_reads")


def source(shape, size):
    if shape == "allocate_drop":
        body = [f"allocate d{i}: F64[1]; drop(d{i});" for i in range(size)]
    elif shape in ("read_loans", "wrapped_reads"):
        body = ["allocate d: F64[1];", "borrow w = write(d, layout(0,1,1,1,false));",
                "fill(w, f64_bits(0)); release(w);"]
        body += [f"borrow r{i} = read(d, layout(0,1,1,1,false));" for i in range(size)]
        body += [f"release(r{i});" for i in reversed(range(size))]
        body += ["drop(d);"]
    elif shape == "write_children":
        body = [f"allocate d: F64[{size}];",
                f"borrow parent = write(d, layout(0,{size},1,{size},false));"]
        body += [f"borrow r{i} = write(parent, layout({8*i},1,1,1,false));" for i in range(size)]
        body += [f"release(r{i});" for i in reversed(range(size))]
        body += ["release(parent); drop(d);"]
    elif shape == "reborrow_chain":
        body = ["allocate d: F64[1];"]
        body += [f"borrow r{i} = write({'d' if i == 0 else f'r{i-1}'}, layout(0,1,1,1,false));"
                 for i in range(size)]
        body += [f"release(r{i});" for i in reversed(range(size))]
        body += ["drop(d);"]
    else:
        raise ValueError(shape)
    body = "\n".join(body)
    if shape == "wrapped_reads":
        functions = [f"resource fn leaf() -> Unit {{\n{body}\nvalue {{ () }}\n}}"]
        previous = "leaf"
        for index in range(10):
            current = f"wrapper{index}"
            functions.append(f"resource fn {current}() -> Unit {{ call {previous}() -> (); value {{ () }} }}")
            previous = current
        functions.append(f"resource fn main() -> Int {{ call {previous}() -> (); value {{ 0 }} }}")
        return "\n".join(functions) + "\n"
    return f"resource fn main() -> Int {{\n{body}\nvalue {{ 0 }}\n}}\n"


def observe(command, env, timeout):
    started = time.monotonic()
    with subprocess.Popen(command, env=env, text=True, stdout=subprocess.PIPE,
                          stderr=subprocess.PIPE, start_new_session=True) as process:
        timed_out = False
        try:
            stdout, stderr = process.communicate(timeout=timeout)
        except subprocess.TimeoutExpired:
            timed_out = True
            try:
                os.killpg(process.pid, signal.SIGTERM)
            except ProcessLookupError:
                pass
            try:
                stdout, stderr = process.communicate(timeout=5)
            except subprocess.TimeoutExpired:
                try:
                    os.killpg(process.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
                stdout, stderr = process.communicate()
        return dict(seconds=time.monotonic() - started, exit_code=process.returncode,
                    timed_out=timed_out, stdout=stdout, stderr=stderr)


def write_package(directory, name, program):
    package = Path(directory) / name
    package.mkdir()
    manifest = package / "Vastitas.toml"
    manifest.write_text("[package]\nname='storage_scaling'\nversion='0.1.0'\nroot='main.vast'\n",
                        encoding="utf-8")
    (package / "main.vast").write_text(program, encoding="utf-8")
    return manifest


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--compiler", type=Path, default=ROOT / "target/debug/vastitas")
    parser.add_argument("--kernel-root", type=Path, default=ROOT / "lean-kernel")
    parser.add_argument("--sizes", type=int, nargs="+", default=[64, 128, 256])
    parser.add_argument("--shapes", choices=SHAPES, nargs="+", default=list(SHAPES))
    parser.add_argument("--timeout", type=float, default=30)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    if (any(size < 1 or size > 1000 for size in args.sizes)
            or not math.isfinite(args.timeout) or args.timeout <= 0):
        parser.error("sizes must be 1..1000 (inside the source work budget); timeout must be positive")
    compiler = args.compiler.resolve(strict=True)
    kernel_root = args.kernel_root.resolve(strict=True)
    kernel = (kernel_root / ".lake/build/bin/vastitas-kernel").resolve(strict=True)
    env = dict(os.environ, VASTITAS_KERNEL=str(kernel), VASTITAS_KERNEL_ROOT=str(kernel_root))
    report = dict(platform=platform.platform(), kernel=str(kernel),
                  kernel_sha256=hashlib.sha256(kernel.read_bytes()).hexdigest(),
                  timeout_seconds=args.timeout, results=[])
    with tempfile.TemporaryDirectory(prefix="vastitas-storage-scaling-") as directory:
        warmup = write_package(directory, "warmup", "resource fn main() -> Int { value { 0 } }\n")
        report["warmup"] = observe([str(compiler), "check", "--manifest-path", str(warmup)], env, args.timeout)
        if report["warmup"]["exit_code"] or report["warmup"]["timed_out"]:
            raise RuntimeError(f"kernel warmup failed: {report['warmup']}")
        for shape in args.shapes:
            for size in args.sizes:
                program = source(shape, size)
                manifest = write_package(directory, f"{shape}-{size}", program)
                result = observe([str(compiler), "check", "--manifest-path", str(manifest)], env, args.timeout)
                result.update(shape=shape, size=size, source_sha256=hashlib.sha256(program.encode()).hexdigest())
                report["results"].append(result)
                status = "timeout" if result["timed_out"] else f"exit {result['exit_code']}"
                print(f"{shape} {size}: {result['seconds']:.3f}s ({status})", flush=True)
    if args.output:
        args.output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    failed = [result for result in report["results"] if result["exit_code"] or result["timed_out"]]
    for result in failed:
        print(result["stderr"])
    return bool(failed)


if __name__ == "__main__":
    raise SystemExit(main())
