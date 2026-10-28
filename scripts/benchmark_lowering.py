#!/usr/bin/env python3
"""Compare real kernel acceptance by size, declaration order and call graph (#141).

Times include process startup, JSON decoding, both lowering passes and final
core/static audits, but exclude payload construction and Rust parsing. Every
sample must be accepted. A rejection or timeout is never a fast timing result.
"""
import argparse
import csv
import json
import pathlib
import statistics
import subprocess
import sys
import time

ROOT = pathlib.Path(__file__).resolve().parents[1]
SPAN = dict(start=0, end=0, line=1, column=1)
INT = dict(kind="named", name="Int")


def expression(kind, **fields):
    return dict(kind=kind, span=SPAN, **fields)


def function(name, result, params=(), statements=()):
    return dict(name=name, params=list(params), return_type=INT,
                body=dict(statements=list(statements), result=result, span=SPAN), span=SPAN)


def program(count, with_lambda, shape="chain", order="forward"):
    functions = []
    parameter = dict(name="x", ty=INT, span=SPAN)
    for index in range(count):
        result = expression("variable", name="x")
        if index + 1 < count:
            callee = index + 1 if shape == "chain" else count - 1
            result = expression("call", callee=f"f{callee}", args=[result])
        functions.append(function(f"f{index}", result, [parameter]))
    if order == "reverse":
        functions.reverse()
    result = expression("call", callee="f0", args=[expression("integer", value="42")])
    statements = []
    if with_lambda:
        value = expression("lambda", params=[parameter], return_type=INT,
                           body=dict(statements=[], result=expression("variable", name="x"), span=SPAN))
        statements.append(dict(kind="let", name="g", annotation=None, value=value, span=SPAN))
        result = expression("invoke", callee=expression("variable", name="g"), args=[result])
    functions.append(function("main", result, statements=statements))
    return dict(version=2, file="benchmark.vast", functions=functions, generics=[], methods=[])


def positive(value):
    result = int(value)
    if result <= 0:
        raise argparse.ArgumentTypeError("must be positive")
    return result


def measure(kernel, payload, timeout):
    start = time.perf_counter()
    output = subprocess.run([str(kernel), "check"], input=payload, capture_output=True,
                            timeout=timeout, check=True)
    elapsed = time.perf_counter() - start
    response = json.loads(output.stdout)
    if response.get("ok") is not True:
        raise RuntimeError(f"{kernel} rejected benchmark: {response}")
    return elapsed


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--kernel", type=pathlib.Path, default=ROOT / "lean-kernel/.lake/build/bin/vastitas-kernel")
    parser.add_argument("--baseline-kernel", type=pathlib.Path,
                        help="already-built baseline; identical payloads and interleaved runs")
    parser.add_argument("--sizes", type=positive, nargs="+", default=[2000, 4000, 8000])
    parser.add_argument("--orders", choices=["forward", "reverse"], nargs="+", default=["forward", "reverse"])
    parser.add_argument("--shapes", choices=["chain", "shared"], nargs="+", default=["chain", "shared"])
    parser.add_argument("--runs", type=positive, default=3)
    parser.add_argument("--timeout", type=positive, default=60)
    args = parser.parse_args()
    kernels = [("candidate", args.kernel.resolve())]
    if args.baseline_kernel:
        kernels.insert(0, ("baseline", args.baseline_kernel.resolve()))
    writer = csv.writer(sys.stdout, lineterminator="\n")
    writer.writerow(["kernel", "functions", "shape", "order", "lambda", "runs",
                     "median_seconds", "min_seconds", "max_seconds", "samples_seconds"])
    for size in args.sizes:
        for shape in args.shapes:
            for order in args.orders:
                for with_lambda in (False, True):
                    payload = json.dumps(program(size, with_lambda, shape, order)).encode()
                    times = {label: [] for label, _ in kernels}
                    # One untimed accepted warmup per binary and workload.
                    for _, kernel in kernels:
                        measure(kernel, payload, args.timeout)
                    for run in range(args.runs):
                        for label, kernel in kernels if run % 2 == 0 else list(reversed(kernels)):
                            times[label].append(measure(kernel, payload, args.timeout))
                    for label, _ in kernels:
                        samples = times[label]
                        writer.writerow([label, size, shape, order, str(with_lambda).lower(), args.runs,
                                         f"{statistics.median(samples):.6f}", f"{min(samples):.6f}",
                                         f"{max(samples):.6f}", json.dumps(samples)])
                    sys.stdout.flush()


if __name__ == "__main__":
    main()
