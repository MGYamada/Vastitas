#!/usr/bin/env python3
"""Measure real kernel acceptance for parameterized call chains (issue #141)."""
import argparse
import json
import pathlib
import statistics
import subprocess
import time

ROOT = pathlib.Path(__file__).resolve().parents[1]
SPAN = dict(start=0, end=0, line=1, column=1)
INT = dict(kind="named", name="Int")


def expression(kind, **fields):
    return dict(kind=kind, span=SPAN, **fields)


def program(count, with_lambda):
    functions = []
    for index in range(count):
        result = expression("variable", name="x")
        if index + 1 < count:
            result = expression("call", callee=f"f{index + 1}", args=[result])
        functions.append(dict(name=f"f{index}", params=[dict(name="x", ty=INT, span=SPAN)],
                              return_type=INT, body=dict(statements=[], result=result, span=SPAN), span=SPAN))
    if with_lambda:
        value = expression("lambda", params=[dict(name="x", ty=INT, span=SPAN)],
                           return_type=INT, body=dict(statements=[], result=expression("variable", name="x"), span=SPAN))
        functions.append(dict(name="unused", params=[], return_type=INT,
                              body=dict(statements=[dict(kind="let", name="g", annotation=None, value=value, span=SPAN)],
                                        result=expression("integer", value="0"), span=SPAN), span=SPAN))
    return dict(version=2, file="benchmark.vast", functions=functions, generics=[], methods=[])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--kernel", type=pathlib.Path, default=ROOT / "lean-kernel/.lake/build/bin/vastitas-kernel")
    parser.add_argument("--runs", type=int, default=3)
    args = parser.parse_args()
    print("functions,lambda,median_seconds")
    for size in (2000, 4000, 8000):
        for with_lambda in (False, True):
            payload = json.dumps(program(size, with_lambda)).encode()
            times = []
            for _ in range(args.runs):
                start = time.monotonic()
                output = subprocess.run([str(args.kernel), "check"], input=payload, capture_output=True, timeout=60, check=True)
                response = json.loads(output.stdout)
                if not response["ok"]:
                    raise RuntimeError(response)
                times.append(time.monotonic() - start)
            print(f"{size},{str(with_lambda).lower()},{statistics.median(times):.3f}")


if __name__ == "__main__":
    main()

