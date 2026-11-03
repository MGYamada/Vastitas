"""Compare resource work admission on identical public source packages."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[4]
sys.path.insert(0, str(ROOT / "scripts"))
from check_storage_scaling import observe, source, write_package

CASES = [
    ("static", "wrapped_reads", 200, 30), ("runtime", "wrapped_reads", 200, 30),
    ("static", "reborrow_chain", 512, 0), ("runtime", "reborrow_chain", 512, 0),
    ("static", "allocate_drop", 512, 0), ("static", "write_children", 64, 0),
    ("static", "write_children", 256, 0), ("runtime", "read_loans", 1300, 0),
    ("static", "wrapped_reads", 200, 90), ("runtime", "wrapped_reads", 200, 90),
    ("static", "borrowed_forward", 0, 32), ("static", "borrowed_forward", 0, 48),
]


def borrowed(depth):
    parts = ["resource fn f0(x: Read<F64, 1, 1>) -> Unit { value { () } }"]
    for i in range(1, depth + 1):
        parts.append(f"resource fn f{i}(x: Read<F64, 1, 1>) -> Unit {{ call f{i-1}(x) -> (); value {{ () }} }}")
    parts.append("resource fn main() -> Int { allocate d: F64[1]; borrow w = write(d, layout(0,1,1,1,false)); "
                 "fill(w, f64_bits(0)); release(w); borrow x = read(d, layout(0,1,1,1,false)); "
                 f"call f{depth}(x) -> (); release(x); drop(d); value {{ 0 }} }}")
    return "\n".join(parts) + "\n"


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("baseline", type=Path)
    parser.add_argument("candidate", type=Path)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    cli = args.baseline.resolve() / "target/debug/vastitas"
    kernels = {k: v.resolve() / "lean-kernel/.lake/build/bin/vastitas-kernel"
               for k, v in (("baseline", args.baseline), ("candidate", args.candidate))}
    report = {"cli_sha256": digest(cli), "kernel_sha256": {k: digest(v) for k, v in kernels.items()}, "cases": []}
    with args.output.open("x") as out, tempfile.TemporaryDirectory(prefix="vastitas-resource-policy-") as work:
        for i, (profile, shape, size, depth) in enumerate(CASES):
            src = borrowed(depth) if shape == "borrowed_forward" else source(shape, size, profile, depth)
            manifest = write_package(Path(work), f"case-{i}", src)
            case = dict(profile=profile, shape=shape, size=size, depth=depth,
                        source_sha256=hashlib.sha256(src.encode()).hexdigest(), runs={})
            for label in (("baseline", "candidate") if i % 2 == 0 else ("candidate", "baseline")):
                result = observe([str(cli), "check", "--manifest-path", str(manifest)],
                                 {**os.environ, "VASTITAS_KERNEL": str(kernels[label])}, 20)
                message = next((line.split(": E_", 1)[1] for line in result["stderr"].splitlines()
                                if ": E_" in line), "")
                case["runs"][label] = dict(seconds=result["seconds"], exit_code=result["exit_code"],
                                           timed_out=result["timed_out"], diagnostic="E_" + message if message else "")
            report["cases"].append(case)
        json.dump(report, out, indent=2)
        out.write("\n")


if __name__ == "__main__":
    main()
