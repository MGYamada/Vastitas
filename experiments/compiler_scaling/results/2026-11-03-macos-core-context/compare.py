"""Reproduce the public long-let and in-process Core checker observations."""
import argparse
import csv
import hashlib
import os
from pathlib import Path
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parents[3] / "scripts"))
from check_storage_scaling import observe, write_package


def source(size, binding):
    lines = ["let root: Int = 1;"]
    for i in range(size):
        operand = "root" if binding == "oldest" or i == 0 else f"v{i - 1}"
        lines.append(f"let v{i}: Int = {operand} + 1;")
    return "fn main() -> Int {\n" + "\n".join(lines) + f"\nv{size - 1}\n}}\n"


def build_audit(checkout, output):
    kernel = checkout / "lean-kernel"
    output.mkdir()

    def build(*args):
        subprocess.run(["lake", "env", *args], cwd=kernel, check=True)

    c_file = output / "bench.c"
    obj_file = output / "bench.o"
    build("lean", "-R", HERE, "-c", c_file, HERE / "CoreAuditBench.lean")
    build("leanc", "-O3", "-c", c_file, "-o", obj_file)
    # Link the measurement driver to the exact objects used by this kernel.
    lines = (kernel / ".lake/build/bin/vastitas-kernel.rsp").read_text().splitlines()
    if not lines[0].endswith('/Main.c.o.export"'):
        raise ValueError("unexpected kernel link response")
    response = output / "link.rsp"
    response.write_text("\n".join([f'"{obj_file}"', *lines[1:]]) + "\n")
    build("leanc", "-o", output / "audit", "@" + str(response))
    return output / "audit"


def alternating(samples):
    for run in range(samples + 1):
        labels = ("baseline", "candidate") if run % 2 == 0 else ("candidate", "baseline")
        for label in labels:
            yield run, label


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("baseline", type=Path)
    parser.add_argument("candidate", type=Path)
    parser.add_argument("output", type=Path, help="new directory for CSV files")
    args = parser.parse_args()
    trees = {"baseline": args.baseline.resolve(), "candidate": args.candidate.resolve()}
    args.output.mkdir()
    compiler = trees["baseline"] / "target/debug/vastitas"
    with tempfile.TemporaryDirectory(prefix="vastitas-core-compare-") as work:
        work = Path(work)
        with (args.output / "public.csv").open("w", newline="") as table:
            writer = csv.writer(table, lineterminator="\n")
            writer.writerow(["binding", "lets", "source_sha256", "run", "kernel", "seconds", "exit_code"])
            for binding in ("previous", "oldest"):
                for size in (128, 512, 1600):
                    program = source(size, binding)
                    manifest = write_package(work, f"{binding}-{size}", program)
                    digest = hashlib.sha256(program.encode()).hexdigest()
                    for run, label in alternating(3):
                        kernel = trees[label] / "lean-kernel/.lake/build/bin/vastitas-kernel"
                        sample = observe([str(compiler), "check", "--manifest-path", str(manifest)],
                                         {**os.environ, "VASTITAS_KERNEL": str(kernel)}, 30)
                        if sample["timed_out"] or sample["exit_code"] != 0:
                            raise RuntimeError(f"{label}/{binding}/{size}: {sample}")
                        writer.writerow([binding, size, digest, run, label, f'{sample["seconds"]:.6f}', 0])
        drivers = {label: build_audit(tree, work / label) for label, tree in trees.items()}
        with (args.output / "core.csv").open("w", newline="") as table:
            writer = csv.writer(table, lineterminator="\n")
            writer.writerow(["binding", "lets", "run", "kernel", "audit_nanoseconds"])
            for binding in ("previous", "oldest"):
                for size in (128, 512, 1600, 4096):
                    for run, label in alternating(5):
                        result = subprocess.check_output([drivers[label], str(size), binding], text=True, timeout=30)
                        writer.writerow([binding, size, run, label, int(result.strip())])


if __name__ == "__main__":
    main()
