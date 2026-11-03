"""Check matched public inputs against two already built kernels."""

import argparse
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import sys
import tempfile

sys.path.insert(0, str(Path(__file__).resolve().parents[4] / "scripts"))
from check_namespace_scaling import source
from check_storage_scaling import observe, write_package


def module_chain(name, length):
    lines = [f"mod {name} {{"]
    lines.extend(f"use self::a{i + 1} as a{i};" for i in range(length))
    lines.extend([f"fn a{length}(x: Int) -> Int {{ x + 1 }}", "}", ""])
    return "\n".join(lines)


def unused_calls(count):
    lines = [f"use self::a{i + 1} as a{i};" for i in range(600)]
    lines.append("fn a600(x: Int) -> Int { x + 1 }")
    for index in range(count):
        lines.append(f"fn f{index}() -> Int {{")
        lines.extend(f"let v{i} = a0(41);" for i in range(100))
        lines.extend(["v99", "}"])
    return "\n".join(lines + ["fn main() -> Int { 42 }", ""])


def wide_dispatch():
    lines = ["generic wide(a,b,c,d,e,f) { domain (Int,Int,Int,Int,Int,Int); }",
             "method wide(a:Any,b:Any,c:Any,d:Any,e:Any,f:Any) -> Int {"]
    lines.extend(f"let value{i}: Int = 0 + 1;" for i in range(300))
    return "\n".join(lines + ["0 }", "fn main() -> Int { 0 }", ""])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("baseline", "candidate", "output"):
        parser.add_argument(name, type=Path)
    args = parser.parse_args()
    cli = args.baseline.resolve() / "target/debug/vastitas"
    kernels = {label: tree.resolve() / "lean-kernel/.lake/build/bin/vastitas-kernel"
               for label, tree in (("baseline", args.baseline), ("candidate", args.candidate))}
    cases = [
        ("one-1000", source(1000, 1), ""),
        ("shared-600", source(600, 300), ""),
        ("two-1050", module_chain("left", 1050) + module_chain("right", 1050)
         + "fn main() -> Int { 42 }\n", "program-wide namespace import validation"),
        ("many-references", unused_calls(24), "program-wide namespace resolution"),
        ("more-references", unused_calls(72), "program-wide namespace resolution"),
        ("dispatch-4096", wide_dispatch(), "program-wide elaboration"),
    ]
    report = {"platform": platform.platform(), "deadline_seconds": 20,
              "cli_sha256": hashlib.sha256(cli.read_bytes()).hexdigest(),
              "kernel_sha256": {k: hashlib.sha256(p.read_bytes()).hexdigest()
                                for k, p in kernels.items()}, "cases": []}
    with tempfile.TemporaryDirectory() as temporary:
        for index, (name, program, expected) in enumerate(cases):
            manifest = write_package(temporary, name, program)
            case = {"name": name, "source_sha256": hashlib.sha256(program.encode()).hexdigest(),
                    "runs": {}}
            for label in (list(kernels) if index % 2 == 0 else list(reversed(kernels))):
                result = observe([str(cli), "check", "--manifest-path", str(manifest)],
                                 {**os.environ, "VASTITAS_KERNEL": str(kernels[label])}, 20)
                match = re.search(r"\b(E_[A-Z_]+):[^\n]*", result["stderr"])
                diagnostic = match.group() if match else ""
                case["runs"][label] = {"seconds": result["seconds"], "exit_code": result["exit_code"],
                                       "timed_out": result["timed_out"], "diagnostic": diagnostic}
                if label == "candidate":
                    accepted = result["exit_code"] == 0 and not diagnostic and not expected
                    limited = bool(expected) and result["exit_code"] != 0 and expected in diagnostic
                    if result["timed_out"] or not (accepted or limited):
                        raise RuntimeError(f"{name}: {result}")
            report["cases"].append(case)
            args.output.write_text(json.dumps(report, indent=2) + "\n")
            print(name, case["runs"], flush=True)


if __name__ == "__main__":
    main()
