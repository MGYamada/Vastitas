#!/usr/bin/env python3
"""Compare the public S3 library with its Lean model and the pinned host backend."""
import argparse
import itertools
import json
from pathlib import Path
import shutil
import subprocess
import tempfile

from run import HERE, ROOT, LEAN_COMMIT, capture, digest, emitter_comparison
from run_table import check_changed_handoff


def execute(work, backend, module, inputs):
    readback = work / "readback.ll"
    shutil.copyfile(module, readback)
    obj = work / "s3.o"
    capture([backend, "emit", module, readback, obj])
    probe = work / "main.c"
    probe.write_text(
        '#include <stdint.h>\n#include <inttypes.h>\n#include <stdio.h>\n'
        'extern uint32_t vq_lookup2(uint32_t, uint32_t);\n'
        'int main(void) { uint32_t g, f;\n'
        '  while (scanf("%" SCNu32 " %" SCNu32, &g, &f) == 2)\n'
        '    printf("%" PRIu32 "\\n", vq_lookup2(g, f));\n'
        '  return !feof(stdin);\n}\n')
    exe = work / "s3"
    capture(["cc", "-std=c11", "-Wall", "-Wextra", "-Werror", probe, obj, "-o", exe])
    native = subprocess.run([exe], input="".join(f"{g} {f}\n" for g, f in inputs),
                            text=True, capture_output=True, check=True).stdout.strip()
    return native, obj.stat().st_size


def run(frontend, backend, lean, llvm):
    target = dict(line.split("=", 1) for line in capture([backend, "describe"]).splitlines())
    if target["llvm"] != "23.1.4" or capture([llvm / "bin/llvm-config", "--version"]) != target["llvm"]:
        raise ValueError("expected pinned LLVM 23.1.4")
    if LEAN_COMMIT not in capture([lean / "bin/lean", "--version"]):
        raise ValueError("unexpected Lean version")
    fixture = ROOT / "llvm/fixtures/S3Composition.vast"
    reference = HERE / "S3Comparison.lean"
    with tempfile.TemporaryDirectory(prefix="vastitas-llvm-binary-") as tmp:
        work = Path(tmp)
        library = work / "library"
        library.mkdir()
        shutil.copyfile(fixture, library / "main.vast")
        manifest = library / "Vastitas.toml"
        manifest.write_text('[package]\nname = "s3_composition"\nversion = "0.1.0"\n'
                            'edition = "2026"\nroot = "main.vast"\n')
        result = subprocess.run([frontend, "check", "--manifest-path", manifest, "--llvm-preview",
                                 "--target-triple", target["triple"], "--data-layout", target["layout"]],
                                cwd=ROOT, check=True, stdout=subprocess.PIPE)
        module = work / "s3.ll"
        module.write_bytes(result.stdout)
        # The target header is part of the corpus theorem. Other hosts emit their own header.
        corpus_target = json.loads((HERE / "results/macos-arm64/unary-table.json").read_bytes())["target"]
        if target == corpus_target and result.stdout != (ROOT / "llvm/src/s3-composition.ll").read_bytes():
            raise ValueError("public preview differs from the retained corpus")

        # Generated Lean/C calls the same function from an ordinary client package.
        app = work / "app"
        app.mkdir()
        (app / "Vastitas.toml").write_text('[package]\nname = "s3_client"\nversion = "0.1.0"\n'
                                           'edition = "2026"\nroot = "main.vast"\n'
                                           '[dependencies]\nlib = { path = "../library" }\n')
        perms = list(itertools.permutations(range(3)))
        tags = ["p" + "".join(map(str, p)) for p in perms]
        def composition(g, f):
            return perms.index(tuple(perms[g][i] for i in perms[f]))
        valid = list(itertools.product(range(6), repeat=2))
        comparisons = [f"composeArrow(S3::{tags[g]}, S3::{tags[f]}) == S3::{tags[composition(g, f)]}"
                       for g, f in valid]
        (app / "main.vast").write_text("use lib::S3;\nuse lib::composeArrow;\nfn main() -> Int { if " +
                                       " &&\n".join(comparisons) + " { 0 } else { 1 } }\n")
        capture([frontend, "build", "--manifest-path", app / "Vastitas.toml", "-o", app / "exe"], cwd=work)
        capture([app / "exe"])

        changed = []
        for name, old, new in (("row-bound", b"icmp ult", b"icmp ule"),
                               ("stride", b"mul i32 %row, u0x0006", b"mul i32 %row, u0x0005"),
                               ("incoming-guard", b"and i1", b"or i1"),
                               ("miss", b"ret i32 -1", b"ret i32 -2")):
            data = result.stdout.replace(old, new, 1)
            if data == result.stdout:
                raise ValueError(f"missing mutation marker {old!r}")
            path = work / f"{name}.ll"
            path.write_bytes(data)
            check_changed_handoff(backend, module, path, work / f"{name}.o")
            changed.append(path)

        model = capture([lean / "bin/lake", "-d", ROOT / "lean-kernel", "env", "lean", "--run",
                         HERE / "BinaryProbe.lean", module, *changed], cwd=ROOT)
        oracle = capture([lean / "bin/lean", "--run", reference])
        words = [0, 1, 2, 3, 4, 5, 6, 7, 0xFFFFFFFF]
        inputs = list(itertools.product(words, repeat=2))
        native, object_bytes = execute(work, backend, module, inputs)
        expected = [composition(g, f) if g < 6 and f < 6 else 0xFFFFFFFF for g, f in inputs]
        if native != model or native != oracle or list(map(int, native.splitlines())) != expected:
            raise ValueError("model, ordinal ABI and independent permutation composition differ")
        swapped = work / "swapped"
        swapped.mkdir()
        original = fixture.read_text()
        if original.count(">(g, f)") != 1:
            raise ValueError("expected one binary composition site")
        (library / "main.vast").write_text(original.replace(">(g, f)", ">(f, g)"))
        reverse = subprocess.run([frontend, "check", "--manifest-path", manifest, "--llvm-preview",
                                  "--target-triple", target["triple"], "--data-layout", target["layout"]],
                                 cwd=ROOT, check=True, stdout=subprocess.PIPE)
        reversed_module = swapped / "s3-reversed.ll"
        reversed_module.write_bytes(reverse.stdout)
        if b"@vq_lookup2(i32 %col, i32 %row)" not in reverse.stdout:
            raise ValueError("reversed source operands did not reach the foreign ABI")
        reversed_native, reversed_object = execute(swapped, backend, reversed_module, inputs)
        reversed_model = capture([lean / "bin/lake", "-d", ROOT / "lean-kernel", "env", "lean", "--run",
                                  HERE / "BinaryProbe.lean", reversed_module], cwd=ROOT)
        if (reversed_native != reversed_model or list(map(int, reversed_native.splitlines())) !=
                [composition(f, g) if g < 6 and f < 6 else 0xFFFFFFFF for g, f in inputs]):
            raise ValueError("reversed source operands or modeled pair differ")
        comparison = emitter_comparison(lean)
        if "LLVM" in json.loads(capture([lean / "bin/lean", "--features"])):
            bitcode = work / "reference.bc"
            emitted = subprocess.run([lean / "bin/lean", "-b", bitcode, reference], capture_output=True)
            if emitted.returncode == 0 and bitcode.is_file():
                text = work / "reference.ll"
                dis = subprocess.run([llvm / "bin/llvm-dis", bitcode, "-o", text], capture_output=True)
                if dis.returncode == 0 and text.is_file():
                    comparison.update(executed=True, disassembled_sha256=digest(text))
                else:
                    comparison["execution_gap"] = "reference bitcode disassembly failed"
            else:
                comparison["execution_gap"] = "reference bitcode emission failed"
        else:
            comparison["execution_gap"] = "pinned Lean binary reports no LLVM feature"
        return {"status": "passed", "target": target, "source_sha256": digest(fixture),
                "source_function": "composeArrow", "module_bytes": len(result.stdout),
                "module_sha256": digest(module), "object_bytes": object_bytes,
                "reversed": {"module_sha256": digest(reversed_module), "object_bytes": reversed_object,
                             "matched_pairs": len(inputs)},
                "reference_sha256": digest(reference), "ordinals_per_axis": words,
                "in_domain_pairs": len(valid), "foreign_pairs": len(inputs) - len(valid),
                "generated_lean_c_pairs": len(valid), "results": expected,
                "rejected_by_parser_and_handoff": [p.stem for p in changed],
                "emitter_comparison": comparison}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    for flag in ("--frontend", "--backend", "--lean-prefix", "--llvm-prefix"):
        parser.add_argument(flag, type=Path, required=True)
    args = parser.parse_args()
    print(json.dumps(run(args.frontend.resolve(), args.backend.resolve(),
                         args.lean_prefix.resolve(), args.llvm_prefix.resolve()), indent=2))
