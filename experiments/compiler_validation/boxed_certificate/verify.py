#!/usr/bin/env python3
"""Verify a live public boxed program's execution-model/bytes certificate."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import stat
import subprocess
import sys
import tempfile
import tomllib

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "official_exit"))
import fast_check as fast
from fast_check import official, require

ROOT = official.ROOT
GOAL = "VastitasProof.obligation"
THEOREM = "VastitasProof.checked"
ROOTS = [*fast.AXIOMS, "Eq.refl", "id", "VastitasOracle.BoxedCertificate.Valid.mk",
         "VastitasOracle.BoxedCertificate.printedLines", GOAL]
KINDS = {"Int": ".int", "Nat": ".nat", "Pair<Int>": "(.pair .int)", "Pair<Nat>": "(.pair .nat)"}
OPS = {f"{k}_{op}": f"(.{k} .{op})" for k in ("int", "nat") for op in ("add", "sub", "mul", "div")}
OPS.update(nat_int_div=".natIntDiv", int_nat_div=".intNatDiv", int_neg=".neg", nat_to_int=".natToInt")
for element in ("nat", "int"):
    OPS[f"{element}_pair"] = f"(.pair .{element})"
    OPS[f"{element}_pair_first"] = f"(.project .{element} true)"
    OPS[f"{element}_pair_second"] = f"(.project .{element} false)"
PROOF = """by
  refine ⟨rfl, ?_, rfl, rfl, rfl, ?_⟩
  · with_unfolding_all rfl
  · exact VastitasOracle.BoxedCertificate.printedLines code headerBytes lines rfl rfl"""


def natural(value):
    require(type(value) is int and value >= 0, "invalid SSA index")
    return str(value)


def integer(value):
    require(type(value) is str and re.fullmatch(r"0|-?[1-9][0-9]*", value, re.ASCII), "invalid integer literal")
    return value


def instruction(step):
    match step:
        case ["nat" | "int" as kind, value]:
            literal = integer(value)
            require(kind == "int" or not literal.startswith("-"), "negative natural literal")
            return f".primitive (.{kind} ({literal}))"
        case ["invoke", callee, refs]:
            return f".invoke {natural(callee)} [{', '.join(map(natural, refs))}]"
        case ["apply", op, refs]:
            return f".primitive (.apply {OPS[op]} [{', '.join(map(natural, refs))}])"
    raise ValueError("unsupported boxed instruction")


def check_manifest_inputs(wire, manifest, files, entry):
    """Follow the paths declared by the physical TOML files from the user's root."""
    by_path = {}
    for path, offset, text in files:
        by_path.setdefault(path, []).append((offset, text))
    packages = {p["source"]: p for p in wire["packages"]}
    require(len(packages) == len(wire["packages"]) and wire["root"] == str(manifest),
            "package owners differ from the physical root")
    pending = [manifest]
    seen = set()
    while pending:
        path = pending.pop()
        if path in seen:
            continue
        seen.add(path)
        rows = by_path.get(os.fsencode(path), [])
        require(len(rows) == 1 and str(path) in packages, "missing or duplicate physical package manifest")
        package = packages[str(path)]
        doc = tomllib.loads(rows[0][1])
        metadata = doc["package"]
        require(metadata["edition"] == "2026" and all(metadata[key] == package[key]
                for key in ("name", "version", "edition")), "manifest and wire package identities differ")
        module = (path.parent / metadata["root"]).resolve(strict=True)
        sources = by_path.get(os.fsencode(module), [])
        roots = [m["span"] for m in package["modules"] if not m["path"]]
        require(module.is_relative_to(path.parent) and len(roots) == 1 and
                any(base <= roots[0]["start"] <= roots[0]["end"] <= base + len(text.encode())
                    for base, text in sources), "package root module lies outside its physical input")
        if path == manifest:
            require(files[entry][0] == os.fsencode(module), "manifest and physical entry differ")
        targets = {alias: (path.parent / dep["path"] / "Vastitas.toml").resolve(strict=True)
                   for alias, dep in doc.get("dependencies", {}).items()}
        edges = package["dependencies"]
        require(len(edges) == len(targets) and {e["alias"]: e["target"] for e in edges} ==
                {alias: str(target) for alias, target in targets.items()},
                "manifest and wire dependencies differ")
        pending.extend(targets.values())
    require(len(seen) == len(packages), "wire contains a package outside the manifest closure")


def read_sources(wire, source, flat_names):
    """Build the expected layout from disk, independently of the modeled graph."""
    root = wire["root_source"]
    rows = root.get("files", [{"path": wire["file"], "offset": 0}])
    require(0 < len(rows) <= 8192, "invalid physical input count")
    names = [os.fsencode(row["path"]) if isinstance(row["path"], str) else bytes(row["path"]) for row in rows]
    if flat_names is not None:
        require(names == list(map(os.fsencode, flat_names)), "physical inputs differ from command arguments")
    else:
        require(names and names[0] == os.fsencode(source), "expected the named root manifest")
    files = []
    offset = total = 0
    entry = None
    for name, row in zip(names, rows, strict=True):
        path = source.parent / os.fsdecode(name)
        with os.fdopen(os.open(path, os.O_RDONLY | os.O_NONBLOCK), "rb") as stream:
            require(stat.S_ISREG(os.fstat(stream.fileno()).st_mode), "expected regular compilation input")
            limit = min(16 * 1024**2, 64 * 1024**2 - total)
            data = stream.read(limit + 1)
        require(len(data) <= limit, "physical source byte limit exceeded")
        text = data.decode("utf-8")
        require(row["offset"] == offset, "physical source offset differs from current files")
        if offset == root["offset"]:
            entry = len(files)
            expected = root["text"]
        else:
            expected = row["text"]
        require(text == expected, "source bytes changed during certificate preparation")
        files.append((name, offset, text))
        total += len(data)
        offset += len(data) + 1
    require(entry is not None, "missing physical entry")
    if flat_names is None:
        check_manifest_inputs(wire, source, files, entry)
    else:
        require(entry == 0, "flat entry must be the first input")
    return files, entry


def authority(revision, model, triple, layout, data, sources):
    # Only closed data is interpolated. All identifiers and proof syntax are fixed.
    quote = official.lean_string
    header_lines = data.split(b"\n", 2)
    require(len(header_lines) == 3, "incomplete printed header")
    header_bytes = list(b"\n".join(header_lines[:2]) + b"\n")
    body = header_lines[2].decode("utf-8").split("\n")
    require(len(body) >= 3 and body[0] == body[-1] == "", "noncanonical body delimiters")
    lines = ", ".join(map(quote, body[1:-1]))
    fields = [(quote(k), 'wire' if k == 'input' else official.json_term(revision[k])) for k in sorted(revision)]
    rev = ", ".join(f"({k}, {v})" for k, v in fields)
    files, entry = sources
    physical = []
    for path, offset, text in files:
        try:
            label = quote(path.decode("utf-8")) + ".toUTF8"
        except UnicodeDecodeError:
            label = f"ByteArray.mk #{list(path)}"
        physical.append(f"⟨{label}, {natural(offset)}, {quote(text)}⟩")
    functions = []
    for f in model["functions"]:
        args = ", ".join(KINDS[k] for k in f["params"])
        steps = ", ".join(map(instruction, f["ops"]))
        functions.append(f"⟨[{args}], {KINDS[f['result']]}, [{steps}], {natural(f['slot'])}⟩")
    return f"""import VastitasOracle.BoxedCertificate
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
namespace VastitasProof
open Lean VastitasKernel VastitasKernel.LLVM VastitasOracle.BoxedCertificate
def wire : Json := {official.json_term(revision['input'])}
def revision : Json := Json.mkObj [{rev}]
def sources : PhysicalSources.Layout := ⟨#[{', '.join(physical)}], {natural(entry)}⟩
def header : TargetHeader := ⟨⟨{quote(triple)}.toUTF8.data.toList, by decide⟩,
  ⟨{quote(layout)}.toUTF8.data.toList, by decide⟩⟩
def code : VastitasKernel.LLVM.ExactProgram.Code := ⟨header, #[{', '.join(functions)}], {natural(model['entry'])}⟩
def headerBytes : List UInt8 := {header_bytes}
def lines : List String := [{lines}]
def subject : Subject := ⟨wire, revision, sources, header, code,
  headerBytes ++ ("\\n" ++ String.intercalate "\\n" lines ++ "\\n").toUTF8.data.toList, {integer(model['value'])}⟩
def obligation : Prop := Valid subject
end VastitasProof
"""


def certificate(proof=PROOF):
    return f"""import Authority
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
namespace VastitasProof
theorem checked : obligation := {proof}
#print axioms checked
end VastitasProof
"""


def snapshot(candidate, authority_path, destination):
    """Authenticate the whole authority prefix, then seal the supplied proof for both checks."""
    digest = hashlib.sha256()
    with os.fdopen(os.open(candidate, os.O_RDONLY | os.O_NONBLOCK), "rb") as src, authority_path.open("rb") as prefix, destination.open("xb") as out:
        info = os.fstat(src.fileno())
        require(stat.S_ISREG(info.st_mode) and prefix.seek(0, os.SEEK_END) < info.st_size <= fast.MAX_EXPORT,
                "expected bounded regular certificate with a proof suffix")
        prefix.seek(0)
        total = 0
        while block := src.read(fast.CHUNK):
            expected = prefix.read(len(block))
            require(block.startswith(expected), "declaration environment differs from current input")
            total += len(block)
            require(total <= info.st_size, "certificate grew during snapshot")
            digest.update(block)
            out.write(block)
        require(total == info.st_size and not prefix.read(1), "truncated certificate")
    return {"bytes": total, "sha256": digest.hexdigest()}


def environment(work, prefix):
    search = [work, ROOT / "lean/.lake/build/lib/lean", ROOT / "lean-kernel/.lake/build/lib/lean", prefix / "lib/lean"]
    return official.proof_environment(prefix, *search)


def verify(args, work, report):
    prefix = fast.pinned_lean("leanchecker") if args.mode == "official" else fast.pinned_tools()
    lean = prefix / "bin/lean"
    env = environment(work, prefix)
    reduction = official.load_reduction()

    def phase(name, command, output=None, *, run_from=None):
        result = reduction.measure(list(map(str, command)), work, env, name, args.timeout,
                                   stdout=output, run_from=run_from)
        report["phases"].append(result)
        if result["status"] != "passed":
            logs = (work / (name + ".stderr")).read_text(errors="replace")
            if output is None:
                logs += (work / (name + ".stdout")).read_text(errors="replace")
            reason = "wall-time limit exceeded" if result["timed_out"] else logs[:1200].strip() or f"exit {result['exit_code']}"
            raise ValueError(f"{name} failed: {reason}")
        return (work / (name + ".stdout")).read_text() if output is None else None

    source = args.manifest_path.resolve(strict=True) if args.manifest_path else args.source.absolute()
    frontend = str(args.frontend.resolve(strict=True))
    cmd = [frontend, "check", *(["--manifest-path"] if args.manifest_path else []), source.name]
    libraries = [os.path.relpath(lib.absolute(), source.parent) for lib in args.lib]
    for library in libraries:
        cmd.extend(["--lib", library])
    revision_path = work / "revision.json"
    phase("revision", [*cmd, "--print-function-revision"], revision_path, run_from=source.parent)
    revision = json.loads(revision_path.read_bytes(), object_pairs_hook=fast.unique_fields)
    require(revision["input"]["version"] == 10, "expected wire 10")
    sources = read_sources(revision["input"], source, None if args.manifest_path else [source.name, *libraries])
    report["physical_inputs"] = len(sources[0])
    preview = work / "preview.ll"
    phase("preview", [*cmd, "--llvm-preview", "--expect-function-revision", revision_path,
                      "--target-triple", args.target_triple, "--data-layout", args.data_layout], preview,
          run_from=source.parent)
    data = preview.read_bytes()
    model = json.loads(phase("capture", [lean, "--run", HERE / "Capture.lean", revision_path,
                                         args.target_triple, args.data_layout]), object_pairs_hook=fast.unique_fields)
    require(model["ir"].encode("utf-8") == data, "captured model and public LLVM bytes differ")
    report.update(bytes=len(data), llvm_sha256=official.digest(data), revision_sha256=official.digest(revision_path.read_bytes()),
                  functions=len(model["functions"]), integer_result=integer(model["value"]))
    (work / "Authority.lean").write_text(authority(revision, model, args.target_triple, args.data_layout, data, sources))
    phase("authority", [lean, "-DwarningAsError=true", "-o", "Authority.olean", "Authority.lean"])
    if args.candidate is None:
        (work / "Certificate.lean").write_text(certificate())
        axioms = phase("proof", [lean, "-DwarningAsError=true", "-o", "Certificate.olean", "Certificate.lean"])
        official_axioms = re.fullmatch(r"'VastitasProof.checked' (?:does not depend on any axioms|depends on axioms: \[([^\]]*)\])\s*", axioms)
        require(official_axioms and set(filter(None, (official_axioms.group(1) or "").split(", "))) <= official.ALLOWED,
                "unexpected proof axioms")
    report["standard_environment"] = fast.standard(prefix, work)
    baseline = work / "authority.ndjson"
    closure, roots = fast.export_roots(work, env, prefix, baseline, "Authority", ROOTS, GOAL, "def",
                                       "boxed", args.timeout, reduction.measure)
    report["authority_closure"] = closure
    supplied = args.candidate
    if supplied is None:
        supplied = work / "generated.ndjson"
        phase("export_proof", [prefix / "bin/leanexport", "Certificate", "--", *roots, THEOREM], supplied)
    sealed = work / "sealed.ndjson"
    report["certificate"] = snapshot(supplied, baseline, sealed)
    stats = fast.inspect_closure(sealed, THEOREM, proof_suffix=(closure["records"], tuple(GOAL.split("."))))
    report["exported_declarations"] = stats["declarations"]
    if args.mode == "official":
        # --from-export replays the constMap in an empty official kernel
        # environment and checks the reconstructed quotient primitives.
        out = phase("official_export", [prefix / "bin/leanchecker", "--from-export", sealed])
        require(out == "Lean default kernel accepts the solution\n" and not (work / "official_export.stderr").read_bytes(),
                "missing official replay of the complete export")
        report["official_replay"] = True
    else:
        policy = work / "nanoda.json"
        policy.write_text(json.dumps(fast.policy_for(sealed)))
        out = phase("nanoda", ["/bin/sh", "-c", 'ulimit -S -s 49152 || exit 2; exec "$@"', "nanoda-stack",
                               prefix / "bin/nanoda_bin", policy])
        count = reduction.checked_count(out, (work / "nanoda.stderr").read_text(), stats["declarations"])
        require(count is not None, "nanoda did not confirm the complete declaration count")
        report["checked_declarations"] = count
    if args.save_candidate:
        with tempfile.TemporaryDirectory(dir=args.save_candidate.parent) as staging:
            complete = Path(staging) / "certificate.ndjson"
            shutil.copyfile(sealed, complete)
            os.link(complete, args.save_candidate)
    return roots


def main():
    p = argparse.ArgumentParser(description=__doc__)
    sources = p.add_mutually_exclusive_group(required=True)
    sources.add_argument("--manifest-path", type=Path)
    sources.add_argument("--source", type=Path)
    p.add_argument("--lib", action="append", type=Path, default=[], help="flat source library, in load order")
    p.add_argument("--frontend", type=Path, default=ROOT / "target/debug/vastitas")
    p.add_argument("--target-triple", required=True)
    p.add_argument("--data-layout", required=True)
    p.add_argument("--mode", choices=["official", "fast"], required=True)
    p.add_argument("--candidate", type=Path)
    p.add_argument("--save-candidate", type=Path)
    p.add_argument("--timeout", type=int, default=120, help="wall seconds per worker")
    args = p.parse_args()
    if args.manifest_path and args.lib:
        p.error("--lib requires a flat source")
    if args.timeout <= 0:
        p.error("positive timeout required")
    report = {"mode": args.mode, "endpoint": "boxed execution model and complete LLVM bytes",
              "verifier": "Lean 4.35.0 leanchecker" if args.mode == "official" else "nanoda 0.4.19",
              "target_triple": args.target_triple, "data_layout": args.data_layout,
              "runtime_abi": "boxed integer shim v1", "native_generated": False,
              "official_replay": False, "phases": []}
    try:
        with tempfile.TemporaryDirectory(prefix="vastitas-boxed-proof-") as tmp:
            verify(args, Path(tmp), report)
        report["status"] = "passed"
    except (OSError, ValueError, KeyError, subprocess.SubprocessError) as exc:
        report.update(status="rejected", reason=str(exc))
    print(json.dumps(report, indent=2))
    return report["status"] != "passed"


if __name__ == "__main__":
    sys.exit(main())
