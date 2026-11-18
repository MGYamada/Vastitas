#!/usr/bin/env python3
"""Run artifact, environment and standard-axiom substitutions against a provisioned fixture."""
import argparse
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
from types import SimpleNamespace

import fast_check as fast
import run as official


def different_record(data, key, edit, *, last=False):
    rows = data.splitlines(keepends=True)
    indices = reversed(range(len(rows))) if last else range(len(rows))
    for i in indices:
        row = json.loads(rows[i])
        if key in row:
            edit(row[key])
            rows[i] = json.dumps(row, separators=(",", ":")).encode() + b"\n"
            return b"".join(rows)
    raise ValueError("expected genuine exporter record")


def different_index(record, field):
    # Keep the decimal representation width; the certificate size remains exact.
    n = record[field]
    record[field] = n - 1 if n % 10 else n + 1


def qualify(args):
    prefix = fast.pinned_tools()
    reduction = official.load_reduction()
    source = official.DEFAULT_SOURCE
    authority = args.authority.resolve()
    certificate = authority / "printed-bytes.ndjson"
    data = certificate.read_bytes()
    theorem = "printed"
    opts = SimpleNamespace(frontend=args.frontend, source=source, module=official.DEFAULT_LL,
                           value=-(2**128+1), timeout=30, stack_kib=49152)
    report = {"checker": "nanoda 0.4.19", "profile": "printed-bytes", "tests": {}}
    genuine = fast.audit("printed-bytes", authority, certificate, opts, prefix, reduction)
    fast.require(genuine["status"] == "passed" and genuine["checked_declarations"] == 1371,
                 f"genuine certificate control failed: {genuine.get('reason')}")
    report["genuine_certificate_control"] = {key: genuine[key] for key in
        ("live", "export", "main_stack_kib", "timeout_seconds", "nanoda", "checked_declarations", "status")}
    with tempfile.TemporaryDirectory(prefix="vast-fast-negative-") as tmp:
        tmp = Path(tmp)
        env = {**os.environ, "LEAN_PATH": str(tmp) + os.pathsep + str(prefix / "lib/lean"), "LEAN_NUM_THREADS": "1"}
        # A valid, independently type-checked export with exactly the requested theorem name.
        (tmp / "Other.lean").write_text("theorem printed : True := True.intro\n")
        subprocess.run([prefix / "bin/lean", "--root", ".", "-o", "Other.olean", "Other.lean"],
                       cwd=tmp, env=env, timeout=30, check=True)
        other = tmp / "other.ndjson"
        with other.open("wb") as out:
            subprocess.run([prefix / "bin/leanexport", "Other", "--", *fast.AXIOMS, theorem],
                           cwd=tmp, env=env, stdout=out, check=True, timeout=30)
        unrelated = fast.inspect_closure(other, theorem)
        config = tmp / "other.json"
        config.write_text(json.dumps(fast.policy_for(other)))
        worker = reduction.measure([str(prefix / "bin/nanoda_bin"), str(config)], tmp, env, "nanoda_other", 30)
        expected = f"Checked {unrelated['declarations']} declarations with no errors\n"
        fast.require(worker["status"] == "passed" and (tmp / "nanoda_other.stdout").read_text() == expected and
                     not (tmp / "nanoda_other.stderr").read_text(), "negative control did not independently check")
        report["standalone_other_theorem_checked"] = unrelated["declarations"]

        def reject(label, phase, reason, *, candidate=certificate, inputs=opts, reference=authority):
            fast.require(candidate.is_file(), f"{label}: missing candidate certificate")
            entry = fast.audit("printed-bytes", reference, candidate, inputs, prefix, reduction)
            outcome = (entry["status"], entry.get("rejection_phase"), entry.get("reason"))
            fast.require(outcome == ("rejected", phase, reason) and "nanoda" not in entry,
                         f"{label}: unexpected outcome {outcome}")
            report["tests"][label] = {"phase": entry["rejection_phase"], "reason": entry["reason"]}

        comparison = "certificate-comparison"
        size_error = "certificate must be a regular file of the complete authority size"
        content_error = "proof or transitive declarations differ"
        reject("independently-valid-same-name-foreign-statement", comparison, size_error, candidate=other)
        false_authority = tmp / "false-authority"
        false_authority.mkdir()
        for filename in ("Inputs.lean", "ExpectedRevision.lean"):
            (false_authority / filename).write_bytes((authority / filename).read_bytes())
        (false_authority / "printed-bytes.ndjson").write_bytes(other.read_bytes())
        reject("same-counterfeit-authority-and-candidate", "qualified-image", "unqualified reference image",
               candidate=other, reference=false_authority)
        for label, reason, forged in (
            ("changed-standard-axiom-statement", content_error,
             different_record(data, "axiom", lambda record: different_index(record, "type"))),
            ("changed-proof-with-retained-theorem-type", content_error,
             different_record(data, "thm", lambda record: different_index(record, "value"), last=True)),
            ("changed-transitive-definition", content_error,
             different_record(data, "def", lambda record: different_index(record, "value"))),
            ("truncated-valid-prefix", size_error, data[:data[:-1].rfind(b"\n") + 1]),
            ("unknown-trailing-declaration", size_error, data + b'{"future":true}\n'),
        ):
            path = tmp / (label + ".ndjson")
            path.write_bytes(forged)
            reject(label, comparison, reason, candidate=path)
        # Same byte size: a digest of just the length or the module name cannot satisfy the binding.
        changed = bytearray(data)
        offset = data.index(b'"str":"Iff"')
        changed[offset + 7] = ord("X")
        path = tmp / "same-length.ndjson"
        path.write_bytes(changed)
        reject("same-length-environment-mutation", comparison, content_error, candidate=path)
        try:
            fast.inspect_closure(path, theorem)
        except ValueError as exc:
            fast.require(str(exc) == "standard axiom closure mismatch", "unexpected axiom rejection")
        else:
            raise ValueError("mutated independent axiom anchor accepted")
        # Exercise the graph policy itself, independently of reference byte equality.
        name_count = sum(1 for line in data.splitlines() if "in" in json.loads(line))
        expr_count = sum(1 for line in data.splitlines() if "ie" in json.loads(line))
        def named(text):
            return {"in": name_count + 1, "str": {"pre": 0, "str": text}}
        axiom = {"axiom": {"name": name_count + 1, "levelParams": [], "type": 0, "isUnsafe": False}}
        axiom_error = "nonstandard or ambiguously named axiom"
        extras = [
            ("dotted-component-axiom-alias", axiom_error, [named("Classical.choice"), axiom]),
            ("unused-unapproved-axiom", axiom_error, [named("Unapproved"), axiom]),
            ("missing-constant-declaration", "missing 1 transitive declarations, including Missing",
             [named("Missing"), {"ie": expr_count, "const": {"name": name_count + 1, "us": []}}]),
            ("unsupported-expression-form", "unsupported expression future", [{"ie": expr_count, "future": {}}]),
            ("duplicate-name-identifier", "invalid name record", [{"in": 1, "str": {"pre": 0, "str": "alias"}}]),
        ]
        for label, reason, extra in extras:
            forged = tmp / (label + ".ndjson")
            forged.write_bytes(data + b"".join(json.dumps(row, separators=(",", ":")).encode() + b"\n" for row in extra))
            try:
                fast.inspect_closure(forged, theorem)
            except ValueError as error:
                fast.require(str(error) == reason, f"{label}: unexpected declaration-closure rejection {error}")
                report["tests"][label] = {"phase": "declaration-closure", "reason": str(error)}
            else:
                raise ValueError("accepted incomplete or ambiguous declarations: " + label)
        llvm = tmp / "changed.ll"
        image = bytearray(official.DEFAULT_LL.read_bytes())
        image[-1] ^= 1
        llvm.write_bytes(image)
        reject("one-altered-llvm-byte", "live-subject", "supplied LLVM bytes differ from the public compiler output",
               inputs=SimpleNamespace(**{**vars(opts), "module": llvm}))
        source_copy = tmp / source.name
        source_copy.write_bytes(source.read_bytes() + b"\n")
        target_args = ["--target-triple", genuine["live"]["target_triple"], "--data-layout", genuine["live"]["data_layout"]]
        compiled = subprocess.check_output([args.frontend.resolve(), "check", source_copy.name,
                                            "--llvm-preview", *target_args], cwd=source_copy.parent, timeout=30)
        fast.require(compiled == opts.module.read_bytes(), "changed source no longer gives the same LLVM image")
        revision_error = "the complete public revision differs from the closed artifact"
        reject("different-source-same-exit", "live-subject", revision_error,
               inputs=SimpleNamespace(**{**vars(opts), "source": source_copy}))
        reject("different-claimed-integer", "live-subject",
               "live source, wire, target, emitted bytes or claimed value differs from Inputs.lean",
               inputs=SimpleNamespace(**{**vars(opts), "value": 255}))
        # Keep the genuine source input and output bytes; alter one public nominal method field.
        original = json.loads(subprocess.check_output([str(args.frontend.resolve()), "check", source.name,
                                                       "--print-function-revision"], cwd=source.parent))
        original["families"][0]["definition"] += 1
        wrapper = tmp / "revised-frontend"
        wrapper.write_text("#!" + sys.executable + "\nimport sys\n"
                           + "if '--print-function-revision' in sys.argv:\n    print(" +
                           repr(json.dumps(original)) + ")\nelse:\n    sys.stdout.buffer.write(" +
                           repr(official.DEFAULT_LL.read_bytes()) + ")\n")
        wrapper.chmod(0o700)
        reject("forged-current-revision-identical-source-and-bytes", "live-subject", revision_error,
               inputs=SimpleNamespace(**{**vars(opts), "frontend": wrapper}))
    return report


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--authority", required=True, type=Path)
    parser.add_argument("--frontend", type=Path, default=official.ROOT / "target/debug/vastitas")
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = json.dumps(qualify(args), indent=2) + "\n"
    if args.output:
        args.output.write_text(result)
    else:
        print(result, end="")
