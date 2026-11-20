#!/usr/bin/env python3
"""Exercise the live proof using the complete boxed program from the LLVM corpus."""
from argparse import ArgumentParser, Namespace
import filecmp
import json
from pathlib import Path
import subprocess
import tempfile

import verify
from verify import fast, require


def run(work, suite):
    # Both modes consume the same public path, bytes, target and function revision.
    source = work / "main.vast"
    source.write_bytes((verify.ROOT / "llvm/fixtures/BoxedProgram.vast").read_bytes())
    target = json.loads(verify.official.TARGET_REPORT.read_bytes())["target"]
    args = Namespace(source=source, lib=[], manifest_path=None, frontend=verify.ROOT / "target/debug/vastitas",
                     mode="official", candidate=None, save_candidate=None, timeout=120,
                     target_triple=target["triple"], data_layout=target["layout"])

    def check(label, mode, *, candidate=None, rejection=None):
        private = work / label
        private.mkdir()
        args.mode, args.candidate = mode, candidate
        report = {"phases": []}
        try:
            roots = verify.verify(args, private, report)
        except ValueError as e:
            if rejection is None or rejection not in str(e):
                raise
            print(f"{label} rejected ({rejection})", flush=True)
            return report, None
        require(rejection is None, f"{label} accepted an invalid candidate")
        print(f"{label} passed ({report['bytes']} LLVM bytes, "
              f"{report['exported_declarations']} exported declarations)", flush=True)
        return report, roots

    if suite == "inputs":
        check_physical_inputs(work, args, source, check)
        return
    if suite == "assembly":
        check_borrowed_operator(work, args, check)
        return

    official, _ = check("official", "official")
    generated, roots = check("fast", "fast")
    for key in ("bytes", "llvm_sha256", "revision_sha256", "integer_result"):
        require(official[key] == generated[key], "modes disagree on " + key)
    require(official["functions"] == 4 and int(official["integer_result"]) == (-2 * (2**128 + 1)) // 3,
            "incorrect direct-call module or unprojected Euclidean quotient")
    retained = (verify.ROOT / "llvm/src/boxed-program.ll").read_bytes()
    for mode in ("official", "fast"):
        require((work / mode / "preview.ll").read_bytes() == retained, "different bytes from the Lean-checked corpus")
    require(official["official_replay"] and "checked_declarations" in generated, "missing named verifier")
    require(filecmp.cmp(work / "official/sealed.ndjson", work / "fast/sealed.ndjson", shallow=False),
            "both workers must receive the identical complete export")

    # Elaborate independently valid proof terms in the producer directory. Only
    # the NDJSON leaves it; verification regenerates Authority in a fresh directory.
    producer = work / "fast"
    prefix = fast.pinned_tools()
    env = verify.environment(producer, prefix)

    def export(label, text):
        (producer / "Certificate.lean").write_text(text)
        subprocess.run([prefix / "bin/lean", "-DwarningAsError=true", "-o", "Certificate.olean", "Certificate.lean"],
                       cwd=producer, env=env, timeout=args.timeout, check=True, stdout=subprocess.DEVNULL)
        target = work / (label + ".ndjson")
        with target.open("xb") as out:
            subprocess.run([prefix / "bin/leanexport", "Certificate", "--", *roots, verify.THEOREM],
                           cwd=producer, env=env, timeout=args.timeout, check=True, stdout=out)
        return target

    alt = export("alternative", verify.certificate("id (α := obligation) (" + verify.PROOF + ")"))
    alternative, _ = check("alternative-proof", "fast", candidate=alt)
    replayed, _ = check("official-alternative", "official", candidate=alt)
    require(replayed["official_replay"] and alternative["certificate"] == replayed["certificate"],
            "the external proof must also pass the fresh official kernel")
    require(alternative["certificate"]["sha256"] != generated["certificate"]["sha256"],
            "the alternate proof must actually have a different export")
    require(all(p["phase"] != "proof" for p in alternative["phases"]), "verifier elaborated a supplied proof")
    other = export("other", verify.certificate().replace("theorem checked : obligation := " + verify.PROOF,
                                                         "theorem checked : True := True.intro"))
    check("other-statement", "fast", candidate=other, rejection="unexpected declaration or proof subject")
    # Exercise the checker on a well-formed export with the correct subject but
    # an ill-typed witness. Its declaration references a valid expression index.
    with alt.open("rb") as src, (work / "invalid-term.ndjson").open("xb") as dst:
        for line in src:
            if line.startswith(b'{"thm"') and src.peek(1) == b"":
                row = json.loads(line)
                row["thm"]["value"] = row["thm"]["type"]
                line = (json.dumps(row, separators=(",", ":")) + "\n").encode()
            dst.write(line)
    rejected, _ = check("invalid-term", "fast", candidate=work / "invalid-term.ndjson", rejection="nanoda")
    worker = rejected["phases"][-1]
    require(worker["phase"] == "nanoda" and worker["exit_code"] > 0 and not worker["timed_out"],
            "the independent checker must reject the invalid proof itself")

    # Keep the capture graph, revision and target identical, then change one
    # SSA operand in the independently supplied bytes used by the proof.
    preview = (producer / "preview.ll").read_bytes()
    old = b"call ptr @vastitas_int_add_v1(ptr %v1, ptr %v0)"
    require(preview.count(old) == 1, "expected one boxed addition")
    changed = preview.replace(old, old.replace(b"%v1", b"%v0"))
    revision = json.loads((producer / "revision.json").read_bytes())
    model = json.loads((producer / "capture.stdout").read_bytes())
    sources = verify.read_sources(revision["input"], source, [source.name])

    def reject_obligation(label, data, inputs, diagnostic):
        altered = work / label
        altered.mkdir()
        (altered / "Authority.lean").write_text(
            verify.authority(revision, model, args.target_triple, args.data_layout, data, inputs))
        (altered / "Certificate.lean").write_text(verify.certificate())
        env = verify.environment(altered, prefix)
        subprocess.run([prefix / "bin/lean", "-o", "Authority.olean", "Authority.lean"], cwd=altered,
                       env=env, timeout=args.timeout, check=True)
        result = subprocess.run([prefix / "bin/lean", "-DwarningAsError=true", "Certificate.lean"], cwd=altered,
                                env=env, timeout=args.timeout, capture_output=True, text=True)
        require(result.returncode != 0 and diagnostic in result.stdout, f"{label} must fail its proof")
        print(f"{label} rejected by Lean", flush=True)

    reject_obligation("one-changed-LLVM-byte", changed, sources, "printedLines")
    [(path, offset, source_text)], entry = sources
    reject_obligation("substituted-physical-source", preview,
                      ([(path, offset, source_text + " ")], entry), "PhysicalSources.layout")
    # Appending a source comment preserves every LLVM byte while changing the revision.
    with source.open("ab") as out:
        out.write(b"\n// different source revision\n")
    stale, _ = check("stale-revision", "fast", candidate=alt, rejection="declaration environment differs")
    require(stale["llvm_sha256"] == official["llvm_sha256"] and stale["revision_sha256"] != official["revision_sha256"],
            "stale-source control must preserve exactly the emitted bytes")

    source.write_bytes((verify.ROOT / "llvm/fixtures/SingletonPower.vast").read_bytes())
    single, _ = check("singleton", "official")
    single_dir = work / "singleton"
    replay, _ = check("singleton-fast", "fast", candidate=single_dir / "sealed.ndjson")
    require(single["functions"] == 1 and int(single["integer_result"]) == 3**256 // 7
            and single["certificate"] == replay["certificate"],
            "the single-function runtime certificate must cover the full quotient in both modes")
    require((single_dir / "preview.ll").read_bytes() == (verify.ROOT / "llvm/src/singleton-power.ll").read_bytes(),
            "single-function certificate differs from the retained LLVM module")


def check_physical_inputs(work, args, source, check):
    """Compile the same helper through each loader and replay a stale proof."""
    helper = "fn helper(x: Int) -> Int { x + x } // λ1"
    library = work / "helper.vast"
    library.write_text(helper)
    source.write_text("fn main() -> Int { helper(21) }")
    args.lib = [library]
    manifest = work / "Vastitas.toml"
    dep = work / "dep"
    dep.mkdir()
    dep_manifest = dep / "Vastitas.toml"
    metadata = '[package]\nedition="2026"\nname="dep"\nversion="0.1.0"\nroot="main.vast"\n'
    dep_manifest.write_text(metadata + "# revision A")
    (dep / "main.vast").write_text("pub " + helper)
    for label, changed_file, replacement, count in [
            ("library", library, helper.replace("λ1", "λ2"), 2),
            ("manifest", dep_manifest, metadata + "# revision B", 4)]:
        if label == "manifest":
            manifest.write_text(metadata.replace('"dep"', '"app"') + '[dependencies]\ndep={path="dep"}\n')
            source.write_text("pub fn main() -> Int { dep::helper(21) }")
            args.manifest_path, args.source, args.lib = manifest, None, []
        baseline, _ = check(label, "official")
        image = work / label / "sealed.ndjson"
        peer, _ = check(label + "-fast", "fast", candidate=image)
        require(baseline["physical_inputs"] == count and baseline["certificate"] == peer["certificate"]
                and baseline["integer_result"] == "42", f"{label} source closure differs")
        if label == "manifest":
            wire = json.loads((work / label / "revision.json").read_bytes())["input"]
            app = next(p for p in wire["packages"] if p["source"] == wire["root"])
            app["dependencies"].clear()
            try:
                verify.read_sources(wire, manifest.resolve(strict=True), None)
            except ValueError as error:
                require("manifest and wire dependencies differ" in str(error), str(error))
            else:
                raise ValueError("the physical manifest must reject an omitted dependency")
            print("omitted dependency rejected against the physical manifest", flush=True)
        changed_file.write_text(replacement)
        stale, _ = check(label + "-stale", "fast", candidate=image, rejection="declaration environment differs")
        require(baseline["llvm_sha256"] == stale["llvm_sha256"]
                and baseline["revision_sha256"] != stale["revision_sha256"], f"{label} stale control differs")

def check_borrowed_operator(work, args, check):
    args.source = None
    args.manifest_path = verify.ROOT / "llvm/fixtures/borrowed-operator/Vastitas.toml"
    compiled = work / "borrowed-operator"
    official, _ = check("borrowed-operator", "official")
    peer, _ = check("borrowed-operator-fast", "fast", candidate=compiled / "sealed.ndjson")
    require(official["certificate"] == peer["certificate"] and official["physical_inputs"] == 6
            and official["integer_result"] == "42", "wrong assembled package certificate")
    retained = verify.ROOT / "llvm/src/borrowed-operator.ll"
    require((compiled / "preview.ll").read_bytes() == retained.read_bytes(), "different assembled module")
    revision = json.loads((compiled / "revision.json").read_bytes())
    pure = revision["pure"]
    call, = pure["dispatch_calls"]
    family, = (f for f in revision["families"] if f["id"] == call["id"])
    selected, = (row["selected"] for row in family["dispatch"] if row["key"] == call["key"])
    require(family["id"]["package"]["name"] == "edit_base" and
            selected["origin"]["contribution"]["package"]["name"] == "edit_addon" and
            (selected["ordinal"], selected["definition"]) == (call["method"], call["definition"]),
            "borrowed method differs from its family and contribution")
    site, = pure["operator_sites"]
    require(site["core"] == call["core"] and site["id"]["name"] == "add" and site["key"] == ["Int", "Int"],
            "addition recorded in a different specialization")
    bodies = json.loads((compiled / "capture.stdout").read_bytes())["functions"]
    sibling, = (s for s in pure["symbols"] if s["id"] == family["id"] and s["core"] != call["core"]
                and bodies[s["core"]]["params"] == ["Int", "Int"])
    call.update(core=sibling["core"], definition=sibling["specialization"]["definition"])
    wrong = work / "other-method.json"
    wrong.write_text(json.dumps(revision))
    result = subprocess.run([args.frontend, "check", "--manifest-path", args.manifest_path, "--llvm-preview",
                             "--target-triple", args.target_triple, "--data-layout", args.data_layout,
                             "--expect-function-revision", wrong], capture_output=True, timeout=args.timeout)
    require(result.returncode != 0 and not result.stdout and b"E_FUNCTION_REVISION" in result.stderr,
            "a same-signature sibling must fail before any module bytes are published")
    print("same-family (Int, Int) sibling rejected by the public emitter", flush=True)

    args.manifest_path = verify.ROOT / "llvm/fixtures/uncalled-operator/Vastitas.toml"
    uncalled, _ = check("uncalled-operator", "official")
    compiled = work / "uncalled-operator"
    peer, _ = check("uncalled-operator-fast", "fast", candidate=compiled / "sealed.ndjson")
    require(uncalled["certificate"] == peer["certificate"] and uncalled["functions"] == 6
            and uncalled["physical_inputs"] == 6 and uncalled["integer_result"] == "7",
            "uncalled method family or entry differs")
    retained = verify.ROOT / "llvm/src/uncalled-operator.ll"
    require((compiled / "preview.ll").read_bytes() == retained.read_bytes(), "different uncalled-family module")



if __name__ == "__main__":
    parser = ArgumentParser(description=__doc__)
    suites = ["boxed", "inputs", "assembly"]
    parser.add_argument("--suite", choices=suites, help="run one suite (default: all)")
    args = parser.parse_args()
    for suite in ([args.suite] if args.suite else suites):
        with tempfile.TemporaryDirectory(prefix=f"vastitas-{suite}-regression-") as tmp:
            run(Path(tmp), suite)
