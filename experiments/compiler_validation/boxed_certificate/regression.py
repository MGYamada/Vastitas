#!/usr/bin/env python3
"""Exercise the live proof using the complete boxed program from the LLVM corpus."""
from argparse import ArgumentParser, Namespace
from copy import deepcopy
import filecmp
import json
import shutil
import subprocess
from pathlib import Path
import sys
import tempfile
import time

import verify
from verify import fast, require

sys.path.insert(0, str(verify.ROOT / "scripts"))
from proof_worker import run_proof_worker


BOOL_COMPARISON = ("bool-comparison", "BoolComparison", "apply equality;", 4, 2**128 + 10, 2**128 + 7)


def check_method_selection(work, source, check, label, fixture, apply, functions, selected_result, default_result):
    body = (verify.ROOT / f"llvm/fixtures/{fixture}.vast").read_text()
    require(body.count(apply) == 1, f"{label}: expected one selection")
    source.write_text(body)
    selected, _ = check(label, "official")
    candidate = work / label / "sealed.ndjson"
    peer, _ = check(f"{label}-fast", "fast", candidate=candidate)
    retained = verify.ROOT / f"llvm/src/{label}.ll"
    require(selected["integer_result"] == str(selected_result) and selected["functions"] == functions
            and selected["certificate"] == peer["certificate"]
            and (work / label / "preview.ll").read_bytes() == retained.read_bytes(),
            f"{label}: incorrect selected method, result or module")
    source.write_text(body.replace(apply, ""))
    default, _ = check(f"{label}-default", "official")
    require(default["integer_result"] == str(default_result)
            and default["revision_sha256"] != selected["revision_sha256"], f"{label}: wrong default method")
    if label == "bool-comparison":
        saved = work / f"{label}-default" / "sealed.ndjson"
        replay, _ = check(f"{label}-default-fast", "fast", candidate=saved)
        require(replay["certificate"] == default["certificate"], "wrong default comparison certificate")
    check(f"{label}-stale", "fast", candidate=candidate, rejection="declaration environment differs")
    candidate.unlink()
    (work / f"{label}-default" / "sealed.ndjson").unlink()


def check_snapshot(work):
    """Exercise a prefix boundary inside a chunk and an existing destination."""
    with tempfile.TemporaryDirectory(dir=work) as tmp:
        authority, candidate, sealed = (Path(tmp) / n for n in ("authority", "candidate", "sealed"))
        prefix = b"a" * (fast.CHUNK + 1)
        suffix = b"proof" * (fast.CHUNK // 5 + 1)
        authority.write_bytes(prefix)
        candidate.write_bytes(prefix[:-1] + b"b" + suffix)
        try:
            verify.snapshot(candidate, authority, sealed)
        except ValueError as error:
            require("declaration environment differs" in str(error), str(error))
        else:
            raise ValueError("accepted a changed final prefix byte")
        require(authority.read_bytes() == prefix and not sealed.exists(), "changed authority after rejection")
        candidate.write_bytes(prefix + suffix)
        sealed.write_bytes(b"previous")
        try:
            verify.snapshot(candidate, authority, sealed)
        except FileExistsError:
            pass
        else:
            raise ValueError("overwrote an existing snapshot")
        require(authority.read_bytes() == prefix and sealed.read_bytes() == b"previous", "failed snapshot changed files")
        sealed.unlink()
        verify.snapshot(candidate, authority, sealed)
        require(sealed.samefile(authority), "sealed export duplicates the private authority on disk")
        require(verify.private_file_bytes(Path(tmp)) == 2 * (len(prefix) + len(suffix)),
                "private disk accounting counted the sealed hard link twice")
        authority.unlink()
        candidate.write_bytes(b"later")
        require(sealed.read_bytes() == prefix + suffix, "sealed proof depends on the candidate")


def run(work, suite, frontend, memory, file_counts=(), timeout=120):
    # Both modes consume the same public path, bytes, target and function revision.
    source = work / "main.vast"
    source.write_bytes((verify.ROOT / "llvm/fixtures/BoxedProgram.vast").read_bytes())
    target = json.loads(verify.official.TARGET_REPORT.read_bytes())["target"]
    args = Namespace(source=source, lib=[], manifest_path=None, frontend=frontend,
                     mode="official", candidate=None, save_candidate=None, timeout=timeout, memory=memory,
                     target_triple=target["triple"], data_layout=target["layout"])

    def check(label, mode, *, candidate=None, rejection=None, keep_authority=False, keep_snapshot=False):
        private = work / label
        private.mkdir()
        args.mode, args.candidate = mode, candidate
        report = {"phases": []}
        started = time.monotonic()
        try:
            roots = verify.verify(args, private, report)
            report["wall_seconds"] = time.monotonic() - started
        except ValueError as e:
            if rejection is None or rejection not in str(e):
                print(f"{label} ({mode}) failed: {e}", flush=True)
                raise
            print(f"{label} rejected ({rejection})", flush=True)
            return report, None
        finally:
            # The generated export is already sealed. Keep the authority module
            # only for the producer that elaborates the alternate proof terms.
            for result in report["phases"]:
                if result["phase"] in {"evaluation", "printing"} or result["status"] != "passed":
                    print(f"{label} {result['phase']}: {result['status']}, {result['wall_seconds']:.2f}s, "
                          f"{result['peak_rss_bytes'] / 1024**2:.1f} MiB peak RSS", flush=True)
            for name in ("authority.ndjson", "generated.ndjson", "Certificate.olean",
                         "FlowEvaluation.olean", "FlowPrinting.olean"):
                (private / name).unlink(missing_ok=True)
            if not keep_authority:
                (private / "Authority.olean").unlink(missing_ok=True)
            if candidate is not None and not keep_snapshot:
                (private / "sealed.ndjson").unlink(missing_ok=True)
        require(rejection is None, f"{label} accepted an invalid candidate")
        print(f"{label} passed ({report['bytes']} LLVM bytes, "
              f"{report['exported_declarations']} exported declarations)", flush=True)
        return report, roots

    if file_counts:
        check_file_scale(work, args, check, file_counts)
        return
    if suite == "inputs":
        check_physical_inputs(work, args, source, check)
        return
    if suite in {"assembly", "host"}:
        args.source = None
        args.manifest_path = work / "Vastitas.toml"
        args.manifest_path.write_text('[package]\nname = "boxed_pairs"\nversion = "0.1.0"\n'
                                      'edition = "2026"\nroot = "main.vast"\n')
        if suite == "host":
            check_method_selection(work, source, check, *BOOL_COMPARISON)
            return
        source.write_bytes((verify.ROOT / "llvm/fixtures/BoxedPairs.vast").read_bytes())
        checked, _ = check("pairs", "official")
        pair_dir = work / "pairs"
        replay, _ = check("pairs-fast", "fast", candidate=pair_dir / "sealed.ndjson")
        require(checked["certificate"] == replay["certificate"] and checked["physical_inputs"] == 2
                and checked["functions"] == 5
                and checked["integer_result"] == "42", "wrong assembled pair method or entry value")
        require((pair_dir / "preview.ll").read_bytes() == (verify.ROOT / "llvm/src/boxed-pairs.ll").read_bytes(),
                "pair certificate differs from the retained LLVM module")
        (pair_dir / "sealed.ndjson").unlink()
        magnitude = 2**128 + 43
        for case in [
            BOOL_COMPARISON,
            ("selected-projection", "SelectedProjection", "apply second_field;", 5, 19, 7),
            ("assembled-comparison", "ComparisonMethod", "apply ordered;", 3, 42, 7),
            ("assembled-negation", "AssembledNegation", "apply reversing;", 4, -magnitude, magnitude),
        ]:
            check_method_selection(work, source, check, *case)
        conversion_source = (verify.ROOT / "llvm/fixtures/AssembledConversion.vast").read_text()
        source.write_text(conversion_source)
        converted, _ = check("conversion", "official")
        conversion = work / "conversion"
        conversion_replay, _ = check("conversion-fast", "fast", candidate=conversion / "sealed.ndjson")
        require(converted["integer_result"] == str(2**128 + 43) and converted["functions"] == 3
                and converted["certificate"] == conversion_replay["certificate"], "wrong assembled Nat conversion")
        require((conversion / "preview.ll").read_bytes() ==
                (verify.ROOT / "llvm/src/assembled-conversion.ll").read_bytes(), "different conversion module")
        body = "{ int(x) }"
        require(conversion_source.count(body) == 1, "expected one selected conversion body")
        source.write_text(conversion_source.replace(body, "{ let y: Nat = x; int(y) }"))
        bound, _ = check("conversion-bound-local", "official")
        bound_dir = work / "conversion-bound-local"
        require((bound_dir / "preview.ll").read_bytes() == (conversion / "preview.ll").read_bytes()
                and bound["integer_result"] == converted["integer_result"]
                and bound["revision_sha256"] != converted["revision_sha256"],
                "the method-local binding must preserve the LLVM bytes and change the function revision")
        source.write_text(conversion_source)
        stale, _ = check("conversion-stale-body", "fast", candidate=bound_dir / "sealed.ndjson",
                         rejection="declaration environment differs")
        require(stale["revision_sha256"] == converted["revision_sha256"],
                "stale replay must check the restored unbound method")
        (conversion / "sealed.ndjson").unlink()
        (bound_dir / "sealed.ndjson").unlink()
        check_borrowed_operator(work, args, check)
        return

    check_snapshot(work)
    generated, roots = check("fast", "fast", keep_authority=True)
    official, _ = check("official", "official", candidate=work / "fast/sealed.ndjson", keep_snapshot=True)
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

    (work / "official/sealed.ndjson").unlink()
    (work / "fast/sealed.ndjson").unlink()

    # Elaborate independently valid proof terms in the producer directory. Only
    # the NDJSON leaves it. Each verifier regenerates Authority in a fresh directory.
    producer = work / "fast"
    prefix = fast.pinned_tools()
    env = verify.environment(producer, prefix)
    lean = verify.lean_command(prefix, memory)

    def export(label, text):
        (producer / "Certificate.lean").write_text(text)
        run_proof_worker([*lean, "-DwarningAsError=true", "-o", "Certificate.olean", "Certificate.lean"],
                       cwd=producer, env=env, timeout=args.timeout, check=True, stdout=subprocess.DEVNULL)
        target = work / (label + ".ndjson")
        with target.open("xb") as out:
            run_proof_worker([prefix / "bin/leanexport", "Certificate", "--", *roots, verify.THEOREM],
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
    other.unlink()
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
    (work / "invalid-term.ndjson").unlink()
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

    def reject_obligation(label, data, inputs, diagnostic, *, authority_fails=False):
        altered = work / label
        altered.mkdir()
        [(name, declaration)] = verify.authority_modules(revision, model, args.target_triple, args.data_layout, data, inputs)
        require(name == "Authority", "single-file mutation must use one authority module")
        (altered / "Authority.lean").write_text(declaration)
        (altered / "Certificate.lean").write_text(verify.certificate())
        env = verify.environment(altered, prefix)
        result = run_proof_worker([*lean, "-o", "Authority.olean", "Authority.lean"], cwd=altered,
                                  env=env, timeout=args.timeout, capture_output=True, text=True)
        if not authority_fails:
            result.check_returncode()
            result = run_proof_worker([*lean, "-DwarningAsError=true", "Certificate.lean"], cwd=altered,
                                      env=env, timeout=args.timeout, capture_output=True, text=True)
        require(result.returncode != 0 and diagnostic in result.stdout, f"{label} must fail its proof")
        print(f"{label} rejected by Lean", flush=True)

    reject_obligation("one-changed-LLVM-byte", changed, sources, "printedLines")
    [(path, offset, source_text)] = sources.files
    reject_obligation("substituted-physical-source", preview,
                      sources._replace(files=[(path, offset, source_text + " ")]), "PhysicalSources.layout", authority_fails=True)
    owner, name, version, dependencies = sources.graph.packages[0]
    changed_graph = sources.graph._replace(packages=[(owner, name, version + "1", dependencies)])
    reject_obligation("substituted-package-version", preview, sources._replace(graph=changed_graph),
                      "CertificatePackages.read", authority_fails=True)
    # Appending a source comment preserves every LLVM byte while changing the revision.
    with source.open("ab") as out:
        out.write(b"\n// different source revision\n")
    stale, _ = check("stale-revision", "fast", candidate=alt, rejection="declaration environment differs")
    require(stale["llvm_sha256"] == official["llvm_sha256"] and stale["revision_sha256"] != official["revision_sha256"],
            "stale-source control must preserve exactly the emitted bytes")

    alt.unlink()
    source.write_bytes((verify.ROOT / "llvm/fixtures/SingletonPower.vast").read_bytes())
    single, _ = check("singleton", "official")
    single_dir = work / "singleton"
    replay, _ = check("singleton-fast", "fast", candidate=single_dir / "sealed.ndjson")
    require(single["functions"] == 1 and int(single["integer_result"]) == 3**256 // 7
            and single["certificate"] == replay["certificate"],
            "the single-function runtime certificate must cover the full quotient in both modes")
    require((single_dir / "preview.ll").read_bytes() == (verify.ROOT / "llvm/src/singleton-power.ll").read_bytes(),
            "single-function certificate differs from the retained LLVM module")


def check_file_scale(work, args, check, counts):
    """Vary only the physical input count and replay each export in both kernels."""
    retained = (verify.ROOT / "llvm/src/boxed-program.ll").read_bytes()
    for count in counts:
        while len(args.lib) + 1 < count:
            path = work / f"library{len(args.lib):04}.vast"
            path.write_text("// library with no declarations\n")
            args.lib.append(path)
        label = f"files-{count}"
        official, _ = check(label, "official")
        generated = work / label
        peer, _ = check(label + "-fast", "fast", candidate=generated / "sealed.ndjson")
        require(official["certificate"] == peer["certificate"], "verifiers read different exports")
        for name, report, directory in [("official", official, generated), ("fast", peer, work / (label + "-fast"))]:
            require(report["physical_inputs"] == count and (directory / "preview.ll").read_bytes() == retained,
                    "file count or retained boxed module differs")
            phases = [*report["phases"], *report["authority_closure"]["export_measurements"]]
            largest = max(phases, key=lambda phase: phase["peak_rss_bytes"])
            worker = "official_export" if name == "official" else "nanoda"
            replay = next(p for p in report["phases"] if p["phase"] == worker)
            print(f"{name} files={count} took {report['wall_seconds']:.1f}s, "
                  f"{worker} replay took {replay['wall_seconds']:.1f}s at {replay['peak_rss_bytes'] / 2**20:.1f} MiB, "
                  f"{largest['phase']} peaked at {largest['peak_rss_bytes'] / 2**20:.1f} MiB, "
                  f"{report['certificate']['bytes']} certificate bytes, "
                  f"{report['private_file_bytes_at_seal']} private bytes at seal", flush=True)
            shutil.rmtree(directory)


def check_external_inputs(work, frontend):
    """Exercise disk resolution without starting a proof worker."""
    root = (work / "module-paths").resolve()
    base = root / "src"
    nested = base / "space/child"
    nested.mkdir(parents=True)
    manifest = root / "Vastitas.toml"
    manifest.write_text('[package]\nname="module_paths"\nversion="0.1.0"\nedition="2026"\nroot="src/main.vast"\n')
    (base / "main.vast").write_text("mod space { pub mod child; } mod other; mod alias; "
                                    "fn main() -> Int { space::child::leaf::answer() }")
    (nested / "mod.vast").write_text("pub mod leaf;")
    body = "pub fn answer() -> Int { 42 }"
    leaf = nested / "leaf.vast"
    leaf.write_text(body)
    (base / "other.vast").write_text(body)
    (base / "alias.vast").symlink_to(leaf)
    output = subprocess.check_output([frontend, "check", "--manifest-path", manifest, "--print-function-revision"])
    wire = json.loads(output)["input"]
    files = verify.read_sources(wire, manifest, None).files
    require([Path(p.decode()).relative_to(root).as_posix() for p, _, _ in files] ==
            ["Vastitas.toml", "src/main.vast", "src/space/child/mod.vast", "src/space/child/leaf.vast",
             "src/other.vast", "src/space/child/leaf.vast"], "incorrect physical module visit order")

    def rejected(candidate, message):
        try:
            verify.read_sources(candidate, manifest, None)
        except ValueError as error:
            require(message in str(error), str(error))
        else:
            raise ValueError("accepted incorrect physical module inputs")

    changed = deepcopy(wire)
    rows = changed["root_source"]["files"]
    rows[3]["path"], rows[4]["path"] = rows[4]["path"], rows[3]["path"]
    rejected(changed, "module path differs")
    (base / "unused.vast").write_text(body)
    changed = deepcopy(wire)
    changed["root_source"]["files"][3]["path"] = str(base / "unused.vast")
    rejected(changed, "module path differs")
    changed = deepcopy(wire)
    _, last, text = files[-1]
    changed["root_source"]["files"].append({"path": str(base / "unused.vast"), "text": body,
                                            "offset": last + len(text.encode()) + 1})
    rejected(changed, "no declaring manifest or module")
    flat = base / "space/child.vast"
    flat.mkdir()
    verify.read_sources(wire, manifest, None)
    flat.rmdir()
    flat.write_text("pub mod leaf;")
    rejected(wire, "one exactly spelled source")
    flat.unlink()
    (base / "other.vast").rename(base / "OTHER.vast")
    changed = deepcopy(wire)
    changed["root_source"]["files"][4]["path"] = str(base / "OTHER.vast")
    rejected(changed, "one exactly spelled source")
    print("nested external modules, repeated source paths and file substitutions checked", flush=True)


def check_final_library_row(directory, args):
    revision = json.loads((directory / "revision.json").read_bytes())
    captured = json.loads((directory / "capture.stdout").read_bytes())
    data = (directory / "preview.ll").read_bytes()
    names = [args.source.name, *(lib.name for lib in args.lib)]
    inputs = verify.read_sources(revision["input"], args.source, names)
    files = inputs.files.copy()
    _, offset, text = files[-1]
    files[-1] = (b"other.vast", offset, text)
    # Retain the genuine preceding batch. Change only the independently supplied
    # path in the last batch while preserving its valid wire row and byte count.
    modules = verify.authority_modules(revision, captured, args.target_triple, args.data_layout,
                                       data, inputs._replace(files=files))
    [(first, _), (last, changed), _] = modules
    require((directory / (first + ".olean")).is_file() and last == "PhysicalBatch1", "expected two batches")
    altered = directory / "ChangedLastBatch.lean"
    altered.write_text(changed)
    prefix = fast.pinned_lean()
    rejected = run_proof_worker([*verify.lean_command(prefix, args.memory), altered.name], cwd=directory,
                                env=verify.environment(directory, prefix), timeout=args.timeout,
                                capture_output=True, text=True)
    require(rejected.returncode != 0 and "flatLibraryStep" in rejected.stdout,
            "Lean must reject the substituted path in the final file proof")
    print("last-batch library path substitution rejected by Lean", flush=True)


def check_physical_inputs(work, args, source, check):
    """Compile the same helper through each loader and replay a stale proof."""
    check_external_inputs(work, args.frontend)
    # The same long source text passes through both the wire and the physical layout.
    helper = 'fn helper(x: Int) -> Int { x + x } // "λ1" 🪐 e\u0301 \\end\r\n'
    library = work / "helper.vast"
    library.write_text(helper)
    source.write_text("fn main() -> Int { helper(21) }")
    # Place the edited helper just across the production proof-batch boundary.
    # Reuse the same CI checks for positive and stale flat-library revisions.
    libraries = [work / f"empty{i}.vast" for i in range(verify.ROWS_PER_MODULE - 1)]
    for empty in libraries:
        empty.write_text("// no declarations\n")
    args.lib = [*libraries, library]
    manifest = work / "Vastitas.toml"
    dep = work / "dep"
    dep.mkdir()
    dep_manifest = dep / "Vastitas.toml"
    metadata = '\ufeff[package]\nedition="2026"\nname="dep"\nversion="0.1.0"\nroot="main.vast"\n'
    dep_manifest.write_text(metadata + "# revision A")
    (dep / "main.vast").write_text("pub mod units;")
    (dep / "units.vast").write_text("pub " + helper)
    for label, changed_file, replacement, count in [
            ("library", library, helper.replace("λ1", "λ2"), len(args.lib) + 1),
            ("manifest", dep_manifest, metadata + "# revision B", 5)]:
        if label == "manifest":
            manifest.write_text(metadata.replace('"dep"', '"app"') + '[dependencies]\ndep={path="dep"}\n')
            source.write_text("pub fn main() -> Int { dep::units::helper(21) }")
            args.manifest_path, args.source, args.lib = manifest, None, []
        baseline, _ = check(label, "official")
        image = work / label / "sealed.ndjson"
        peer, _ = check(label + "-fast", "fast", candidate=image)
        require(baseline["physical_inputs"] == count and baseline["certificate"] == peer["certificate"]
                and baseline["integer_result"] == "42", f"{label} source closure differs")
        if label == "library":
            check_final_library_row(work / label, args)
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
        image.unlink()

    # A lawful field edit in a dependency can preserve every executable instruction.
    source.write_bytes((verify.ROOT / "llvm/fixtures/OrderedCalls.vast").read_bytes())
    library = dep / "main.vast"
    declarations = """pub indexed marker A;
pub indexed marker B;
pub indexed implementation X(A, affine_descriptor) capabilities();
pub indexed implementation Y(A, affine_descriptor) capabilities();
pub indexed classification C { parents(); domain(X, Y); };
pub indexed family Rel(object(C), object(C)) = token constraints(same_base(0, 1));
pub indexed family Tag(natural) = token constraints();
pub indexed package Hidden { case(Y, A) { Tag(7); } };
pub indexed primitive chosen = descriptor(Y);
"""
    fixtures = verify.ROOT / "tests/fixtures"
    groups = [
        ("indexed-definitions", declarations, [
            ("marker", "X(A,", "X(B,"),
            ("domain", "domain(X, Y)", "domain(Y, X)"),
            ("family-slot", "same_base(0, 1)", "same_base(1, 0)"),
            ("package-index", "Tag(7);", "Tag(8);"),
            ("primitive-argument", "descriptor(Y)", "descriptor(X)"),
        ]),
        ("metric-frames", (fixtures / "metric-frame-source.vast").read_text(), [
            ("metric-gram", "gram((2, 0,)", "gram((3, 0,)"),
            ("evidence-subject", "nondegenerate(Written)", "nondegenerate(Default)"),
            ("frame-inverse", "(x, 1,),) inverse = columns((1, 0,), (-x, 1,)",
                              "(y, 1,),) inverse = columns((1, 0,), (-y, 1,)"),
        ]),
        ("indexed-records", (fixtures / "indexed-record-source.vast").read_text(), [
            ("scale-magnitude", "frac(1, 2) of Period", "frac(1, 3) of Period"),
            ("module-basis", "basis(ground, excited)", "basis(excited, ground)"),
            ("manifold-witness", "by(u -> South::y);", "by(u -> South::y + 0);"),
        ]),
    ]
    retained = (verify.ROOT / "llvm/src/ordered-calls.ll").read_bytes()
    for group, declarations, edits in groups:
        library.write_text(declarations)
        baseline, _ = check(group, "official")
        compiled = work / group
        candidate = compiled / "sealed.ndjson"
        replay, _ = check(group + "-fast", "fast", candidate=candidate)
        require(baseline["physical_inputs"] == 4 and baseline["integer_result"] == "23" and
                baseline["certificate"] == replay["certificate"] and (compiled / "preview.ll").read_bytes() == retained,
                f"{group} and the ordered calls must share one certificate")
        for label, old, new in edits:
            require(declarations.count(old) == 1, "expected one " + label + " field")
            library.write_text(declarations.replace(old, new))
            stale, _ = check(group + "-stale-" + label, "fast", candidate=candidate,
                             rejection="declaration environment differs")
            require(stale["revision_sha256"] != baseline["revision_sha256"] and
                    (work / (group + "-stale-" + label) / "preview.ll").read_bytes() == retained,
                    "a stale " + label + " must change the revision and preserve the LLVM bytes")
        candidate.unlink()


def check_package_substitutions(wire, manifest):
    # Keep all six physical files and the compiled module unchanged.
    root = wire["packages"][-1]
    require(len(root["dependencies"]) == 2, "expected two direct dependencies")
    for label, mutate, diagnostic in [
        ("dependency order", lambda ps: ps[-1]["dependencies"].reverse(), "manifest and wire dependencies"),
        ("dependency target", lambda ps: ps[-1]["dependencies"][0].update(target=ps[-1]["dependencies"][1]["target"]),
         "manifest and wire dependencies"),
        ("package order", lambda ps: ps.reverse(), "manifest dependency order"),
    ]:
        altered = deepcopy(wire)
        mutate(altered["packages"])
        try:
            verify.read_sources(altered, manifest, None)
        except ValueError as error:
            require(diagnostic in str(error), str(error))
        else:
            raise ValueError(f"accepted a substituted {label}")


def check_borrowed_operator(work, args, check):
    args.source = None
    args.manifest_path = verify.ROOT / "llvm/fixtures/borrowed-operator/Vastitas.toml"
    compiled = work / "borrowed-operator"
    official, _ = check("borrowed-operator", "official")
    peer, _ = check("borrowed-operator-fast", "fast", candidate=compiled / "sealed.ndjson")
    require(official["certificate"] == peer["certificate"] and official["physical_inputs"] == 6
            and official["integer_result"] == "42", "wrong assembled package certificate")
    nanoda, = (phase for phase in peer["phases"] if phase["phase"] == "nanoda")
    peak_mib = nanoda["peak_rss_bytes"] / 2**20
    require(peak_mib <= 1536, f"borrowed-operator nanoda peak {peak_mib:.1f} MiB exceeds 1,536 MiB")
    print(f"borrowed-operator nanoda peak {peak_mib:.1f} MiB", flush=True)
    retained = verify.ROOT / "llvm/src/borrowed-operator.ll"
    require((compiled / "preview.ll").read_bytes() == retained.read_bytes(), "different assembled module")
    revision = json.loads((compiled / "revision.json").read_bytes())
    check_package_substitutions(revision["input"], args.manifest_path.resolve())
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
    (compiled / "sealed.ndjson").unlink()

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
    selection = parser.add_mutually_exclusive_group()
    selection.add_argument("--file-counts", type=int, nargs="+", metavar="N",
                           help=f"qualify increasing physical input counts (1 to {verify.MAX_PHYSICAL_INPUTS}) in both modes")
    selection.add_argument("--suite", choices=[*suites, "host"], help="run one suite (default: all full suites)")
    parser.add_argument("--frontend", type=Path, default=verify.ROOT / "target/debug/vastitas")
    parser.add_argument("--timeout", type=int, default=120, metavar="SECONDS", help="wall time limit per worker")
    verify.add_memory_argument(parser)
    args = parser.parse_args()
    if args.timeout <= 0:
        parser.error("positive timeout required")
    if args.file_counts and (args.file_counts != sorted(set(args.file_counts)) or
                             args.file_counts[0] < 1 or args.file_counts[-1] > verify.MAX_PHYSICAL_INPUTS):
        parser.error(f"--file-counts must increase strictly within 1 to {verify.MAX_PHYSICAL_INPUTS}")
    for suite in ([args.suite or "file-scale"] if args.suite or args.file_counts else suites):
        with tempfile.TemporaryDirectory(prefix=f"vastitas-{suite}-regression-") as tmp:
            run(Path(tmp), suite, args.frontend.resolve(), args.memory, args.file_counts, args.timeout)
