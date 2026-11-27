#!/usr/bin/env python3
"""Exercise the live proof using the complete boxed program from the LLVM corpus."""
from argparse import ArgumentParser, Namespace
from copy import deepcopy
import filecmp
import json
import os
import random
import shutil
import subprocess
from pathlib import Path
import sys
import tempfile
import time

import verify
import source_decode
from verify import fast, require

sys.path.insert(0, str(verify.ROOT / "scripts"))
from proof_worker import run_proof_worker


BOOL_COMPARISON = ("bool-comparison", "BoolComparison", "apply equality;", 4, 2**128 + 10, 2**128 + 7)
DEPENDENCY_MANIFEST = '[package]\nedition="2026"\nname="dep"\nversion="0.1.0"\nroot="main.vast"\n'
DEPENDENCY_UNIT = "pub fn helper(x: Int) -> Int { x + x }\n"


def published_revision(directory):
    with (directory / "proof-input.json").open(encoding="utf-8") as stream:
        return json.load(stream, object_pairs_hook=fast.unique_fields)["revision"]


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
        for contents, diagnostic in [
            (prefix[:-1] + b"b" + suffix, "declaration environment differs"),
            (prefix[:-1] + b"b", "declaration environment differs"),
            (prefix[:-1], "declaration environment differs"),
            (prefix, "proof suffix"),
        ]:
            candidate.write_bytes(contents)
            try:
                verify.snapshot(candidate, authority, sealed)
            except ValueError as error:
                require(diagnostic in str(error), str(error))
            else:
                raise ValueError("accepted a changed or incomplete certificate")
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


def run(work, suite, frontend, memory, *, file_counts=(), declaration_counts=(), library_bytes=(), entry_bytes=(),
        aggregate_bytes=(), dependency_bytes=(), packaged=False, with_entry_comment=False, timeout=120):
    # Both modes consume the same public path, bytes, target and function revision.
    source = work / "main.vast"
    source.write_bytes((verify.ROOT / "llvm/fixtures/BoxedProgram.vast").read_bytes())
    if with_entry_comment:
        with source.open("ab") as stream:
            stream.write(b"//" + b"0123456789abcdef" * 4096 + b"\n")
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
                for path in private.glob("Source*.olean"):
                    path.unlink()
            if candidate is not None and not keep_snapshot:
                (private / "sealed.ndjson").unlink(missing_ok=True)
        require(rejection is None, f"{label} accepted an invalid candidate")
        print(f"{label} passed ({report['bytes']} LLVM bytes, "
              f"{report['exported_declarations']} exported declarations)", flush=True)
        return report, roots

    if declaration_counts:
        args.manifest_path, _, unit = dependency_files(
            work, "pub fn main() -> Int { dep::units::helper(21) }\n", DEPENDENCY_UNIT, DEPENDENCY_MANIFEST)
        args.source = None
        reference = subprocess.check_output(
            [frontend, "check", "--manifest-path", args.manifest_path.name, "--llvm-preview",
             "--target-triple", args.target_triple, "--data-layout", args.data_layout], cwd=work, timeout=timeout)
        for count in declaration_counts:
            with unit.open("w") as stream:
                stream.write(DEPENDENCY_UNIT)
                size = len(DEPENDENCY_UNIT)
                for i in range(count):
                    line = f"pub indexed marker Marker{i};\n"
                    size += len(line)
                    require(size <= 16 * 1024**2, "generated dependency exceeds the physical input limit")
                    stream.write(line)
            value = check_file_sample(work, check, "indexed-markers", count, 5, reference)
            require(value == "42", "adding unused markers must preserve the dependency call result")
        return
    if dependency_bytes:
        check_dependency_scale(work, args, check, dependency_bytes)
        return
    if file_counts or library_bytes or entry_bytes or aggregate_bytes:
        check_file_scale(work, args, check, file_counts, library_bytes, entry_bytes, aggregate_bytes, packaged)
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

    publication = json.loads((producer / "proof-input.json").read_bytes())
    publication["revision"]["schema"] = "changed-schema"
    changed = work / "changed-revision.json"
    changed.write_text(json.dumps(publication))
    result = run_proof_worker([*lean, "--run", verify.HERE / "Capture.lean", changed,
                               args.target_triple, args.data_layout, "program"],
                              cwd=producer, env=env, timeout=args.timeout, capture_output=True, text=True)
    require(result.returncode != 0 and "different complete function revision" in result.stderr,
            "an altered revision field must fail independent capture even with identical wire and LLVM")
    print("changed revision schema rejected by Lean", flush=True)

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
    revision = published_revision(producer)
    model = json.loads((producer / "capture.stdout").read_bytes())
    sources = verify.read_sources(revision["input"], source, [source.name])

    def reject_obligation(label, data, inputs, diagnostic, *, authority_fails=False):
        altered = work / label
        altered.mkdir()
        [(name, declaration)] = verify.authority_modules(revision, model, args.target_triple, args.data_layout, data, inputs)
        require(name == "Authority", "single-file mutation must use one authority module")
        for path in producer.glob("Source*.olean"):
            os.link(path, altered / path.name)
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
    singleton = (verify.ROOT / "llvm/fixtures/SingletonPower.vast").read_bytes()
    comment = "// λ界🪐 ".encode() + b"ab" * 600 + b" endA\n"
    source.write_bytes(singleton + comment)
    single, _ = check("singleton", "official")
    single_dir = work / "singleton"
    replay, _ = check("singleton-fast", "fast", candidate=single_dir / "sealed.ndjson")
    require(single["functions"] == 1 and int(single["integer_result"]) == 3**256 // 7
            and single["certificate"] == replay["certificate"],
            "the single-function runtime certificate must cover the full quotient in both modes")
    require((single_dir / "preview.ll").read_bytes() == (verify.ROOT / "llvm/src/singleton-power.ll").read_bytes(),
            "single-function certificate differs from the retained LLVM module")
    source.write_bytes(singleton + comment.replace(b"endA", b"endB"))
    stale, _ = check("singleton-stale", "fast", candidate=single_dir / "sealed.ndjson",
                     rejection="declaration environment differs")
    require(single["llvm_sha256"] == stale["llvm_sha256"] and single["revision_sha256"] != stale["revision_sha256"],
            "changing the last source chunk must preserve the module and invalidate its certificate")


def write_padded_source(path, program, size, *, comment=b"//"):
    pattern = "λ界🪐0123456789abcdef".encode()
    copies, tail = divmod(size - len(program) - len(comment) - 1, len(pattern))
    require(copies >= 0, "qualification source is too small")
    block = pattern * 4096
    with path.open("wb") as stream:
        stream.write(program)
        stream.write(comment)
        blocks, remainder = divmod(copies, 4096)
        for _ in range(blocks):
            stream.write(block)
        stream.write(pattern * remainder + b"x" * tail + b"\n")
    require(path.stat().st_size == size, "qualification source byte count differs")


def dependency_files(work, main, helper, metadata):
    dep = work / "dep"
    dep.mkdir()
    manifest = work / "Vastitas.toml"
    manifest.write_text(metadata.replace('"dep"', '"app"') + '[dependencies]\ndep={path="dep"}\n')
    (work / "main.vast").write_text(main)
    (dep / "main.vast").write_text("pub mod units;\n")
    unit = dep / "units.vast"
    unit.write_text(helper)
    dep_manifest = dep / "Vastitas.toml"
    dep_manifest.write_text(metadata)
    return manifest, dep_manifest, unit


def check_file_sample(work, check, metric, size, count, reference):
    label = f"{metric}-{size}"
    official, _ = check(label, "official")
    generated = work / label
    peer, _ = check(label + "-fast", "fast", candidate=generated / "sealed.ndjson")
    require(official["certificate"] == peer["certificate"], "verifiers read different exports")
    require(official["integer_result"] == peer["integer_result"], "verifiers report different integer results")
    for name, report, directory in [("official", official, generated), ("fast", peer, work / (label + "-fast"))]:
        require(report["physical_inputs"] == count and (directory / "preview.ll").read_bytes() == reference,
                "file count or reference module differs")
        phases = [*report["phases"], *report["authority_closure"]["export_measurements"]]
        largest = max(phases, key=lambda phase: phase["peak_rss_bytes"])
        worker = "official_export" if name == "official" else "nanoda"
        replay = next(p for p in report["phases"] if p["phase"] == worker)
        print(f"{name} {metric}={size} took {report['wall_seconds']:.1f}s, "
              f"{worker} replay took {replay['wall_seconds']:.1f}s at {replay['peak_rss_bytes'] / 2**20:.1f} MiB, "
              f"{largest['phase']} peaked at {largest['peak_rss_bytes'] / 2**20:.1f} MiB, "
              f"{report['certificate']['bytes']} certificate bytes, "
              f"{report['private_file_bytes_at_seal']} private bytes at seal", flush=True)
        shutil.rmtree(directory)
    return official["integer_result"]


def reject_oversized_file(work, path, command, args):
    with path.open("r+b") as stream:
        limit = stream.seek(0, os.SEEK_END)
        require(limit == 16 * 1024**2, "expected a file at the protocol limit")
        stream.write(b" ")
        stream.flush()
        try:
            request = [*command, "--llvm-proof-input", "--target-triple", args.target_triple,
                       "--data-layout", args.data_layout]
            result = subprocess.run(request, cwd=work, capture_output=True, timeout=args.timeout)
        finally:
            stream.truncate(limit)
    require(result.returncode != 0 and not result.stdout and b"E_LIMIT" in result.stderr,
            f"{path.name}: expected E_LIMIT before publishing any bytes")


def check_dependency_scale(work, args, check, sizes):
    args.manifest_path, manifest, unit = dependency_files(
        work, "pub fn main() -> Int { dep::units::helper(21) }\n", DEPENDENCY_UNIT, DEPENDENCY_MANIFEST)
    args.source = None
    command = [args.frontend, "check", "--manifest-path", args.manifest_path.name]
    reference = subprocess.check_output([*command, "--llvm-preview", "--target-triple", args.target_triple,
                                         "--data-layout", args.data_layout], cwd=work, timeout=args.timeout)
    for size in sizes:
        write_padded_source(manifest, DEPENDENCY_MANIFEST.encode(), size, comment=b"#")
        write_padded_source(unit, DEPENDENCY_UNIT.encode(), size)
        result = check_file_sample(work, check, "dependency-file-bytes", size, 5, reference)
        require(result == "42", "expected 42 from the dependency helper")
        if size == 16 * 1024**2:
            for path in (manifest, unit):
                reject_oversized_file(work, path, command, args)
            print("dependency manifest and module size limits enforced", flush=True)


def check_file_scale(work, args, check, counts, library_bytes, entry_bytes, aggregate_bytes, packaged):
    """Vary one physical input dimension and replay each export in both kernels."""
    source = args.source
    if packaged:
        args.source = None
        args.manifest_path = work / "Vastitas.toml"
        args.manifest_path.write_text('[package]\nname="boxed_pairs"\nversion="0.1.0"\nedition="2026"\nroot="main.vast"\n')
        program = (verify.ROOT / "llvm/fixtures/ComparisonMethod.vast").read_bytes()
        retained = (verify.ROOT / "llvm/src/assembled-comparison.ll").read_bytes()
    else:
        program = source.read_bytes()
        retained = (verify.ROOT / "llvm/src/boxed-program.ll").read_bytes()
    for size in counts or library_bytes or entry_bytes or aggregate_bytes:
        if entry_bytes:
            metric, count = ("package-entry-bytes", 2) if packaged else ("entry-bytes", 1)
            write_padded_source(source, program, size)
        elif aggregate_bytes:
            metric, count = "aggregate-bytes", 4
            per_file, extra = divmod(size, count)
            args.lib = [work / f"lib{i}.vast" for i in range(1, count)]
            for index, path in enumerate([source, *args.lib]):
                prefix = program if index == 0 else f"// library {index}\n".encode()
                write_padded_source(path, prefix, per_file + (index < extra))
        elif library_bytes:
            metric, count = "bytes", 2
            library = work / "library.vast"
            # Fixed seed, distinct chunks, one to four UTF-8 bytes per scalar.
            prefix = "//λ界🪐".encode()
            body = random.Random(1226).randbytes((size + 1) // 2).hex().encode()
            library.write_bytes(prefix + body[:size - len(prefix) - 1] + b"\n")
            require(library.stat().st_size == size, "qualification library byte count differs")
            args.lib = [library]
        else:
            metric, count = "files", size
        while counts and len(args.lib) + 1 < count:
            path = work / f"library{len(args.lib):04}.vast"
            path.write_text("// library with no declarations\n")
            args.lib.append(path)
        result = check_file_sample(work, check, metric, size, count, retained)
        if packaged:
            require(result == "42", "expected the selected comparison method")
        if entry_bytes and size == 16 * 1024**2:
            cmd = [args.frontend, "check", *(["--manifest-path", args.manifest_path.name] if packaged else [source.name])]
            receipt = subprocess.run([*cmd, "--print-function-revision"], cwd=work,
                                     capture_output=True, timeout=args.timeout)
            require(receipt.returncode != 0 and not receipt.stdout and b"16 MiB receipt limit" in receipt.stderr,
                    "the standalone receipt must retain its size limit")
            reject_oversized_file(work, source, cmd, args)
            print("standalone receipt and source size limits enforced", flush=True)
        if aggregate_bytes and size == 64 * 1024**2:
            extra = work / "extra.vast"
            extra.write_bytes(b"\n")
            cmd = [args.frontend, "check", source.name, "--llvm-proof-input",
                   "--target-triple", args.target_triple, "--data-layout", args.data_layout]
            for path in [*args.lib, extra]:
                cmd.extend(["--lib", path.name])
            receipt = [args.frontend, "check", source.name, "--print-function-revision"]
            for path in args.lib:
                receipt.extend(["--lib", path.name])
            standalone = subprocess.run(receipt, cwd=work, capture_output=True, timeout=args.timeout)
            require(standalone.returncode != 0 and not standalone.stdout and b"64 MiB output limit" in standalone.stderr,
                    "serializing the standalone kernel revision must still enforce the full-envelope limit")
            over = subprocess.run(cmd, cwd=work, capture_output=True, timeout=args.timeout)
            require(over.returncode != 0 and not over.stdout and b"E_LIMIT" in over.stderr,
                    "one extra byte in a fifth file must fail before publication")
            print("aggregate byte limit enforced", flush=True)


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
    body = "pub fn answer() -> Int { 42 }\n//" + "λ界🪐" * 5500 + "a"
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

    leaf.write_text(body[:-1] + "b")
    rejected(wire, "source bytes changed")
    leaf.write_text(body)
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


def reject_lean_control(directory, args, filename, contents, control, *diagnostics):
    prefix = fast.pinned_lean()
    (directory / filename).write_text(contents)
    result = run_proof_worker([*verify.lean_command(prefix, args.memory), filename], cwd=directory,
                              env=verify.environment(directory, prefix), timeout=args.timeout,
                              capture_output=True, text=True)
    require(result.returncode != 0 and all(term in result.stdout for term in diagnostics),
            f"{control}: expected Lean rejection at {', '.join(diagnostics)} (exit {result.returncode})\n"
            f"{result.stdout[:1200]}{result.stderr[:400]}")
    print(f"{control} rejected by Lean", flush=True)


def check_final_library_row(directory, args):
    revision = published_revision(directory)
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
    [(first, _), (last, changed)] = [(n, body) for n, body in modules if n.startswith("PhysicalBatch")]
    require((directory / (first + ".olean")).is_file() and last == "PhysicalBatch1", "expected two batches")
    reject_lean_control(directory, args, "ChangedLastBatch.lean", changed, "last-batch library path substitution", "flatLibraryStep")
    # Lambda and mu have the same UTF-8 width. The literal must spell its witness.
    reject_lean_control(directory, args, "ChangedLiteral.lean", """import PhysicalText0
open VastitasProof
example : {s : String // s.utf8ByteSize = 2} := sizedLiteral "λ" ['μ'] rfl
""", "same-width literal substitution", "rfl", "String.ofList")

    wrong = deepcopy(revision)
    wrong["input"]["root_source"]["files"][0]["path"] = "other-entry.vast"
    modules = verify.authority_modules(wrong, captured, args.target_triple, args.data_layout, data, inputs)
    entry = next(body for n, body in modules if n == first)
    reject_lean_control(directory, args, "ChangedEntryRow.lean", entry, "protected entry row path substitution", "flatEntryStep")


def check_manifest_entry_span(directory, args):
    revision = published_revision(directory)
    wire = revision["input"]
    inputs = verify.read_sources(wire, args.manifest_path.resolve(strict=True), None)
    _, offset, text = inputs.files[inputs.entry]
    owner = next(package for package in wire["packages"] if package["source"] == wire["root"])
    root_module = next(module for module in owner["modules"] if not module["path"])
    root_module["span"]["end"] = offset + len(text.encode("utf-8")) + 1
    # Keep the accepted physical files and change only the package table's span.
    # Prove the public decoder's exact error without elaborating a second,
    # deliberately stale declaration-header proof after the physical rejection.
    packages = verify.official.json_term(wire["packages"])
    filename = "ChangedPackageSpan.lean"
    (directory / filename).write_text(f"""import Authority
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
namespace VastitasProof
open Lean VastitasKernel
def outsideEntry : Json := wire.setObjVal! "packages" ({packages})
example : PhysicalSources.layout outsideEntry = .error "root module is outside the physical entry" := by
  with_unfolding_all rfl
end VastitasProof
""")
    prefix = fast.pinned_lean()
    result = run_proof_worker([*verify.lean_command(prefix, args.memory), "-DwarningAsError=true", filename],
                              cwd=directory, env=verify.environment(directory, prefix), timeout=args.timeout,
                              capture_output=True, text=True)
    require(result.returncode == 0, f"wrong physical entry span rejection: {result.stdout[:1200]}{result.stderr[:400]}")
    print("root module one byte beyond the physical entry rejected by Lean", flush=True)


def check_dependency_file_contents(directory, args, manifest, module):
    revision = published_revision(directory)
    wire = revision["input"]
    inputs = verify.read_sources(wire, args.manifest_path.resolve(strict=True), None)
    rows = wire["root_source"]["files"]
    paths = {row["path"]: i for i, row in enumerate(rows)}
    manifest_row, module_row = (rows[paths[str(path.resolve())]] for path in (manifest, module))
    require(manifest_row["text"] != module_row["text"] and
            len(manifest_row["text"].encode()) == len(module_row["text"].encode()),
            "the substitution must preserve both file byte lengths")
    model = json.loads((directory / "capture.stdout").read_bytes())
    data = (directory / "preview.ll").read_bytes()
    for name, row, other in [("Manifest", manifest_row, module_row), ("Module", module_row, manifest_row)]:
        original = row["text"]
        row["text"] = other["text"]
        modules = verify.authority_modules(revision, model, args.target_triple, args.data_layout, data, inputs)
        changed = next(body for label, body in modules if label == "Authority")
        reject_lean_control(directory, args, f"ChangedDependency{name}.lean", changed,
                            f"same-length dependency {name.lower()} substitution",
                            "Tactic `rfl` failed", "is not definitionally equal")
        row["text"] = original


def check_physical_inputs(work, args, source, check):
    """Compile the same helper through each loader and replay a stale proof."""
    check_external_inputs(work, args.frontend)
    # The same long source text passes through both the wire and the physical layout.
    helper = 'fn helper(x: Int) -> Int { x + x } // "λ1" 🪐 e\u0301 \\end\r\n'
    library = work / "helper.vast"
    flat_helper = helper + "// " + "quoted 🪐 e\u0301 " * 160 + "end λ1\r\n"
    library.write_text(flat_helper)
    source.write_text("fn main() -> Int { helper(21) } // " + "λ界🪐 abc" * 180 + "\n")
    # Place the edited helper just across the production proof-batch boundary.
    # Reuse the same CI checks for positive and stale flat-library revisions.
    libraries = [work / f"empty{i}.vast" for i in range(verify.ROWS_PER_MODULE - 1)]
    if sys.platform.startswith("linux"):
        libraries[0] = work / os.fsdecode(b"empty-\xff.vast")
    for empty in libraries:
        empty.write_text("// no declarations\n")
    args.lib = [*libraries, library]
    dep = work / "dep"
    metadata = '\ufeff' + DEPENDENCY_MANIFEST
    for label in ("library", "manifest"):
        if label == "library":
            changed_file, replacement, count = library, flat_helper.replace("end λ1", "end λ2"), len(args.lib) + 1
        else:
            main = "pub fn main() -> Int { dep::units::helper(21) } //" + "λ界🪐 abc" * 180 + "\n"
            manifest, dep_manifest, unit = dependency_files(work, main, "pub " + helper, metadata)
            write_padded_source(dep_manifest, (metadata + "# revision A\n").encode(), 65536, comment=b"#")
            write_padded_source(unit, ("pub " + helper).encode(), 65536)
            changed_file, count = dep_manifest, 5
            replacement = dep_manifest.read_text().replace("revision A", "revision B", 1)
            args.manifest_path, args.source, args.lib = manifest, None, []
        baseline, _ = check(label, "official", keep_authority=True)
        image = work / label / "sealed.ndjson"
        peer, _ = check(label + "-fast", "fast", candidate=image)
        require(baseline["physical_inputs"] == count and baseline["certificate"] == peer["certificate"]
                and baseline["integer_result"] == "42", f"{label} source closure differs")
        if label == "library":
            if sys.platform.startswith("linux"):
                encoded = published_revision(work / label)["input"]["root_source"]["files"][1]["path"]
                require(encoded == list(os.fsencode(libraries[0].name)), "wire differs from the raw filename")
            check_final_library_row(work / label, args)
        if label == "manifest":
            check_manifest_entry_span(work / label, args)
            check_dependency_file_contents(work / label, args, dep_manifest, unit)
            wire = published_revision(work / label)["input"]
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

    dep_manifest.write_text(metadata + "# revision B")
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
        if group == "indexed-records":
            check_last_declaration(compiled, args)
        for label, old, new in edits:
            require(declarations.count(old) == 1, "expected one " + label + " field")
            library.write_text(declarations.replace(old, new))
            stale, _ = check(group + "-stale-" + label, "fast", candidate=candidate,
                             rejection="declaration environment differs")
            require(stale["revision_sha256"] != baseline["revision_sha256"] and
                    (work / (group + "-stale-" + label) / "preview.ll").read_bytes() == retained,
                    "a stale " + label + " must change the revision and preserve the LLVM bytes")
        candidate.unlink()


def check_last_declaration(directory, args):
    wire = published_revision(directory)["input"]
    (p, m, rows), = ((i, j, mod["indexed_declarations"])
                     for i, pkg in enumerate(wire["packages"]) for j, mod in enumerate(pkg["modules"])
                     if mod.get("indexed_declarations"))
    require(len(rows) > source_decode.ROWS_PER_WORKER, "expected multiple declaration batches")
    rows[-1]["kind"] = "invalid"
    last = f"def p{p}m{m}indexed_declarations{len(rows) - 1}Wire : Json"
    body, = (source for _, source in verify.declaration_modules(wire) if last in source)
    reject_lean_control(directory, args, "InvalidLastDeclaration.lean", body,
                        "malformed final indexed declaration", "Except.error", "Except.ok")


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


def check_uncalled_declaration(directory, args):
    wire = published_revision(directory)["input"]
    index, = (i for i, pkg in enumerate(wire["packages"]) if pkg["name"] == "edit_base")
    base = wire["packages"][index]
    method, = base["modules"][0]["methods"]
    result = method["body"]["result"]
    require(method["name"] == "choose" and result["kind"] == "integer" and result["value"] == "0",
            "expected the uncalled fallback method")
    # Only the encoded fallback changes. Keep the file texts, owner graph and LLVM bytes.
    result["kind"] = "invalid"
    mutated = next(body for name, body in verify.declaration_modules(wire) if name == f"SourcePackage{index}")
    reject_lean_control(directory, args, "InvalidFallback.lean", mutated,
                        "malformed uncalled method body", "Except.error", "Except.ok")
    result.update(kind="integer", value="1")
    old_header = "VastitasProof.Source.headerWire"
    changed = verify.official.json_term(dict(wire, root_source=None))
    reject_lean_control(directory, args, "StaleFallback.lean", f"""import SourceOperators
open Lean VastitasKernel.ResourceSource
def changed : Json := {changed}
example : Wire.requestFields changed = Wire.requestFields {old_header} := by with_unfolding_all rfl
""", "saved decoder proof for a different uncalled literal", "rfl", "Wire.requestFields")


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
    revision = published_revision(compiled)
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
    uncalled, _ = check("uncalled-operator", "official", keep_authority=True)
    compiled = work / "uncalled-operator"
    peer, _ = check("uncalled-operator-fast", "fast", candidate=compiled / "sealed.ndjson")
    require(uncalled["certificate"] == peer["certificate"] and uncalled["functions"] == 6
            and uncalled["physical_inputs"] == 6 and uncalled["integer_result"] == "7",
            "uncalled method family or entry differs")
    retained = verify.ROOT / "llvm/src/uncalled-operator.ll"
    require((compiled / "preview.ll").read_bytes() == retained.read_bytes(), "different uncalled-family module")
    check_uncalled_declaration(compiled, args)



if __name__ == "__main__":
    parser = ArgumentParser(description=__doc__)
    suites = ["boxed", "inputs", "assembly"]
    selection = parser.add_mutually_exclusive_group()
    selection.add_argument("--file-counts", type=int, nargs="+", metavar="N",
                           help=f"qualify increasing physical input counts (1 to {verify.MAX_PHYSICAL_INPUTS}) in both modes")
    selection.add_argument("--declaration-counts", type=int, nargs="+", metavar="N",
                           help="replay increasing counts of physical marker declarations in one dependency module")
    selection.add_argument("--library-bytes", type=int, nargs="+", metavar="N",
                           help="qualify increasing UTF-8 byte sizes of one flat library in both modes")
    selection.add_argument("--entry-bytes", type=int, nargs="+", metavar="N",
                           help="qualify increasing sizes of a single entry with a repeated UTF-8 comment")
    selection.add_argument("--aggregate-bytes", type=int, nargs="+", metavar="N",
                           help="qualify the total bytes of four flat files with repeated UTF-8 comments")
    selection.add_argument("--package-entry-bytes", type=int, nargs="+", metavar="N",
                           help="qualify the assembled comparison package at increasing entry sizes")
    selection.add_argument("--dependency-file-bytes", type=int, nargs="+", metavar="N",
                           help="qualify a dependency manifest and its external module at each file size")
    selection.add_argument("--suite", choices=[*suites, "host"], help="run one suite (default: all full suites)")
    parser.add_argument("--with-entry-comment", action="store_true",
                        help="append the 64 KiB comment payload to the entry in a file-count sweep")
    parser.add_argument("--frontend", type=Path, default=verify.ROOT / "target/debug/vastitas")
    parser.add_argument("--timeout", type=int, default=120, metavar="SECONDS", help="wall time limit per worker")
    verify.add_memory_argument(parser)
    args = parser.parse_args()
    if args.timeout <= 0:
        parser.error("positive timeout required")
    if args.with_entry_comment and not args.file_counts:
        parser.error("--with-entry-comment requires --file-counts")
    if args.file_counts and (args.file_counts != sorted(set(args.file_counts)) or
                             args.file_counts[0] < 1 or args.file_counts[-1] > verify.MAX_PHYSICAL_INPUTS):
        parser.error(f"--file-counts must increase strictly within 1 to {verify.MAX_PHYSICAL_INPUTS}")
    if args.library_bytes and (args.library_bytes != sorted(set(args.library_bytes)) or
                               args.library_bytes[0] < 16 or args.library_bytes[-1] > 16 * 1024**2):
        parser.error("--library-bytes must increase strictly between 16 bytes and 16 MiB")
    entry_bytes = args.entry_bytes or args.package_entry_bytes
    if entry_bytes:
        fixture = "ComparisonMethod" if args.package_entry_bytes else "BoxedProgram"
        minimum = (verify.ROOT / f"llvm/fixtures/{fixture}.vast").stat().st_size + 3
        if (entry_bytes != sorted(set(entry_bytes)) or
                entry_bytes[0] < minimum or entry_bytes[-1] > 16 * 1024**2):
            parser.error(f"entry sizes must increase strictly between {minimum} bytes and 16 MiB")
    if args.aggregate_bytes:
        minimum = 4 * ((verify.ROOT / "llvm/fixtures/BoxedProgram.vast").stat().st_size + 3)
        if (args.aggregate_bytes != sorted(set(args.aggregate_bytes)) or
                args.aggregate_bytes[0] < minimum or args.aggregate_bytes[-1] > 64 * 1024**2):
            parser.error(f"aggregate sizes must increase strictly between {minimum} bytes and 64 MiB")
    if args.dependency_file_bytes:
        minimum = max(len(DEPENDENCY_MANIFEST.encode()) + 2, len(DEPENDENCY_UNIT.encode()) + 3)
        if (args.dependency_file_bytes != sorted(set(args.dependency_file_bytes)) or
                args.dependency_file_bytes[0] < minimum or args.dependency_file_bytes[-1] > 16 * 1024**2):
            parser.error(f"--dependency-file-bytes must increase strictly between {minimum} bytes and 16 MiB")
    if args.declaration_counts and (args.declaration_counts != sorted(set(args.declaration_counts))
                                    or args.declaration_counts[0] < 1):
        parser.error("--declaration-counts requires strictly increasing positive counts")
    scale = (args.file_counts or args.declaration_counts or args.library_bytes or entry_bytes or
             args.aggregate_bytes or args.dependency_file_bytes)
    selected = [args.suite or "file-scale"] if args.suite or scale else suites
    for suite in selected:
        with tempfile.TemporaryDirectory(prefix=f"vastitas-{suite}-regression-") as tmp:
            run(Path(tmp), suite, args.frontend.resolve(), args.memory, file_counts=args.file_counts,
                declaration_counts=args.declaration_counts, library_bytes=args.library_bytes,
                entry_bytes=entry_bytes, aggregate_bytes=args.aggregate_bytes,
                dependency_bytes=args.dependency_file_bytes, packaged=bool(args.package_entry_bytes),
                with_entry_comment=args.with_entry_comment, timeout=args.timeout)
