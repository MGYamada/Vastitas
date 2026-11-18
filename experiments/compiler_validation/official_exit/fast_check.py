#!/usr/bin/env python3
"""Offline differential qualification of the concrete signed-literal export."""

import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import stat
import subprocess
import tempfile

import run as official


HERE = Path(__file__).resolve().parent
STANDARD = HERE / "standard-axioms.ndjson"
AXIOMS = ["propext", "Classical.choice", "Quot.sound"]
TARGETS = {
    "public-artifact": ("FastSubject", "VastitasQualification.ExitAdmission.boundArtifact"),
    "printed-bytes": ("Printed", "printed"),
    "signed-endpoints": ("Facts", "endpoints"),
}
POLICY = {
    "use_stdin": False, "permitted_axioms": AXIOMS,
    "unpermitted_axiom_hard_error": True, "unsafe_permit_all_axioms": False,
    "nat_extension": True, "string_extension": True, "num_threads": 1,
    "print_axioms": False, "print_success_message": True,
}
CHUNK = 1024 * 1024
MAX_EXPORT = 1024 * CHUNK


def require(condition, message):
    if not condition:
        raise ValueError(message)


def namestr(parts):
    return ".".join(str(x) for x in parts)


def unique_fields(pairs):
    obj = dict(pairs)
    require(len(obj) == len(pairs), "duplicate JSON field")
    return obj


def inspect_closure(path, theorem, pending=None, *, expected_kind="thm", proof_suffix=None):
    """Audit the reference index and declaration graph independently of nanoda."""
    names = [()]
    name_components = set()
    levels = 1  # Level.zero is implicit.
    exprs = records = 0
    declared = {}
    referenced = set()
    axioms = []
    expected = tuple(theorem.split("."))
    goal_types = set()
    suffix_checked = False
    base = {"name", "type", "levelParams"}
    declaration_fields = {
        "def": {"value", "hints", "safety", "all"}, "thm": {"value", "all"},
        "opaque": {"value", "isUnsafe", "all"}, "axiom": {"isUnsafe"}, "quot": {"kind"},
        "types": {"all", "ctors", "numParams", "numIndices", "numNested", "isRec", "isReflexive", "isUnsafe"},
        "ctors": {"induct", "cidx", "numParams", "numFields", "isUnsafe"},
        "recs": {"all", "rules", "numParams", "numIndices", "numMotives", "numMinors", "k", "isUnsafe"},
    }
    literal_dependencies = set()

    def index(n, bound):
        require(type(n) is int and 0 <= n < bound, "dangling or noncanonical index")
        return n

    def name(n):
        return index(n, len(names))

    def fields(node, *keys):
        require(isinstance(node, dict) and set(node) == set(keys), "unknown or ambiguous fields")

    def decl(kind, node):
        nonlocal suffix_checked
        require(isinstance(node, dict) and set(node) == base | declaration_fields[kind],
                "unsupported declaration fields for " + kind)
        if kind == "quot":
            require(node["kind"] in {"type", "ctor", "lift", "ind"}, "unknown quotient primitive")
        if kind == "def":
            hints = node["hints"]
            require(hints in ("opaque", "abbrev") or isinstance(hints, dict) and set(hints) == {"regular"}
                    and type(hints["regular"]) is int and hints["regular"] >= 0, "invalid reducibility hints")
        ident = name(node["name"])
        if proof_suffix and records > proof_suffix[0]:
            require(kind == "thm" and names[ident] == expected and not suffix_checked
                    and node["type"] in goal_types and node["levelParams"] == []
                    and node["all"] in ([], [ident]), "unexpected declaration or proof subject after authority")
            suffix_checked = True
        require(ident > 0 and ident not in declared, "duplicate or anonymous declaration")
        declared[ident] = kind
        index(node["type"], exprs)
        for u in node["levelParams"]:
            name(u)
        if kind in ("def", "thm", "opaque"):
            index(node["value"], exprs)
        require(not node.get("isUnsafe", False) and node.get("safety", "safe") == "safe",
                "unsafe or partial declaration")
        for field in ("all", "ctors"):
            referenced.update(name(i) for i in node.get(field, ()))
        if "induct" in node:
            referenced.add(name(node["induct"]))
        for rule in node.get("rules", ()):
            fields(rule, "ctor", "nfields", "rhs")
            referenced.add(name(rule["ctor"]))
            index(rule["rhs"], exprs)
        if kind == "axiom":
            require(names[ident] in [tuple(item.split(".")) for item in AXIOMS],
                    "nonstandard or ambiguously named axiom")
            axioms.append(namestr(names[ident]))

    with path.open("rb") as stream:
        require(stream.read(STANDARD.stat().st_size) == STANDARD.read_bytes(), "standard axiom closure mismatch")
        stream.seek(0)
        for line in stream:
            records += 1
            require(line.endswith(b"\n"), "unterminated record")
            node = json.loads(line, object_pairs_hook=unique_fields)
            if records == 1:
                fields(node, "meta")
                continue
            kinds = set(node) - {"in", "ie", "il"}
            require(len(kinds) == 1, "ambiguous record")
            kind, = kinds
            val = node[kind]
            if "in" in node:
                fields(node, "in", kind)
                require(type(node["in"]) is int and node["in"] == len(names) and kind in {"str", "num"}, "invalid name record")
                component = "str" if kind == "str" else "i"
                fields(val, "pre", component)
                part = val[component]
                require(type(part) is str if kind == "str" else type(part) is int and part >= 0,
                        "invalid name component")
                parent = name(val["pre"])
                require((parent, part) not in name_components, "duplicate structured name")
                name_components.add((parent, part))
                names.append(names[parent] + (part,))
            elif "il" in node:
                fields(node, "il", kind)
                require(type(node["il"]) is int and node["il"] == levels, "duplicate or skipped universe index")
                if kind == "param":
                    name(val)
                elif kind == "succ":
                    index(val, levels)
                elif kind in {"max", "imax"}:
                    require(isinstance(val, list) and len(val) == 2, "invalid universe expression")
                    for n in val:
                        index(n, levels)
                else:
                    raise ValueError("unsupported universe " + kind)
                levels += 1
            elif "ie" in node:
                fields(node, "ie", kind)
                require(type(node["ie"]) is int and node["ie"] == exprs, "duplicate or skipped expression index")
                if kind == "const":
                    fields(val, "name", "us")
                    referenced.add(name(val["name"]))
                    if proof_suffix and names[val["name"]] == proof_suffix[1] and val["us"] == []:
                        goal_types.add(exprs)
                    for n in val["us"]:
                        index(n, levels)
                elif kind == "proj":
                    fields(val, "idx", "struct", "typeName")
                    require(type(val["idx"]) is int and val["idx"] >= 0, "invalid projection index")
                    referenced.add(name(val["typeName"]))
                    index(val["struct"], exprs)
                elif kind == "sort":
                    index(val, levels)
                elif kind in {"lam", "forallE", "letE", "app"}:
                    if kind == "app":
                        fields(val, "fn", "arg")
                        children = ["fn", "arg"]
                    else:
                        children = ["type", "body"]
                        if kind == "letE":
                            fields(val, "name", "type", "value", "body", "nondep")
                            children.append("value")
                        else:
                            fields(val, "name", "type", "body", "binderInfo")
                            require(val["binderInfo"] in {"default", "implicit", "strictImplicit", "instImplicit"}, "unknown binder")
                        name(val["name"])
                    for field in children:
                        index(val[field], exprs)
                elif kind in {"natVal", "strVal"}:
                    require(type(val) is str and (kind != "natVal" or val.isascii() and val.isdecimal()), "invalid literal")
                    literal_dependencies.add(("Nat",) if kind == "natVal" else ("String",))
                elif kind == "bvar":
                    require(type(val) is int and val >= 0, "invalid de Bruijn index")
                else:
                    raise ValueError("unsupported expression " + kind)
                exprs += 1
            else:
                fields(node, kind)
                if kind == "inductive":
                    require(not proof_suffix or records <= proof_suffix[0], "inductive declaration after authority")
                    fields(val, "types", "ctors", "recs")
                    for group, entries in val.items():
                        for item in entries:
                            decl(group, item)
                elif kind in {"axiom", "def", "thm", "opaque", "quot"}:
                    decl(kind, val)
                else:
                    raise ValueError("unsupported declaration " + kind)

    missing = referenced - declared.keys()
    if pending is None:
        require(not missing, f"missing {len(missing)} transitive declarations, including " +
                ", ".join(namestr(names[i]) for i in sorted(missing)[:3]))
    else:
        pending.extend(names[i] for i in sorted(missing))
    require(literal_dependencies.issubset(names[i] for i in declared), "missing literal type")
    require(sorted(axioms) == sorted(AXIOMS), "missing or duplicated standard axiom")
    require(any(names[i] == expected and kind == expected_kind for i, kind in declared.items()), "missing required declaration")
    require(not proof_suffix or suffix_checked, "missing proof of the current obligation")
    return {"records": records, "expressions": exprs, "declarations": len(declared),
            "standard_axioms": sorted(axioms), "closed_references": len(referenced)}


def compare_stream(candidate, reference, destination):
    """Snapshot only bytes identical to the independent authority stream."""
    count = 0
    audit_digest = hashlib.sha256()
    with os.fdopen(os.open(candidate, os.O_RDONLY | os.O_NONBLOCK), "rb") as supplied, reference.open("rb") as trusted, destination.open("xb") as out:
        info = os.fstat(supplied.fileno())
        expected_size = os.fstat(trusted.fileno()).st_size
        require(stat.S_ISREG(info.st_mode) and info.st_size == expected_size <= MAX_EXPORT,
                "certificate must be a regular file of the complete authority size")
        while True:
            block = trusted.read(CHUNK)
            require(supplied.read(len(block) if block else 1) == block, "proof or transitive declarations differ")
            if not block:
                break
            count += len(block)
            require(count <= MAX_EXPORT, "export exceeds qualification bound")
            audit_digest.update(block)
            out.write(block)
    return {"bytes": count, "sha256": audit_digest.hexdigest()}


def check_qualified_image(profile, image):
    # A caller cannot replace both the authority directory and candidate with a
    # weaker, independently valid same-name theorem. The pin identifies the full
    # qualified image; closure, exact bytes and checker outcome are still required.
    pins = json.loads((HERE / "qualified-exports.json").read_text(), object_pairs_hook=unique_fields)
    require(set(pins) == set(TARGETS) and image == pins[profile], "unqualified reference image")


def policy_for(path):
    policy = json.loads((official.ROOT / "config/nanoda-internal-audit.json").read_text())
    require(json.dumps(policy, sort_keys=True) == json.dumps(POLICY, sort_keys=True), "nanoda policy drift")
    return {**policy, "export_file_path": str(path)}


def pinned_lean(*extra_binaries):
    elan = Path(os.environ.get("ELAN_HOME", Path.home() / ".elan"))
    prefix = (elan / "toolchains/leanprover--lean4---v4.35.0").resolve(strict=True)
    bindir = prefix / "bin"
    for binary in ("lean", "leanexport", *extra_binaries):
        path = (bindir / binary).resolve(strict=True)
        require(path.parent == bindir and path.is_file() and os.access(path, os.X_OK),
                "missing pinned toolchain binary")
    version = subprocess.check_output([bindir / "lean", "--version"], text=True, timeout=10)
    require("version 4.35.0," in version and "commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release)" in version,
            "unexpected Lean identity")
    return prefix


def pinned_tools():
    prefix = pinned_lean("nanoda_bin")
    bindir = prefix / "bin"
    identity = subprocess.run([bindir / "nanoda_bin", "--help"], capture_output=True, text=True, timeout=10)
    require(identity.returncode == 0 and "nanoda_bin 0.4.19" in (identity.stdout + identity.stderr).splitlines(),
            "unexpected nanoda identity")
    return prefix


def standard(prefix, temp):
    # The standard environment is independent of all compiler and fixture imports.
    env = {**os.environ, "LEAN_PATH": str(prefix / "lib/lean"), "LEAN_NUM_THREADS": "1"}
    proc = subprocess.run([prefix / "bin/leanexport", "Init", "--", *AXIOMS], cwd=temp,
                          env=env, capture_output=True, timeout=30, check=True)
    require(not proc.stderr and proc.stdout == STANDARD.read_bytes(), "pinned Init axiom environment changed")
    return {"bytes": len(proc.stdout), "records": len(proc.stdout.splitlines()),
            "sha256": hashlib.sha256(proc.stdout).hexdigest()}


def export_closed(work, env, prefix, image, profile, timeout, measure):
    module, theorem = TARGETS[profile]
    stats, _ = export_roots(work, env, prefix, image, module, [*AXIOMS, theorem],
                            theorem, "thm", profile, timeout, measure)
    return stats


def export_roots(work, env, prefix, image, module, roots, target, kind, profile, timeout, measure):
    additional = []
    phases = []
    for attempt in range(8):
        result = measure([str(prefix / "bin/leanexport"), module, "--", *roots, *additional],
                         work, env, f"export_{profile}_{attempt}", timeout, stdout=image)
        phases.append(result)
        require(result["status"] == "passed" and image.stat().st_size <= MAX_EXPORT,
                "failed or oversized authority export for " + profile)
        missing = []
        stats = inspect_closure(image, target, missing, expected_kind=kind)
        if not missing:
            return {**stats, "additional_roots": len(additional), "export_passes": attempt + 1,
                    "bytes": image.stat().st_size, "export_measurements": phases}, [*roots, *additional]
        for parts in missing:
            require(all(not isinstance(part, str) or "»" not in part for part in parts),
                    "unsupported escape in a mutual declaration name")
            # Preserve numeric and string components, including dots inside strings.
            root = ".".join(str(x) if type(x) is int else "«" + x + "»" for x in parts)
            require(root not in additional, "pinned exporter did not emit a requested declaration")
            additional.append(root)
        require(len(additional) <= 2048 and sum(len(x.encode()) + 1 for x in additional) < 65536,
                "unsupported size of mutual closure")
    raise ValueError("mutual closure exceeds qualification bound")


def provision(work, env, prefix, dest, timeout, measure):
    """Called by the authority builder after the complete named Official replay."""
    require(prefix.resolve() == pinned_tools(), "provisioning must use the pinned installation")
    require(not dest.exists(), "authority destination must be new")
    dest.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(dir=dest.parent) as tmp:
        temp = Path(tmp)
        authority = temp / "authority"
        authority.mkdir()
        pinned = standard(prefix, temp)
        proofs = []
        for module in ("RevisionData", "ExpectedRevision", "RevisionBinding", "FastSubject"):
            shutil.copyfile(HERE / (module + ".lean"), work / (module + ".lean"))
            phase = measure([str(prefix / "bin/lean"), "-M", "2048", "-DwarningAsError=true", "--root", ".",
                             "-o", module + ".olean", module + ".lean"], work, env, "prepare_" + module, timeout)
            phase["module_source_sha256"] = hashlib.sha256((work / (module + ".lean")).read_bytes()).hexdigest()
            proofs.append(phase)
            require(phase["status"] == "passed", "could not elaborate revision binding " + module)
            label = "official_prepare_" + module
            phase = measure([str(prefix / "bin/leanchecker"), "-v", module], work, env, label, timeout)
            proofs.append(phase)
            replay = (work / (label + ".stdout")).read_text() + (work / (label + ".stderr")).read_text()
            require(phase["status"] == "passed" and "replaying " + module in replay.splitlines(),
                    "could not independently replay revision binding " + module)
        for module in ("Inputs.lean", "ExpectedRevision.lean"):
            shutil.copyfile(work / module, authority / module)
        coverage = {}
        for profile in TARGETS:
            image = authority / (profile + ".ndjson")
            coverage[profile] = export_closed(work, env, prefix, image, profile, timeout, measure)
            with image.open("rb") as file:
                fingerprint = {"sha256": hashlib.file_digest(file, "sha256").hexdigest(), "bytes": image.stat().st_size}
            check_qualified_image(profile, fingerprint)
            coverage[profile].update(fingerprint)
        record = {"standard_environment": pinned, "official_binding_phases": proofs, "exports": coverage}
        (authority / "coverage.json").write_text(json.dumps(record, indent=2) + "\n")
        authority.rename(dest)
        return record


def audit(profile, authority, candidate, args, prefix, reduction):
    _, theorem = TARGETS[profile]
    terminus = {"public-artifact": "public-emission-and-bytes", "printed-bytes": "llvm-parser-endpoint",
                "signed-endpoints": "source-decoder-and-llvm-byte-endpoints"}[profile]
    entry = {"profile": profile, "theorem": theorem, "verifier": "nanoda", "official_kernel_checked_by_audit": False,
             "verification_terminus": terminus}
    phase = "live-subject"
    try:
        live = official.live_fixture(args, bind_revision=True)
        entry["live"] = live
        phase = "authority-inputs"
        for module in ("Inputs.lean", "ExpectedRevision.lean"):
            require((authority / module).read_bytes() == (HERE / module).read_bytes(),
                    "provisioned obligation differs from current source, target, bytes or full revision")
        with tempfile.TemporaryDirectory(prefix="vast-fast-cert-") as tmp:
            temp = Path(tmp)
            phase = "standard-environment"
            entry["standard_environment"] = standard(prefix, temp)
            copy = temp / "checked.ndjson"
            phase = "certificate-comparison"
            entry["export"] = compare_stream(candidate, authority / (profile + ".ndjson"), copy)
            phase = "qualified-image"
            check_qualified_image(profile, entry["export"])
            phase = "declaration-closure"
            entry["closure"] = inspect_closure(copy, theorem)
            phase = "nanoda"
            config = temp / "policy.json"
            config.write_text(json.dumps(policy_for(copy)))
            cmd = [str(prefix / "bin/nanoda_bin"), str(config)]
            if args.stack_kib:
                # Run exactly one checker, with a declared POSIX main-thread stack limit.
                # Data paths are arguments to exec, never shell code.
                cmd = ["/bin/sh", "-c", 'ulimit -S -s "$1" || exit 2; shift; exec "$@"',
                       "nanoda-stack", str(args.stack_kib), *cmd]
            entry["main_stack_kib"] = args.stack_kib or "inherited"
            entry["timeout_seconds"] = args.timeout
            checker = reduction.measure(cmd, temp, dict(os.environ), "nanoda", args.timeout)
            out = (temp / "nanoda.stdout").read_text(errors="replace")
            err = (temp / "nanoda.stderr").read_text(errors="replace")
            entry["nanoda"] = checker
            count = reduction.checked_count(out, err, entry["closure"]["declarations"])
            if checker["status"] != "passed" or count is None:
                if "overflowed its stack" in err:
                    raise ValueError("nanoda exceeded its checking stack")
                if checker["timed_out"]:
                    raise ValueError("nanoda exceeded its time limit")
                raise ValueError("nanoda did not confirm the complete declaration count")
            entry["checked_declarations"] = count
        entry["status"] = "passed"
    except subprocess.SubprocessError as error:
        entry["status"] = "rejected"
        entry["reason"] = ("independent tool timed out" if isinstance(error, subprocess.TimeoutExpired)
                           else "independent tool failed")
    except OSError as error:
        entry["status"] = "rejected"
        entry["reason"] = f"could not read qualification inputs (errno {error.errno})"
    except (KeyError, ValueError) as error:
        entry["status"] = "rejected"
        entry["reason"] = str(error)
    if entry["status"] == "rejected":
        entry["rejection_phase"] = phase
    return entry


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--authority", type=Path, required=True, help="authority-provisioned directory, trusted separately from candidate")
    parser.add_argument("--candidate", type=Path, required=True, help="untrusted certificate")
    parser.add_argument("--profile", choices=TARGETS, default="public-artifact")
    parser.add_argument("--frontend", type=Path, default=official.ROOT / "target/debug/vastitas")
    parser.add_argument("--source", type=Path, default=official.DEFAULT_SOURCE)
    parser.add_argument("--module", type=Path, default=official.DEFAULT_LL)
    parser.add_argument("--value", type=int, default=-(2**128 + 1))
    parser.add_argument("--timeout", type=float, default=900)
    parser.add_argument("--stack-kib", type=int, choices=(0, 49152), default=49152, help="bounded checker stack, or 0 for the inherited host stack")
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    # Resolve the toolchain by the trusted installation, not by an export-specified path.
    require(args.timeout > 0, "expected a positive timeout")
    report = audit(args.profile, args.authority, args.candidate, args, pinned_tools(), official.load_reduction())
    content = json.dumps(report, indent=2) + "\n"
    if args.output:
        args.output.write_text(content)
    else:
        print(content, end="")
    raise SystemExit(0 if report["status"] == "passed" else 1)
