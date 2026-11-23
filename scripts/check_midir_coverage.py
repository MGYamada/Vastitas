#!/usr/bin/env python3
"""Guard the reviewed #750 input schema; this does not admit or lower MidIR.

The finite source inventory intentionally includes payload records, diagnostic
variants and old Core forms: no constructor in those files is silently omitted.
The scanner accepts the repository's explicit, column-zero Lean declarations.
Unsupported declaration syntax fails closed; Lean remains the language checker.
Use --inventory to obtain a fresh *pending* candidate, then review its diff.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

from check_boundaries import lean_imports

ROOT = Path(__file__).resolve().parents[1]
LEDGER = "config/midir-coverage.json"
# Adding a source here is a reviewable scope change, never a wildcard admission.
SOURCE_NAMES = (
    "Core", "Indexed", "IndexedCore", "FiniteSort", "FiniteLookup", "FiniteLookupLayout", "Storage", "StorageLayout", "StorageCodegen",
    "StorageDiagonalData", "StorageTensorLayout", "StorageFunctionSyntax",
    "StorageNumerical", "StorageRealization", "StorageOwnedPackages", "StorageFunctionReceipts", "StorageFunctionContext",
    "NumericalCoverage", "StorageShapeExpr", "StorageShapes",
    "StorageShapeNumerical", "StorageShapeFunctions", "StorageValueFlow",
    "TensorNumerical", "TensorNetwork", "TensorTree", "AffineRealizationProfile", "ResourceSource", "MidIR/IR",
)
SOURCES = tuple(f"lean-kernel/VastitasKernel/{name}.lean" for name in SOURCE_NAMES)
NAME = r"(?:[A-Za-z_][A-Za-z_0-9']*|«[^»\n]+»)(?:\.(?:[A-Za-z_][A-Za-z_0-9']*|«[^»\n]+»))*"
DECL = re.compile(rf"^(?:private\s+)?(?P<kind>inductive|structure)\s+(?P<name>{NAME})(?=\s|$)")
SCOPE = re.compile(rf"^(namespace|section|mutual|end)(?:\s+({NAME}))?\s*$")
HASH = re.compile(r"[0-9a-f]{64}\Z")
MODULE = re.compile(r"[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*\Z")


LITERAL_THEOREM = "VastitasOracle.MidIR.literal_constructor_coverage"
FINITE_TAG_THEOREM = "VastitasOracle.MidIR.finite_tag_constructor_coverage"
LOOKUP_THEOREM = "VastitasOracle.MidIR.finite_lookup_constructor_coverage"
STATIC_CALL_THEOREM = "VastitasOracle.MidIR.static_call_constructor_coverage"
STATIC_CALL_ORIGIN = "VastitasKernel.Indexed.Core.Term.call"
CONVERSION_ORIGIN = "VastitasKernel.Indexed.Core.Term.natToInt"
CONVERSION_THEOREM = "VastitasOracle.MidIR.nat_to_int_constructor_coverage"
EXACT_MAPPINGS = {
    "VastitasKernel.Indexed.Core.Term.unary": (
        "unary operator", ["midir.bool.not.v1", "midir.int_neg.v1", "midir.int.const.v1"],
        "VastitasOracle.MidIR.unary_constructor_coverage"),
    "VastitasKernel.Indexed.Core.Term.pair": (
        "homogeneous pair", ["midir.nat_pair.v1", "midir.int_pair.v1"],
        "VastitasOracle.MidIR.pair_constructor_coverage"),
    "VastitasKernel.Indexed.Core.Term.project": (
        "pair projection", ["midir.nat_pair_first.v1", "midir.nat_pair_second.v1",
                            "midir.int_pair_first.v1", "midir.int_pair_second.v1"],
        "VastitasOracle.MidIR.projection_constructor_coverage"),
    STATIC_CALL_ORIGIN: ("static call", "midir.static.call.v1", STATIC_CALL_THEOREM),
    CONVERSION_ORIGIN: ("Nat-to-Int conversion", "midir.nat_to_int.v1", CONVERSION_THEOREM),
}
STRUCTURAL_THEOREMS = {
    "VastitasKernel.Indexed.Core.Term." + origin: "VastitasOracle.MidIR." + theorem + "_constructor_coverage"
    for origin, theorem in [("variable", "variable"), ("scope", "scope"), ("ascribe", "ascription"), ("letE", "let"),
                            ("branch", "branch")]
}


class CoverageError(ValueError):
    """The inventory or evidence is incomplete or has drifted."""


def digest(value):
    return hashlib.sha256(json.dumps(value, ensure_ascii=False, sort_keys=True,
                                     separators=(",", ":")).encode()).hexdigest()


def lexical_views(source, language="lean", capture_literals=False):
    """Return comment-free text and a same-length view with literals masked.

    Nested block comments are recognized. Lean interpolated strings are handled
    recursively, so a quoted word in an interpolation cannot manufacture a
    top-level declaration. Unsupported Rust raw strings fail closed.
    """
    clean, masked, literals = list(source), list(source), []

    def erase(start, end, comments=False):
        for index in range(start, end):
            if source[index] != "\n":
                masked[index] = " "
                if comments:
                    clean[index] = " "

    def string_end(start):
        interpolated = language == "lean" and start > 0 and source[start - 1] == "!"
        cursor = start + 1
        while cursor < len(source):
            char = source[cursor]
            if char == "\\":
                cursor += 2
            elif char == '"':
                return cursor + 1
            elif interpolated and char == "{":
                if source.startswith("{{", cursor):
                    cursor += 2
                    continue
                depth = 1
                cursor += 1
                while cursor < len(source) and depth:
                    if source[cursor] == '"':
                        cursor = string_end(cursor)
                    elif source[cursor] == "{":
                        depth += 1
                        cursor += 1
                    elif source[cursor] == "}":
                        depth -= 1
                        cursor += 1
                    else:
                        cursor += 1
                if depth:
                    raise CoverageError("unterminated interpolated string")
            else:
                cursor += 1
        raise CoverageError("unterminated string")

    position = 0
    line_comment = "--" if language == "lean" else "//"
    block_open, block_close = (("/-", "-/") if language == "lean" else ("/*", "*/"))
    while position < len(source):
        if source.startswith(line_comment, position):
            end = source.find("\n", position)
            end = len(source) if end < 0 else end
            erase(position, end, True)
            position = end
        elif source.startswith(block_open, position):
            start, depth = position, 1
            position += 2
            while position < len(source) and depth:
                if source.startswith(block_open, position):
                    depth += 1
                    position += 2
                elif source.startswith(block_close, position):
                    depth -= 1
                    position += 2
                else:
                    position += 1
            if depth:
                raise CoverageError("unterminated block comment")
            erase(start, position, True)
        elif source[position] == '"':
            if language == "rust" and re.search(r"r#*$", source[:position]):
                raise CoverageError("unsupported Rust raw string")
            end = string_end(position)
            literals.append((position, end))
            erase(position, end)
            position = end
        elif source[position] == "'" and (position == 0 or not (
                source[position - 1].isalnum() or source[position - 1] in "_'")):
            # Rust lifetimes (e.g. &'static) are names, not character literals.
            match = re.match(r"'(?:\\(?:u\{[0-9a-fA-F]+\}|x[0-9a-fA-F]{2}|.)|[^'\\\n])'", source[position:])
            if match:
                end = position + len(match.group())
                literals.append((position, end))
                erase(position, end)
                position = end
            else:
                position += 1
        else:
            position += 1
    result = ("".join(clean), "".join(masked))
    return (*result, literals) if capture_literals else result


def normalize(source):
    """Normalize token spacing, preserving every literal byte."""
    clean, _, literals = lexical_views(source, capture_literals=True)
    literal_ends = dict(literals)
    tokens, position = [], 0
    while position < len(clean):
        if clean[position].isspace():
            position += 1
        elif position in literal_ends:
            end = literal_ends[position]
            tokens.append(clean[position:end])
            position = end
        else:
            match = re.match(r"[\w']+|[^\w\s]", clean[position:])
            if match is None:
                raise CoverageError("unsupported schema token")
            tokens.append(match.group())
            position += len(match.group())
    return " ".join(tokens)


def qualified(scopes, name):
    if name.startswith("_root_."):
        return name[7:]
    return ".".join([value for kind, value in scopes if kind == "namespace"] + [name])


def scan_declarations(source, path):
    """Inventory every explicit inductive/record in one reviewed source file."""
    clean, masked = lexical_views(source)
    lines, visible = clean.splitlines(keepends=True), masked.splitlines(keepends=True)
    scopes, declarations = [], []
    index = 0
    while index < len(lines):
        line = visible[index].rstrip()
        scope = SCOPE.fullmatch(line)
        if scope:
            kind, name = scope.groups()
            if kind == "end":
                if not scopes:
                    raise CoverageError(f"{path}: unmatched end")
                _, opening = scopes.pop()
                if name is not None and name != opening:
                    raise CoverageError(f"{path}: mismatched scope end {name}")
            else:
                if kind == "namespace" and not name:
                    raise CoverageError(f"{path}: unnamed namespace")
                scopes.append((kind, name or ""))
            index += 1
            continue
        indentation = len(line) - len(line.lstrip())
        match = DECL.match(line.lstrip())
        if match is not None and indentation and not any(kind == "mutual" for kind, _ in scopes):
            raise CoverageError(f"{path}:{index + 1}: unsupported indented declaration")
        if match is None:
            # Modifiers/indentation/mutual declarations need scanner review.
            if re.search(r"\b(?:inductive|structure)\s", line) or line.startswith("|"):
                raise CoverageError(f"{path}:{index + 1}: unsupported declaration syntax")
            index += 1
            continue
        end = index + 1
        while end < len(lines) and (not visible[end].strip() or
                len(visible[end]) - len(visible[end].lstrip()) > indentation):
            end += 1
        block, block_visible = "".join(lines[index:end]), "".join(visible[index:end])
        where = re.search(r"\bwhere\b", block_visible)
        if where is None:
            raise CoverageError(f"{path}:{index + 1}: declaration without explicit where")
        name = qualified(scopes, match.group("name"))
        body, body_visible = block[where.end():], block_visible[where.end():]
        deriving = re.search(r"(?m)^\s*deriving\b", body_visible)
        if deriving:
            body, body_visible = body[:deriving.start()], body_visible[:deriving.start()]
        record = {"id": name, "source": path, "kind": match.group("kind"),
                  "header": normalize(block[:where.start()])}
        if match.group("kind") == "structure":
            record["fields"] = normalize(body)
        else:
            starts, depth = [], []
            pairs = {"(": ")", "[": "]", "{": "}"}
            for offset, char in enumerate(body_visible):
                if char in pairs:
                    depth.append(pairs[char])
                elif char in ")]}":
                    if not depth or depth.pop() != char:
                        raise CoverageError(f"{path}: unbalanced constructor signature in {name}")
                elif char == "|" and not depth:
                    starts.append(offset)
            if depth or not starts or body_visible[:starts[0]].strip():
                raise CoverageError(f"{path}: unsupported constructor list in {name}")
            constructors = []
            for start, stop in zip(starts, starts[1:] + [len(body)]):
                signature = body[start + 1:stop].strip()
                ctor = re.match(rf"({NAME})(?=\s|$)", signature)
                if ctor is None:
                    raise CoverageError(f"{path}: unsupported constructor in {name}")
                constructors.append({"id": f"{name}.{ctor.group(1)}", "signature": normalize(signature)})
            if len({item["id"] for item in constructors}) != len(constructors):
                raise CoverageError(f"{path}: duplicate constructor in {name}")
            record["constructors"] = constructors
        declarations.append(record)
        index = end
    if scopes:
        raise CoverageError(f"{path}: unclosed scope")
    return declarations


def string_list(text):
    """Parse only the manifest's literal string-list grammar."""
    parts = [part.strip() for part in text.split(",")]
    if parts[-1:] == [""]:
        parts.pop()
    if any(not re.fullmatch(r'"[^"\\\n]*"', part) for part in parts):
        raise CoverageError("runtime manifest needs literal string lists")
    result = [json.loads(part) for part in parts]
    if len(set(result)) != len(result):
        raise CoverageError("duplicate runtime manifest item")
    return result


def parse_runtime_manifest(source):
    clean, masked = lexical_views(source, "rust")
    declarations = list(re.finditer(r"(?m)^pub const (\w+): Package = Package \{", masked))
    packages = []
    for match in declarations:
        end = masked.find("};", match.end())
        if end < 0:
            raise CoverageError("unterminated runtime package")
        body = clean[match.end():end]
        fields = {}
        field_pattern = re.compile(r'\s*(\w+)\s*:\s*("[^"\\\n]*"|&\[[^\]]*\])\s*,')
        position = 0
        while body[position:].strip():
            field = field_pattern.match(body, position)
            if field is None or field.group(1) in fields:
                raise CoverageError("unsupported or duplicate runtime package field")
            key, value = field.groups()
            fields[key] = string_list(value[2:-1]) if value.startswith("&[") else json.loads(value)
            position = field.end()
        if set(fields) != {"name", "directory", "files", "forbidden", "modules"}:
            raise CoverageError("incomplete runtime package")
        if any(not isinstance(fields[key], str) for key in ("name", "directory")) or any(
                not isinstance(fields[key], list) for key in ("files", "forbidden", "modules")):
            raise CoverageError("runtime package field type mismatch")
        packages.append({"id": match.group(1), **fields})
    # Count every declaration, including a changed type/syntax our parser cannot read.
    if not packages or len(packages) != len(re.findall(r"\bpub\s+const\s+\w+\s*:\s*Package\b", masked)):
        raise CoverageError("unsupported runtime package declaration")
    if len({package["id"] for package in packages}) != len(packages):
        raise CoverageError("duplicate runtime package declaration")
    library = re.search(r"const TOOLCHAIN_LIBRARIES:\s*&\[&str\]\s*=\s*&\[([^\]]*)\];", clean)
    if library is None:
        raise CoverageError("missing literal toolchain libraries")
    return packages, string_list(library.group(1))


def relative_path(value):
    if not isinstance(value, str) or "\\" in value or value.startswith("/") or ".." in value.split("/"):
        raise CoverageError(f"non-repository-relative path: {value!r}")
    return value


def runtime_inventory(root):
    manifest = root / "src/runtime_inputs.rs"
    packages, libraries = parse_runtime_manifest(manifest.read_text())
    owners = {}
    for package in packages:
        relative_path(package["directory"])
        if not package["modules"]:
            raise CoverageError("empty runtime package")
        for module in package["modules"]:
            if not MODULE.fullmatch(module):
                raise CoverageError(f"unsupported runtime module {module}")
            library = module.split(".")[0]
            if library in owners and owners[library]["id"] != package["id"]:
                raise CoverageError(f"ambiguous runtime module owner: {library}")
            if library in libraries:
                raise CoverageError(f"runtime shadows toolchain library: {library}")
            owners[library] = package
    modules, files = {}, []
    for package in packages:
        directory = root / "lean-kernel" / package["directory"]
        for name in package["forbidden"]:
            if (directory / relative_path(name)).exists():
                raise CoverageError(f"forbidden runtime file: {package['id']}/{name}")
        for name in package["files"]:
            path = directory / relative_path(name)
            if not path.is_file():
                raise CoverageError(f"missing runtime input: {package['id']}/{name}")
            files.append({"source": path.relative_to(root).as_posix(),
                          "sha256": hashlib.sha256(path.read_bytes()).hexdigest()})
    pending = [module for package in packages for module in package["modules"]]
    while pending:
        module = pending.pop()
        if module in modules:
            continue
        owner = owners.get(module.split(".")[0])
        if owner is None:
            if module.split(".")[0] not in libraries:
                raise CoverageError(f"unregistered external runtime import: {module}")
            continue
        if not MODULE.fullmatch(module):
            raise CoverageError(f"unsupported runtime module {module}")
        path = root / "lean-kernel" / owner["directory"] / (module.replace(".", "/") + ".lean")
        if not path.is_file():
            raise CoverageError(f"missing runtime module: {module}")
        source = path.read_text()
        imports = sorted(set(lean_imports(source)))
        modules[module] = {"module": module, "package": owner["id"],
                           "source": path.relative_to(root).as_posix(), "imports": imports,
                           "sha256": hashlib.sha256(path.read_bytes()).hexdigest()}
        pending.extend(imports)
    return {"manifest": "src/runtime_inputs.rs", "manifest_sha256": hashlib.sha256(manifest.read_bytes()).hexdigest(),
            "packages": packages,
            "toolchain_libraries": libraries, "modules": [modules[key] for key in sorted(modules)],
            "files": sorted(files, key=lambda item: item["source"])}


def inventory(root):
    declarations = []
    for source in SOURCES:
        declarations.extend(scan_declarations((root / source).read_text(), source))
    if len({item["id"] for item in declarations}) != len(declarations):
        raise CoverageError("duplicate declaration identity")
    return {"sources": list(SOURCES), "declarations": sorted(declarations, key=lambda item: item["id"]),
            "runtime": runtime_inventory(root)}


def pending_ledger(root, base_commit):
    schema = inventory(root)
    coverage = []
    for declaration in schema["declarations"]:
        for constructor in declaration.get("constructors", []):
            origin = constructor["id"]
            coverage.append({"origin": origin, "disposition": "pending", "owner": "#751",
                             "planned_opcode": "midir." + origin.removeprefix("VastitasKernel."),
                             "reason": "Requires typed MidIR lowering, closed registry entry and preservation evidence.",
                             "evidence": []})
    return {"schema_version": 2, "scope": "constructor coverage only; no compiler admission",
            "snapshot": {"base_commit": base_commit, "schema_sha256": digest(schema)},
            "schema": schema, "coverage": sorted(coverage, key=lambda item: item["origin"])}


def validate(ledger, actual, require_complete=False):
    if (set(ledger) != {"schema_version", "scope", "snapshot", "schema", "coverage"} or
            type(ledger["schema_version"]) is not int or ledger["schema_version"] != 2):
        raise CoverageError("unsupported coverage ledger schema")
    if ledger["scope"] != "constructor coverage only; no compiler admission":
        raise CoverageError("coverage ledger must not claim compiler admission")
    snapshot = ledger["snapshot"]
    if set(snapshot) != {"base_commit", "schema_sha256"} or not re.fullmatch(r"[0-9a-f]{40}", snapshot["base_commit"]):
        raise CoverageError("snapshot requires a full base commit and a separate schema digest")
    if not HASH.fullmatch(snapshot["schema_sha256"]) or snapshot["schema_sha256"] != digest(ledger["schema"]):
        raise CoverageError("ledger schema digest mismatch")
    if ledger["schema"] != actual:
        expected = {item["id"]: item for item in ledger["schema"]["declarations"]}
        current = {item["id"]: item for item in actual["declarations"]}
        changed = sorted(key for key in expected.keys() | current.keys() if expected.get(key) != current.get(key))
        details = ", ".join(changed[:8]) or "runtime inputs or source inventory"
        raise CoverageError(f"source schema drift: {details}; regenerate a pending candidate and review the diff")
    origins = {ctor["id"] for decl in actual["declarations"] for ctor in decl.get("constructors", [])}
    seen, counts = set(), {"pending": 0, "lowered": 0, "structural": 0, "rejected": 0, "admitted": 0}
    for item in ledger["coverage"]:
        if set(item) != {"origin", "disposition", "owner", "planned_opcode", "reason", "evidence"}:
            raise CoverageError("incomplete constructor disposition")
        origin = item["origin"]
        if origin not in origins or origin in seen:
            raise CoverageError(f"unknown or duplicate constructor disposition: {origin}")
        seen.add(origin)
        status = item["disposition"]
        if status not in counts:
            raise CoverageError(f"unknown disposition for {origin}")
        if not re.fullmatch(r"#[1-9][0-9]*", item["owner"]):
            raise CoverageError(f"missing issue owner for {origin}")
        opcode = item["planned_opcode"]
        if status == "structural":
            if opcode is not None or origin not in STRUCTURAL_THEOREMS or item["evidence"] != [STRUCTURAL_THEOREMS[origin]]:
                raise CoverageError(f"structural lowering requires its checked binding theorem and no opcode: {origin}")
        elif isinstance(opcode, list):
            if status != "lowered" or origin not in EXACT_MAPPINGS or opcode != EXACT_MAPPINGS[origin][1]:
                raise CoverageError(f"unknown opcode alternatives for {origin}")
        elif not isinstance(opcode, str) or not MODULE.fullmatch(opcode) or not opcode.startswith("midir."):
            raise CoverageError(f"missing exact planned opcode for {origin}")
        if not isinstance(item["reason"], str) or not item["reason"].strip() or not isinstance(item["evidence"], list):
            raise CoverageError(f"missing disposition reason/evidence for {origin}")
        # Reserved for the later closed registry + validator integration. A JSON
        # change or an arbitrary evidence path cannot admit an operation today.
        if status == "admitted":
            raise CoverageError(f"admission unavailable before closed-registry evidence checking: {origin}")
        if status == "lowered":
            if origin in EXACT_MAPPINGS:
                label, expected_opcode, theorem = EXACT_MAPPINGS[origin]
                if (opcode, item["evidence"]) != (expected_opcode, [theorem]):
                    raise CoverageError(f"{label} requires its checked opcode and constructor theorem: {origin}")
            elif item["evidence"] not in ([LITERAL_THEOREM], [FINITE_TAG_THEOREM], [LOOKUP_THEOREM]):
                raise CoverageError(f"missing checked local lowering theorem for {origin}")
        elif status != "structural" and item["evidence"]:
            raise CoverageError(f"unrecognized evidence schema for {origin}")
        counts[status] += 1
    if seen != origins:
        raise CoverageError("missing constructor dispositions: " + ", ".join(sorted(origins - seen)[:8]))
    if require_complete and (counts["pending"] or counts["lowered"] or counts["structural"] or not counts["admitted"]):
        raise CoverageError("MidIR coverage is incomplete; the constructor guard is not release acceptance")
    return counts


def check_lowerings(ledger, rows):
    """Resolve every local mapping against the proved registry in the built Oracle."""
    expected = {}
    for row in rows:
        if (set(row) != {"origin", "opcode", "theorem"} or not isinstance(row["origin"], str)
                or not isinstance(row["theorem"], str)):
            raise CoverageError("invalid compiled lowering row")
        origin = row["origin"]
        if origin in expected:
            raise CoverageError(f"duplicate compiled lowering for {origin}")
        opcode = row["opcode"]
        if isinstance(opcode, list):
            if (len(opcode) < 2 or not all(isinstance(op, str) and MODULE.fullmatch(op) for op in opcode)
                    or len(set(opcode)) != len(opcode)):
                raise CoverageError(f"invalid compiled opcode alternatives for {origin}")
            opcode = ["midir." + op for op in opcode]
        elif isinstance(opcode, str) and MODULE.fullmatch(opcode):
            opcode = "midir." + opcode
        elif opcode is not None:
            raise CoverageError("invalid compiled lowering row")
        expected[origin] = (opcode, [row["theorem"]])
    recorded = {r["origin"]: (r["planned_opcode"], r["evidence"]) for r in ledger["coverage"] if r["disposition"] in {"lowered", "structural"}}
    if expected != recorded:
        changed = sorted(k for k in expected.keys() | recorded.keys() if expected.get(k) != recorded.get(k))
        raise CoverageError("compiled lowering differs from ledger: " + ", ".join(changed))


def unique_json(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise CoverageError(f"duplicate JSON key {key}")
        result[key] = value
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=ROOT)
    parser.add_argument("--ledger", type=Path, default=None)
    parser.add_argument("--inventory", action="store_true", help="print a fresh pending candidate; never overwrite a reviewed ledger")
    parser.add_argument("--require-complete", action="store_true", help="fail while any planned lowering remains pending")
    parser.add_argument("--check-lowerings", action="store_true", help="compare every local mapping with the compiled Lean registry")
    args = parser.parse_args()
    try:
        root = args.root.resolve()
        if args.inventory:
            commit = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=root, text=True).strip()
            print(json.dumps(pending_ledger(root, commit), ensure_ascii=False, indent=2))
        else:
            path = args.ledger or root / LEDGER
            ledger = json.loads(path.read_text(), object_pairs_hook=unique_json)
            actual = inventory(root)
            counts = validate(ledger, actual, args.require_complete)
            if args.check_lowerings or args.require_complete:
                command = ["lake", "-d", "lean", "env", "lean", "-DwarningAsError=true",
                           "--run", "scripts/export_midir_lowerings.lean"]
                report = subprocess.check_output(command, cwd=root, text=True)
                check_lowerings(ledger, json.loads(report, object_pairs_hook=unique_json))
            print(json.dumps({"status": "covered", "compiler_admission": False,
                              "schema_sha256": digest(actual), "dispositions": counts,
                              "runtime_modules": len(actual["runtime"]["modules"])}))
    except (CoverageError, OSError, ValueError, KeyError, TypeError, subprocess.CalledProcessError) as error:
        print(f"MidIR coverage error: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
