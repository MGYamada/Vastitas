#!/usr/bin/env python3
"""Verify a live public boxed program's execution-model/bytes certificate."""
import argparse
from bisect import bisect_right
from collections import defaultdict
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
from typing import NamedTuple

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "official_exit"))
import fast_check as fast
from fast_check import official, require

ROOT = official.ROOT
MAX_PHYSICAL_INPUTS = 8192
GOAL = "VastitasProof.obligation"
THEOREM = "VastitasProof.checked"
ROOTS = [*fast.AXIOMS, "Eq.refl", "id", "VastitasOracle.BoxedCertificate.Valid.mk",
         "VastitasOracle.BoxedCertificate.printedLines", "VastitasProof.packageOwners", "VastitasProof.physicalInputs", GOAL]
KINDS = {"Int": ".int", "Nat": ".nat", "Bool": ".bool", "Pair<Int>": "(.pair .int)", "Pair<Nat>": "(.pair .nat)"}
OPS = {f"{k}_{op}": f"(.{k} .{op})" for k in ("int", "nat") for op in ("add", "sub", "mul", "div")}
OPS.update(nat_int_div=".natIntDiv", int_nat_div=".intNatDiv", int_neg=".neg", nat_to_int=".natToInt")
for element in ("nat", "int"):
    OPS[f"{element}_pair"] = f"(.pair .{element})"
    OPS[f"{element}_pair_first"] = f"(.project .{element} true)"
    OPS[f"{element}_pair_second"] = f"(.project .{element} false)"


def add_memory_argument(parser):
    def positive_mib(value):
        amount = int(value)
        if amount <= 0:
            raise argparse.ArgumentTypeError("expected a positive MiB limit")
        return amount

    parser.add_argument("--memory", type=positive_mib, default=1536, metavar="MiB",
                        help="Lean memory limit per capture or elaboration process (default: 1536 MiB)")


def lean_command(prefix, memory):
    return [prefix / "bin/lean", "-M", str(memory)]


PROOF = """by
  refine ⟨rfl, physicalInputs, packageOwners, rfl, rfl, rfl, ?_⟩
  exact VastitasOracle.BoxedCertificate.printedLines code headerBytes lines rfl rfl"""

FLOW_PROOF = """by
  exact ⟨rfl, physicalInputs, packageOwners, rfl, rfl, evaluated, printed⟩"""


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


def flow_op(step):
    match step:
        case ["compare", ("Nat" | "Int") as sort, tag, a, b]:
            ops = {f"exact.{k}.v1": k for k in ("eq", "ne", "lt", "le", "gt", "ge")}
            return f".exact (.compare {KINDS[sort]} .{ops[tag]} {natural(a)} {natural(b)})"
        case ["bool", bool() as v]:
            return ".boolean " + ("true" if v else "false")
        case ["not", a]:
            return ".boolNot " + natural(a)
        case ["and" | "or" | "eq" | "ne" as op, a, b]:
            return f".bool{op.title()} {natural(a)} {natural(b)}"
        case _:
            return instruction(step).replace(".primitive ", ".exact ", 1)


def flow_edge(e):
    target, refs = e
    return f"⟨{natural(target)}, [{', '.join(map(natural, refs))}]⟩"


def flow_block(b):
    match b["exit"]:
        case ["ret", r]:
            end = ".ret " + natural(r)
        case ["jump", e]:
            end = ".jump " + flow_edge(e)
        case ["branch", r, yes, no]:
            end = f".branch {natural(r)} {flow_edge(yes)} {flow_edge(no)}"
        case _:
            raise ValueError("unsupported control-flow terminator")
    params = ", ".join(KINDS[k] for k in b["params"])
    ops = ", ".join(map(flow_op, b["ops"]))
    return f"⟨[{params}], [{ops}], {end}⟩"


def resolve_module(base, logical, names, listings):
    # Match each directory entry's actual spelling, including on case-insensitive hosts.
    candidates = []
    for parts in [(*logical[:-1], logical[-1] + ".vast"), (*logical, "mod.vast")]:
        path = base.joinpath(*parts)
        try:
            mode = path.stat().st_mode
        except (FileNotFoundError, NotADirectoryError):
            continue
        if stat.S_ISDIR(mode):
            continue
        parent = base
        for part in parts:
            if parent not in listings:
                with os.scandir(parent) as entries:
                    listings[parent] = names.intersection(entry.name for entry in entries)
            if part not in listings[parent]:
                break
            parent /= part
        else:
            candidates.append(path)
    require(len(candidates) == 1, "external module requires one exactly spelled source file")
    return candidates[0].resolve(strict=True)


def check_module_files(package, root, directory, files, offsets, claimed):
    # Lean checks each mod declaration against its tokens. An inline span covers
    # just 'mod'. An external span extends through its semicolon. Reconstruct the
    # loader's depth-first file order, keeping separate occurrences of aliased paths.
    owners = {}
    sites = defaultdict(list)
    external = defaultdict(list)
    names = {"mod.vast"}
    for module in sorted(package["modules"], key=lambda m: len(m["path"])):
        logical = tuple(module["path"])
        span = module["span"]
        require(logical not in owners, "duplicate module path")
        if not logical:
            owners[()] = ()
            sites[()].append(span)
            continue
        require(logical[:-1] in owners and re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", logical[-1]),
                "invalid declared module path")
        names.add(logical[-1])
        host = owners[logical[:-1]]
        sites[host].append(span)
        if span["end"] - span["start"] == len("mod"):
            owners[logical] = host
        else:
            owners[logical] = logical
            names.add(logical[-1] + ".vast")
            external[host].append((span["start"], logical))

    require(() in owners, "missing package root module")
    first = bisect_right(offsets, sites[()][0]["start"]) - 1
    index = first
    listings = {}
    pending = [()]
    while pending:
        logical = pending.pop()
        path = resolve_module(root.parent, logical, names, listings) if logical else root
        require(path.is_relative_to(directory) and path.suffix == ".vast",
                "module file outside package or invalid extension")
        require(0 <= index < len(files) and index not in claimed and files[index][0] == os.fsencode(path),
                "module path differs from its physical source")
        claimed.add(index)
        start = offsets[index]
        end = offsets[index + 1] - 1 if index + 1 < len(files) else start + len(files[index][2].encode())
        require(all(start <= s["start"] <= s["end"] <= end for s in sites[logical]),
                "module declaration lies outside its declaring file")
        pending.extend(child for _, child in sorted(external[logical], reverse=True))
        index += 1
    return first


class PackageGraph(NamedTuple):
    file: str
    root: str
    legacy_geometry: bool
    packages: list


class PhysicalInputs(NamedTuple):
    files: list
    entry: int
    graph: PackageGraph


def check_manifest_inputs(wire, manifest, files, entry):
    """Follow the paths declared by the physical TOML files from the user's root."""
    by_path = {}
    for i, (path, _, _) in enumerate(files):
        by_path.setdefault(path, []).append(i)
    offsets = [offset for _, offset, _ in files]
    claimed = set()
    packages = {p["source"]: p for p in wire["packages"]}
    require(len(packages) == len(wire["packages"]) and wire["root"] == str(manifest),
            "package owners differ from the physical root")
    pending = [(manifest, False)]
    owners = {}
    ordered = []
    active = set()
    while pending:
        path, finished = pending.pop()
        if finished:
            ordered.append(owners[path])
            active.remove(path)
            continue
        require(path not in active, "cyclic manifest dependency")
        if path in owners:
            continue
        active.add(path)
        rows = by_path.get(os.fsencode(path), [])
        require(len(rows) == 1 and str(path) in packages, "missing or duplicate physical package manifest")
        claimed.add(rows[0])
        package = packages[str(path)]
        # The frontend accepts one UTF-8 BOM at the start of a manifest.
        # Keep the original text in the certificate's physical layout.
        doc = tomllib.loads(files[rows[0]][2].removeprefix("\ufeff"))
        metadata = doc["package"]
        require(metadata["edition"] == "2026" and all(metadata[key] == package[key]
                for key in ("name", "version", "edition")), "manifest and wire package identities differ")
        module = (path.parent / metadata["root"]).resolve(strict=True)
        first = check_module_files(package, module, path.parent, files, offsets, claimed)
        if path == manifest:
            require(first == entry, "manifest and physical entry differ")
        targets = {alias: (path.parent / dep["path"] / "Vastitas.toml").resolve(strict=True)
                   for alias, dep in doc.get("dependencies", {}).items()}
        edges = [(alias, str(targets[alias])) for alias in sorted(targets)]
        require([(e["alias"], e["target"]) for e in package["dependencies"]] == edges,
                "manifest and wire dependencies differ")
        owners[path] = (str(path), metadata["name"], metadata["version"], edges)
        pending.append((path, True))
        pending.extend((targets[alias], False) for alias, _ in reversed(edges))
    require(list(packages) == [owner[0] for owner in ordered], "wire differs from manifest dependency order")
    require(len(claimed) == len(files), "physical input has no declaring manifest or module")
    return PackageGraph(str(manifest), str(manifest), wire.get("legacy_geometry", False), ordered)


def read_sources(wire, source, flat_names):
    """Build the expected layout from disk, independently of the modeled graph."""
    root = wire["root_source"]
    rows = root.get("files", [{"path": wire["file"], "offset": 0}])
    require(0 < len(rows) <= MAX_PHYSICAL_INPUTS, "invalid physical input count")
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
            info = os.fstat(stream.fileno())
            require(stat.S_ISREG(info.st_mode), "expected regular compilation input")
            limit = min(16 * 1024**2, 64 * 1024**2 - total)
            require(info.st_size <= limit, "physical source byte limit exceeded")
            data = stream.read(info.st_size + 1)
        require(len(data) == info.st_size, "source size changed during certificate preparation")
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
        graph = check_manifest_inputs(wire, source, files, entry)
    else:
        require(entry == 0, "flat entry must be the first input")
        owner = "vastitas:compat:flat"
        graph = PackageGraph(os.fsencode(flat_names[0]).decode("utf-8", errors="replace"), owner, True,
                             [(owner, "legacy_flat", "1.0.0", [])])
    return PhysicalInputs(files, entry, graph)


def string_literal(value):
    # Reducing a long String literal unfolds the UTF-8 encoding of its entire
    # character list. A balanced append keeps those reductions short.
    if len(value) <= 24:
        return official.lean_string(value)
    middle = len(value) // 2
    return f"({string_literal(value[:middle])} ++ {string_literal(value[middle:])})"


# Elaboration retains the current module's declarations until the worker exits.
# Keep file rows in bounded modules and compose their proofs in source order.
ROWS_PER_MODULE = 128


def physical_proof(wire, inputs, quote, physical):
    """Construct an exact transition for each file and compose bounded runs."""
    statement = "theorem physicalInputs : PhysicalSources.layout wire = .ok sources := by"
    rows = wire["root_source"].get("files")
    if rows is None:
        return [], "", f"#[{', '.join(physical)}]", statement + "\n  with_unfolding_all rfl"
    flat = inputs.graph.root == "vastitas:compat:flat"
    owners = [] if flat else [p[0] for p in inputs.graph.packages]
    manifests = f"([{', '.join(map(quote, owners))}] : List String).foldl (fun s n => s.insert n) {{}}"
    table = (f"⟨{quote(inputs.graph.file)}, {quote(inputs.graph.root)}, {natural(inputs.files[inputs.entry][1])}, "
             f"{quote(inputs.files[inputs.entry][2])}, {len(rows)}, manifestNames⟩")
    lines = ["def expectedFiles0 : Array PhysicalSources.File := #[]",
             f"def manifestNames : PhysicalSources.ManifestSet := {manifests}",
             f"def table : PhysicalSources.Table := {table}",
             "def cursor0 : PhysicalSources.Cursor := {missing := table.manifests}"]
    names = set(owners)
    entry = "none"
    total = 0
    batches = []
    missing = "table.manifests"
    extent_proofs = {}
    for i, (row, (label, offset, text)) in enumerate(zip(rows, inputs.files, strict=True)):
        lines.append(f"def expectedFiles{i+1} := expectedFiles{i}.push {physical[i]}")
        # Only the exact canonical wire shape can use the shared decoder proof.
        # Build the JSON from the captured wire and the output cursor from disk.
        flat_library = (flat and i != inputs.entry and set(row) == {"offset", "path", "text"}
                        and isinstance(row["path"], str))
        size = len(text.encode("utf-8"))
        if flat_library:
            if text not in extent_proofs:
                extent_proofs[text] = f"fileExtent{i}"
                lines.append(f"theorem fileExtent{i} : {quote(text)}.utf8ByteSize = {size} := by with_unfolding_all rfl")
            wire_path = quote(row["path"])
            row_term = (f"VastitasOracle.CertificatePackages.flatLibraryRow {natural(row['offset'])} "
                        f"{wire_path} {quote(row['text'])}")
            proof = (f"VastitasOracle.CertificatePackages.flatLibraryStep table.filename table.entryText "
                     f"{wire_path} {quote(text)} table.count table.base "
                     f"{natural(offset)} {total} {size} expectedFiles{i} cursor{i}.entry {extent_proofs[text]} "
                     "rfl rfl (by with_unfolding_all rfl) rfl")
        else:
            row_term = official.json_term(row, quote)
            proof = "by with_unfolding_all rfl"
        lines.append(f"def row{i} : Json := {row_term}")
        name = os.fsdecode(label)
        if name in names:
            lines.append(f"def missing{i+1} := {missing}.erase {quote(name)}")
            missing = f"missing{i+1}"
        if i == inputs.entry:
            entry = f"some {i}"
        total += size
        lines.extend([
            f"def cursor{i+1} : PhysicalSources.Cursor := "
            f"⟨expectedFiles{i+1}, {offset+size+1}, {total}, {entry}, {missing}⟩",
            f"theorem rowStep{i} : table.step cursor{i} row{i} = .ok cursor{i+1} := {proof}",
        ])
        end = i + 1
        if end % ROWS_PER_MODULE == 0 or end == len(rows):
            start = len(batches) * ROWS_PER_MODULE
            prefix = "".join(f"row{j} :: " for j in range(start, end))
            steps = "".join(f"VastitasOracle.CertificatePackages.prepend_row rowStep{j} (" for j in range(start, end))
            lines.extend([
                f"def rowsFrom{start} (tail : List Json) := {prefix}tail",
                f"theorem scanFrom{start} {{tail : List Json}} {{last : PhysicalSources.Cursor}}",
                f"    (h : tail.foldlM table.step cursor{end} = .ok last) :",
                f"    (rowsFrom{start} tail).foldlM table.step cursor{start} = .ok last :=",
                "  " + steps + "h" + ")" * (end-start),
            ])
            batches.append("\n".join(lines))
            lines = []
    starts = range(0, len(rows), ROWS_PER_MODULE)
    data = "".join(f"rowsFrom{start} (" for start in starts) + "[]" + ")" * len(starts)
    scan = "".join(f"scanFrom{start} (" for start in starts) + "by rfl" + ")" * len(starts)
    evidence = "\n".join([
        "theorem prepared : PhysicalSources.prepare wire = .ok (.inr (table, rows)) := by with_unfolding_all rfl",
        statement,
        f"  apply VastitasOracle.CertificatePackages.table_layout prepared (last := cursor{len(rows)})",
        f"  · exact {scan}",
        "  · rfl",
    ])
    return batches, f"def rows : Array Json := ({data}).toArray", f"expectedFiles{len(rows)}", evidence


def physical_wire(wire, quote):
    # Reference the exact row definitions above in the captured JSON as well.
    # Preserve every other field of both objects, including unfamiliar fields.
    def object_with(fields, name, term):
        pairs = [(official.lean_string(key), term if key == name else official.json_term(fields[key], quote))
                 for key in sorted(fields)]
        return "(Json.mkObj [" + ", ".join(f"({key}, {value})" for key, value in pairs) + "])"

    if "files" not in wire["root_source"]:
        return official.json_term(wire, quote)
    root = object_with(wire["root_source"], "files", ".arr rows")
    return object_with(wire, "root_source", root)


def authority_modules(revision, model, triple, layout, data, sources):
    # Only closed data is interpolated. All identifiers and proof syntax are fixed.
    strings = {}

    def quote(value):
        if len(value) <= 40:
            return official.lean_string(value)
        if value not in strings:
            strings[value] = f"text{len(strings)}"
        return strings[value]

    header_lines = data.split(b"\n", 2)
    require(len(header_lines) == 3, "incomplete printed header")
    header_bytes = list(b"\n".join(header_lines[:2]) + b"\n")
    body = header_lines[2].decode("utf-8").split("\n")
    require(len(body) >= 3 and body[0] == body[-1] == "", "noncanonical body delimiters")
    flow = model.get("kind") == "flow"
    # Keep LLVM lines as literal strings for direct comparison in the export
    # checker. Source text still uses shared bindings and balanced appends.
    lines = ", ".join(map(official.lean_string, body[1:-1]))
    fields = [(quote(k), 'wire' if k == 'input' else official.json_term(revision[k], quote)) for k in sorted(revision)]
    rev = ", ".join(f"({k}, {v})" for k, v in fields)
    files, entry, graph = sources
    package_rows = []
    for path, name, version, dependencies in graph.packages:
        owner = f"⟨{quote(path)}, {quote(name)}, {quote(version)}⟩"
        edges = ", ".join(f"({quote(alias)}, {quote(target)})" for alias, target in dependencies)
        package_rows.append(f"({owner}, [{edges}])")
    require(type(graph.legacy_geometry) is bool, "invalid compatibility profile")
    package_graph = f"⟨{quote(graph.file)}, {quote(graph.root)}, {str(graph.legacy_geometry).lower()}, [{', '.join(package_rows)}]⟩"
    physical = []
    for path, offset, text in files:
        try:
            label = quote(path.decode("utf-8")) + ".toUTF8"
        except UnicodeDecodeError:
            label = f"ByteArray.mk #{list(path)}"
        physical.append(f"⟨{label}, {natural(offset)}, {quote(text)}⟩")
    namespace = "FlowCertificate" if flow else "BoxedCertificate"
    code_type = "ExactFlow" if flow else "ExactProgram"
    functions = []
    for f in model["functions"]:
        if flow:
            blocks = ", ".join(map(flow_block, f["blocks"]))
            functions.append(f"⟨{KINDS[f['result']]}, #[{blocks}]⟩")
            continue
        args = ", ".join(KINDS[k] for k in f["params"])
        steps = ", ".join(map(instruction, f["ops"]))
        functions.append(f"⟨[{args}], {KINDS[f['result']]}, [{steps}], {natural(f['slot'])}⟩")
    wire = physical_wire(revision["input"], quote)
    triple_term, layout_term = quote(triple), quote(layout)
    batches, rows, expected_files, file_evidence = physical_proof(revision["input"], sources, quote, physical)
    bindings = "\n".join(f"def {name} : String := {string_literal(value)}" for value, name in strings.items())
    dependency = "VastitasOracle.FlowCertificate.Subject" if flow else "VastitasOracle.BoxedCertificate"

    def module_source(dependency, body):
        return f"""import {dependency}
set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
namespace VastitasProof
open Lean VastitasKernel VastitasKernel.LLVM VastitasOracle.{namespace}
{body}
end VastitasProof
"""

    # Small packages need a single Lean invocation. At larger sizes each batch
    # imports its predecessor, preserving every checked row in the final export.
    parts = [bindings]
    for index, batch in enumerate(batches):
        parts.append(batch)
        if len(batches) > 1:
            name = f"PhysicalBatch{index}"
            yield name, module_source(dependency, "\n".join(parts))
            dependency = name
            parts = []
    parts.append(f"""{rows}
def wire : Json := {wire}
def revision : Json := Json.mkObj [{rev}]
def sources : PhysicalSources.Layout := ⟨{expected_files}, {natural(entry)}⟩
def packages : VastitasOracle.CertificatePackages.Graph := {package_graph}
def header : TargetHeader := ⟨⟨{triple_term}.toUTF8.data.toList, by decide⟩,
  ⟨{layout_term}.toUTF8.data.toList, by decide⟩⟩
def code : VastitasKernel.LLVM.{code_type}.Code := ⟨header, #[{', '.join(functions)}], {natural(model['entry'])}⟩
def headerBytes : List UInt8 := {header_bytes}
def lines : List String := [{lines}]
def subject : Subject := ⟨wire, revision, sources, packages, header, code,
  headerBytes ++ ("\\n" ++ String.intercalate "\\n" lines ++ "\\n").toUTF8.data.toList, {integer(model['value'])}⟩
{file_evidence}
theorem packageOwners : VastitasOracle.CertificatePackages.read wire = .ok packages := by
  with_unfolding_all rfl
def obligation : Prop := Valid subject
""")
    yield "Authority", module_source(dependency, "\n".join(parts))


def certificate(proof=PROOF, module="Authority"):
    return f"""import {module}
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
namespace VastitasProof
theorem checked : obligation := {proof}
#print axioms checked
end VastitasProof
"""


def flow_helpers(model, work, lean, phase):
    # Prove exactly the same two fields on the current code, in separate workers.
    # The full declarations and their proofs enter the authenticated export.
    # Reduce repeated calls in the kernel. In Lean 4.35.0 cbv can generate an
    # ill-typed ite_true application for a StateT guard in this computation.
    repeated_calls = any(sum(op[0] == "invoke" for op in block["ops"]) > 1
                         for function in model["functions"] for block in function["blocks"])
    evaluation = "by decide +kernel" if repeated_calls else "rfl"
    modules = [
        ("evaluation", "FlowEvaluation", "Authority",
         f"theorem evaluated : code.entryValue = some ({integer(model['value'])} : Int) := {evaluation}"),
        ("printing", "FlowPrinting", "FlowEvaluation",
         "theorem printed : code.print = subject.bytes :=\n"
         "  VastitasOracle.FlowCertificate.printedLines code headerBytes lines rfl (by with_unfolding_all rfl)"),
    ]
    for name, module, dependency, theorem in modules:
        source = f"""import {dependency}
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
namespace VastitasProof
{theorem}
end VastitasProof
"""
        (work / f"{module}.lean").write_text(source)
        phase(name, [*lean, "-DwarningAsError=true", "-o", f"{module}.olean", f"{module}.lean"])


def snapshot(candidate, authority_path, destination):
    """Compare the private authority in full, then extend it with the candidate's proof."""
    digest = hashlib.sha256()
    with os.fdopen(os.open(candidate, os.O_RDONLY | os.O_NONBLOCK), "rb") as src, authority_path.open("r+b", buffering=0) as image:
        info = os.fstat(src.fileno())
        prefix_size = os.fstat(image.fileno()).st_size
        require(stat.S_ISREG(info.st_mode) and prefix_size < info.st_size <= fast.MAX_EXPORT,
                "expected bounded regular certificate with a proof suffix")
        while expected := image.read(fast.CHUNK):
            require(src.read(len(expected)) == expected, "declaration environment differs from current input")
            digest.update(expected)
        total = prefix_size
        try:
            while block := src.read(fast.CHUNK):
                total += len(block)
                require(total <= info.st_size, "certificate grew during snapshot")
                digest.update(block)
                require(image.write(block) == len(block), "incomplete private certificate write")
            require(total == info.st_size, "truncated certificate")
            # Both names are in the verifier's private directory. The caller
            # drops the authority name before launching the independent checker.
            os.link(authority_path, destination)
        except BaseException:
            image.truncate(prefix_size)
            raise
    return {"bytes": total, "sha256": digest.hexdigest()}


def private_file_bytes(work):
    """Logical bytes in regular files at this checkpoint, counting hard links once."""
    seen = set()
    total = 0
    for path in work.iterdir():
        info = path.lstat()
        identity = (info.st_dev, info.st_ino)
        if stat.S_ISREG(info.st_mode) and identity not in seen:
            seen.add(identity)
            total += info.st_size
    return total


def environment(work, prefix):
    search = [work, ROOT / "lean/.lake/build/lib/lean", ROOT / "lean-kernel/.lake/build/lib/lean", prefix / "lib/lean"]
    return official.proof_environment(prefix, *search)


def verify(args, work, report):
    prefix = fast.pinned_lean("leanchecker") if args.mode == "official" else fast.pinned_tools()
    lean = lean_command(prefix, args.memory)
    report["lean_memory_limit_mib"] = args.memory
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
    report["physical_inputs"] = len(sources.files)
    preview = work / "preview.ll"
    phase("preview", [*cmd, "--llvm-preview", "--expect-function-revision", revision_path,
                      "--target-triple", args.target_triple, "--data-layout", args.data_layout], preview,
          run_from=source.parent)
    data = preview.read_bytes()
    graph = "flow" if b"\n; flow -> " in data else "program"
    namespace = "FlowCertificate" if graph == "flow" else "BoxedCertificate"
    model = json.loads(phase("capture", [*lean, "--run", HERE / "Capture.lean", revision_path,
                                         args.target_triple, args.data_layout, graph]), object_pairs_hook=fast.unique_fields)
    require(model["kind"] == graph and model["ir"].encode("utf-8") == data, "captured model and public LLVM bytes differ")
    report.update(bytes=len(data), llvm_sha256=official.digest(data), revision_sha256=official.digest(revision_path.read_bytes()),
                  functions=len(model["functions"]), integer_result=integer(model["value"]))
    for module, source_text in authority_modules(revision, model, args.target_triple, args.data_layout, data, sources):
        (work / (module + ".lean")).write_text(source_text)
        phase(module.lower(), [*lean, "-DwarningAsError=true", "-o", module + ".olean", module + ".lean"])
    module = "Authority"
    proof = PROOF
    required_roots = [root.replace("BoxedCertificate", namespace) for root in ROOTS]
    if graph == "flow":
        flow_helpers(model, work, lean, phase)
        module = "FlowPrinting"
        proof = FLOW_PROOF
        required_roots.extend(["VastitasProof.evaluated", "VastitasProof.printed"])
    if args.candidate is None:
        (work / "Certificate.lean").write_text(certificate(proof, module))
        axioms = phase("proof", [*lean, "-DwarningAsError=true", "-o", "Certificate.olean", "Certificate.lean"])
        official_axioms = re.fullmatch(r"'VastitasProof.checked' (?:does not depend on any axioms|depends on axioms: \[([^\]]*)\])\s*", axioms)
        require(official_axioms and set(filter(None, (official_axioms.group(1) or "").split(", "))) <= official.ALLOWED,
                "unexpected proof axioms")
    report["standard_environment"] = fast.standard(prefix, work)
    baseline = work / "authority.ndjson"
    closure, roots = fast.export_roots(work, env, prefix, baseline, module, required_roots, GOAL, "def",
                                       "boxed", args.timeout, reduction.measure)
    report["authority_closure"] = closure
    supplied = args.candidate
    if supplied is None:
        supplied = work / "generated.ndjson"
        phase("export_proof", [prefix / "bin/leanexport", "Certificate", "--", *roots, THEOREM], supplied)
    sealed = work / "sealed.ndjson"
    report["certificate"] = snapshot(supplied, baseline, sealed)
    report["private_file_bytes_at_seal"] = private_file_bytes(work)
    # Later stages read only the private, sealed file. Free the worker's copies
    # before the external checker needs memory and swap.
    baseline.unlink()
    if args.candidate is None:
        supplied.unlink()
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
    add_memory_argument(p)
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
