"""Synthetic join/repair example and optional existing kernel-response import."""

import argparse
import hashlib
import itertools
import json
from pathlib import Path

import diagnostic_reference as dr


# A finite truth-table experiment, not a replacement for nominal dispatch.
METHODS = {"default": ("Any", "Any"), "A": ("Number", "Any"),
           "B": ("Any", "Number"), "repair": ("Number", "Number")}


def dispatch_table(names):
    def matches(selector, scalar):
        return selector == "Any" or scalar in ("Nat", "Int")

    def stricter(left, right):
        return left != right and all(a == b or (a == "Number" and b == "Any")
                                     for a, b in zip(left, right))

    return {key: tuple(name for name in applicable if not any(
                stricter(METHODS[other], METHODS[name]) for other in applicable))
            for key in itertools.product(dr.SCALARS, repeat=2)
            for applicable in [[name for name in names if all(
                matches(selector, scalar) for selector, scalar in zip(METHODS[name], key))]]}


def fixture():
    def ref(package, declaration):
        return {"package": "fixture:" + package, "revision": "r1", "declaration": declaration}

    def role(name, subject):
        return {"role": name, "status": "unresolved", "basis": "reference_fixture", "subject": subject}

    function, assembly = ref("base", "choose"), ref("app", "root-assembly")
    a, b = ref("addon", "A.method-0"), ref("addon", "B.method-0")
    by_name = {"A": a, "B": b}
    table = dispatch_table(("default", "A", "B"))
    conflicts = {name for winners in table.values() if len(winners) > 1 for name in winners}
    pins = [{"package": "fixture:" + name, "revision": "r1"} for name in ("app", "base", "addon")]
    source = package_sources(("A", "B"), repair=False)
    return {"schema": dr.SCHEMA, "origin": "reference_fixture", "semantic": {
        "code": "E_DISPATCH_AMBIGUOUS", "outcome": "rejected", "phase": "assembly_completion",
        "obligation": {"kind": "dispatch_unique", "id": "choose:unique-winner", "status": "unresolved"},
        "function": function, "assembly": assembly,
        "participants": [role("function_authority", ref("base", "root-module")),
                         role("method_contributor", a), role("method_contributor", b)],
        "holder": role("current_obligation_holder", assembly),
        "conflict_set": [by_name[name] for name in sorted(conflicts)],
        "witness_keys": [list(key) for key, winners in table.items() if len(winners) > 1],
        "history": [{"op": "borrow", "subject": ref("base", "integers"), "loan": "edit"},
                    {"op": "apply", "subject": a, "loan": "edit"},
                    {"op": "apply", "subject": b, "loan": "edit"},
                    {"op": "return", "subject": function, "loan": "edit"},
                    {"op": "seal", "subject": function, "loan": None}],
        "environment": {"profile": dr.PROFILE,
                        "input_revision": "sha256:" + hashlib.sha256(dr.canonical_json(source)).hexdigest(),
                        "environment_revision": "fixture-env:r1", "compiler_revision": "reference:r1",
                        "toolchain_revision": "reference:r1", "dependencies": pins,
                        "dependency_edges": [{"from": pins[0], "to": pins[1]},
                                             {"from": pins[0], "to": pins[2]},
                                             {"from": pins[2], "to": pins[1]}]}},
        "presentation": {"diagnostic": {"code": "E_DISPATCH_AMBIGUOUS",
            "message": "The two contributions overlap at the joined assembly.",
            "span": {"start": 0, "end": 0, "line": 1, "column": 1}},
            "source_path": "example/app/main.vast",
            "next_action": "After returning the edit loan, apply the authorized Number x Number "
                           "owner repair and recheck before sealing."}, "external_candidates": []}


def package_sources(names, repair=False):
    """Adapt open_return_can_be_repaired_by_owner_before_seal into separate A/B.

    These files can be passed to the actual compiler; the Python truth table
    does not validate their bodies, authority or borrow/return transitions.
    """
    region = ", ".join(f"({a}, {b})" for a, b in itertools.product(dr.SCALARS, repeat=2))
    base = f'''pub generic choose(x, y) {{ domain (Int, Int); }}
method choose(x: Any, y: Any) -> Int {{ 0 }}
pub grant integers : choose to module("../addon/Vastitas.toml", "") {{ domain {region}; }}
pub contribution repair : choose {{ method choose(x: Number, y: Number) -> Int {{ 42 }} }}
'''
    addon = '''pub contribution A : base::choose {
method base::choose(x: Number, y: Any) -> Int { 1 } }
pub contribution B : base::choose {
method base::choose(x: Any, y: Number) -> Int { 2 } }
'''
    events = "borrow base::integers as edit; "
    events += " ".join(f"apply addon::{name} using edit;" for name in names)
    events += " return edit; " + ("apply base::repair; " if repair else "") + "seal base::choose;"
    app = "assembly { " + events + " } fn main() -> Int { base::choose(40, 2) }"
    files = {}
    for name, source, deps in (("base", base, ""), ("addon", addon, "base={path='../base'}"),
                               ("app", app, "base={path='../base'}\naddon={path='../addon'}")):
        files[f"{name}/main.vast"] = source
        files[f"{name}/Vastitas.toml"] = (
            f"[package]\nname='{name}'\nversion='0.1.0'\nroot='main.vast'\n[dependencies]\n{deps}\n")
    return files


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json", action="store_true", help="emit the same record plus identity projection")
    parser.add_argument("--kernel-response", type=Path, help="read a saved failure envelope; no ledger assumed")
    parser.add_argument("--expected-version", type=int)
    args = parser.parse_args()
    if args.kernel_response:
        if args.expected_version is None:
            parser.error("--kernel-response requires --expected-version from the actual request")
        records = dr.from_kernel_response(dr.load_json(args.kernel_response.read_text()), args.expected_version)
    else:
        records = [fixture()]
    for record in records:
        print(json.dumps(dr.machine_report(record), indent=2) if args.json else dr.render(record))
    # Importing a failed compiler result must not report compiler success.
    return 1 if args.kernel_response else 0


if __name__ == "__main__":
    raise SystemExit(main())
