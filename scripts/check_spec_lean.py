#!/usr/bin/env python3
"""Exercise scripts/spec_resolve.lean against isolated fixture modules.

Run with the pinned toolchain on the path, as CI does:
lake -d lean env python3 scripts/check_spec_lean.py
Each case writes a statement pins file for fixture modules that exist only in a
temporary package, and checks that the resolver accepts it or rejects it with
the expected message. The fixtures use only Lean's prelude, so the case runs
need no project module. A fixture package earlier on the search path hides the
project's modules with the same top-level name, which the cases never import.
"""
import hashlib
import json
import os
from pathlib import Path
import subprocess
import tempfile


ROOT = Path(__file__).resolve().parents[1]
RESOLVER = ROOT / "scripts/spec_resolve.lean"

FIXTURES = {
    "VastitasOracle.SpecFixture": """
namespace VastitasOracle.SpecFixture
theorem good (n : Nat) : n + 0 = n := Nat.add_zero n
theorem other (n : Nat) : 0 + n = n := Nat.zero_add n
theorem withSorry : (1 : Nat) = 2 := sorry
axiom unsound : False
theorem withAxiom : (1 : Nat) = 2 := unsound.elim
def notTheorem : Nat := 1
theorem goodRenamed {m : Nat} : m + 0 = m := Nat.add_zero m
theorem poly.{u} (α : Sort (max u 1)) (a : α) : a = a := rfl
end VastitasOracle.SpecFixture
""",
    "VastitasOracle.SpecFixtureOther": """
namespace VastitasOracle.SpecFixtureOther
theorem unrelated : True := trivial
end VastitasOracle.SpecFixtureOther
""",
    "VastitasKernel.SpecFixture": """
namespace VastitasKernel.SpecFixture
def check (n : Nat) : Bool := n == 0
def withSorryDefinition : Nat := sorry
theorem notDefinition : True := trivial
end VastitasKernel.SpecFixture
namespace VastitasOracle.Misplaced
theorem elsewhere : True := trivial
end VastitasOracle.Misplaced
""",
    "VastitasBridge.SpecFixture": """
namespace VastitasBridge.SpecFixture
theorem good (n : Nat) : n * 1 = n := Nat.mul_one n
end VastitasBridge.SpecFixture
""",
    # A module without Lean's prelude that declares its own `propext`.
    "VastitasOracle.SpecEvil": """prelude
axiom propext : ∀ p : Prop, p
theorem VastitasOracle.SpecEvil.bad : ∀ p : Prop, p := propext
""",
    # Two modules that declare one theorem, which Lean merges on import.
    "VastitasOracle.SpecTwinA": """
theorem VastitasOracle.SpecTwin.t : True := trivial
""",
    "VastitasOracle.SpecTwinB": """
theorem VastitasOracle.SpecTwin.t : True := trivial
""",
    # An axiom and a theorem of one name and type, which Lean merges on import,
    # and a theorem that uses the merged constant.
    "VastitasOracle.SpecMergeAxiom": """
axiom VastitasOracle.SpecMerge.t : True
""",
    "VastitasOracle.SpecMergeTheorem": """
theorem VastitasOracle.SpecMerge.t : True := trivial
""",
    "VastitasOracle.SpecMerge": """
import VastitasOracle.SpecMergeAxiom
import VastitasOracle.SpecMergeTheorem
theorem VastitasOracle.SpecMerge.uses : True := VastitasOracle.SpecMerge.t
""",
    "VastitasOracle.SpecStaleBase": """
def VastitasOracle.SpecStale.k : Nat := 0
""",
    "VastitasOracle.SpecStale": """
import VastitasOracle.SpecStaleBase
theorem VastitasOracle.SpecStale.uses : VastitasOracle.SpecStale.k = 0 := rfl
""",
}

# The canonical text of `VastitasOracle.SpecFixture.poly.{u} (α : Sort (max u 1)) (a : α) : a = a`,
# which covers universe parameters, `max` and `succ` levels.
POLY_TEXT = ("vastitas-statement-v1 U{_.s1:u,} P(Sm(p_.s1:u;,sz); P(#0; "
             "A(A(A(C_.s2:Eq{m(sz,p_.s1:u;),} #1;) #0;) #0;)))")

# The canonical text of `VastitasOracle.SpecFixture.good`, `∀ n : Nat, n + 0 = n`.
# A change here is a change of the pin format, which changes every pin.
GOOD_TEXT = (
    "vastitas-statement-v1 U{} P(C_.s3:Nat{} A(A(A(C_.s2:Eq{sz,} C_.s3:Nat{}) "
    "A(A(A(A(A(A(C_.s4:HAdd.s4:hAdd{z,z,z,} C_.s3:Nat{}) C_.s3:Nat{}) C_.s3:Nat{}) "
    "A(A(C_.s8:instHAdd{z,} C_.s3:Nat{}) C_.s10:instAddNat{})) #0;) "
    "A(A(A(C_.s5:OfNat.s5:ofNat{z,} C_.s3:Nat{}) N0;) A(C_.s12:instOfNatNat{} N0;)))) #0;))")


def lean(arguments, environment, cwd):
    return subprocess.run(["lean", *map(str, arguments)], cwd=cwd, env=environment, text=True,
                          stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=600, check=False)


def compile_module(package, environment, module, source):
    output = package / ".lake/build/lib/lean"
    file = package.joinpath(*module.split(".")).with_suffix(".lean")
    file.parent.mkdir(parents=True, exist_ok=True)
    file.write_text(source, encoding="utf-8")
    target = output.joinpath(*module.split(".")).with_suffix(".olean")
    target.parent.mkdir(parents=True, exist_ok=True)
    result = lean(["--root", package, "-o", target, file], environment, package)
    if result.returncode:
        raise RuntimeError(f"fixture {module} failed to compile\n{result.stdout}")


def build(package):
    """Compile the fixture modules into `package/.lake/build/lib/lean`. Then
    recompile `VastitasOracle.SpecStaleBase` without the constant that the
    compiled `VastitasOracle.SpecStale` uses, so that its object file is stale."""
    output = package / ".lake/build/lib/lean"
    output.mkdir(parents=True)
    environment = dict(os.environ)
    environment["LEAN_PATH"] = os.pathsep.join(filter(None, [str(output), environment.get("LEAN_PATH")]))
    for module, source in FIXTURES.items():
        compile_module(package, environment, module, source)
    compile_module(package, environment, "VastitasOracle.SpecStaleBase", "def VastitasOracle.SpecStale.other : Nat := 0\n")
    return environment


def pins(environment_name, imports, entries):
    return {"format": 1, "environment": environment_name, "imports": imports, "entries": entries}


def run(environment, directory, data, report=False, extra=None):
    source = directory / "pins.json"
    source.write_text(json.dumps(data), encoding="utf-8")
    variables = dict(environment, VASTITAS_SPEC_INPUT=str(source))
    for name in ("VASTITAS_SPEC_REPORT", "VASTITAS_SPEC_CANONICAL", "VASTITAS_SPEC_STATEMENT_LIMIT"):
        variables.pop(name, None)
    variables.update(extra or {})
    output = directory / "report.json"
    if report:
        variables.update(VASTITAS_SPEC_REPORT=str(output), VASTITAS_SPEC_CANONICAL="1")
    result = lean(["-DwarningAsError=true", RESOLVER], variables, ROOT)
    if report:
        if result.returncode or not output.is_file():
            raise RuntimeError(f"report mode failed\n{result.stdout}")
        return json.loads(output.read_text(encoding="utf-8"))
    return result


def main():
    if not os.environ.get("LEAN_PATH"):
        raise SystemExit("run with: lake -d lean env python3 scripts/check_spec_lean.py")
    passed = 0
    with tempfile.TemporaryDirectory(prefix="vastitas-spec-lean-") as temporary:
        directory = Path(temporary)
        environment = build(directory / "package")
        fixture = ["VastitasKernel.SpecFixture", "VastitasOracle.SpecFixture", "VastitasOracle.SpecFixtureOther"]

        # Report mode: the facts, and the canonical text that the hash covers.
        facts = run(environment, directory, pins("oracle", fixture, [
            {"name": "VastitasOracle.SpecFixture.good", "kind": "theorem"},
            {"name": "VastitasOracle.SpecFixture.other", "kind": "theorem"},
            {"name": "VastitasOracle.SpecFixture.goodRenamed", "kind": "theorem"},
            {"name": "VastitasOracle.SpecFixture.poly", "kind": "theorem"},
            {"name": "VastitasKernel.SpecFixture.check", "kind": "definition"}]), report=True)
        if facts["problems"]:
            raise RuntimeError(f"valid fixtures reported problems: {facts['problems']}")
        found = {entry["name"]: entry for entry in facts["entries"]}
        good, other = found["VastitasOracle.SpecFixture.good"], found["VastitasOracle.SpecFixture.other"]
        renamed, poly = found["VastitasOracle.SpecFixture.goodRenamed"], found["VastitasOracle.SpecFixture.poly"]
        for entry in (good, other, renamed, poly):
            expected = "sha256:" + hashlib.sha256(entry["canonical"].encode("utf-8")).hexdigest()
            if entry["statement"] != expected:
                raise RuntimeError(f"Lean SHA-256 {entry['statement']} differs from Python's {expected}")
        if good["module"] != "VastitasOracle.SpecFixture" or good["kind"] != "theorem" \
                or not set(good["axioms"]) <= {"propext", "Classical.choice", "Quot.sound"}:
            raise RuntimeError(f"unexpected facts for good: {good}")
        if {key: value for key, value in found["VastitasKernel.SpecFixture.check"].items() if key != "axioms"} != {
                "name": "VastitasKernel.SpecFixture.check", "kind": "definition",
                "module": "VastitasKernel.SpecFixture"}:
            raise RuntimeError(f"unexpected facts for check: {found['VastitasKernel.SpecFixture.check']}")
        if good["canonical"] != GOOD_TEXT:
            raise RuntimeError(f"the canonical statement text changed:\n{good['canonical']}")
        if good["statement"] == other["statement"]:
            raise RuntimeError("two different statements have the same hash")
        if renamed["statement"] != good["statement"]:
            raise RuntimeError("renaming a binder or making it implicit changed the statement hash")
        if poly["canonical"] != POLY_TEXT:
            raise RuntimeError(f"the canonical text of a universe-polymorphic statement changed:\n{poly['canonical']}")
        print("passed: report mode, and Lean's SHA-256 equals Python's on the canonical text", flush=True)
        passed += 1

        def theorem(name, entry, **changes):
            return dict({"name": name, "kind": "theorem", "module": entry["module"],
                         "statement": entry["statement"]}, **changes)

        valid = [theorem("VastitasOracle.SpecFixture.good", good),
                 {"name": "VastitasKernel.SpecFixture.check", "kind": "definition",
                  "module": "VastitasKernel.SpecFixture"}]

        def case(label, data, expected=(), extra=None):
            nonlocal passed
            result = run(environment, directory, data, extra=extra)
            if not expected:
                if result.returncode or "resolved in" not in result.stdout:
                    raise RuntimeError(f"{label}: valid pins rejected\n{result.stdout}")
            elif not result.returncode or not all(text in result.stdout for text in expected):
                raise RuntimeError(f"{label}: expected a rejection containing {expected!r}\n{result.stdout}")
            print(f"passed: {label}", flush=True)
            passed += 1

        case("valid pins resolve", pins("oracle", fixture, valid))
        case("an inherited report variable keeps the comparison", pins("oracle", fixture, [
            theorem("VastitasOracle.SpecFixture.other", other, statement=good["statement"])]),
            ["has a changed statement"], extra={"VASTITAS_SPEC_REPORT": str(directory / "inherited.json")})
        case("a missing theorem", pins("oracle", fixture, valid + [
            theorem("VastitasOracle.SpecFixture.absent", good)]),
            ["VastitasOracle.SpecFixture.absent: is not found in the imported modules"])
        case("an unqualified theorem", pins("oracle", fixture, valid + [theorem("good", good)]),
             ["good: is not a fully qualified name under VastitasOracle"])
        case("a theorem in another module than its pin", pins("oracle", fixture, [
            theorem("VastitasOracle.SpecFixture.good", good, module="VastitasOracle.SpecFixtureOther")]),
            ["is defined in VastitasOracle.SpecFixture, not in the pinned module VastitasOracle.SpecFixtureOther"])
        case("a definition pinned as a theorem", pins("oracle", fixture, [
            theorem("VastitasOracle.SpecFixture.notTheorem", good)]),
            ["VastitasOracle.SpecFixture.notTheorem: is a definition, not a theorem"])
        case("a theorem pinned as a kernel definition", pins("oracle", fixture, [
            {"name": "VastitasKernel.SpecFixture.notDefinition", "kind": "definition",
             "module": "VastitasKernel.SpecFixture"}]),
            ["VastitasKernel.SpecFixture.notDefinition: is a theorem, not a definition"])
        case("a theorem that uses sorry", pins("oracle", fixture, [
            theorem("VastitasOracle.SpecFixture.withSorry", good)]),
            ["withSorry: depends on the unapproved axiom sorryAx"])
        case("a theorem that uses another axiom", pins("oracle", fixture, [
            theorem("VastitasOracle.SpecFixture.withAxiom", good)]),
            ["withAxiom: depends on the unapproved axiom VastitasOracle.SpecFixture.unsound"])
        case("a changed statement", pins("oracle", fixture, [
            theorem("VastitasOracle.SpecFixture.other", other, statement=good["statement"])]),
            ["VastitasOracle.SpecFixture.other: has a changed statement", good["statement"], other["statement"]])
        case("a pin without a statement", pins("oracle", fixture, [
            {"name": "VastitasOracle.SpecFixture.good", "kind": "theorem", "module": "VastitasOracle.SpecFixture"}]),
            ["VastitasOracle.SpecFixture.good: has no pinned statement"])
        case("a missing kernel definition", pins("oracle", fixture, [
            {"name": "VastitasKernel.SpecFixture.absent", "kind": "definition", "module": "VastitasKernel.SpecFixture"}]),
            ["VastitasKernel.SpecFixture.absent: is not found in the imported modules"])
        case("an oracle theorem defined in a kernel module", pins("oracle", fixture, [
            theorem("VastitasOracle.Misplaced.elsewhere", good, module="VastitasKernel.SpecFixture")]),
            ["VastitasOracle.Misplaced.elsewhere: is defined in VastitasKernel.SpecFixture, outside VastitasOracle"])
        case("a kernel definition outside VastitasKernel", pins("oracle", fixture, [
            {"name": "VastitasOracle.SpecFixture.notTheorem", "kind": "definition",
             "module": "VastitasOracle.SpecFixture"}]),
            ["is not a fully qualified name under VastitasKernel",
             "is defined in VastitasOracle.SpecFixture, outside VastitasKernel"])
        bridge = run(environment, directory, pins("bridge", ["VastitasBridge.SpecFixture"], [
            {"name": "VastitasBridge.SpecFixture.good", "kind": "theorem"}]), report=True)
        case("valid bridge pins resolve", pins("bridge", ["VastitasBridge.SpecFixture"], [
            theorem("VastitasBridge.SpecFixture.good", bridge["entries"][0])]))
        case("a kernel definition in the bridge environment", pins("bridge", fixture, [
            {"name": "VastitasKernel.SpecFixture.check", "kind": "definition", "module": "VastitasKernel.SpecFixture"}]),
            ["the bridge environment resolves no definition"])
        case("an oracle theorem in the bridge environment", pins("bridge", fixture, [
            theorem("VastitasOracle.SpecFixture.good", good)]),
            ["is not a fully qualified name under VastitasBridge", "outside VastitasBridge"])
        case("a kernel definition that uses sorry", pins("oracle", fixture, [
            {"name": "VastitasKernel.SpecFixture.withSorryDefinition", "kind": "definition",
             "module": "VastitasKernel.SpecFixture"}]),
            ["withSorryDefinition: depends on the unapproved axiom sorryAx"])
        case("an axiom named propext outside Lean's prelude", pins("oracle", ["VastitasOracle.SpecEvil"], [
            {"name": "VastitasOracle.SpecEvil.bad", "kind": "theorem", "module": "VastitasOracle.SpecEvil",
             "statement": good["statement"]}]),
            ["the imported modules declare the axiom propext in VastitasOracle.SpecEvil, not in Init.Core",
             "bad: depends on the unapproved axiom propext of VastitasOracle.SpecEvil"])
        case("a theorem that two modules declare", pins(
            "oracle", ["VastitasOracle.SpecTwinA", "VastitasOracle.SpecTwinB"], [
                {"name": "VastitasOracle.SpecTwin.t", "kind": "theorem", "module": "VastitasOracle.SpecTwinA",
                 "statement": good["statement"]}]),
            ["VastitasOracle.SpecTwin.t: is declared by more than one imported module"])
        case("a theorem that reaches an axiom merged with a theorem", pins("oracle", ["VastitasOracle.SpecMerge"], [
            {"name": "VastitasOracle.SpecMerge.uses", "kind": "theorem", "module": "VastitasOracle.SpecMerge",
             "statement": good["statement"]}]),
            ["uses: depends on the unapproved axiom VastitasOracle.SpecMerge.t"])
        case("a theorem that reaches a constant its modules no longer define", pins(
            "oracle", ["VastitasOracle.SpecStale"], [
                {"name": "VastitasOracle.SpecStale.uses", "kind": "theorem", "module": "VastitasOracle.SpecStale",
                 "statement": good["statement"]}]),
            ["uses: reaches VastitasOracle.SpecStale.k, which the imported modules do not define"])
        case("a pin without a module", pins("oracle", fixture, [
            {"name": "VastitasOracle.SpecFixture.good", "kind": "theorem", "statement": good["statement"]}]),
            ["VastitasOracle.SpecFixture.good: has no pinned module"])
        case("a name with an empty component", pins("oracle", fixture, [
            theorem("VastitasOracle..good", good)]), ["VastitasOracle..good: is not a Lean name"])
        case("another input format", dict(pins("oracle", fixture, valid), format=2), ["the input must have format 1"])
        case("an import that is not a module name", pins("oracle", fixture + ["Vastitas Oracle"], valid),
             ["the import `Vastitas Oracle` is not a module name"])
        case("no modules to import", pins("oracle", [], valid), ["no modules to import"])
        result = run(environment, directory, pins("oracle", fixture, valid), extra={"VASTITAS_SPEC_STATEMENT_LIMIT": "100"})
        if not result.returncode or "more than 100 bytes of canonical text" not in result.stdout:
            raise RuntimeError(f"a statement over the size limit was not rejected\n{result.stdout}")
        print("passed: a statement longer than the size limit", flush=True)
        passed += 1
        case("no pinned declarations", pins("oracle", fixture, []), ["no pinned declarations"])
        case("an unknown environment", pins("mathlib", fixture, valid),
             ["unknown specification environment mathlib"])
    print(f"specification resolver regressions passed: {passed} cases")


if __name__ == "__main__":
    main()
