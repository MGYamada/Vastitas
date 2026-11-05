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
}

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


def build(package):
    """Compile the fixture modules into `package/.lake/build/lib/lean`."""
    output = package / ".lake/build/lib/lean"
    output.mkdir(parents=True)
    environment = dict(os.environ)
    environment["LEAN_PATH"] = os.pathsep.join(filter(None, [str(output), environment.get("LEAN_PATH")]))
    for module, source in FIXTURES.items():
        file = package.joinpath(*module.split(".")).with_suffix(".lean")
        file.parent.mkdir(parents=True, exist_ok=True)
        file.write_text(source, encoding="utf-8")
        target = output.joinpath(*module.split(".")).with_suffix(".olean")
        target.parent.mkdir(parents=True, exist_ok=True)
        result = lean(["--root", package, "-o", target, file], environment, package)
        if result.returncode:
            raise RuntimeError(f"fixture {module} failed to compile\n{result.stdout}")
    return environment


def pins(environment_name, imports, entries):
    return {"format": 1, "environment": environment_name, "imports": imports, "entries": entries}


def run(environment, directory, data, report=False):
    source = directory / "pins.json"
    source.write_text(json.dumps(data), encoding="utf-8")
    variables = dict(environment, VASTITAS_SPEC_INPUT=str(source))
    variables.pop("VASTITAS_SPEC_REPORT", None)
    variables.pop("VASTITAS_SPEC_CANONICAL", None)
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
            {"name": "VastitasKernel.SpecFixture.check", "kind": "definition"}]), report=True)
        if facts["problems"]:
            raise RuntimeError(f"valid fixtures reported problems: {facts['problems']}")
        found = {entry["name"]: entry for entry in facts["entries"]}
        good, other = found["VastitasOracle.SpecFixture.good"], found["VastitasOracle.SpecFixture.other"]
        for entry in (good, other):
            expected = "sha256:" + hashlib.sha256(entry["canonical"].encode("utf-8")).hexdigest()
            if entry["statement"] != expected:
                raise RuntimeError(f"Lean SHA-256 {entry['statement']} differs from Python's {expected}")
        if good["module"] != "VastitasOracle.SpecFixture" or good["kind"] != "theorem" \
                or not set(good["axioms"]) <= {"propext", "Classical.choice", "Quot.sound"}:
            raise RuntimeError(f"unexpected facts for good: {good}")
        if found["VastitasKernel.SpecFixture.check"] != {
                "name": "VastitasKernel.SpecFixture.check", "kind": "definition",
                "module": "VastitasKernel.SpecFixture"}:
            raise RuntimeError(f"unexpected facts for check: {found['VastitasKernel.SpecFixture.check']}")
        if good["canonical"] != GOOD_TEXT:
            raise RuntimeError(f"the canonical statement text changed:\n{good['canonical']}")
        if good["statement"] == other["statement"]:
            raise RuntimeError("two different statements have the same hash")
        print("passed: report mode, and Lean's SHA-256 equals Python's on the canonical text", flush=True)
        passed += 1

        def theorem(name, entry, **changes):
            return dict({"name": name, "kind": "theorem", "module": entry["module"],
                         "statement": entry["statement"]}, **changes)

        valid = [theorem("VastitasOracle.SpecFixture.good", good),
                 {"name": "VastitasKernel.SpecFixture.check", "kind": "definition",
                  "module": "VastitasKernel.SpecFixture"}]

        def case(label, data, expected=()):
            nonlocal passed
            result = run(environment, directory, data)
            if not expected:
                if result.returncode or "resolved in" not in result.stdout:
                    raise RuntimeError(f"{label}: valid pins rejected\n{result.stdout}")
            elif not result.returncode or not all(text in result.stdout for text in expected):
                raise RuntimeError(f"{label}: expected a rejection containing {expected!r}\n{result.stdout}")
            print(f"passed: {label}", flush=True)
            passed += 1

        case("valid pins resolve", pins("oracle", fixture, valid))
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
        case("no pinned declarations", pins("oracle", fixture, []), ["no pinned declarations"])
        case("an unknown environment", pins("mathlib", fixture, valid),
             ["unknown specification environment mathlib"])
    print(f"specification resolver regressions passed: {passed} cases")


if __name__ == "__main__":
    main()
