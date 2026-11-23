#!/usr/bin/env python3
"""Compare checked boxed libraries and hosted programs with generated Lean controls."""
import argparse
import json
import operator
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
BIG = 2**130 + 7


def quotient(a, b):
    # Lean Int uses Euclidean division for either sign of the divisor.
    return 0 if b == 0 else (a - a % abs(b)) // b


def cases():
    for kind in ("Nat", "Int"):
        for glyph, operation in [("+", lambda a, b: a + b), ("-", lambda a, b: a - b),
                                 ("*", lambda a, b: a * b), ("/", quotient)]:
            fn = (lambda a, b: max(0, a - b)) if (kind, glyph) == ("Nat", "-") else operation
            yield (kind, kind), kind, f"a {glyph} b", f"a {glyph} b", fn
    yield ("Nat", "Int"), "Int", "a / b", "Int.ofNat a / b", quotient
    yield ("Int", "Nat"), "Int", "std::operator::div(a, b)", "a / Int.ofNat b", quotient
    yield ("Int",), "Int", "-a", "-a", lambda a: -a
    yield ("Nat",), "Int", "int(a)", "Int.ofNat a", lambda a: a
    yield ("Nat",), "Nat", "let unused = a * a; a", "a", lambda a: a
    yield ("Int",), "Int", f"a + (-{BIG})", f"a + (-{BIG})", lambda a: a - BIG
    yield ("Nat", "Int"), "Int", None, "let q := Int.ofNat (a - 5) / b; q + q", (
        lambda n, d: 2 * quotient(max(0, n - 5), d))


def inputs(kinds):
    values = [0, 2, 7, BIG]
    if len(kinds) == 1:
        return [(a,) for a in (values + ([-7, -BIG] if kinds[0] == "Int" else []))]
    pairs = [(0, 0), (7, 0), (2, 5), (7, 3), (BIG, BIG + 2), (BIG + 2, 3)]
    if kinds[0] == "Int":
        pairs += [(-7, 3), (-BIG, 0), (-BIG, 7)]
    if kinds[1] == "Int":
        pairs += [(7, -3), (BIG, -7)]
    if kinds == ("Int", "Int"):
        pairs += [(-7, -3), (-BIG, -7)]
    return pairs


def ownership_probe(kinds):
    """Check each distinct heap argument before and after dropping the owned result."""
    ctors = {"Nat": "lean_cstr_to_nat", "Int": "lean_cstr_to_int"}
    # Equal sorts share the same heap object in both argument positions.
    distinct = list(dict.fromkeys(kinds))
    signature = ", ".join("b_lean_obj_arg" for _ in kinds)
    actuals = ", ".join(f"inputs[{distinct.index(k)}]" for k in kinds)
    heap = ", ".join(f'{ctors[k]}("{BIG if k == "Nat" else -BIG}")' for k in distinct)
    return f"""#include <lean/lean.h>
extern lean_obj_res vq_exact({signature});
uint8_t vq_ownership_probe(uint8_t seed) {{
    (void)seed;
    lean_object *inputs[] = {{{heap}}};
    int before[{len(distinct)}];
    for (size_t i = 0; i < {len(distinct)}; ++i) {{
        if (lean_is_scalar(inputs[i])) return 0;
        lean_inc(inputs[i]);
        before[i] = lean_internal_get_rc(inputs[i]);
    }}
    lean_object *result = vq_exact({actuals});
    for (size_t i = 0; i < {len(distinct)}; ++i)
        if (lean_internal_get_rc(inputs[i]) != before[i] + (result == inputs[i])) return 0;
    lean_dec(result);
    for (size_t i = 0; i < {len(distinct)}; ++i) {{
        if (lean_internal_get_rc(inputs[i]) != before[i]) return 0;
        lean_dec(inputs[i]);
        lean_dec(inputs[i]);
    }}
    return 1;
}}
"""


def output(cmd, **opts):
    return subprocess.check_output(cmd, text=True, **opts).strip()


def check_comparison_control(prefix, sdk, work, emit):
    source = "ComparisonMethodControl.lean"
    shutil.copyfile(ROOT / "llvm/fixtures" / source, work / source)
    subprocess.run([prefix / "bin/lean", "-c", "predicates.c", source], check=True, cwd=work)
    subprocess.run([prefix / "bin/leanc", *sdk, "predicates.c", "-o", "predicates"], check=True, cwd=work)
    values = [(1, 1), (2**128 + 1, 2**128 + 257), (2**1024 + 1, 2**1024 - 255), (0, 2**128)]
    predicates = [("==", operator.eq), ("!=", operator.ne), ("<", operator.lt),
                  ("<=", operator.le), (">", operator.gt), (">=", operator.ge)]
    probe = ROOT / "llvm/fixtures/IntegerPredicateProbe.c"
    subprocess.run(["cc", *sdk, "-std=c11", "-O2", "-I", prefix / "include", "-c", probe, "-o", "predicate-probe.o"],
                   check=True, cwd=work)

    def compile_candidate(name, source):
        obj = f"predicate-{name}.o"
        emit(source, obj)
        subprocess.run([prefix / "bin/leanc", *sdk, "predicate-probe.o", obj, "shim.o",
                        "-o", "candidate"], check=True, cwd=work)

    def check_candidate(kind, a, b, expected, alias=False):
        mode = "alias" if alias else "distinct"
        actual = output([work / "candidate", kind, str(a), str(b), mode], cwd=work)
        if actual != expected:
            raise ValueError(f"{kind} comparison on {a} and {b} ({mode}): expected {expected}, got {actual}")
    count = 0
    for kind, sign in [("Nat", 1), ("Int", -1)]:
        for code, (glyph, predicate) in enumerate(predicates):
            compile_candidate(f"{kind}-{code}", f"pub fn compare(a: {kind}, b: {kind}) -> Bool {{ a {glyph} b }}")
            for x, y in values:
                a, b = sign * x, sign * y
                result = output([work / "predicates", kind, str(code), str(a), str(b)], cwd=work)
                expected = "42" if predicate(a, b) else "7"
                check_candidate(kind, a, b, expected)
                if result != expected:
                    raise ValueError(f"{kind} {predicate.__name__}: wrong native control result for {a} and {b}")
                count += 1
            heap = sign * (2**1024 + 1)
            check_candidate(kind, heap, heap, "42" if predicate(heap, heap) else "7", alias=True)
    compile_candidate("offset", (ROOT / "llvm/fixtures/IntegerPredicate.vast").read_text())
    for delta in (-257, -256, -255, 1):
        a, b = -(2**1024 + 1), -(2**1024 + 1) + delta
        check_candidate("Int", a, b, "42" if a - 256 <= b else "7")
    emit("pub fn pick(a: Bool) -> Bool { a }", "bool-id.o")
    (work / "bool-id.c").write_text("#include <stdint.h>\nextern uint32_t vq_exact(uint32_t);\n"
                                   "int main(void) { return vq_exact(0) != 0 || vq_exact(1) != 1; }\n")
    subprocess.run(["cc", *sdk, "bool-id.c", "bool-id.o", "-o", "bool-id"], cwd=work, check=True)
    subprocess.run([work / "bool-id"], cwd=work, check=True)
    print(f"{count} compiled predicate results matched generated Lean/C and unbounded integers", flush=True)
    print("12 aliased heap comparisons and 4 comparisons using owned temporaries passed", flush=True)


def native(args, work):
    prefix = Path(output(["lean", "--print-prefix"], cwd=ROOT))
    sdk = ["-isysroot", output(["xcrun", "--show-sdk-path"])] if sys.platform == "darwin" else []
    clang = prefix / "bin/clang"
    leanc = prefix / "bin/leanc"
    if args.backend:
        target = dict(row.split("=", 1) for row in output([args.backend, "describe"]).splitlines())
        if target["llvm"] != "23.1.4":
            raise ValueError("expected LLVM 23.1.4")
    else:
        probe = output([clang, "-x", "c", "-S", "-emit-llvm", "-", "-o", "-"], input="void probe(void) {}")
        target = dict(re.findall(r'^target (triple|datalayout) = "([^"]+)"', probe, flags=re.M))
        target["layout"] = target["datalayout"]
    def run(cmd):
        subprocess.run(cmd, cwd=work, check=True)

    run([leanc, *sdk, "-O2", "-c", ROOT / "llvm/runtime/exact.c", "-o", "shim.o"])
    run([leanc, *sdk, "-O2", "-Dvastitas_exit_status_v1=original_exit_status",
         "-c", ROOT / "llvm/runtime/exact.c", "-o", "observed-shim.o"])
    run(["cc", *sdk, "-std=c11", "-O2", "-I", prefix / "include",
         "-c", ROOT / "llvm/fixtures/BoxedResultProbe.c", "-o", "probe.o"])

    def check_integer(obj, expected):
        # Relink the same object. The probe borrows the entire Int before the
        # production projection consumes it. Both controls have the same status.
        run([leanc, *sdk, obj, "observed-shim.o", "probe.o", "-o", "observed"])
        for candidate, verdict in [(expected, "match"), (expected + 256, "mismatch")]:
            child = subprocess.run([work / "observed"], cwd=work, capture_output=True, text=True,
                                   env={**os.environ, "VASTITAS_TEST_EXPECT_INTEGER": str(candidate)})
            if child.returncode != expected % 256 or child.stdout != verdict + "\n" or child.stderr:
                raise ValueError(f"{obj}: full integer comparison failed for {candidate}")
    (work / "Vastitas.toml").write_text('[package]\nname = "exact"\nversion = "0.1.0"\n'
                                       'edition = "2026"\nroot = "main.vast"\n')
    check = [args.frontend, "check", "--manifest-path", work / "Vastitas.toml"]
    preview = [*check, "--llvm-preview", "--target-triple", target["triple"], "--data-layout", target["layout"]]

    def emit_preview(command, obj):
        if (work / obj).exists():
            raise ValueError(f"duplicate native fixture output: {obj}")
        verified = subprocess.check_output(command, cwd=ROOT)
        (work / "checked.ll").write_bytes(verified)
        if args.backend:
            (work / "handoff.ll").write_bytes(verified)
            run([args.backend, "emit", "checked.ll", "handoff.ll", obj])
        else:
            run([clang, "-Werror=override-module", "-c", "checked.ll", "-o", obj])

    def emit(source, obj):
        (work / "main.vast").write_text(source)
        emit_preview(preview, obj)

    check_comparison_control(prefix, sdk, work, emit)
    count = examples = 0
    for kinds, result, vast_expr, lean_expr, evaluate in cases():
        names = "ab"[:len(kinds)]
        params = list(zip(names, kinds))
        if vast_expr is None:
            source = (ROOT / "llvm/fixtures/BoxedArithmetic.vast").read_text()
        else:
            signature = ", ".join(f"{a}: {k}" for a, k in params)
            source = f"pub fn calculate({signature}) -> {result} {{ {vast_expr} }}"
        obj = f"exact-{count}.o"
        emit(source, obj)
        binders = " ".join(f"({a} : @& {k})" for a, k in params)
        call = " ".join(names)
        rows = inputs(kinds)
        (work / "ownership.c").write_text(ownership_probe(kinds))
        control = ['@[extern "vq_ownership_probe"] opaque ownershipProbe (seed : UInt8) : Bool',
                   f'@[extern "vq_exact"] opaque candidate {binders} : {result}',
                   f"@[noinline] def reference {binders} : {result} := {lean_expr}",
                   f"def checkValue {binders} (expected : {result}) : IO Unit := do",
                   f"  let actual := candidate {call}",
                   f"  unless actual == expected && reference {call} == expected do",
                   '    throw (IO.userError s!"expected {expected}, received {actual}")',
                   "def main : IO Unit := do",
                   '  unless ownershipProbe 1 do throw (IO.userError "invalid borrow or result reference count")']
        control.extend("  checkValue " + " ".join(f"({n})" for n in (*row, evaluate(*row))) for row in rows)
        (work / "Control.lean").write_text("\n".join(control) + "\n")
        run([prefix / "bin/lean", "-c", "Control.c", "Control.lean"])
        run([leanc, *sdk, "Control.c", "ownership.c", "shim.o", obj, "-o", "compare"])
        run([work / "compare"])
        count += 1
        examples += len(rows)
    for kind in ("Nat", "Int"):
        obj = f"swap-{kind}.o"
        emit(f"pub fn swap(p: Pair<{kind}>) -> Pair<{kind}> {{ pair(pair_second(p), pair_first(p)) }}", obj)
        pair_type = f"({kind} × {kind})"
        left = BIG if kind == "Nat" else -BIG
        control = [
            '@[extern "vq_pair_ownership"] opaque ownership (useNat : UInt8) : Bool',
            f'@[extern "vq_exact"] opaque candidate (p : @& {pair_type}) : {pair_type}',
            f"@[noinline] def reference (p : @& {pair_type}) : {pair_type} := (p.2, p.1)",
            "def main : IO Unit := do",
            f'  unless ownership {int(kind == "Nat")} do throw (IO.userError "incorrect pair reference counts")',
            f"  for input in [(({left}), {BIG + 2}), (({left}), ({left})), (0, 1)] do",
            "    unless candidate input == reference input && candidate input == (input.2, input.1) do",
            '      throw (IO.userError "incorrect ordered pair components")',
        ]
        (work / "SwapControl.lean").write_text("\n".join(control) + "\n")
        run([prefix / "bin/lean", "-c", "SwapControl.c", "SwapControl.lean"])
        run([leanc, *sdk, "SwapControl.c", ROOT / "llvm/fixtures/PairOwnership.c", "shim.o", obj, "-o", "swap"])
        run([work / "swap"])

    pair_source = (ROOT / "llvm/fixtures/BoxedPairs.vast").read_text()
    for source, obj, expected in [(pair_source, "applied-pair.o", 42),
                                  (pair_source.replace("apply prioritized;", ""), "default-pair.o", 2**128 + 43)]:
        emit(source, obj)
        check_integer(obj, expected)
        run([leanc, *sdk, "shim.o", obj, "-o", "pairs"])
        if subprocess.run([work / "pairs"], cwd=work).returncode != expected % 256:
            raise ValueError("pair-returning method selected the wrong exit")
    projection = (ROOT / "llvm/fixtures/SelectedProjection.vast").read_text()
    (work / "ProjectionControl.lean").write_bytes((ROOT / "llvm/fixtures/SelectedProjectionControl.lean").read_bytes())
    run([prefix / "bin/lean", "-c", "ProjectionControl.c", "ProjectionControl.lean"])
    run([leanc, *sdk, "ProjectionControl.c", "-o", "projection-control"])
    for source, obj, field, expected in [(projection, "applied-projection.o", ["second"], 19),
                                         (projection.replace("apply second_field;", ""), "default-projection.o", [], 7)]:
        emit(source, obj)
        reference = subprocess.run([work / "projection-control", *field], cwd=work).returncode
        if reference != expected:
            raise ValueError("compiled Lean selected the wrong field")
        check_integer(obj, reference)
    negation = (ROOT / "llvm/fixtures/AssembledNegation.vast").read_text()
    (work / "NegationControl.lean").write_bytes((ROOT / "llvm/fixtures/AssembledNegationControl.lean").read_bytes())
    run([prefix / "bin/lean", "-c", "NegationControl.c", "NegationControl.lean"])
    run([leanc, *sdk, "NegationControl.c", "-o", "negation-control"])
    magnitude = 2**128 + 43
    for body, obj, argv, expected in [(negation, "applied-negation.o", ["flip"], -magnitude),
                                      (negation.replace("apply reversing;", ""), "default-negation.o", [], magnitude)]:
        emit(body, obj)
        reference = int(output([work / "negation-control", *argv]))
        if reference != expected:
            raise ValueError("compiled Lean returned the wrong signed integer")
        check_integer(obj, reference)
    conversion = (ROOT / "llvm/fixtures/AssembledConversion.vast").read_text()
    if conversion.count("apply exact;") != 1:
        raise ValueError("expected one applied conversion method")
    for body, obj, expected in [(conversion, "applied-conversion.o", 2**128 + 43),
                                (conversion.replace("apply exact;", ""), "default-conversion.o", 0)]:
        emit(body, obj)
        check_integer(obj, expected)
    hosted = (ROOT / "llvm/fixtures/BoxedProgram.vast").read_text()
    numerator = -(2**128 + 1)
    divisors = [3, 0, 1]
    for divisor in divisors:
        obj = f"hosted-{divisor}.o"
        emit(hosted.replace(", 3)", f", {divisor})"), obj)
        run([leanc, *sdk, "shim.o", obj, "-o", "hosted"])
        control = ["@[noinline] def keep (x : @& Int) : Int := x",
                   "@[noinline] def twice (x : @& Int) : Int := keep x + x",
                   "@[noinline] def quotient (x : @& Int) (d : @& Nat) : Int := x / Int.ofNat d",
                   f"def main : IO UInt32 := pure (((quotient (twice ({numerator})) {divisor}) % 256).toNat.toUInt32)"]
        (work / "HostedControl.lean").write_text("\n".join(control) + "\n")
        run([prefix / "bin/lean", "-c", "HostedControl.c", "HostedControl.lean"])
        run([leanc, *sdk, "HostedControl.c", "-o", "control"])
        full = quotient(2 * numerator, divisor)
        check_integer(obj, full)
        expected = full % 256
        for executable in ["hosted", "control"]:
            observed = subprocess.run([work / executable], cwd=work).returncode
            if observed != expected:
                raise ValueError(f"{executable} with divisor {divisor}: expected {expected}, got {observed}")
    emit((ROOT / "llvm/fixtures/SingletonPower.vast").read_text(), "power.o")
    check_integer("power.o", 3**256 // 7)
    run([leanc, *sdk, "shim.o", "power.o", "-o", "power"])
    control = ["@[noinline] def powerQuotient (x0 : @& Int) : Int :="]
    control.extend(f"  let x{i+1} := x{i} * x{i}" for i in range(8))
    control += ["  x8 / 7", "def main : IO UInt32 := pure (((powerQuotient 3) % 256).toNat.toUInt32)"]
    (work / "PowerControl.lean").write_text("\n".join(control) + "\n")
    run([prefix / "bin/lean", "-c", "PowerControl.c", "PowerControl.lean"])
    run([leanc, *sdk, "PowerControl.c", "-o", "power-control"])
    for executable in ["power", "power-control"]:
        if subprocess.run([work / executable], cwd=work).returncode != (3**256 // 7) % 256:
            raise ValueError(f"{executable}: incorrect singleton quotient status")
    # The two adjust methods share a family and ABI. The revision also records
    # the arithmetic site in the checked, nonwinning method.
    obj = "assembled.o"
    emit("""fn adjust(x: Int) -> Int { x - 1 }
contribution preferred : adjust {
    fn adjust(x: Int) requires (HasEq) -> Int { x + 2 }
}
assemble adjust { apply preferred; }
fn main() -> Int { adjust(40) }
""", obj)
    revision = json.loads(output([*check, "--print-function-revision"], cwd=ROOT))
    pure = revision["pure"]
    dispatch, = pure["dispatch_calls"]
    methods = [s for s in pure["symbols"] if s["id"] == dispatch["id"]]
    selected, = [s for s in methods if s["core"] == dispatch["core"]]
    sibling, = [s for s in methods if s["core"] != dispatch["core"]]
    sites = {s["core"]: s["id"]["name"] for s in pure["operator_sites"]}
    if (sites != {selected["core"]: "add", sibling["core"]: "sub"} or
        selected["specialization"]["definition"] != dispatch["definition"]):
        raise ValueError("assembled arithmetic methods differ from the checked operator sites")
    path = work / "revision.json"
    replay = [*preview, "--expect-function-revision", path]
    path.write_text(json.dumps(revision))
    if subprocess.check_output(replay, cwd=ROOT) != (work / "checked.ll").read_bytes():
        raise ValueError("assembled revision replay changed the complete module")
    dispatch.update(core=sibling["core"], definition=sibling["specialization"]["definition"])
    path.write_text(json.dumps(revision))
    invalid = subprocess.run(replay, cwd=ROOT, capture_output=True)
    if invalid.returncode == 0 or invalid.stdout or b"E_FUNCTION_REVISION" not in invalid.stderr:
        raise ValueError("accepted a nonwinning method from the same family and ABI")
    run([leanc, *sdk, "shim.o", obj, "-o", "assembled"])
    check_integer(obj, 42)
    if subprocess.run([work / "assembled"], cwd=work).returncode != 42:
        raise ValueError("assembled integer entry did not call the selected method")
    for fixture, control, expected in [("borrowed-operator", "chosen 40 2", 42),
                                       ("uncalled-operator", "(7 : Int)", 7)]:
        manifest = ROOT / "llvm/fixtures" / fixture / "Vastitas.toml"
        obj = fixture + ".o"
        emit_preview([args.frontend, "check", "--manifest-path", manifest, "--llvm-preview",
                      "--target-triple", target["triple"], "--data-layout", target["layout"]], obj)
        run([leanc, *sdk, "shim.o", obj, "-o", fixture])
        check_integer(obj, expected)
        (work / "BorrowedControl.lean").write_text(
            "@[noinline] def chosen (x y : @& Int) : Int := x + y\n"
            f"def main : IO UInt32 := pure (({control}) % 256).toNat.toUInt32\n")
        run([prefix / "bin/lean", "-c", "BorrowedControl.c", "BorrowedControl.lean"])
        run([leanc, *sdk, "BorrowedControl.c", "-o", "borrowed-control"])
        for executable in [fixture, "borrowed-control"]:
            if subprocess.run([work / executable], cwd=work).returncode != expected:
                raise ValueError(f"{fixture}: {executable} must return {expected}")
    return count, examples, len(divisors) + 1


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--frontend", type=Path, default=ROOT / "target/debug/vastitas")
    emission = parser.add_mutually_exclusive_group(required=True)
    emission.add_argument("--backend", type=Path, help="use the pinned libLLVM qualification adapter")
    emission.add_argument("--lean-clang", action="store_true", help="use the pinned Lean toolchain's clang")
    args = parser.parse_args()
    args.frontend = args.frontend.resolve()
    if args.backend:
        args.backend = args.backend.resolve()
    with tempfile.TemporaryDirectory(prefix="vastitas-boxed-exact-") as tmp:
        count, examples, programs = native(args, Path(tmp))
    print(f"{count} checked libraries, {examples} native results matched Lean and exact integer expectations; {count} heap ownership probes passed")
    print(f"{programs} hosted executable statuses matched generated Lean and independent expectations")
    print("both pair exports matched compiled Lean on heap and immediate values; distinct and aliased field counts matched before and after release")
    print("pair-returning assembly selected full integer results 42 and 2^128 + 43")
    print("selected and default pair projections matched compiled Lean at 19 and 7")
    print("hosted result probes matched each full integer and distinguished a value larger by 256")
    print("assembled integer entry returned 42 and rejected the sibling method in the expected revision")
    print("called and uncalled cross-package methods matched the generated Lean controls at exit 42 and 7")


if __name__ == "__main__":
    main()
