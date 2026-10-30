"""Finite reduction-plan reference for Vastitas #303; standard library only.

This is neither a Vastitas acceptance route nor a Lean certificate verifier.
The target is a separate caller input, never reconstructed from the candidate.
The closed law table is an explicit reference assumption, not a proof engine.
Run: python3 scripts/reduction_reference.py TARGET.json CANDIDATE.json
Exit codes: 0 accepted, 1 rejected, 2 unsupported, 3 malformed CLI input.
"""

from __future__ import annotations

import argparse
from collections import Counter
from dataclasses import asdict, dataclass
from fractions import Fraction
import hashlib
import json
import re
from types import MappingProxyType
from typing import Callable


class Failure(ValueError):
    def __init__(self, code: str, message: str, status: str = "rejected"):
        super().__init__(message)
        self.code, self.status = code, status


def require(ok: bool, code: str, message: str) -> None:
    if not ok:
        raise Failure(code, message)


def fields(value: object, names: set[str], where: str) -> dict:
    require(type(value) is dict, "SCHEMA", f"{where}: expected object")
    require(set(value) == names, "SCHEMA", f"{where}: exact fields required: {sorted(names)}")
    return value


def name(value: object, where: str) -> str:
    require(type(value) is str and 0 < len(value) <= 200, "SCHEMA", f"{where}: invalid name")
    return value


@dataclass(frozen=True)
class Profile:
    representation: str
    precision: str
    rounding: str
    fma: str
    subnormals: str
    exceptional: str
    signed_zero: str
    backend: str


@dataclass(frozen=True)
class Binding:
    operation: str
    revision: str
    carrier: str
    coefficients: str
    profile: Profile


EXACT = Profile("rational", "unbounded", "exact", "none", "not_applicable",
                "not_applicable", "not_applicable", "python-fraction-reference-v1")
BINARY64 = Profile("binary64", "53", "nearest_ties_even", "forbidden", "gradual",
                   "reject_nonfinite", "preserve", "software-binary64-add-v1")
MATMUL = Binding("reference::mat2_mul", "v1", "Mat2(QQ)", "QQ-canonical-v1", EXACT)
MATMUL_V2 = Binding("reference::mat2_mul", "v2", "Mat2(QQ)", "QQ-canonical-v1", EXACT)
ADD = Binding("reference::add", "v1", "QQ", "QQ-canonical-v1", EXACT)
MUL = Binding("reference::mul", "v1", "QQ", "QQ-canonical-v1", EXACT)
SUB = Binding("reference::sub", "v1", "QQ", "QQ-canonical-v1", EXACT)
FLOAT_ADD = Binding("reference::add", "v1", "FiniteBinary64", "binary64-values-v1", BINARY64)


def decode_binding(raw: object) -> Binding:
    x = fields(raw, {"operation", "revision", "carrier", "coefficients", "profile"}, "binding")
    p = fields(x["profile"], set(Profile.__dataclass_fields__), "numeric profile")
    return Binding(*(name(x[k], k) for k in ("operation", "revision", "carrier", "coefficients")),
                   Profile(**{k: name(v, k) for k, v in p.items()}))


def match_binding(actual: Binding, expected: Binding, code: str) -> None:
    """Compare semantic identity dimensions independently, including each profile field."""
    different = [k for k in ("operation", "revision", "carrier", "coefficients")
                 if getattr(actual, k) != getattr(expected, k)]
    different += [f"profile.{k}" for k in Profile.__dataclass_fields__
                  if getattr(actual.profile, k) != getattr(expected.profile, k)]
    require(not different, code, "selected binding mismatch: " + ", ".join(different))


def parse_rational(raw: object) -> Fraction:
    # No float coercion, booleans, approximate decimal or arbitrary expression.
    require(type(raw) is str and len(raw) <= 256 and
            re.fullmatch(r"-?(0|[1-9][0-9]*)(/[1-9][0-9]*)?", raw) is not None,
            "VALUE", "expected exact integer or numerator/positive-denominator string")
    return Fraction(raw)


def matmul(a: tuple, b: tuple) -> tuple:
    return tuple(tuple(sum((a[i][k] * b[k][j] for k in range(2)), Fraction(0))
                       for j in range(2)) for i in range(2))


@dataclass(frozen=True)
class Bits64:
    bits: int

    def rational(self) -> Fraction:
        sign = -1 if self.bits >> 63 else 1
        exponent = (self.bits >> 52) & 0x7FF
        fraction = self.bits & ((1 << 52) - 1)
        if exponent == 0:
            return sign * Fraction(fraction, 1 << 1074)
        significand = (1 << 52) | fraction
        shift = exponent - 1023 - 52
        return sign * Fraction(significand << max(shift, 0), 1 << max(-shift, 0))

    def hex(self) -> str:
        return f"{self.bits:016x}"


def parse_bits(raw: object) -> Bits64:
    require(type(raw) is str and re.fullmatch(r"[0-9a-f]{16}", raw) is not None,
            "VALUE", "expected 16 lowercase binary64 hex digits")
    bits = int(raw, 16)
    require((bits >> 52) & 0x7FF != 0x7FF, "NONFINITE_INPUT", "NaN and infinity are outside this profile")
    return Bits64(bits)


def _round_integer(n: int, d: int) -> int:
    q, r = divmod(n, d)
    return q + int(2 * r > d or (2 * r == d and q % 2 == 1))


def _round_binary64(value: Fraction) -> Bits64:
    """Integer-only RN-even rounding; no host floating-point arithmetic."""
    if value == 0:
        return Bits64(0)
    sign = int(value < 0) << 63
    n, d = abs(value.numerator), value.denominator
    exponent = n.bit_length() - d.bit_length()
    below_power = n < d << exponent if exponent >= 0 else n << -exponent < d
    if below_power:
        exponent -= 1
    if exponent < -1022:
        significand = _round_integer(n << 1074, d)
        # Rounding to the smallest normal value is represented by bit 52.
        return Bits64(sign | significand)
    shift = 52 - exponent
    significand = _round_integer(n << max(shift, 0), d << max(-shift, 0))
    if significand == 1 << 53:
        significand >>= 1
        exponent += 1
    require(exponent <= 1023, "NONFINITE_RESULT", "binary64 overflow is excluded by the selected profile")
    return Bits64(sign | ((exponent + 1023) << 52) | (significand - (1 << 52)))


def add_binary64(a: Bits64, b: Bits64) -> Bits64:
    value = a.rational() + b.rational()
    if value == 0:
        # In RN-even, exact cancellation gives +0; only -0 + -0 gives -0.
        return Bits64(1 << 63 if a.bits == b.bits == 1 << 63 else 0)
    return _round_binary64(value)


@dataclass(frozen=True)
class Operation:
    apply: Callable
    exact: bool


_OPERATIONS = MappingProxyType({
    MATMUL: Operation(matmul, True), MATMUL_V2: Operation(matmul, True),
    ADD: Operation(lambda a, b: a + b, True), MUL: Operation(lambda a, b: a * b, True),
    SUB: Operation(lambda a, b: a - b, True), FLOAT_ADD: Operation(add_binary64, False),
})


@dataclass(frozen=True)
class LawReference:
    certificate: str
    law: str
    subject: Binding


# Closed reference fixtures, independent of candidate JSON. They are explicit
# mathematical assumptions of this Python model, NOT accepted Lean certificates.
# In particular there is no associativity certificate for binary64 addition.
_LAW_ROWS = (
    LawReference("matmul-v1-assoc", "associative", MATMUL),
    LawReference("matmul-v2-assoc", "associative", MATMUL_V2),
    LawReference("qq-add-assoc", "associative", ADD),
    LawReference("qq-add-comm", "commutative", ADD),
    LawReference("qq-mul-assoc", "associative", MUL),
    LawReference("qq-mul-comm", "commutative", MUL),
)
_LAWS = MappingProxyType({row.certificate: row for row in _LAW_ROWS})


def law_reference(certificate: str) -> dict:
    """Build a reference to a known fixture; does not let callers register laws."""
    return asdict(_LAWS[certificate])


@dataclass(frozen=True)
class Input:
    occurrence: str
    revision: str
    value: object


@dataclass(frozen=True)
class Leaf:
    occurrence: str
    revision: str


@dataclass(frozen=True)
class Node:
    binding: Binding
    left: Leaf | Node
    right: Leaf | Node


Tree = Leaf | Node
MAX_INPUTS = 128
MAX_NODES = 255
MAX_DEPTH = 128
MAX_RATIONAL_BITS = 8192


def decode_tree(raw: object, binding: Binding, inputs: dict[str, Input]) -> Tree:
    visits = 0

    def walk(x: object, depth: int) -> Tree:
        nonlocal visits
        visits += 1
        require(visits <= MAX_NODES and depth <= MAX_DEPTH, "TREE_LIMIT", "finite tree budget exceeded")
        require(type(x) is dict, "SCHEMA", "tree node must be an object")
        if "leaf" in x:
            fields(x, {"leaf", "revision"}, "leaf")
            ident = name(x["leaf"], "leaf identity")
            require(ident in inputs, "LEAF_IDENTITY", f"unknown occurrence: {ident}")
            revision = name(x["revision"], "leaf revision")
            require(revision == inputs[ident].revision, "LEAF_REVISION", f"stale occurrence: {ident}")
            return Leaf(ident, revision)
        fields(x, {"binding", "left", "right"}, "binary node")
        actual = decode_binding(x["binding"])
        match_binding(actual, binding, "NODE_BINDING")
        return Node(actual, walk(x["left"], depth + 1), walk(x["right"], depth + 1))

    return walk(raw, 1)


def leaf_sequence(tree: Tree) -> tuple[str, ...]:
    if isinstance(tree, Leaf):
        return (tree.occurrence,)
    return leaf_sequence(tree.left) + leaf_sequence(tree.right)


def bracket_shape(tree: Tree) -> object:
    return "leaf" if isinstance(tree, Leaf) else (bracket_shape(tree.left), bracket_shape(tree.right))


def left_fold(inputs: tuple[Input, ...], binding: Binding) -> Tree:
    tree: Tree = Leaf(inputs[0].occurrence, inputs[0].revision)
    for item in inputs[1:]:
        tree = Node(binding, tree, Leaf(item.occurrence, item.revision))
    return tree


def evaluate(tree: Tree, inputs: dict[str, Input], operation: Operation) -> object:
    if isinstance(tree, Leaf):
        return inputs[tree.occurrence].value
    value = operation.apply(evaluate(tree.left, inputs, operation), evaluate(tree.right, inputs, operation))
    entries = (entry for row in value for entry in row) if isinstance(value, tuple) else (value,)
    for entry in entries:
        if isinstance(entry, Fraction) and max(abs(entry.numerator).bit_length(), entry.denominator.bit_length()) > MAX_RATIONAL_BITS:
            raise Failure("ARITHMETIC_LIMIT", "exact intermediate exceeds reference bit budget", "unsupported")
    return value


def render(value: object) -> object:
    if isinstance(value, Fraction):
        return str(value)
    if isinstance(value, Bits64):
        return {"bits": value.hex(), "exact_value": str(value.rational())}
    if isinstance(value, tuple):
        return [render(x) for x in value]
    raise TypeError("unsupported result")


def digest(raw: object) -> str:
    return hashlib.sha256(json.dumps(raw, sort_keys=True, separators=(",", ":"), allow_nan=False).encode()).hexdigest()


def check(target: object, candidate: object) -> dict:
    """Audit separate JSON-compatible target/candidate; fail closed.

    An accepted result is a finite Python reference observation. The digests are
    trace identifiers, not authentication, kernel certificates or reusable authority.
    """
    audit: dict = {}
    try:
        t = fields(target, {"schema", "id", "binding", "inputs", "contract"}, "independent target")
        require(type(t["schema"]) is int and t["schema"] == 1, "SCHEMA", "unknown target schema")
        target_id = name(t["id"], "target identity")
        binding = decode_binding(t["binding"])
        if binding not in _OPERATIONS:
            raise Failure("UNSUPPORTED_BINDING", "no evaluator for exact selected binding", "unsupported")
        operation = _OPERATIONS[binding]
        raw_inputs = t["inputs"]
        require(type(raw_inputs) is list and 1 <= len(raw_inputs) <= MAX_INPUTS,
                "INPUT_DOMAIN", "this slice requires 1..128 inputs; no implicit empty identity or seed")
        parsed = []
        for raw in raw_inputs:
            x = fields(raw, {"id", "revision", "value"}, "input occurrence")
            ident, revision = name(x["id"], "input identity"), name(x["revision"], "input revision")
            if binding.carrier == "Mat2(QQ)":
                v = x["value"]
                require(type(v) is list and len(v) == 2 and all(type(r) is list and len(r) == 2 for r in v),
                        "VALUE", "expected exact 2 by 2 matrix")
                value = tuple(tuple(parse_rational(entry) for entry in row) for row in v)
            elif operation.exact:
                value = parse_rational(x["value"])
            else:
                value = parse_bits(x["value"])
            parsed.append(Input(ident, revision, value))
        inputs = tuple(parsed)
        by_id = {x.occurrence: x for x in inputs}
        require(len(by_id) == len(inputs), "TARGET_OCCURRENCES", "target occurrence identities must be unique")
        expected_order = tuple(x.occurrence for x in inputs)
        contract = t["contract"]
        require(type(contract) is dict, "SCHEMA", "contract must be object")
        kind = contract.get("kind")
        if kind == "exact":
            fields(contract, {"kind", "allow_permutation"}, "exact contract")
            require(type(contract["allow_permutation"]) is bool, "SCHEMA", "allow_permutation must be boolean")
            require(operation.exact, "EXACT_REPRESENTATION", "Float execution cannot inherit exact algebraic laws")
        elif kind == "fixed_tree":
            fields(contract, {"kind", "tree"}, "fixed-tree contract")
        elif kind == "left_fold_equivalent":
            fields(contract, {"kind"}, "finite left-fold contract")
        elif kind == "relaxed":
            fields(contract, {"kind", "policy", "error_contract"}, "relaxed contract")
            name(contract["policy"], "relaxed policy")
            name(contract["error_contract"], "error contract")
        else:
            raise Failure("UNSUPPORTED_CONTRACT", "unsupported independently selected contract", "unsupported")

        reference = left_fold(inputs, binding)
        if kind == "fixed_tree":
            reference = decode_tree(contract["tree"], binding, by_id)
            require(leaf_sequence(reference) == expected_order, "TARGET_TREE", "pinned tree must retain target occurrence order exactly")

        c = fields(candidate, {"schema", "target_id", "binding", "tree", "evidence"}, "candidate")
        require(type(c["schema"]) is int and c["schema"] == 1, "SCHEMA", "unknown candidate schema")
        require(c["target_id"] == target_id, "TARGET_ID", "candidate is for another independent target")
        match_binding(decode_binding(c["binding"]), binding, "PLAN_BINDING")
        tree = decode_tree(c["tree"], binding, by_id)
        order = leaf_sequence(tree)
        counts = Counter(order)
        audit.update({"leaf_identity": "matched", "multiplicity": dict(counts),
                      "order": list(order), "order_preserved": order == expected_order,
                      "bracket_shape": bracket_shape(tree),
                      "reference_shape": bracket_shape(reference),
                      "same_bracketing": bracket_shape(tree) == bracket_shape(reference),
                      "same_tree": tree == reference,
                      "binding_checks": {"operation": "matched", "revision": "matched",
                                         "carrier": "matched", "coefficients": "matched",
                                         "numeric_profile": "matched", "every_binary_node": "matched"},
                      "binding": asdict(binding)})
        require(counts == Counter(expected_order), "LEAF_MULTIPLICITY", "missing or duplicate input occurrences")

        refs = c["evidence"]
        require(type(refs) is list and len(refs) <= 16, "SCHEMA", "evidence must be a bounded list of references")
        laws, certificates = set(), set()
        for raw in refs:
            e = fields(raw, {"certificate", "law", "subject"}, "law evidence reference")
            cert = name(e["certificate"], "certificate identity")
            require(cert not in certificates, "DUPLICATE_EVIDENCE", "duplicate evidence reference")
            certificates.add(cert)
            ref = LawReference(cert, name(e["law"], "law"), decode_binding(e["subject"]))
            require(cert in _LAWS, "UNKNOWN_EVIDENCE", "candidate label is not registered law evidence")
            require(ref == _LAWS[cert], "EVIDENCE_RECORD", "reference does not match the independent closed record")
            match_binding(ref.subject, binding, "EVIDENCE_SUBJECT")
            laws.add(ref.law)
        audit["evidence"] = sorted(certificates)

        if kind == "exact":
            if order != expected_order:
                require(contract["allow_permutation"], "LEAF_ORDER", "independent target requires input order")
                require("commutative" in laws, "COMMUTATIVITY_REQUIRED", "associativity cannot justify permutation")
            # Conservatively require associativity whenever a non-identical
            # binary tree is proposed (including permutations). No value shortcut.
            if tree != reference:
                require("associative" in laws, "ASSOCIATIVITY_REQUIRED", "changed tree requires exact associativity evidence")
        else:
            require(order == expected_order, "LEAF_ORDER", "this contract preserves target leaf order")
            if kind == "fixed_tree":
                require(tree == reference, "PINNED_TREE", "candidate differs from independently pinned tree")
            elif kind == "relaxed":
                raise Failure("RELAXED_UNSUPPORTED", "error/enclosure evidence validation is unimplemented", "unsupported")

        actual_value = evaluate(tree, by_id, operation)
        reference_value = evaluate(reference, by_id, operation)
        same = actual_value == reference_value  # Bits64 equality compares all bits.
        audit.update({"candidate_value": render(actual_value), "reference_value": render(reference_value),
                      "matches_reference": same})
        require(same, "VALUE_MISMATCH", "finite results disagree under the selected contract")

        # This observation is deliberately separate from fixed-tree admission.
        try:
            left_value = evaluate(left_fold(inputs, binding), by_id, operation)
            audit["left_fold_observation"] = {"status": "evaluated", "value": render(left_value),
                                               "equal_for_this_input": actual_value == left_value}
        except Failure as exc:
            audit["left_fold_observation"] = {"status": "outside_profile", "code": exc.code,
                                               "equal_for_this_input": None}
        guarantee = {
            "exact": "finite_exact_equality_with_closed_reference_law_assumptions",
            "fixed_tree": "same_pinned_tree_and_profile_reference_evaluation",
            "left_fold_equivalent": "bit_or_exact_value_equality_for_these_inputs_only",
        }[kind]
        return {"status": "accepted", "code": "OK", "guarantee": guarantee,
                "target_sha256": digest(target), "candidate_sha256": digest(candidate), "audit": audit}
    except Failure as exc:
        return {"status": exc.status, "code": exc.code, "message": str(exc), "audit": audit}
    except (RecursionError, OverflowError):
        return {"status": "rejected", "code": "RESOURCE_LIMIT", "message": "reference resource limit", "audit": audit}


def load_json(path: str) -> object:
    def pairs(items: list) -> dict:
        out = {}
        for key, value in items:
            if key in out:
                raise ValueError(f"duplicate JSON field: {key}")
            out[key] = value
        return out

    def invalid_constant(value: str) -> None:
        raise ValueError(f"non-JSON numeric constant: {value}")

    with open(path, encoding="utf-8") as stream:
        data = stream.read(1_000_001)
    if len(data) > 1_000_000:
        raise ValueError("JSON input exceeds reference limit")
    return json.loads(data, object_pairs_hook=pairs, parse_constant=invalid_constant)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("target", help="independently selected specification JSON")
    parser.add_argument("candidate", help="untrusted plan JSON (cannot choose its own contract)")
    args = parser.parse_args()
    try:
        report = check(load_json(args.target), load_json(args.candidate))
    except (OSError, ValueError, RecursionError) as exc:
        print(json.dumps({"status": "rejected", "code": "CLI_INPUT", "message": str(exc)}))
        return 3
    print(json.dumps(report, indent=2, sort_keys=True))
    return {"accepted": 0, "rejected": 1, "unsupported": 2}[report["status"]]


if __name__ == "__main__":
    raise SystemExit(main())
