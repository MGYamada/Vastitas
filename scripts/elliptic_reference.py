"""Exact reference for #253: y^2 = x^3 - x over F5 and Q 2-torsion only.

Python arithmetic and finite table checks, NOT Lean or accepted Vastitas Core.
Curve, coefficient-field and presentation handles have nominal identity. Raw
points/evidence are claims; public operations recheck their subjects and values.
See docs/elliptic-reference.md for the deliberately narrow trust boundary.
"""

from dataclasses import dataclass
from fractions import Fraction as Q
from itertools import product


class Invalid(ValueError):
    def __init__(self, code, message):
        self.code = code
        super().__init__(message)


def _name(value):
    if type(value) is not str or not value:
        raise Invalid("INVALID_NAME", "expected a nonempty display name")


@dataclass(frozen=True, eq=False)
class Field:
    """An in-process nominal field handle; equal display names do not identify it."""

    kind: str
    name: str

    def __post_init__(self):
        _name(self.name)
        if type(self.kind) is not str or self.kind not in ("F5", "QQ"):
            raise Invalid("UNSUPPORTED_FIELD", "only fixed F5 and QQ profiles")

    def scalar(self, value):
        if self.kind == "F5":
            if type(value) is not int:
                raise Invalid("INEXACT_SCALAR", "F5 inputs must be integers, never float/bool")
            return value % 5
        if type(value) not in (int, Q):
            raise Invalid("INEXACT_SCALAR", "QQ inputs must be int or Fraction")
        return Q(value)

    def require_canonical(self, value):
        expected_type = int if self.kind == "F5" else Q
        if type(value) is not expected_type or self.scalar(value) != value:
            raise Invalid("NONCANONICAL_SCALAR", "claim must use exact canonical field scalars")

    def inv0(self, value):
        """Total field inverse: inv0(0) = 0, including in QQ."""
        value = self.scalar(value)
        if value == 0:
            return self.scalar(0)
        return pow(value, 3, 5) if self.kind == "F5" else 1 / value


@dataclass(frozen=True, eq=False)
class Curve:
    """One nominal copy of the FIXED equation y^2=x^3-x, with its infinity."""

    field: Field
    name: str

    def __post_init__(self):
        _name(self.name)
        if type(self.field) is not Field:
            raise Invalid("INVALID_FIELD", "expected a nominal coefficient field")


@dataclass(frozen=True, eq=False)
class Model:
    """A separate nominal handle for the fixed short Weierstrass presentation."""

    curve: Curve
    name: str

    def __post_init__(self):
        _name(self.name)
        if type(self.curve) is not Curve:
            raise Invalid("INVALID_CURVE", "expected a nominal curve")

    @property
    def field(self):
        return self.curve.field


def require_model(model):
    if type(model) is not Model:
        raise Invalid("INVALID_MODEL", "expected a fixed short Weierstrass model")


@dataclass(frozen=True)
class ModelEvidence:
    model: Model
    discriminant: object


def certify_model(model):
    require_model(model)
    # -16 * (4*A^3 + 27*B^2), for A=-1, B=0 only.
    delta = model.field.scalar(-16 * (4 * (-1) ** 3))
    if delta == 0:
        raise Invalid("SINGULAR_MODEL", "fixed field profile must have nonzero discriminant")
    return ModelEvidence(model, delta)


def check_model_evidence(model, evidence):
    expected = certify_model(model)
    if type(evidence) is not ModelEvidence or evidence.model is not model:
        raise Invalid("EVIDENCE_SUBJECT", "model evidence belongs to another presentation")
    model.field.require_canonical(evidence.discriminant)
    if evidence != expected:
        raise Invalid("DISCRIMINANT_MISMATCH", "recomputed discriminant differs")
    return expected


@dataclass(frozen=True)
class Point:
    """Untrusted claim: None is O=[0:1:0]; otherwise exact affine (x,y)."""

    model: Model
    coordinates: tuple | None


def check_point(model, candidate):
    require_model(model)
    if type(candidate) is not Point or candidate.model is not model:
        raise Invalid("POINT_SUBJECT", "point must retain the exact curve/field/model handles")
    if candidate.coordinates is None:
        return candidate
    if type(candidate.coordinates) is not tuple or len(candidate.coordinates) != 2:
        raise Invalid("INVALID_COORDINATES", "expected O or an immutable affine pair")
    x, y = candidate.coordinates
    field = model.field
    field.require_canonical(x)
    field.require_canonical(y)
    if field.scalar(y * y - x * x * x + x) != 0:
        raise Invalid("OFF_CURVE", "exact curve equation fails")
    if field.kind == "QQ" and (y != 0 or x not in (-1, 0, 1)):
        raise Invalid("UNSUPPORTED_POINT", "QQ profile is restricted to the listed 2-torsion")
    return candidate


def point(model, x, y):
    require_model(model)
    return check_point(model, Point(model, (model.field.scalar(x), model.field.scalar(y))))


def zero(model):
    return check_point(model, Point(model, None))


def neg(model, value):
    check_point(model, value)
    if value.coordinates is None:
        return zero(model)
    x, y = value.coordinates
    return point(model, x, -y)


@dataclass(frozen=True)
class MembershipEvidence:
    point: Point
    residual: object


def certify_membership(model, value):
    check_point(model, value)
    # For O the homogenized equation Y^2 Z = X^3 - X Z^2 has residual 0.
    return MembershipEvidence(value, model.field.scalar(0))


def check_membership_evidence(model, value, evidence):
    expected = certify_membership(model, value)
    if type(evidence) is not MembershipEvidence or evidence.point != value:
        raise Invalid("EVIDENCE_SUBJECT", "membership evidence must describe this exact point")
    check_point(model, evidence.point)
    model.field.require_canonical(evidence.residual)
    if evidence != expected:
        raise Invalid("MEMBERSHIP_MISMATCH", "recomputed membership differs")
    return expected


def slope_inverse(field, denominator):
    """Formula applicability guard, NOT a change to total field inversion."""
    denominator = field.scalar(denominator)
    if denominator == 0:
        raise Invalid("ZERO_SLOPE_DENOMINATOR", "affine slope requires a nonzero denominator")
    return field.inv0(denominator)


@dataclass(frozen=True)
class AdditionEvidence:
    model: Model
    left: Point
    right: Point
    result: Point
    branch: str
    denominator: object = None
    slope: object = None


def addition(model, left, right):
    """Return an exact result and a replayable branch/denominator claim."""
    # Audit BOTH inputs before identity shortcuts.
    check_point(model, left)
    check_point(model, right)
    denominator = slope = None
    if left.coordinates is None:
        result, branch = right, "left_identity"
    elif right.coordinates is None:
        result, branch = left, "right_identity"
    else:
        x1, y1 = left.coordinates
        x2, y2 = right.coordinates
        field = model.field
        if left == right and y1 == 0:
            result, branch = zero(model), "double_y_zero"
        elif x1 == x2 and field.scalar(y1 + y2) == 0:
            result, branch = zero(model), "inverse_pair"
        else:
            if left == right:
                numerator = field.scalar(3 * x1 * x1 - 1)
                denominator, branch = field.scalar(2 * y1), "tangent"
            else:
                numerator = field.scalar(y2 - y1)
                denominator, branch = field.scalar(x2 - x1), "chord"
            slope = field.scalar(numerator * slope_inverse(field, denominator))
            x3 = field.scalar(slope * slope - x1 - x2)
            y3 = field.scalar(slope * (x1 - x3) - y1)
            result = point(model, x3, y3)
    return AdditionEvidence(model, left, right, result, branch, denominator, slope)


def add(model, left, right):
    return addition(model, left, right).result


def check_addition_evidence(model, left, right, evidence):
    """Recompute the actual request; membership alone never validates addition."""
    expected = addition(model, left, right)
    if (type(evidence) is not AdditionEvidence or evidence.model is not model
            or evidence.left != left or evidence.right != right):
        raise Invalid("EVIDENCE_SUBJECT", "addition evidence must bind the exact ordered inputs")
    check_point(model, evidence.left)
    check_point(model, evidence.right)
    check_point(model, evidence.result)
    if type(evidence.branch) is not str:
        raise Invalid("INVALID_BRANCH", "expected a branch name")
    for scalar in (evidence.denominator, evidence.slope):
        if scalar is not None:
            model.field.require_canonical(scalar)
    if evidence != expected:
        raise Invalid("ADDITION_MISMATCH", "branch, applicability or result does not replay")
    return expected


def f5_points(model):
    """Enumerate all 25 affine candidates, plus the unique projective infinity."""
    require_model(model)
    if model.field.kind != "F5":
        raise Invalid("UNSUPPORTED_ENUMERATION", "no enumeration of E(QQ) is claimed")
    return (zero(model),) + tuple(
        point(model, x, y) for x, y in product(range(5), repeat=2)
        if (y * y - x * x * x + x) % 5 == 0
    )


def label(value):
    if value.coordinates is None:
        return "O"
    return "(" + ",".join(str(c) for c in value.coordinates) + ")"


@dataclass(frozen=True)
class LawCheck:
    checked: int
    failures: int
    witness: tuple[str, ...] | None


@dataclass(frozen=True)
class GroupAudit:
    """A finite observation bound to this model and table, never Group authority."""

    model: Model
    points: tuple[Point, ...]
    table: tuple[tuple[Point, ...], ...]
    checks: dict[str, LawCheck]

    @property
    def passed(self):
        return all(check.failures == 0 for check in self.checks.values())


def audit_f5_group(model, operation=add):
    """Check the entire F5 carrier, not a caller-selected sample or subgroup.

    Each output is rechecked for its nominal subject and equation BEFORE table
    lookup. An off-curve/foreign result is rejected rather than silently coerced.
    The laws below concern this exact finite, deterministic operation table.
    """
    points = f5_points(model)
    table = tuple(tuple(operation(model, p, q) for q in points) for p in points)
    for row in table:
        for value in row:
            check_point(model, value)
            if value not in points:
                raise Invalid("NOT_CLOSED", "operation leaves the exhaustive F5 carrier")
    checks = {"closure": LawCheck(len(points) ** 2, 0, None)}
    indices = {p: i for i, p in enumerate(points)}

    def op(p, q):
        return table[indices[p]][indices[q]]

    def record(name, cases, predicate):
        checked = failures = 0
        witness = None
        for case in cases:
            checked += 1
            if not predicate(*case):
                failures += 1
                if witness is None:
                    witness = tuple(label(p) for p in case)
        checks[name] = LawCheck(checked, failures, witness)

    identity = zero(model)
    record("left_identity", product(points), lambda p: op(identity, p) == p)
    record("right_identity", product(points), lambda p: op(p, identity) == p)
    record("left_inverse", product(points), lambda p: op(neg(model, p), p) == identity)
    record("right_inverse", product(points), lambda p: op(p, neg(model, p)) == identity)
    record("commutativity", product(points, repeat=2), lambda p, q: op(p, q) == op(q, p))
    record("associativity", product(points, repeat=3),
           lambda p, q, r: op(op(p, q), r) == op(p, op(q, r)))
    return GroupAudit(model, points, table, checks)


def check_f5_group(model, operation=add):
    """Recompute the table and laws; never consume a caller's report as proof."""
    audit = audit_f5_group(model, operation)
    if not audit.passed:
        raise Invalid("GROUP_LAW_FAILURE", "finite reference table fails group laws")
    return audit
