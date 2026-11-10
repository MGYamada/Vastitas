"""Exact, finite semilinear time-reversal observations for #301.

Reuse #275's Q(i) and matrix arithmetic verbatim. This is a Python reference,
not Lean evidence, accepted Core, or verification of a physical hypothesis.
The caller selects the target independently of the candidate and any report.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from types import MappingProxyType
from typing import TypeAlias

from car_reference import (
    I, ID2, ONE, ZERO, Matrix, Qi, Rejected, Relation, audit_matrix,
    conjugate_transpose, matrix, mul, scale,
)


class ScalarAction(str, Enum):
    IDENTITY = "identity"
    CONJUGATE = "conjugation"


Vector: TypeAlias = tuple[Qi, ...]
E0, E1 = (ONE, ZERO), (ZERO, ONE)
SPIN_U = matrix([[0, 1], [-1, 0]])


def conjugate(a: Matrix) -> Matrix:
    audit_matrix(a)
    return matrix([[x.conjugate() for x in row] for row in a])


def scalar_matrix(action: ScalarAction, a: Matrix) -> Matrix:
    if type(action) is not ScalarAction:
        raise Rejected("explicit identity/conjugation scalar action required")
    audit_matrix(a)
    return conjugate(a) if action is ScalarAction.CONJUGATE else a


def audit_vector(v: Vector) -> None:
    if type(v) is not tuple or len(v) != 2 or any(type(x) is not Qi for x in v):
        raise Rejected("two exact Q(i) coordinates in an immutable vector required")


def vector_scale(a: Qi, v: Vector) -> Vector:
    audit_vector(v)
    if type(a) is not Qi:
        raise Rejected("exact Q(i) scalar required")
    return tuple(a * x for x in v)


def matvec(a: Matrix, v: Vector) -> Vector:
    audit_matrix(a)
    audit_vector(v)
    if len(a) != 2:
        raise Rejected("only two-dimensional finite models are supported")
    return tuple(sum((x * y for x, y in zip(row, v)), ZERO) for row in a)


def inner(v: Vector, w: Vector) -> Qi:
    """Chosen positive Hermitian realization, conjugate-linear in the first slot."""
    audit_vector(v)
    audit_vector(w)
    return sum((x.conjugate() * y for x, y in zip(v, w)), ZERO)


@dataclass(frozen=True)
class Coefficients:
    field_id: str
    embedding_id: str
    generator_image: Qi
    conjugate_generator: Qi
    rational_embedding: str


COEFFICIENTS = Coefficients(
    "QQ(i)", "QQ(i)->CC: i maps to +sqrt(-1)", I, -I,
    "QQ->QQ(i): a maps to (a,0)",
)


@dataclass(frozen=True)
class AntiunitaryProfile:
    profile_id: str
    scalar_action: ScalarAction
    square: Qi
    inner_product_id: str


@dataclass(frozen=True)
class Model:
    model_id: str
    owner_id: str
    carrier_id: str
    revision: str
    reference_basis: tuple[str, str]
    reference_matrix: Matrix
    profile: AntiunitaryProfile
    physical_assumption: str


SPIN_HALF = Model(
    "fixture:spin-half", "fixture-owner:time-reversal", "fixture:C2:spin", "1",
    ("up", "down"), SPIN_U,
    AntiunitaryProfile("fixture:spin-half:T", ScalarAction.CONJUGATE, -ONE,
                      "positive-Hermitian:orthonormal-Gram-I"),
    "Assume this doublet describes one spin-1/2 with T=UK; not an empirical claim.",
)
SPINLESS = Model(
    "fixture:spinless", "fixture-owner:time-reversal", "fixture:C2:orbital", "1",
    ("orbital-0", "orbital-1"), ID2,
    AntiunitaryProfile("fixture:spinless:T", ScalarAction.CONJUGATE, ONE,
                      "positive-Hermitian:orthonormal-Gram-I"),
    "Assume two spinless orbital coordinates with T=K; not every spinless system.",
)
MODELS = MappingProxyType({m.model_id: m for m in (SPIN_HALF, SPINLESS)})


@dataclass(frozen=True)
class Basis:
    basis_id: str
    model_id: str
    ordered_labels: tuple[str, str]
    to_reference: Matrix  # v_reference = B v_this; columns are basis vectors.
    gram: Matrix = ID2


@dataclass(frozen=True)
class Coordinates:
    model: Model
    basis: Basis
    coefficients: Coefficients


def audit_coordinates(c: Coordinates) -> None:
    if type(c) is not Coordinates or type(c.model) is not Model:
        raise Rejected("explicit selected finite model required")
    if (type(c.model.profile) is not AntiunitaryProfile or
            type(c.model.profile.scalar_action) is not ScalarAction or
            type(c.model.profile.square) is not Qi or
            c.model != MODELS.get(c.model.model_id)):
        raise Rejected("unknown/stale model, carrier, interpretation or profile")
    audit_matrix(c.model.reference_matrix)
    if (type(c.coefficients) is not Coefficients or
            type(c.coefficients.generator_image) is not Qi or
            type(c.coefficients.conjugate_generator) is not Qi or
            c.coefficients != COEFFICIENTS):
        raise Rejected("unsupported coefficient field, embedding or involution")
    b = c.basis
    if (type(b) is not Basis or type(b.basis_id) is not str or not b.basis_id or
            b.model_id != c.model.model_id or type(b.ordered_labels) is not tuple or
            len(b.ordered_labels) != 2 or
            any(type(x) is not str or not x for x in b.ordered_labels) or
            len(set(b.ordered_labels)) != 2):
        raise Rejected("explicit ordered basis of the selected model required")
    audit_matrix(b.to_reference)
    audit_matrix(b.gram)
    if (b.gram != ID2 or len(b.to_reference) != 2 or
            mul(conjugate_transpose(b.to_reference), b.to_reference) != ID2):
        raise Rejected("this finite profile requires an exact orthonormal basis")


def reference_coordinates(model: Model) -> Coordinates:
    c = Coordinates(model, Basis(f"{model.model_id}:reference", model.model_id,
                                model.reference_basis, ID2), COEFFICIENTS)
    audit_coordinates(c)
    return c


def audit_phase(phase: Qi) -> None:
    if type(phase) is not Qi or phase * phase.conjugate() != ONE:
        raise Rejected("explicit unit-norm Q(i) phase required")


@dataclass(frozen=True)
class Selection:
    """Trusted caller input; never inferred from an untrusted candidate/report."""

    coordinates: Coordinates
    profile: AntiunitaryProfile
    phase: Qi = ONE


def audit_selection(expected: Selection) -> None:
    if type(expected) is not Selection:
        raise Rejected("independent target selection required")
    audit_coordinates(expected.coordinates)
    if (type(expected.profile) is not AntiunitaryProfile or
            type(expected.profile.scalar_action) is not ScalarAction or
            type(expected.profile.square) is not Qi or
            expected.profile != expected.coordinates.model.profile):
        raise Rejected("antiunitary profile does not belong to the selected model")
    audit_phase(expected.phase)


def expected_matrix(expected: Selection) -> Matrix:
    """Transport the independently fixed representative: B† (phase U0) bar(B)."""
    audit_selection(expected)
    b = expected.coordinates.basis.to_reference
    u = scale(expected.phase, expected.coordinates.model.reference_matrix)
    return mul(mul(conjugate_transpose(b), u), conjugate(b))


@dataclass(frozen=True)
class Semilinear:
    coordinates: Coordinates
    name: str  # Diagnostic label only; never selects a mathematical action.
    entries: Matrix
    scalar_action: ScalarAction

    def __post_init__(self):
        audit_coordinates(self.coordinates)
        audit_matrix(self.entries)
        if len(self.entries) != 2 or type(self.scalar_action) is not ScalarAction:
            raise Rejected("explicit 2x2 matrix and scalar action required")
        if type(self.name) is not str or not self.name:
            raise Rejected("diagnostic action label required")


def apply(action: Semilinear, v: Vector) -> Vector:
    audit_vector(v)
    acted = (tuple(x.conjugate() for x in v)
             if action.scalar_action is ScalarAction.CONJUGATE else v)
    return matvec(action.entries, acted)


def compose(left: Semilinear, right: Semilinear) -> Semilinear:
    """left after right: (A,sigma)(B,tau) = (A sigma(B), sigma tau)."""
    if left.coordinates != right.coordinates:
        raise Rejected("composition requires the same model, basis and embedding")
    sigma = (ScalarAction.IDENTITY if left.scalar_action is right.scalar_action
             else ScalarAction.CONJUGATE)
    return Semilinear(left.coordinates, f"({left.name}) after ({right.name})",
                      mul(left.entries, scalar_matrix(left.scalar_action, right.entries)), sigma)


def rephase(action: Semilinear, phase: Qi) -> Semilinear:
    audit_phase(phase)
    return Semilinear(action.coordinates, f"phase*({action.name})",
                      scale(phase, action.entries), action.scalar_action)


def basis_change(source: Coordinates, target: Coordinates) -> Matrix:
    audit_coordinates(source)
    audit_coordinates(target)
    if source.model != target.model or source.coefficients != target.coefficients:
        raise Rejected("basis transport cannot change model or coefficient embedding")
    return mul(conjugate_transpose(source.basis.to_reference), target.basis.to_reference)


def transport(action: Semilinear, target: Coordinates) -> Semilinear:
    """S maps target coordinates to source: A_target = S† A_source sigma(S)."""
    s = basis_change(action.coordinates, target)
    entries = mul(mul(conjugate_transpose(s), action.entries),
                  scalar_matrix(action.scalar_action, s))
    return Semilinear(target, action.name, entries, action.scalar_action)


def transport_vector(v: Vector, source: Coordinates, target: Coordinates) -> Vector:
    return matvec(conjugate_transpose(basis_change(source, target)), v)


def transform_operator(action: Semilinear, a: Matrix) -> Matrix:
    """A sigma(O) A†; only unitary A makes A† the required inverse here."""
    if mul(conjugate_transpose(action.entries), action.entries) != ID2:
        raise Rejected("operator conjugation requires a unitary matrix part")
    return mul(mul(action.entries, scalar_matrix(action.scalar_action, a)),
               conjugate_transpose(action.entries))


@dataclass(frozen=True)
class VectorRelation:
    label: str
    lhs: Vector
    rhs: Vector

    @property
    def holds(self) -> bool:
        return self.lhs == self.rhs


@dataclass(frozen=True)
class TimeReversalObservation:
    expected: Selection
    candidate: Semilinear
    square: Semilinear
    matrix_relations: tuple[Relation, ...]
    vector_relations: tuple[VectorRelation, ...]

    @property
    def all_hold(self) -> bool:
        return (self.candidate.scalar_action is self.expected.profile.scalar_action and
                self.square.scalar_action is ScalarAction.IDENTITY and
                all(r.holds for r in self.matrix_relations + self.vector_relations))


def observe_time_reversal(expected: Selection, candidate: Semilinear) -> TimeReversalObservation:
    audit_selection(expected)
    if type(candidate) is not Semilinear or candidate.coordinates != expected.coordinates:
        raise Rejected("candidate is not bound to the independently selected coordinates")
    square = compose(candidate, candidate)
    relations = (
        Relation("selected representative", candidate.entries, expected_matrix(expected)),
        Relation("unitarity", mul(conjugate_transpose(candidate.entries), candidate.entries), ID2),
        Relation("T squared", square.entries, scale(expected.profile.square, ID2)),
    )
    vectors = tuple(VectorRelation(f"T(i e{j}) = -i T(e{j})",
                                   apply(candidate, vector_scale(I, e)),
                                   vector_scale(-I, apply(candidate, e)))
                    for j, e in enumerate((E0, E1)))
    return TimeReversalObservation(expected, candidate, square, relations, vectors)


def check_time_reversal(expected: Selection, candidate: Semilinear,
                        observation: TimeReversalObservation | None = None) -> TimeReversalObservation:
    """Recompute; a name or an all_hold report grants no authority."""
    actual = observe_time_reversal(expected, candidate)
    if observation is not None and (type(observation) is not TimeReversalObservation or
                                    observation != actual):
        raise Rejected("stale, cross-target or altered time-reversal observation")
    if not actual.all_hold:
        failed = [r.label for r in actual.matrix_relations + actual.vector_relations if not r.holds]
        if candidate.scalar_action is not expected.profile.scalar_action:
            failed.append("scalar action")
        if actual.square.scalar_action is not ScalarAction.IDENTITY:
            failed.append("square scalar action")
        raise Rejected("time-reversal mismatch: " + ", ".join(failed))
    return actual


class SubjectKind(str, Enum):
    HAMILTONIAN = "Hamiltonian"
    PURE_STATE_PROJECTOR = "pure-state projector"


@dataclass(frozen=True)
class Subject:
    coordinates: Coordinates
    object_id: str
    kind: SubjectKind
    entries: Matrix


def audit_subject(subject: Subject, coordinates: Coordinates) -> None:
    if (type(subject) is not Subject or subject.coordinates != coordinates or
            type(subject.object_id) is not str or not subject.object_id or
            type(subject.kind) is not SubjectKind):
        raise Rejected("independent subject, kind and matching coordinates required")
    audit_matrix(subject.entries)
    a = subject.entries
    if len(a) != 2 or conjugate_transpose(a) != a:
        raise Rejected("selected Hamiltonian/state projector must be Hermitian")
    if subject.kind is SubjectKind.PURE_STATE_PROJECTOR and (
            mul(a, a) != a or a[0][0] + a[1][1] != ONE):
        raise Rejected("pure-state subject requires an exact rank-one projector")


@dataclass(frozen=True)
class InvarianceObservation:
    time_reversal: TimeReversalObservation
    subject: Subject
    transformed: Matrix

    @property
    def holds(self) -> bool:
        return self.transformed == self.subject.entries


def observe_invariance(expected: Selection, candidate: Semilinear,
                       subject: Subject) -> InvarianceObservation:
    checked = check_time_reversal(expected, candidate)
    audit_subject(subject, expected.coordinates)
    return InvarianceObservation(checked, subject, transform_operator(candidate, subject.entries))


def check_invariance(expected: Selection, candidate: Semilinear, subject: Subject,
                     observation: InvarianceObservation | None = None) -> InvarianceObservation:
    actual = observe_invariance(expected, candidate, subject)
    if observation is not None and (type(observation) is not InvarianceObservation or
                                    observation != actual):
        raise Rejected("invariance observation is not bound to this action and subject")
    if not actual.holds:
        raise Rejected("selected subject is not invariant")
    return actual
