"""Exact QQ 2x2 spectral pairs for #337; external reference, not Lean/Core.

Reuse shared Poly and the existing rational 2x2 arithmetic. The only quotient
algorithm is monic quadratic reduction. No root finder or eigenbasis solver.
"""

from dataclasses import dataclass

from rational_polynomial_reference import Invalid, Poly
from metric_free_reference import (
    IDENTITY, determinant, matrix, matvec, multiply, rational, vector,
)


T = Poly.variable(0, arity=1)
ONE = Poly.constant(1, arity=1)
ZERO = Poly.constant(0, arity=1)
ZERO_MATRIX = matrix(((0, 0), (0, 0)))
RULESET = "QQ-free-rank-two-spectral/v1"


def _text(value):
    if type(value) is not str or not value:
        raise Invalid("INVALID_SCHEMA", "expected a nonempty identity")


def _poly(value):
    if type(value) is not Poly or value.arity != 1:
        raise Invalid("INVALID_POLYNOMIAL", "expected shared univariate QQ Poly")


def _coefficient(value, degree):
    return dict(value.terms).get((degree,), rational(0))


@dataclass(frozen=True)
class Frame:
    environment_id: str
    coefficient_id: str
    space_id: str
    basis_id: str
    scalar_profile: str = "QQ"

    def __post_init__(self):
        for value in (self.environment_id, self.coefficient_id, self.space_id,
                      self.basis_id, self.scalar_profile):
            _text(value)
        if self.scalar_profile != "QQ":
            raise Invalid("UNSUPPORTED_SCALARS", "only exact commutative QQ inputs")


@dataclass(frozen=True)
class Subject:
    map_id: str
    revision: str
    source: Frame
    target: Frame
    h: tuple
    ruleset: str = RULESET

    def __post_init__(self):
        _text(self.map_id)
        _text(self.revision)
        if type(self.source) is not Frame or type(self.target) is not Frame:
            raise Invalid("INVALID_SCHEMA", "expected named frames")
        if self.source != self.target:
            raise Invalid("ENDPOINT_MISMATCH", "H must be an endomorphism in one basis")
        if self.ruleset != RULESET:
            raise Invalid("UNSUPPORTED_PROFILE", "unsupported reference ruleset")
        object.__setattr__(self, "h", matrix(self.h))


@dataclass(frozen=True)
class QuadraticAlgebra:
    """QQ[x]/(monic quadratic), on the fixed ordered QQ basis (1,x).

    The name binds the generator role. Elements are shared Poly expressions in
    that role, interpreted only under an explicitly supplied algebra. This is
    not a field assertion, generic ideal algorithm, or nominal Core ring type.
    """

    generator: str
    relation: Poly

    def __post_init__(self):
        _text(self.generator)
        _poly(self.relation)
        if (not self.relation.terms or self.relation.terms[-1] != ((2,), rational(1))):
            raise Invalid("NOT_MONIC_QUADRATIC", "retain the entire degree-two relation")

    def reduce(self, value):
        _poly(value)
        while value.terms and value.terms[-1][0][0] >= 2:
            (degree,), coefficient = value.terms[-1]
            value = value - coefficient * T ** (degree - 2) * self.relation
        return value

    def product(self, left, right):
        return self.reduce(self.reduce(left) * self.reduce(right))

    def regular_action(self):
        """Multiplication by x on O_Sigma, not automatically on M_H."""
        columns = tuple(self.reduce(T * p) for p in (ONE, T))
        return matrix(tuple(tuple(_coefficient(p, i) for p in columns) for i in range(2)))


def characteristic_polynomial(h):
    """Producer route: trace/determinant coefficients."""
    h = matrix(h)
    return T ** 2 - (h[0][0] + h[1][1]) * T + determinant(h)


def evaluate_at(poly, h):
    """Evaluate an arbitrary QQ polynomial using existing matrix multiplication."""
    _poly(poly)
    h = matrix(h)
    result, power, degree = ZERO_MATRIX, IDENTITY, 0
    for (exponent,), coefficient in poly.terms:
        while degree < exponent:
            power = multiply(power, h)
            degree += 1
        result = matrix(tuple(tuple(result[i][j] + coefficient * power[i][j]
                                    for j in range(2)) for i in range(2)))
    return result


@dataclass(frozen=True)
class Evidence:
    subject: Subject
    algebra: QuadraticAlgebra
    unit_action: tuple
    t_action: tuple
    pushforward: tuple

    def __post_init__(self):
        if type(self.subject) is not Subject or type(self.algebra) is not QuadraticAlgebra:
            raise Invalid("INVALID_SCHEMA", "expected both the scheme and its module")
        for name in ("unit_action", "t_action", "pushforward"):
            object.__setattr__(self, name, matrix(getattr(self, name)))


def propose(subject):
    if type(subject) is not Subject:
        raise Invalid("INVALID_SCHEMA", "expected an independent Subject")
    return Evidence(subject, QuadraticAlgebra("t", characteristic_polynomial(subject.h)),
                    IDENTITY, subject.h, IDENTITY)


def check_characteristic(subject, algebra):
    """Verifier route: expand det(t I - H), without calling the producer."""
    (a, b), (c, d) = subject.h
    expanded = (T - a) * (T - d) - b * c
    if algebra.generator != "t" or algebra.relation != expanded:
        raise Invalid("CHARACTERISTIC_MISMATCH", "the characteristic scheme was changed")
    return expanded


def check_cayley_hamilton(subject, algebra):
    if evaluate_at(algebra.relation, subject.h) != ZERO_MATRIX:
        raise Invalid("CAYLEY_HAMILTON_FAILURE", "the claimed relation does not annihilate H")


def check_quotient_action(evidence):
    if evidence.unit_action != IDENTITY:
        raise Invalid("NONUNITAL_ACTION", "1 must act as the identity on the whole module")
    if evaluate_at(evidence.algebra.relation, evidence.t_action) != ZERO_MATRIX:
        raise Invalid("QUOTIENT_ACTION_FAILURE", "the defining ideal does not act by zero")


def check_recovery(subject, evidence):
    p = evidence.pushforward  # M coordinates -> the declared V coordinates
    if determinant(p) == 0:
        raise Invalid("INVALID_PUSHFORWARD", "the identified pushforward must be invertible")
    if multiply(subject.h, p) != multiply(p, evidence.t_action):
        raise Invalid("RECOVERY_MISMATCH", "the retained coordinate action does not recover H")


def verify(expected, evidence):
    """Recheck separate obligations against an independently supplied request.

    Return the checked payload for convenience, not an authenticated certificate.
    IDs and revisions are fixture data; Python object construction is no proof.
    """
    if type(expected) is not Subject or type(evidence) is not Evidence:
        raise Invalid("INVALID_SCHEMA", "expected a Subject and a complete spectral pair")
    if evidence.subject != expected:
        raise Invalid("SUBJECT_MISMATCH", "stale or differently indexed spectral evidence")
    check_characteristic(expected, evidence.algebra)
    check_cayley_hamilton(expected, evidence.algebra)
    check_quotient_action(evidence)
    check_recovery(expected, evidence)
    return evidence


def act(expected, evidence, polynomial, coordinates):
    """Quotient action on M coordinates; no reduction of the characteristic scheme."""
    verify(expected, evidence)
    return matvec(evaluate_at(evidence.algebra.reduce(polynomial), evidence.t_action), coordinates)


def check_similarity(left, right, left_evidence, right_evidence, change):
    """Explicit U: V_right -> V_left; check H_left U = U H_right."""
    verify(left, left_evidence)
    verify(right, right_evidence)
    if ((left.source.environment_id, left.source.coefficient_id)
            != (right.source.environment_id, right.source.coefficient_id)):
        raise Invalid("COEFFICIENT_BASE_MISMATCH", "similarity needs the same named coefficients")
    change = matrix(change)
    if determinant(change) == 0:
        raise Invalid("SINGULAR_COMPARISON", "an intertwiner alone need not be an isomorphism")
    if multiply(left.h, change) != multiply(change, right.h):
        raise Invalid("NOT_INTERTWINING", "same characteristic polynomial is not module isomorphism")
    if left_evidence.algebra != right_evidence.algebra:
        raise Invalid("CHARACTERISTIC_MISMATCH", "similarity must retain the characteristic algebra")
    return change


def check_structure_sheaf_isomorphism(expected, evidence, change):
    """Check a supplied A -> V isomorphism; never infer M = A from chi alone."""
    verify(expected, evidence)
    change = matrix(change)
    if determinant(change) == 0:
        raise Invalid("SINGULAR_COMPARISON", "a cyclic generator must span all of V")
    if multiply(expected.h, change) != multiply(change, evidence.algebra.regular_action()):
        raise Invalid("NOT_REGULAR_MODULE", "the proposed structure-sheaf comparison fails")
    return change


def check_eigenvector(expected, evidence, eigenvalue, coordinates, *, selection):
    """Optional explicitly selected observation, never part of the descriptor."""
    verify(expected, evidence)
    if selection != "explicit":
        raise Invalid("UNSUPPORTED_CANONICAL_SELECTION", "no canonical eigenvector/frame authority")
    eigenvalue, coordinates = rational(eigenvalue), vector(coordinates)
    if coordinates == (0, 0) or matvec(expected.h, coordinates) != tuple(
            eigenvalue * x for x in coordinates):
        raise Invalid("INVALID_EIGENVECTOR", "expected a nonzero exact eigenvector")
    return coordinates


@dataclass(frozen=True)
class ScalarExtension:
    """QQ -> S=QQ[u]/q(u), constant inclusion only, in the identified V basis.

    This finite presentation retains S explicitly. It does not compute kernels
    of eigenvectors or assert S is a field. characteristic lists (c0,c1,1).
    """

    subject: Subject
    scalars: QuadraticAlgebra
    characteristic: tuple
    action: tuple

    def __post_init__(self):
        if type(self.subject) is not Subject or type(self.scalars) is not QuadraticAlgebra:
            raise Invalid("INVALID_SCHEMA", "expected a source and an explicit coefficient algebra")
        if type(self.characteristic) is not tuple or len(self.characteristic) != 3:
            raise Invalid("INVALID_SCHEMA", "retain all three characteristic coefficients")
        if (type(self.action) is not tuple or len(self.action) != 2
                or any(type(row) is not tuple or len(row) != 2 for row in self.action)):
            raise Invalid("INVALID_SCHEMA", "expected two action columns in two rows")
        for p in self.characteristic + tuple(x for row in self.action for x in row):
            _poly(p)
            if self.scalars.reduce(p) != p:
                raise Invalid("NONCANONICAL_ELEMENT", "use unique coefficient remainders in S")


def propose_scalar_extension(expected, evidence, scalars):
    verify(expected, evidence)
    return ScalarExtension(expected, scalars,
                           tuple(Poly.constant(_coefficient(evidence.algebra.relation, i), 1)
                                 for i in range(3)),
                           tuple(tuple(Poly.constant(x, 1) for x in row) for row in expected.h))


def _extended_t_action(extension, coordinates):
    s = extension.scalars
    if type(coordinates) is not tuple or len(coordinates) != 2:
        raise Invalid("INVALID_SCHEMA", "expected two S-valued coordinates")
    return tuple(s.reduce(sum((s.product(x, y) for x, y in zip(row, coordinates)), ZERO))
                 for row in extension.action)


def check_scalar_extension(expected, evidence, scalars, extension):
    verify(expected, evidence)
    if type(extension) is not ScalarExtension:
        raise Invalid("INVALID_SCHEMA", "expected a complete extension presentation")
    if extension.subject != expected or extension.scalars != scalars:
        raise Invalid("BASE_CHANGE_SUBJECT_MISMATCH", "source or coefficient algebra changed")
    s = scalars
    (a, b), (c, d) = extension.action
    # Determinant over S, independent of the original QQ coefficient producer.
    expanded = (s.reduce(a * d - b * c), s.reduce(-a - d), ONE)
    embedded = tuple(Poly.constant(_coefficient(evidence.algebra.relation, i), 1) for i in range(3))
    if extension.characteristic != expanded or expanded != embedded:
        raise Invalid("BASE_CHANGE_CHARACTERISTIC_MISMATCH", "determinant does not commute with inclusion")
    actual = tuple(tuple(Poly.constant(x, 1) for x in row) for row in expected.h)
    if extension.action != actual:
        raise Invalid("BASE_CHANGE_ACTION_MISMATCH", "preserve H, not just its determinant")
    for v in ((ONE, ZERO), (ZERO, ONE)):
        hv = _extended_t_action(extension, v)
        hhv = _extended_t_action(extension, hv)
        if any(s.reduce(hhv[i] + expanded[1] * hv[i] + expanded[0] * v[i]) != ZERO
               for i in range(2)):
            raise Invalid("BASE_CHANGE_CH_FAILURE", "extended relation fails on a module basis")
    return extension


def extended_act(expected, evidence, scalars, extension, constant, linear, coordinates):
    """Act by a(u)+b(u)t on an S-vector, retaining nonrational coefficients."""
    check_scalar_extension(expected, evidence, scalars, extension)
    hv = _extended_t_action(extension, coordinates)
    return tuple(scalars.reduce(scalars.product(constant, x) + scalars.product(linear, y))
                 for x, y in zip(coordinates, hv))
