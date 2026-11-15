"""Exact standard-etale chart reference for #765; NOT Lean or Vastitas acceptance.

Check supplied unit witnesses for charts (A[t]/(p))[1/g] over A = QQ[x_1..x_m],
the self-overlap descent of a function on a finite chart, and the identities of
the spectral chart of an exact matrix. No root finding, search, Groebner basis,
eigensolver, family cover decision or object gluing.
See docs/reference/geometry.md#etale-reference for the fixed interpretation and remaining obligations.
"""

from __future__ import annotations

from dataclasses import dataclass, fields
from fractions import Fraction

from rational_polynomial_reference import Invalid, Poly


SITE = "etale-standard/v1"
SCALAR_PROFILE = "QQ-polynomial-base/v1"
MAX_BASE, MAX_DEGREE, MAX_RANK, MAX_EXPONENT = 4, 8, 4, 8


def identifier(value, name):
    if type(value) is not str or not value:
        raise Invalid("INVALID_SCHEMA", f"{name} must be a nonempty identifier")


def bounded(value, name, limit):
    if type(value) is not int or not 0 <= value <= limit:
        raise Invalid("INVALID_SCHEMA", f"{name} must be an integer in 0..{limit}")


@dataclass(frozen=True)
class Context:
    """The base A = QQ[variables] and the fiber coordinate t of a chart over it."""

    environment_id: str
    object_id: str
    base_id: str
    model_id: str
    model_revision: str
    scalar_profile: str
    site: str
    variables: tuple[str, ...]
    fiber: str

    def __post_init__(self):
        for field in fields(self):
            if field.name != "variables":
                identifier(getattr(self, field.name), field.name)
        if self.scalar_profile != SCALAR_PROFILE or self.site != SITE:
            raise Invalid("UNSUPPORTED_PROFILE", "only QQ polynomial bases on the standard-etale site")
        names = self.variables + (self.fiber,) if type(self.variables) is tuple else ()
        if (not names or len(names) > MAX_BASE + 1 or len(set(names)) != len(names)
                or any(type(v) is not str or not v for v in names)):
            raise Invalid("INVALID_VARIABLE_ORDER", "expected distinct ordered base and fiber IDs")

    @property
    def arity(self):
        """Polynomials of A[t] have the base variables and then the fiber coordinate."""
        return len(self.variables) + 1


def element(value, context, name):
    if type(value) is not Poly or value.arity != context.arity:
        raise Invalid("INVALID_SCHEMA", f"{name} must be a polynomial of the declared A[t]")


# Exact arithmetic in A[t]/(p) for a monic p: division by p needs no Groebner basis.
def degree(poly, index):
    """Degree in one variable; the zero polynomial has degree -1."""
    return max((powers[index] for powers, _ in poly.terms), default=-1)


def is_base(poly):
    """An element of A: no positive power of the fiber coordinate."""
    return degree(poly, poly.arity - 1) <= 0


def is_monic(poly, index):
    top = degree(poly, index)
    leading = [term for term in poly.terms if term[0][index] == top]
    return top >= 1 and len(leading) == 1 and sum(leading[0][0]) == top and leading[0][1] == 1


def monomial(index, power, arity):
    return Poly.from_terms([(tuple(power * int(i == index) for i in range(arity)), 1)], arity)


def reduce(poly, relation, index=None):
    """Remainder modulo a monic relation in one variable (the last by default)."""
    index = poly.arity - 1 if index is None else index
    if type(relation) is not Poly or relation.arity != poly.arity or not is_monic(relation, index):
        raise Invalid("RELATION_NOT_MONIC", "reduction needs a monic relation of positive degree")
    top = degree(relation, index)
    tail = relation - monomial(index, top, poly.arity)
    while (high := degree(poly, index)) >= top:
        leading = Poly(tuple(term for term in poly.terms if term[0][index] == high), poly.arity)
        lowered = Poly.from_terms(
            ((tuple(n - top * int(i == index) for i, n in enumerate(powers)), c)
             for powers, c in leading.terms), poly.arity)
        poly = poly - leading - lowered * tail
    return poly


def trace(value, relation):
    """Trace over A of multiplication by an element of the free A-module A[t]/(p)."""
    fiber, total = value.arity - 1, Poly.constant(0, value.arity)
    for power in range(degree(relation, fiber)):
        image = reduce(value * monomial(fiber, power, value.arity), relation)
        total += Poly.from_terms(((powers[:-1] + (0,), c) for powers, c in image.terms
                                  if powers[fiber] == power), value.arity)
    return total


# The self-overlap ring A[t,s]/(p(t),p(s)) appends the second fiber coordinate s.
def first(poly):
    return Poly.from_terms(((powers + (0,), c) for powers, c in poly.terms), poly.arity + 1)


def second(poly):
    return Poly.from_terms(((powers[:-1] + (0, powers[-1]), c) for powers, c in poly.terms),
                           poly.arity + 1)


def overlap_difference(value, relation):
    """Normal form of b(t) - b(s): the two pullbacks of b to the self-overlap."""
    arity = value.arity + 1
    partial = reduce(first(value) - second(value), first(relation), arity - 2)
    return reduce(partial, second(relation), arity - 1)


def divided_difference(poly):
    """q(t,s) with p(t) - p(s) = (t - s) q(t,s); its diagonal q(t,t) is p'(t)."""
    arity = poly.arity + 1
    return Poly.from_terms(
        ((powers[:-1] + (i, powers[-1] - 1 - i), c)
         for powers, c in poly.terms for i in range(powers[-1])), arity)


@dataclass(frozen=True)
class Chart:
    """Spec of (A[t]/(relation))[1/localizer], with its structure map to Spec A."""

    chart_id: str
    revision: str
    relation: Poly
    localizer: Poly


@dataclass(frozen=True)
class Subject:
    context: Context
    chart: Chart

    def __post_init__(self):
        if type(self.context) is not Context or type(self.chart) is not Chart:
            raise Invalid("INVALID_SCHEMA", "expected Context and Chart")
        identifier(self.chart.chart_id, "chart_id")
        identifier(self.chart.revision, "revision")
        element(self.chart.relation, self.context, "relation")
        element(self.chart.localizer, self.context, "localizer")


@dataclass(frozen=True)
class ChartCertificate:
    """Candidate W and e with W * p' = g^e in A[t]/(p): p' is a unit after inverting g."""

    subject: Subject
    witness: Poly
    exponent: int

    def __post_init__(self):
        if type(self.subject) is not Subject:
            raise Invalid("INVALID_SCHEMA", "expected a bound Subject")
        element(self.witness, self.subject.context, "witness")
        bounded(self.exponent, "exponent", MAX_EXPONENT)


@dataclass(frozen=True)
class Check:
    name: str
    status: str
    code: str
    detail: str


@dataclass(frozen=True)
class Report:
    checks: tuple[Check, ...]
    returned: object

    @property
    def accepted(self):
        return self.returned is not None and all(check.status == "pass" for check in self.checks)


class Ledger:
    """Ordered named checks; a check after a failed prerequisite is never a success."""

    def __init__(self, names):
        self.names, self.checks = names, []

    def add(self, valid, failure, detail, status="fail"):
        name = self.names[len(self.checks)]
        self.checks.append(Check(name, "pass" if valid else status, "OK" if valid else failure, detail))
        return valid

    def report(self, returned):
        blocked = tuple(Check(name, "not_checked", "PREREQUISITE_REQUIRED", "an earlier check did not pass")
                        for name in self.names[len(self.checks):])
        checks = tuple(self.checks) + blocked
        return Report(checks, returned if all(c.status == "pass" for c in checks) else None)


def binding(ledger, expected, supplied):
    if expected == supplied:
        return ledger.add(True, "", "full subject, order and coefficient equality")
    changed = [f.name for f in fields(type(expected))
               if getattr(expected, f.name) != getattr(supplied, f.name)]
    return ledger.add(False, "SUBJECT_MISMATCH", "different " + ", ".join(changed))


CHART_CHECKS = ("binding", "monic_relation", "reduced_presentation", "nonzero_localizer",
                "unit_witness")


def is_finite(chart):
    """g in A: the chart is free of finite rank over the principal open D(g) of the base."""
    return is_base(chart.localizer) and bool(chart.localizer.terms)


def verify_chart(expected, certificate):
    """Bind to an INDEPENDENT request, then check the supplied unit witness.

    Acceptance means the chart is standard etale over Spec A. It proves neither
    that the chart is nonempty nor that it covers any open of the base; only a
    finite chart (g in A, g nonzero) is a cover, of D(g). A rejected candidate
    says nothing about whether another witness exists.
    """
    if type(expected) is not Subject or type(certificate) is not ChartCertificate:
        raise Invalid("INVALID_SCHEMA", "expected Subject and ChartCertificate")
    ledger = Ledger(CHART_CHECKS)
    if not binding(ledger, expected, certificate.subject):
        return ledger.report(None)
    relation, localizer = expected.chart.relation, expected.chart.localizer
    fiber = expected.context.arity - 1
    top = degree(relation, fiber)
    if not ledger.add(is_monic(relation, fiber) and top <= MAX_DEGREE, "RELATION_NOT_MONIC",
                      f"p is monic in the fiber coordinate, of degree 1..{MAX_DEGREE}"):
        return ledger.report(None)
    ledger.add(degree(localizer, fiber) < top and degree(certificate.witness, fiber) < top,
               "NOT_REDUCED", "g and W are normal forms modulo p; nothing is reduced silently")
    ledger.add(bool(localizer.terms), "EMPTY_CHART", "g is not the zero polynomial")
    product = certificate.witness * relation.derivative(fiber) - localizer ** certificate.exponent
    ledger.add(reduce(product, relation) == Poly.constant(0, relation.arity),
               "UNIT_WITNESS_MISMATCH", "W * p' = g^e in A[t]/(p), coefficientwise")
    return ledger.report(certificate)


@dataclass(frozen=True)
class Section:
    """The function numerator / g^exponent on a finite chart."""

    section_id: str
    revision: str
    numerator: Poly
    exponent: int


@dataclass(frozen=True)
class DescentSubject:
    chart: Subject
    section: Section

    def __post_init__(self):
        if type(self.chart) is not Subject or type(self.section) is not Section:
            raise Invalid("INVALID_SCHEMA", "expected a chart Subject and a Section")
        identifier(self.section.section_id, "section_id")
        identifier(self.section.revision, "revision")
        element(self.section.numerator, self.chart.context, "numerator")
        bounded(self.section.exponent, "exponent", MAX_EXPONENT)


@dataclass(frozen=True)
class DescentCertificate:
    """A chart certificate and the candidate function descended / g^exponent on D(g)."""

    subject: DescentSubject
    chart_certificate: ChartCertificate
    descended: Poly

    def __post_init__(self):
        if (type(self.subject) is not DescentSubject
                or type(self.chart_certificate) is not ChartCertificate):
            raise Invalid("INVALID_SCHEMA", "expected DescentSubject and ChartCertificate")
        element(self.descended, self.subject.chart.context, "descended")


DESCENT_CHECKS = ("binding", "chart", "finite_chart", "reduced_section", "self_overlap",
                  "restriction")


def verify_descent(expected, certificate):
    """Descend one function along a finite chart, which covers D(g).

    The chart is not a monomorphism, so the overlap of the chart with itself is
    a separate obligation: the two pullbacks of the section must agree there.
    The restriction check compares the supplied function on D(g) with the section.
    """
    if type(expected) is not DescentSubject or type(certificate) is not DescentCertificate:
        raise Invalid("INVALID_SCHEMA", "expected DescentSubject and DescentCertificate")
    ledger = Ledger(DESCENT_CHECKS)
    if not binding(ledger, expected, certificate.subject):
        return ledger.report(None)
    if not ledger.add(verify_chart(expected.chart, certificate.chart_certificate).accepted,
                      "CHART_NOT_VERIFIED", "the chart certificate is replayed on the expected chart"):
        return ledger.report(None)
    if not ledger.add(is_finite(expected.chart.chart), "UNSUPPORTED_COVER",
                      "g lies in A; cover evidence for other charts is outside this profile",
                      status="unsupported"):
        return ledger.report(None)
    relation, numerator = expected.chart.chart.relation, expected.section.numerator
    fiber = expected.chart.context.arity - 1
    ledger.add(degree(numerator, fiber) < degree(relation, fiber), "NOT_REDUCED",
               "the numerator is a normal form modulo p")
    ledger.add(not overlap_difference(numerator, relation).terms, "SELF_OVERLAP_DISAGREEMENT",
               "b(t) = b(s) in A[t,s]/(p(t),p(s))")
    ledger.add(is_base(certificate.descended) and certificate.descended == numerator,
               "RESTRICTION_MISMATCH", "the descended numerator lies in A and restricts to b")
    return ledger.report(certificate)


# Exact square matrices over A[t], as tuples of rows.
def zero_matrix(rank, arity):
    return tuple(tuple(Poly.constant(0, arity) for _ in range(rank)) for _ in range(rank))


def identity(rank, arity):
    return tuple(tuple(Poly.constant(int(i == j), arity) for j in range(rank)) for i in range(rank))


def scale(matrix, factor):
    return tuple(tuple(entry * factor for entry in row) for row in matrix)


def add(left, right):
    return tuple(tuple(a + b for a, b in zip(r, s)) for r, s in zip(left, right))


def multiply(left, right):
    size = range(len(left))
    return tuple(tuple(sum((left[i][k] * right[k][j] for k in size), Poly.constant(0, left[0][0].arity))
                       for j in size) for i in size)


def matrix_trace(matrix):
    return sum((matrix[i][i] for i in range(len(matrix))), Poly.constant(0, matrix[0][0].arity))


def entrywise(matrix, function):
    return tuple(tuple(function(entry) for entry in row) for row in matrix)


def determinant(matrix):
    """Laplace expansion along the first row; the rank is at most MAX_RANK."""
    if len(matrix) == 1:
        return matrix[0][0]
    total = Poly.constant(0, matrix[0][0].arity)
    for column, entry in enumerate(matrix[0]):
        minor = tuple(row[:column] + row[column + 1:] for row in matrix[1:])
        total += entry * determinant(minor) * (-1) ** column
    return total


def cofactor_adjugate(matrix):
    size = len(matrix)
    if size == 1:
        return identity(1, matrix[0][0].arity)

    def minor(row, column):
        return tuple(r[:column] + r[column + 1:] for k, r in enumerate(matrix) if k != row)

    return tuple(tuple(determinant(minor(j, i)) * (-1) ** (i + j) for j in range(size))
                 for i in range(size))


def audit_matrix(value, context, name):
    if (type(value) is not tuple or not 1 <= len(value) <= MAX_RANK
            or any(type(row) is not tuple or len(row) != len(value) for row in value)):
        raise Invalid("INVALID_MATRIX_SHAPE",
                      f"{name} must be an immutable square matrix of size 1..{MAX_RANK}")
    for row in value:
        for entry in row:
            element(entry, context, name)


@dataclass(frozen=True)
class SpectralSubject:
    """An exact endomorphism H of the free module A^n in a declared ordered basis."""

    context: Context
    map_id: str
    revision: str
    matrix: tuple

    def __post_init__(self):
        if type(self.context) is not Context:
            raise Invalid("INVALID_SCHEMA", "expected Context")
        identifier(self.map_id, "map_id")
        identifier(self.revision, "revision")
        audit_matrix(self.matrix, self.context, "matrix")
        if not all(is_base(entry) for row in self.matrix for entry in row):
            raise Invalid("INVALID_SCHEMA", "matrix entries must lie in the base A")


@dataclass(frozen=True)
class SpectralCandidate:
    """Candidate chi_H(t) = det(t I - H) and adj(t I - H), both over A[t]."""

    subject: SpectralSubject
    characteristic: Poly
    adjugate: tuple

    def __post_init__(self):
        if type(self.subject) is not SpectralSubject:
            raise Invalid("INVALID_SCHEMA", "expected a bound SpectralSubject")
        element(self.characteristic, self.subject.context, "characteristic")
        audit_matrix(self.adjugate, self.subject.context, "adjugate")
        if len(self.adjugate) != len(self.subject.matrix):
            raise Invalid("INVALID_MATRIX_SHAPE", "adjugate must have the rank of the matrix")


def shifted(subject):
    """t I - H over A[t]."""
    rank, arity = len(subject.matrix), subject.context.arity
    return add(scale(identity(rank, arity), monomial(arity - 1, 1, arity)), scale(subject.matrix, -1))


def propose_spectral(subject):
    """Convenience producer (Faddeev-LeVerrier). verify_spectral never calls it."""
    rank, arity = len(subject.matrix), subject.context.arity
    fiber = arity - 1
    step, adjugate = identity(rank, arity), zero_matrix(rank, arity)
    characteristic = monomial(fiber, rank, arity)
    for k in range(1, rank + 1):
        adjugate = add(adjugate, scale(step, monomial(fiber, rank - k, arity)))
        product = multiply(subject.matrix, step)
        coefficient = matrix_trace(product) * Fraction(-1, k)
        characteristic += coefficient * monomial(fiber, rank - k, arity)
        step = add(product, scale(identity(rank, arity), coefficient))
    return SpectralCandidate(subject, characteristic, adjugate)


def evaluate_second_at(poly, matrix, arity):
    """Substitute s = H in q(t,s): a matrix over A[t]. Horner in the second coordinate."""
    rank = len(matrix)
    result = zero_matrix(rank, arity)
    for power in range(degree(poly, arity), -1, -1):
        coefficient = Poly.from_terms(((powers[:-1], c) for powers, c in poly.terms
                                       if powers[-1] == power), arity)
        result = add(multiply(result, matrix), scale(identity(rank, arity), coefficient))
    return result


SPECTRAL_CHECKS = ("binding", "characteristic", "adjugate", "jacobi_trace", "eigen_columns",
                   "idempotent", "rank_one", "divided_difference")


def verify_spectral(expected, candidate):
    """Recompute by cofactor expansion, then check each identity of the candidate.

    With p = chi_H and C = A[t]/(p), on the chart D(p') of Spec C the matrix
    P = adj(t I - H) / p'(t) is an idempotent of trace one with H P = t P.
    The identities hold over all of A, with no gap between eigenvalues.
    """
    if type(expected) is not SpectralSubject or type(candidate) is not SpectralCandidate:
        raise Invalid("INVALID_SCHEMA", "expected SpectralSubject and SpectralCandidate")
    ledger = Ledger(SPECTRAL_CHECKS)
    if not binding(ledger, expected, candidate.subject):
        return ledger.report(None)
    arity, rank = expected.context.arity, len(expected.matrix)
    fiber, pencil = arity - 1, shifted(expected)
    chi, adjugate = candidate.characteristic, candidate.adjugate
    ledger.add(chi == determinant(pencil), "CHARACTERISTIC_MISMATCH", "chi = det(t I - H) by expansion")
    ledger.add(adjugate == cofactor_adjugate(pencil), "ADJUGATE_MISMATCH",
               "adj(t I - H) by signed minors")
    derivative = chi.derivative(fiber)
    ledger.add(matrix_trace(adjugate) == derivative, "JACOBI_TRACE_MISMATCH",
               "sum_i adj_ii = chi'(t): the opens D(adj_ii) cover D(chi')")
    if not is_monic(chi, fiber):
        ledger.add(False, "RELATION_NOT_MONIC", "identities modulo chi need a monic candidate")
        return ledger.report(None)

    def vanishes(matrix):
        return entrywise(matrix, lambda entry: reduce(entry, chi)) == zero_matrix(rank, arity)

    ledger.add(vanishes(multiply(pencil, adjugate)), "EIGEN_COLUMN_MISMATCH",
               "(t I - H) adj = 0 modulo chi: each column is an eigenvector for t")
    ledger.add(vanishes(add(multiply(adjugate, adjugate), scale(adjugate, derivative * -1))),
               "PROJECTOR_NOT_IDEMPOTENT", "adj^2 = chi' adj modulo chi")
    minors = [adjugate[i][j] * adjugate[k][l] - adjugate[i][l] * adjugate[k][j]
              for i in range(rank) for k in range(i + 1, rank)
              for j in range(rank) for l in range(j + 1, rank)]
    ledger.add(all(not reduce(minor, chi).terms for minor in minors), "RANK_ONE_MINOR_NONZERO",
               "every 2 by 2 minor of adj vanishes modulo chi: the columns are proportional")
    quotient = evaluate_second_at(divided_difference(chi), expected.matrix, arity)
    ledger.add(adjugate == quotient, "DIVIDED_DIFFERENCE_MISMATCH",
               "adj(t I - H) = q(t,H) for chi(t) - chi(s) = (t - s) q(t,s)")
    return ledger.report(candidate)


def simple_root_chart(candidate, chart_id, revision):
    """The chart D(chi') of Spec A[t]/(chi), with the unit witness W = 1, e = 1."""
    subject = candidate.subject
    fiber = subject.context.arity - 1
    derivative = candidate.characteristic.derivative(fiber)
    chart = Chart(chart_id, revision, candidate.characteristic, derivative)
    return ChartCertificate(Subject(subject.context, chart), Poly.constant(1, subject.context.arity), 1)


RESOLUTION_CHECKS = ("binding", "spectral", "chart_binding", "chart", "finite_chart",
                     "completeness", "recovery")


def verify_resolution(expected, expected_chart, candidate, chart_certificate):
    """On a finite chart over D(g), the trace over branches recovers I and H.

    With W * chi' = g^e, the sum over the branches of P = adj / chi' is
    tr(W adj) / g^e = I, and the sum of t P is tr(t W adj) / g^e = H. The
    traces are computed in the free module A[t]/(chi); no root is extracted.
    """
    if (type(expected) is not SpectralSubject or type(expected_chart) is not Subject
            or type(candidate) is not SpectralCandidate
            or type(chart_certificate) is not ChartCertificate):
        raise Invalid("INVALID_SCHEMA", "expected spectral and chart subjects with their candidates")
    ledger = Ledger(RESOLUTION_CHECKS)
    if not binding(ledger, expected, candidate.subject):
        return ledger.report(None)
    if not ledger.add(verify_spectral(expected, candidate).accepted, "SPECTRAL_NOT_VERIFIED",
                      "the spectral candidate is replayed on the expected matrix"):
        return ledger.report(None)
    chi = candidate.characteristic
    if not ledger.add(expected_chart.context == expected.context
                      and expected_chart.chart.relation == chi, "CHART_RELATION_MISMATCH",
                      "the chart has the context of H and the relation chi_H"):
        return ledger.report(None)
    if not ledger.add(verify_chart(expected_chart, chart_certificate).accepted,
                      "CHART_NOT_VERIFIED", "the chart certificate is replayed on the expected chart"):
        return ledger.report(None)
    if not ledger.add(is_finite(expected_chart.chart), "UNSUPPORTED_CHART",
                      "g lies in A; the trace is over a free module on D(g)", status="unsupported"):
        return ledger.report(None)
    arity, rank = expected.context.arity, len(expected.matrix)
    power = expected_chart.chart.localizer ** chart_certificate.exponent
    weighted = scale(candidate.adjugate, chart_certificate.witness)
    ledger.add(entrywise(weighted, lambda entry: trace(entry, chi))
               == scale(identity(rank, arity), power), "RESOLUTION_MISMATCH",
               "tr(W adj) = g^e I: the branch projectors sum to the identity")
    moved = scale(weighted, monomial(arity - 1, 1, arity))
    ledger.add(entrywise(moved, lambda entry: trace(entry, chi)) == scale(expected.matrix, power),
               "OPERATOR_NOT_RECOVERED", "tr(t W adj) = g^e H: the branches recover H")
    return ledger.report(candidate)
