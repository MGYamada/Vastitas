"""Exact scalar first-order polynomial variation reference for #305.

L is in Q[t,q,v], q and eta in Q[t], with real interpretation on [0,1].
Two routes compare [epsilon] S(q+epsilon*eta) with integral(EL*eta) + [p*eta].
First variations are scalar evaluations of a metric-free linear functional.
No general function-space, stationarity, Lean or actual-Core acceptance claim.
"""

from dataclasses import dataclass
from fractions import Fraction as Q

from rational_polynomial_reference import Invalid, Poly
from rational_polynomial_calculus import evaluate, integrate, substitute


PROFILE = "Q-to-R-scalar-polynomial-variation/v1"
RULESET = "first-order-bulk-plus-boundary/v1"
UNIT_INTERVAL = (Q(0), Q(1))
T = Poly.variable(0, arity=1)


def _text(value):
    if type(value) is not str or not value:
        raise Invalid("INVALID_SCHEMA", "expected a nonempty identity/revision")


def _poly(value, arity):
    if type(value) is not Poly or value.arity != arity:
        raise Invalid("INVALID_POLYNOMIAL", f"expected a shared Poly of arity {arity}")


def _rational(value):
    # Equality alone would let float(1) or True masquerade as exact evidence.
    if type(value) is not Q:
        raise Invalid("INEXACT_INPUT", "evidence scalars must be Fraction values")


def _pair(value):
    if type(value) is not tuple or len(value) != 2:
        raise Invalid("INVALID_SCHEMA", "expected an immutable pair of rationals")
    for x in value:
        _rational(x)


@dataclass(frozen=True)
class Lagrangian:
    definition_id: str
    revision: str
    variables: tuple[str, str, str]
    expression: Poly

    def __post_init__(self):
        _text(self.definition_id)
        _text(self.revision)
        if (type(self.variables) is not tuple or len(self.variables) != 3
                or any(type(x) is not str for x in self.variables)
                or set(self.variables) != {"t", "q", "v"}):
            raise Invalid("UNSUPPORTED_VARIABLES", "use an explicit permutation of (t,q,v)")
        _poly(self.expression, 3)


@dataclass(frozen=True)
class Subject:
    """Independent request, including actual coefficients and variation space.

    Identities are fixture data, not authenticated compiler declarations. Other
    rational intervals can be represented for replay tests but not calculated.
    """

    lagrangian: Lagrangian
    path: Poly
    variation: Poly
    admissible_variations: str = "unrestricted"
    interval: tuple[Q, Q] = UNIT_INTERVAL
    environment_id: str = "polynomial-real-line"
    configuration_id: str = "scalar-path"
    scalar_profile: str = PROFILE
    ruleset: str = RULESET

    def __post_init__(self):
        if type(self.lagrangian) is not Lagrangian:
            raise Invalid("INVALID_SCHEMA", "expected a named Lagrangian")
        _poly(self.path, 1)
        _poly(self.variation, 1)
        _pair(self.interval)
        for value in (self.admissible_variations, self.environment_id,
                      self.configuration_id, self.scalar_profile, self.ruleset):
            _text(value)
        if self.admissible_variations not in ("unrestricted", "fixed_endpoints"):
            raise Invalid("UNSUPPORTED_VARIATIONS", "only unrestricted or fixed_endpoints")


def _supported(subject):
    if type(subject) is not Subject:
        raise Invalid("INVALID_SCHEMA", "expected an independent Subject")
    if (subject.interval != UNIT_INTERVAL or subject.scalar_profile != PROFILE
            or subject.ruleset != RULESET):
        raise Invalid("UNSUPPORTED_PROFILE", "only the declared real [0,1] profile")


def check_admissibility(subject):
    """Compute eta(0), eta(1); the caller's fixed_endpoints tag is no proof."""
    _supported(subject)
    endpoints = tuple(evaluate(subject.variation, (x,)) for x in subject.interval)
    if subject.admissible_variations == "fixed_endpoints" and endpoints != (Q(0), Q(0)):
        raise Invalid("INADMISSIBLE_VARIATION", "fixed endpoints require eta(0)=eta(1)=0")
    return endpoints


def _coordinates(subject, t, q, v):
    roles = {"t": t, "q": q, "v": v}
    return tuple(roles[name] for name in subject.lagrangian.variables)


@dataclass(frozen=True)
class DirectExpansion:
    action_in_epsilon: Poly
    first_variation: Q

    def __post_init__(self):
        _poly(self.action_in_epsilon, 1)
        _rational(self.first_variation)


def direct_first_variation(subject):
    """Expand/integrate the whole action; never call EL or differentiate L."""
    check_admissibility(subject)
    t, epsilon = (Poly.variable(i, arity=2) for i in range(2))
    q = substitute(subject.path, (t,))
    eta = substitute(subject.variation, (t,))
    v = substitute(subject.path.derivative(0), (t,))
    eta_prime = substitute(subject.variation.derivative(0), (t,))
    integrand = substitute(subject.lagrangian.expression,
                           _coordinates(subject, t, q + epsilon * eta,
                                        v + epsilon * eta_prime))
    action = integrate(integrand, 0, *subject.interval)
    first = dict(action.terms).get((1,), Q(0))
    return DirectExpansion(action, first)


@dataclass(frozen=True)
class BulkBoundary:
    euler_lagrange: Poly
    bulk: Q
    boundary_at_endpoints: tuple[Q, Q]
    boundary: Q
    first_variation: Q

    def __post_init__(self):
        _poly(self.euler_lagrange, 1)
        _pair(self.boundary_at_endpoints)
        for x in (self.bulk, self.boundary, self.first_variation):
            _rational(x)


def bulk_boundary_first_variation(subject):
    """Independently calculate EL=L_q-d_t(L_v) and the oriented boundary.

    Differentiate L_v AFTER substituting the actual path, retaining explicit
    t-dependence and q'' contributions. Never call the epsilon expansion.
    """
    check_admissibility(subject)
    lagrangian = subject.lagrangian
    coordinates = _coordinates(subject, T, subject.path, subject.path.derivative(0))
    lq = substitute(lagrangian.expression.derivative(lagrangian.variables.index("q")),
                    coordinates)
    momentum = substitute(lagrangian.expression.derivative(lagrangian.variables.index("v")),
                          coordinates)
    el = lq - momentum.derivative(0)
    bulk = evaluate(integrate(el * subject.variation, 0, *subject.interval), ())
    boundary_density = momentum * subject.variation
    at_endpoints = tuple(evaluate(boundary_density, (x,)) for x in subject.interval)
    boundary = at_endpoints[1] - at_endpoints[0]
    return BulkBoundary(el, bulk, at_endpoints, boundary, bulk + boundary)


@dataclass(frozen=True)
class Evidence:
    subject: Subject
    variation_at_endpoints: tuple[Q, Q]
    parts: BulkBoundary

    def __post_init__(self):
        if type(self.subject) is not Subject or type(self.parts) is not BulkBoundary:
            raise Invalid("INVALID_SCHEMA", "expected a bound polynomial variation witness")
        _pair(self.variation_at_endpoints)


def propose(subject):
    """Convenience producer using only the bulk/boundary route; no authority."""
    endpoints = check_admissibility(subject)
    return Evidence(subject, endpoints, bulk_boundary_first_variation(subject))


@dataclass(frozen=True)
class ReferenceCheck:
    subject: Subject
    variation_at_endpoints: tuple[Q, Q]
    direct: DirectExpansion
    parts: BulkBoundary


def verify(subject, evidence):
    """Recompute both routes and each component, bound to the independent input.

    This checks a finite polynomial identity instance, not a general theorem.
    Re-run verify on consumption; constructing a Python record grants no trust.
    """
    if type(subject) is not Subject or type(evidence) is not Evidence:
        raise Invalid("INVALID_SCHEMA", "expected a request and an Evidence record")
    if evidence.subject != subject:
        raise Invalid("EVIDENCE_SUBJECT_MISMATCH", "different L, revision, order, interval or variation context")
    endpoints = check_admissibility(subject)
    if evidence.variation_at_endpoints != endpoints:
        raise Invalid("ENDPOINT_EVIDENCE_MISMATCH", "variation endpoint claims do not match eta")
    direct = direct_first_variation(subject)
    parts = bulk_boundary_first_variation(subject)
    for field, code in (("euler_lagrange", "EULER_LAGRANGE_MISMATCH"),
                        ("bulk", "BULK_MISMATCH"),
                        ("boundary_at_endpoints", "BOUNDARY_ENDPOINT_MISMATCH"),
                        ("boundary", "BOUNDARY_MISMATCH"),
                        ("first_variation", "FIRST_VARIATION_MISMATCH")):
        if getattr(evidence.parts, field) != getattr(parts, field):
            raise Invalid(code, f"incorrect {field} in supplied evidence")
    if direct.first_variation != parts.first_variation:
        raise Invalid("VARIATION_IDENTITY_MISMATCH", "epsilon expansion and bulk plus boundary disagree")
    return ReferenceCheck(subject, endpoints, direct, parts)
