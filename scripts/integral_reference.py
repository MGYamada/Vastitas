"""Finite QQ-polynomial integral enclosures for #293; Python reference only.

No adaptive quadrature, arbitrary function callbacks, Lean proof, actual Core
acceptance or native rounding guarantee. See docs/integral-reference.md.
"""

from __future__ import annotations

import argparse
import json
from dataclasses import asdict, dataclass
from fractions import Fraction as Q

from rational_polynomial_reference import Invalid, Poly
# Reuse #281's data-only exact wire codecs, not its SOS acceptance algorithm.
from sos_reference import (
    exact, identifier, load_json, poly_data, poly_from_data, rational_data,
    rational_from_data, record, sequence,
)


SCALAR_PROFILE = "QQ-to-R-polynomial/v1"
MEASURE = "real-lebesgue/v1"
LOCAL_PROOF = "quadratic-extrema/v1"


def univariate(poly):
    if type(poly) is not Poly or poly.arity != 1:
        raise Invalid("UNSUPPORTED_FUNCTION", "expected a concrete arity-1 QQ polynomial")


@dataclass(frozen=True)
class Interval:
    lower: Q
    upper: Q

    def __post_init__(self):
        exact(self.lower)
        exact(self.upper)


@dataclass(frozen=True)
class PolynomialFunction:
    function_id: str
    revision: str
    polynomial: Poly

    def __post_init__(self):
        identifier(self.function_id, "function_id")
        identifier(self.revision, "revision")
        univariate(self.polynomial)


@dataclass(frozen=True)
class Target:
    environment_id: str
    domain_id: str
    variable_id: str
    function: PolynomialFunction
    interval: Interval
    scalar_profile: str = SCALAR_PROFILE
    measure: str = MEASURE

    def __post_init__(self):
        for name in ("environment_id", "domain_id", "variable_id", "scalar_profile", "measure"):
            identifier(getattr(self, name), name)
        if type(self.function) is not PolynomialFunction or type(self.interval) is not Interval:
            raise Invalid("INVALID_SCHEMA", "expected a polynomial function and exact interval")


@dataclass(frozen=True)
class Request:
    target: Target
    absolute_radius: Q | None = None

    def __post_init__(self):
        if type(self.target) is not Target:
            raise Invalid("INVALID_SCHEMA", "expected an independently supplied target")
        if self.absolute_radius is not None:
            exact(self.absolute_radius)
            if self.absolute_radius <= 0:
                raise Invalid("INVALID_GOAL", "absolute radius goal must be strictly positive")


@dataclass(frozen=True)
class Cell:
    interval: Interval
    polynomial: Poly
    delta: Q
    proof_interval: Interval
    proof_form: str = LOCAL_PROOF

    def __post_init__(self):
        if type(self.interval) is not Interval or type(self.proof_interval) is not Interval:
            raise Invalid("INVALID_SCHEMA", "expected cell and proof intervals")
        univariate(self.polynomial)
        exact(self.delta)
        identifier(self.proof_form, "proof_form")


def audit_cells(cells):
    if type(cells) is not tuple or any(type(cell) is not Cell for cell in cells):
        raise Invalid("INVALID_SCHEMA", "expected an immutable ordered tuple of cells")


@dataclass(frozen=True)
class Totals:
    local_integrals: tuple[Q, ...]
    q: Q
    error: Q
    enclosure: Interval

    def __post_init__(self):
        if type(self.local_integrals) is not tuple or type(self.enclosure) is not Interval:
            raise Invalid("INVALID_SCHEMA", "expected immutable local integrals and enclosure")
        for value in (*self.local_integrals, self.q, self.error):
            exact(value)


@dataclass(frozen=True)
class Certificate:
    target: Target
    cells: tuple[Cell, ...]
    claimed: Totals

    def __post_init__(self):
        if type(self.target) is not Target or type(self.claimed) is not Totals:
            raise Invalid("INVALID_SCHEMA", "expected target and claimed exact totals")
        audit_cells(self.cells)


@dataclass(frozen=True)
class Check:
    name: str
    status: str
    code: str
    detail: str


@dataclass(frozen=True)
class ReferenceEnclosure:
    """Returned reference data, never an authenticated Vastitas evidence object."""

    target: Target
    cells: tuple[Cell, ...]
    totals: Totals
    absolute_radius: Q | None
    goal_status: str


@dataclass(frozen=True)
class Report:
    request: Request
    certificate: Certificate
    checks: tuple[Check, ...]
    recomputed: Totals | None
    artifact: ReferenceEnclosure | None

    @property
    def accepted(self):
        return self.artifact is not None

    @property
    def goal_status(self):
        return self.artifact.goal_status if self.accepted else "NotEvaluated"


def checked(name, valid, code, detail):
    return Check(name, "pass" if valid else "fail", "OK" if valid else code, detail)


def evaluate(poly, x):
    univariate(poly)
    exact(x)
    return sum((coefficient * x ** powers[0] for powers, coefficient in poly.terms), Q(0))


def antiderivative(poly):
    """Coefficient rule over QQ; independent of any approximation/error proof."""
    univariate(poly)
    return Poly.from_terms((((powers[0] + 1,), coefficient / (powers[0] + 1))
                            for powers, coefficient in poly.terms), arity=1)


def integrate_polynomial(poly, interval):
    univariate(poly)
    if type(interval) is not Interval:
        raise Invalid("INVALID_SCHEMA", "expected an exact interval")
    if interval.lower > interval.upper:
        raise Invalid("REVERSED_INTERVAL", "orientation reversal is outside this profile")
    if interval.lower == interval.upper:
        return Q(0)
    primitive = antiderivative(poly)
    return evaluate(primitive, interval.upper) - evaluate(primitive, interval.lower)


def check_partition(interval, cells):
    """Check supplied order/coverage, never sort or repair a producer's partition."""
    audit_cells(cells)
    a, b = interval.lower, interval.upper
    if a > b:
        return Check("partition", "fail", "REVERSED_INTERVAL", "target requires a <= b")
    if a == b:
        return checked("partition", not cells, "NONEMPTY_ZERO_PARTITION",
                       "zero-length target requires the canonical empty partition")
    if not cells:
        return Check("partition", "fail", "EMPTY_PARTITION", "positive-length target needs cells")
    cursor = a
    for index, cell in enumerate(cells):
        left, right = cell.interval.lower, cell.interval.upper
        if left >= right:
            return Check("partition", "fail", "NONPOSITIVE_CELL", f"cell {index} needs left < right")
        if left != cursor:
            code = "PARTITION_GAP" if left > cursor else "PARTITION_OVERLAP_OR_ORDER"
            return Check("partition", "fail", code, f"cell {index} must start at {cursor}")
        cursor = right
    return checked("partition", cursor == b, "PARTITION_END_MISMATCH", f"last endpoint must be {b}")


def quadratic_extrema(poly, interval):
    """Exhaustive extremum candidates for a polynomial of degree <= 2.

    This finite reduction requires a mathematical theorem; arbitrary samples
    cannot be substituted for these structurally derived candidates.
    """
    univariate(poly)
    if type(interval) is not Interval or interval.lower > interval.upper:
        raise Invalid("REVERSED_INTERVAL", "extrema require an ordered interval")
    if any(powers[0] > 2 for powers, _ in poly.terms):
        raise Invalid("UNSUPPORTED_DIFFERENCE_DEGREE", "only degree <= 2 error polynomials")
    coefficients = dict(poly.terms)
    points = {interval.lower, interval.upper}
    quadratic = coefficients.get((2,), Q(0))
    if quadratic:
        vertex = -coefficients.get((1,), Q(0)) / (2 * quadratic)
        if interval.lower < vertex < interval.upper:
            points.add(vertex)
    return tuple((point, evaluate(poly, point)) for point in sorted(points))


def check_local_error(function, cell, index=0):
    name = f"local_error[{index}]"
    if cell.proof_interval != cell.interval:
        return Check(name, "fail", "LOCAL_DOMAIN_MISMATCH", "proof must cover the entire cell")
    if cell.proof_form != LOCAL_PROOF:
        return Check(name, "unsupported", "UNSUPPORTED_PROOF_FORM", cell.proof_form)
    if cell.interval.lower >= cell.interval.upper:
        return Check(name, "fail", "NONPOSITIVE_CELL", "local cells must have positive length")
    if cell.delta < 0:
        return Check(name, "fail", "NEGATIVE_DELTA", "delta must be nonnegative")
    difference = function.polynomial - cell.polynomial
    try:
        extrema = quadratic_extrema(difference, cell.interval)
    except Invalid as error:
        if error.code != "UNSUPPORTED_DIFFERENCE_DEGREE":
            raise
        return Check(name, "unsupported", error.code, str(error))
    point, value = max(extrema, key=lambda pair: abs(pair[1]))
    return checked(name, abs(value) <= cell.delta, "LOCAL_BOUND_FALSE",
                   f"max abs(f-p) = {abs(value)} at x = {point}; delta = {cell.delta}")


def recompute_totals(cells):
    """Arithmetic only: these sums do not establish coverage or local bounds."""
    audit_cells(cells)
    integrals = tuple(integrate_polynomial(cell.polynomial, cell.interval) for cell in cells)
    q = sum(integrals, Q(0))
    error = sum(((cell.interval.upper - cell.interval.lower) * cell.delta
                 for cell in cells), Q(0))
    return Totals(integrals, q, error, Interval(q - error, q + error))


def check_totals(claimed, actual):
    # Each comparison uses recomputed data, never another producer-supplied total.
    return (
        checked("polynomial_integrals", claimed.local_integrals == actual.local_integrals,
                "LOCAL_INTEGRALS_MISMATCH", "each q_i recomputed by exact coefficient integration"),
        checked("q", claimed.q == actual.q, "Q_MISMATCH", "q = sum of recomputed q_i"),
        checked("error", claimed.error == actual.error, "ERROR_MISMATCH", "E = sum(length_i * delta_i)"),
        checked("enclosure", claimed.enclosure == actual.enclosure,
                "ENCLOSURE_MISMATCH", "B = [recomputed q - E, recomputed q + E]"),
    )


def verify(request, certificate):
    """Validate against an independent request; produce no artifact on any failure."""
    if type(request) is not Request or type(certificate) is not Certificate:
        raise Invalid("INVALID_SCHEMA", "expected Request and Certificate")
    target = request.target
    checks = [checked("binding", target == certificate.target, "TARGET_MISMATCH",
                      "full target equality, including coefficients, revision and interpretation")]
    supported = target.scalar_profile == SCALAR_PROFILE and target.measure == MEASURE
    checks.append(Check("profile", "pass" if supported else "unsupported",
                        "OK" if supported else "UNSUPPORTED_PROFILE",
                        "QQ polynomial interpreted in R with ordinary real Lebesgue measure"))
    checks.append(checked("interval", target.interval.lower <= target.interval.upper,
                          "REVERSED_INTERVAL", "finite rational endpoints with a <= b"))
    downstream = ("polynomial_integrability", "partition",
                  *(f"local_error[{i}]" for i in range(len(certificate.cells))),
                  "polynomial_integrals", "q", "error", "enclosure")
    if any(check.status != "pass" for check in checks):
        checks.extend(Check(name, "not_checked", "PREREQUISITE_FAILED",
                            "binding, supported interpretation and ordered interval required")
                      for name in downstream)
        return Report(request, certificate, tuple(checks), None, None)

    checks.append(Check("polynomial_integrability", "pass", "OK",
                        "concrete real polynomial on a compact interval; no caller continuity tag"))
    checks.append(check_partition(target.interval, certificate.cells))
    checks.extend(check_local_error(target.function, cell, i)
                  for i, cell in enumerate(certificate.cells))
    actual = None
    if any(cell.interval.lower > cell.interval.upper for cell in certificate.cells):
        checks.extend(Check(name, "not_checked", "REVERSED_CELL",
                            "cannot integrate a reversed cell in this profile")
                      for name in ("polynomial_integrals", "q", "error", "enclosure"))
    else:
        actual = recompute_totals(certificate.cells)
        checks.extend(check_totals(certificate.claimed, actual))
    artifact = None
    if all(check.status == "pass" for check in checks):
        goal = ("NotRequested" if request.absolute_radius is None else
                "GoalMet" if actual.error <= request.absolute_radius else "GoalUnmet")
        artifact = ReferenceEnclosure(target, certificate.cells, actual, request.absolute_radius, goal)
    return Report(request, certificate, tuple(checks), actual, artifact)


def interval_data(interval):
    return [rational_data(interval.lower), rational_data(interval.upper)]


def interval_from_data(value):
    if len(sequence(value)) != 2:
        raise Invalid("INVALID_SCHEMA", "interval needs exactly two endpoints")
    return Interval(*(rational_from_data(endpoint) for endpoint in value))


def target_data(target):
    return {"environment_id": target.environment_id, "domain_id": target.domain_id,
            "variable_id": target.variable_id, "scalar_profile": target.scalar_profile,
            "measure": target.measure, "interval": interval_data(target.interval),
            "function": {"function_id": target.function.function_id,
                         "revision": target.function.revision,
                         "polynomial": poly_data(target.function.polynomial)}}


def target_from_data(value):
    record(value, ("environment_id", "domain_id", "variable_id", "scalar_profile",
                   "measure", "interval", "function"))
    f = record(value["function"], ("function_id", "revision", "polynomial"))
    function = PolynomialFunction(f["function_id"], f["revision"], poly_from_data(f["polynomial"], 1))
    return Target(value["environment_id"], value["domain_id"], value["variable_id"], function,
                  interval_from_data(value["interval"]), value["scalar_profile"], value["measure"])


def request_data(request):
    return {"target": target_data(request.target),
            "absolute_radius": (None if request.absolute_radius is None else
                                rational_data(request.absolute_radius))}


def request_from_data(value):
    record(value, ("target", "absolute_radius"))
    radius = value["absolute_radius"]
    return Request(target_from_data(value["target"]), None if radius is None else rational_from_data(radius))


def cell_data(cell):
    return {"interval": interval_data(cell.interval), "polynomial": poly_data(cell.polynomial),
            "delta": rational_data(cell.delta), "proof_interval": interval_data(cell.proof_interval),
            "proof_form": cell.proof_form}


def cell_from_data(value):
    record(value, ("interval", "polynomial", "delta", "proof_interval", "proof_form"))
    return Cell(interval_from_data(value["interval"]), poly_from_data(value["polynomial"], 1),
                rational_from_data(value["delta"]), interval_from_data(value["proof_interval"]),
                value["proof_form"])


def totals_data(totals):
    return {"local_integrals": [rational_data(q) for q in totals.local_integrals],
            "q": rational_data(totals.q), "error": rational_data(totals.error),
            "enclosure": interval_data(totals.enclosure)}


def totals_from_data(value):
    record(value, ("local_integrals", "q", "error", "enclosure"))
    return Totals(tuple(rational_from_data(q) for q in sequence(value["local_integrals"])),
                  rational_from_data(value["q"]), rational_from_data(value["error"]),
                  interval_from_data(value["enclosure"]))


def certificate_data(certificate):
    return {"target": target_data(certificate.target), "cells": [cell_data(c) for c in certificate.cells],
            "claimed": totals_data(certificate.claimed)}


def certificate_from_data(value):
    record(value, ("target", "cells", "claimed"))
    return Certificate(target_from_data(value["target"]),
                       tuple(cell_from_data(c) for c in sequence(value["cells"])),
                       totals_from_data(value["claimed"]))


def report_data(report):
    artifact = None
    if report.accepted:
        artifact = {"target": target_data(report.artifact.target),
                    "cells": [cell_data(c) for c in report.artifact.cells],
                    "totals": totals_data(report.artifact.totals),
                    "absolute_radius": request_data(report.request)["absolute_radius"],
                    "goal_status": report.artifact.goal_status}
    return {"status": "accepted_reference" if report.accepted else "rejected_reference",
            "scope": "Python polynomial integral reference only; no Lean/Core/native guarantee",
            "goal_status": report.goal_status, "request": request_data(report.request),
            "certificate": certificate_data(report.certificate),
            "checks": [asdict(check) for check in report.checks],
            "recomputed": None if report.recomputed is None else totals_data(report.recomputed),
            "artifact": artifact}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("request", help="independently supplied request JSON")
    parser.add_argument("certificate", help="untrusted finite certificate JSON")
    args = parser.parse_args()
    try:
        request = request_from_data(load_json(args.request))
        certificate = certificate_from_data(load_json(args.certificate))
        report = verify(request, certificate)
        output = report_data(report)
    except (Invalid, OSError, UnicodeError, ValueError, RecursionError, MemoryError) as error:
        print(json.dumps({"status": "invalid_reference_input", "artifact": None,
                          "goal_status": "NotEvaluated", "code": getattr(error, "code", "INPUT_ERROR"),
                          "detail": str(error)}))
        return 2
    print(json.dumps(output, indent=2))
    return 0 if report.accepted else 1


if __name__ == "__main__":
    raise SystemExit(main())
