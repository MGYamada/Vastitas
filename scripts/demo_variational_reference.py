"""Reproduce #305's exact examples and representative rejected claims."""

import json
from dataclasses import replace
from fractions import Fraction as Q

from rational_polynomial_reference import Invalid, Poly
from variational_reference import Lagrangian, Subject, T, propose, verify


def run_demo():
    _, q, v = (Poly.variable(i, arity=3) for i in range(3))
    total = Lagrangian("demo:total-derivative", "1", ("t", "q", "v"), q * v)
    free = Subject(total, T, T)
    fixed = Subject(total, T, T * (1 + -T), "fixed_endpoints")
    oscillator = replace(fixed, lagrangian=Lagrangian(
        "demo:oscillator", "1", ("t", "q", "v"), Q(1, 2) * (v ** 2 - q ** 2)))
    positives = []
    for name, request in (("total_derivative_free", free),
                          ("total_derivative_fixed", fixed),
                          ("oscillator_fixed", oscillator)):
        result = verify(request, propose(request))
        positives.append({
            "name": name,
            "epsilon_coefficient": str(result.direct.first_variation),
            "bulk": str(result.parts.bulk),
            "boundary_at_endpoints": list(map(str, result.parts.boundary_at_endpoints)),
            "boundary": str(result.parts.boundary),
            "bulk_plus_boundary": str(result.parts.first_variation),
            "variation_at_endpoints": list(map(str, result.variation_at_endpoints)),
        })

    good = propose(free)
    claimed_fixed = replace(free, admissible_variations="fixed_endpoints")
    negative_inputs = (
        ("missing_boundary", free,
         replace(good, parts=replace(good.parts, boundary=Q(0), first_variation=Q(0)))),
        ("wrong_boundary_sign", free,
         replace(good, parts=replace(good.parts, boundary=Q(-1), first_variation=Q(-1)))),
        ("fixed_endpoint_tag", claimed_fixed,
         replace(good, subject=claimed_fixed, variation_at_endpoints=(Q(0), Q(0)))),
        ("stale_revision", replace(free, lagrangian=replace(total, revision="2")), good),
        ("wrong_interval", replace(free, interval=(Q(0), Q(2))), good),
        ("wrong_variable_order", replace(free, lagrangian=replace(total, variables=("t", "v", "q"))), good),
    )
    negatives = []
    for name, request, evidence in negative_inputs:
        try:
            verify(request, evidence)
        except Invalid as error:
            negatives.append({"name": name, "outcome": "rejected", "code": error.code})
        else:
            raise AssertionError(f"incorrectly accepted {name}")
    return {"scope": "finite exact polynomial reference; no Lean/Core acceptance",
            "positive": positives, "negative": negatives}


if __name__ == "__main__":
    print(json.dumps(run_demo(), indent=2))
