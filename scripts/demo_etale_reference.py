"""Reproduce the standard-etale chart examples of #765 and their rejection reasons."""

import json
import sys
from dataclasses import asdict, replace
from fractions import Fraction as Q

import etale_reference as ref
from rational_polynomial_reference import Poly


def context(variables, name):
    return ref.Context("reference:environment:1", f"base:{name}", "Spec-QQ", f"model:{name}", "1",
                       ref.SCALAR_PROFILE, ref.SITE, variables, "t")


def text(value, names):
    """Demo rendering only; never parsed back."""
    def term(powers, coefficient):
        factors = [n if p == 1 else f"{n}^{p}" for n, p in zip(names, powers) if p]
        return "*".join([str(coefficient)] * (coefficient != 1 or not factors) + factors)
    return " + ".join(term(p, c) for p, c in value.terms) or "0"


def stage5():
    """H = [[x, y], [y, -x]] over QQ[x, y]: eigenvalues +-sqrt(x^2 + y^2) meet at the origin."""
    ctx = context(("x", "y"), "plane")
    x, y, t = (Poly.variable(i, 3) for i in range(3))
    zero = Poly.constant(0, 3)
    subject = ref.SpectralSubject(ctx, "map:H", "1", ((x, y), (y, zero - x)))
    candidate = ref.propose_spectral(subject)
    gap = x * x + y * y
    finite = ref.Subject(ctx, ref.Chart("chart:gap", "1", candidate.characteristic, gap))
    certificate = ref.ChartCertificate(finite, t * Q(1, 2), 1)
    return {"context": ctx, "subject": subject, "candidate": candidate, "gap": gap,
            "simple": ref.simple_root_chart(candidate, "chart:simple-root", "1"),
            "finite": finite, "certificate": certificate}


def cubic():
    """p = t^3 - 3t + x: a simple root exists over every x, a double root at x = 2 and x = -2."""
    ctx = context(("x",), "line")
    x, t = Poly.variable(0, 2), Poly.variable(1, 2)
    relation = t ** 3 - t * 3 + x
    zero, one = Poly.constant(0, 2), Poly.constant(1, 2)
    subject = ref.SpectralSubject(ctx, "map:companion", "1",
                                  ((zero, zero, zero - x), (one, zero, one * 3), (zero, one, zero)))
    candidate = ref.propose_spectral(subject)
    witness = t * t * Q(-2, 3) - t * x * Q(1, 3) + Q(4, 3)
    finite = ref.Subject(ctx, ref.Chart("chart:discriminant", "1", relation, x * x - 4))
    everywhere = ref.Subject(ctx, ref.Chart("chart:everywhere", "1", relation, one))
    return {"context": ctx, "relation": relation, "subject": subject, "candidate": candidate,
            "simple": ref.simple_root_chart(candidate, "chart:simple-root", "1"),
            "finite": finite, "certificate": ref.ChartCertificate(finite, witness, 1),
            "everywhere": everywhere, "false_certificate": ref.ChartCertificate(everywhere, witness, 0)}


def number_fields():
    """Finite etale covers of Spec QQ: QQ(sqrt 2) and the cyclotomic field QQ(zeta_3)."""
    ctx = context((), "point")
    t = Poly.variable(0, 1)
    one = Poly.constant(1, 1)
    sqrt2 = ref.Subject(ctx, ref.Chart("chart:sqrt2", "1", t * t - 2, one))
    zeta3 = ref.Subject(ctx, ref.Chart("chart:zeta3", "1", t * t + t + 1, one))
    return {"context": ctx,
            "sqrt2": sqrt2, "sqrt2_certificate": ref.ChartCertificate(sqrt2, t * Q(1, 4), 0),
            "zeta3": zeta3,
            "zeta3_certificate": ref.ChartCertificate(zeta3, t * Q(-2, 3) - Q(1, 3), 0)}


def descent(chart, certificate, numerator, descended=None, name="section"):
    subject = ref.DescentSubject(chart, ref.Section(f"section:{name}", "1", numerator, 0))
    return subject, ref.DescentCertificate(subject, certificate,
                                           numerator if descended is None else descended)


def examples():
    """name -> (verifier, arguments, accepted, codes of the checks that do not pass)."""
    s5, cu, nf = stage5(), cubic(), number_fields()
    t3, t1 = Poly.variable(2, 3), Poly.variable(0, 1)
    branch = descent(s5["finite"], s5["certificate"], t3, name="eigenvalue")
    invariant = descent(s5["finite"], s5["certificate"], s5["gap"], name="energy-squared")
    unreduced = descent(s5["finite"], s5["certificate"], t3 * t3, s5["gap"], name="unreduced")
    on_simple = descent(s5["simple"].subject, s5["simple"], s5["gap"], name="energy-squared")
    conjugate = descent(nf["zeta3"], nf["zeta3_certificate"], t1 + 1, name="zeta-plus-one")
    negated = replace(s5["subject"], matrix=ref.scale(s5["subject"].matrix, -1))
    wrong_sign = replace(s5["candidate"], adjugate=ref.propose_spectral(negated).adjugate)
    return {
        "stage5_spectral": (ref.verify_spectral, (s5["subject"], s5["candidate"]), True, ()),
        "stage5_simple_root_chart": (ref.verify_chart, (s5["simple"].subject, s5["simple"]), True, ()),
        "stage5_finite_over_gap": (ref.verify_chart, (s5["finite"], s5["certificate"]), True, ()),
        "stage5_branch_does_not_descend": (ref.verify_descent, branch, False,
                                           ("SELF_OVERLAP_DISAGREEMENT", "RESTRICTION_MISMATCH")),
        "stage5_invariant_descends": (ref.verify_descent, invariant, True, ()),
        "stage5_unreduced_section": (ref.verify_descent, unreduced, False,
                                     ("NOT_REDUCED", "RESTRICTION_MISMATCH")),
        "stage5_descent_needs_cover": (ref.verify_descent, on_simple, False, ("UNSUPPORTED_COVER",)),
        "stage5_resolution": (ref.verify_resolution,
                              (s5["subject"], s5["finite"], s5["candidate"], s5["certificate"]),
                              True, ()),
        "stage5_resolution_needs_gap": (ref.verify_resolution,
                                        (s5["subject"], s5["simple"].subject, s5["candidate"],
                                         s5["simple"]), False, ("UNSUPPORTED_CHART",)),
        "stage5_projector_of_minus_H": (ref.verify_spectral, (s5["subject"], wrong_sign), False,
                                        ("ADJUGATE_MISMATCH", "EIGEN_COLUMN_MISMATCH",
                                         "DIVIDED_DIFFERENCE_MISMATCH")),
        "cubic_spectral": (ref.verify_spectral, (cu["subject"], cu["candidate"]), True, ()),
        "cubic_simple_root_chart": (ref.verify_chart, (cu["simple"].subject, cu["simple"]), True, ()),
        "cubic_finite_off_discriminant": (ref.verify_chart, (cu["finite"], cu["certificate"]), True, ()),
        "cubic_not_finite_etale_everywhere": (ref.verify_chart,
                                              (cu["everywhere"], cu["false_certificate"]),
                                              False, ("UNIT_WITNESS_MISMATCH",)),
        "cubic_resolution": (ref.verify_resolution,
                             (cu["subject"], cu["finite"], cu["candidate"], cu["certificate"]),
                             True, ()),
        "sqrt2_cover_of_point": (ref.verify_chart, (nf["sqrt2"], nf["sqrt2_certificate"]), True, ()),
        "zeta3_cover_of_point": (ref.verify_chart, (nf["zeta3"], nf["zeta3_certificate"]), True, ()),
        "zeta3_conjugate_does_not_descend": (ref.verify_descent, conjugate, False,
                                             ("SELF_OVERLAP_DISAGREEMENT", "RESTRICTION_MISMATCH")),
    }


def main():
    s5 = stage5()
    names = ("x", "y", "t")
    cases, agreed = {}, True
    for name, (verifier, arguments, accepted, codes) in examples().items():
        report = verifier(*arguments)
        failed = tuple(c.code for c in report.checks if c.status in ("fail", "unsupported"))
        matches = report.accepted == accepted and failed == codes
        agreed = agreed and matches
        cases[name] = {"accepted_reference": report.accepted, "expected": matches,
                       "checks": [asdict(check) for check in report.checks]}
    chi = s5["candidate"].characteristic
    square = ref.multiply(s5["subject"].matrix, s5["subject"].matrix)
    output = {
        "status": "tested Python reference; no Lean proof or accepted-Core attachment",
        "site": ref.SITE,
        "stage5": {
            "characteristic": text(chi, names),
            "adjugate": [[text(entry, names) for entry in row] for row in s5["candidate"].adjugate],
            "finite_chart": {"localizer": text(s5["gap"], names),
                             "unit_witness": text(s5["certificate"].witness, names), "exponent": 1},
            "trace_of_t": text(ref.trace(Poly.variable(2, 3), chi), names),
            "trace_of_t_squared": text(ref.trace(Poly.variable(2, 3) ** 2, chi), names),
            "matrix_trace_of_H_squared": text(ref.matrix_trace(square), names),
        },
        "cases": cases,
        "additional_obligations": ["image opens and cover witnesses for families of charts",
                                   "descent of modules and objects; effectivity theorems",
                                   "Lean checker soundness and actual returned-Core bridge"],
    }
    print(json.dumps(output, indent=2))
    return 0 if agreed else 1


if __name__ == "__main__":
    sys.exit(main())
