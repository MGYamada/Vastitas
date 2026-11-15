"""Exact reference fixture of the Stage 5 spectral observations (#806).

This is a fixture writer, not a Lean proof and not the compiler's
implementation. It serializes values that two independent reference models
compute, so that the kernel regressions of Stage 5 can check that the kernel
computes the same values:

- `etale_reference.py` (#765): characteristic polynomials and adjugates of
  exact matrices over QQ[x_1..x_m] (its verifier recomputes both by cofactor
  expansion and checks the spectral identities), trace powers, unit-witness
  charts, and the eigenprojector and the branch differential at rational
  branch points of a finite chart;
- `finite_spectral_reference.py` (#337): the 2 by 2 spectral pairs over QQ,
  where a scalar matrix and a Jordan block share the characteristic
  polynomial and differ in the action of t.

The writer asserts the identities it relies on (Newton's identities, Jacobi's
formula, Hellmann-Feynman, P^2 = P, tr P = 1) before it writes anything.

Encoding, as in `tests/fixtures/frames.json`: a polynomial is a list of terms
`[exponents, "num/den"]` in strictly decreasing degLex order, coordinate 0
most significant. A polynomial of the base QQ[x_1..x_m] has m exponents; a
polynomial of A[t] has one more, for the fiber coordinate t, last. Matrices
are lists of rows.

Run `python3 scripts/spectral_fixture.py --check` to compare the fixture with
the models, or `--write` to regenerate it.
"""

import argparse
import json
import sys
from fractions import Fraction as Q
from pathlib import Path

import etale_reference as er
import finite_spectral_reference as fs
from affine_algebra_reference import encode_rational, key
from rational_polynomial_reference import Poly

FIXTURE = Path(__file__).resolve().parent.parent / "tests" / "fixtures" / "spectral.json"
MAX_POWER = 5


def context(variables, name):
    return er.Context("reference:environment:1", f"base:{name}", "Spec-QQ", f"model:{name}", "1",
                      er.SCALAR_PROFILE, er.SITE, variables, "t")


# Encoding.
def encode_poly(value, arity):
    """Terms in decreasing degLex order, truncated to `arity` exponents (the rest must be zero)."""
    terms = []
    for powers, coefficient in value.terms:
        assert all(p == 0 for p in powers[arity:]), "a base polynomial has a fiber exponent"
        terms.append((tuple(powers[:arity]), coefficient))
    return [[list(m), encode_rational(c)] for m, c in sorted(terms, key=lambda t: key(t[0]), reverse=True)]


def encode_matrix(rows, arity):
    return [[encode_poly(entry, arity) for entry in row] for row in rows]


def encode_rationals(values):
    return [encode_rational(Q(v)) for v in values]


def encode_rational_matrix(rows):
    return [encode_rationals(row) for row in rows]


# Exact evaluation of reference polynomials.
def evaluate(poly, values):
    total = Q(0)
    for powers, coefficient in poly.terms:
        term = Q(coefficient)
        for value, power in zip(values, powers):
            term *= Q(value) ** power
        total += term
    return total


def evaluate_matrix(rows, values):
    return tuple(tuple(evaluate(entry, values) for entry in row) for row in rows)


def rational_product(left, right):
    size = range(len(left))
    return tuple(tuple(sum((left[i][k] * right[k][j] for k in size), Q(0)) for j in size) for i in size)


# Spectra: exact matrices over the base, with their characteristic polynomial,
# adjugate, trace powers and coefficients.
def spectral_subject(name, variables, rows):
    ctx = context(variables, name)
    arity = len(variables) + 1
    zero = Poly.constant(0, arity)

    def entry(value):
        return value if isinstance(value, Poly) else zero + value

    matrix = tuple(tuple(entry(value) for value in row) for row in rows)
    return er.SpectralSubject(ctx, f"map:{name}", "1", matrix)


def subjects():
    x, y, t = (Poly.variable(i, 3) for i in range(3))
    xc = Poly.variable(0, 2)
    zero3, zero2 = Poly.constant(0, 3), Poly.constant(0, 2)
    return {
        "stage5": spectral_subject("stage5", ("x", "y"), ((x, y), (y, zero3 - x))),
        "cubic": spectral_subject("cubic", ("x",), ((0, 0, zero2 - xc), (1, 0, 3), (0, 1, 0))),
        "symmetric3": spectral_subject("symmetric3", ("x", "y"), ((x, y, 1), (y, 0, x), (1, x, zero3 - y))),
        "quartic": spectral_subject("quartic", ("x", "y"), ((0, 0, 0, x), (1, 0, 0, y), (0, 1, 0, 1), (0, 0, 1, 0))),
        "zero": spectral_subject("zero", (), ((0, 0), (0, 0))),
        "nilpotent": spectral_subject("nilpotent", (), ((0, 1), (0, 0))),
        "scalar": spectral_subject("scalar", (), ((2, 0), (0, 2))),
        "jordan": spectral_subject("jordan", (), ((2, 1), (0, 2))),
    }


def trace_powers(subject):
    rank, arity = len(subject.matrix), subject.context.arity
    power, values = er.identity(rank, arity), []
    for _ in range(MAX_POWER):
        power = er.multiply(power, subject.matrix)
        values.append(er.matrix_trace(power))
    return values


def coefficients(chi):
    """Coefficient of t^i in chi, as base polynomials, i = 0..deg."""
    arity = chi.arity
    top = er.degree(chi, arity - 1)
    return [Poly.from_terms(((p[:-1] + (0,), c) for p, c in chi.terms if p[-1] == i), arity)
            for i in range(top + 1)]


def spectrum_case(name, subject):
    candidate = er.propose_spectral(subject)
    report = er.verify_spectral(subject, candidate)
    assert report.accepted, (name, [c for c in report.checks if c.status != "pass"])
    chi, arity, m = candidate.characteristic, subject.context.arity, len(subject.context.variables)
    powers = trace_powers(subject)
    for k, value in enumerate(powers, start=1):
        # Newton: the trace of t^k over A[t]/(chi) is tr(H^k).
        assert er.trace(Poly.variable(arity - 1, arity) ** k, chi) == value, (name, k)
    fiber = arity - 1
    for i in range(m):
        # Jacobi's formula: d_i chi = -tr(adj * d_i H).
        derivative = er.entrywise(subject.matrix, lambda e: e.derivative(i))
        product = er.multiply(candidate.adjugate, derivative)
        assert chi.derivative(i) == Poly.constant(0, arity) - er.matrix_trace(product), (name, i)
    del fiber
    return {
        "name": name,
        "variables": list(subject.context.variables),
        "matrix": encode_matrix(subject.matrix, m),
        "characteristic": encode_poly(chi, arity),
        "adjugate": encode_matrix(candidate.adjugate, arity),
        "tracePowers": [encode_poly(value, m) for value in powers],
        "coefficients": [encode_poly(value, m) for value in coefficients(chi)],
    }


# Charts: unit witnesses W * chi' = g^e modulo chi, with the reference verdict.
def chart_cases(table):
    s5, cu, jo = table["stage5"], table["cubic"], table["jordan"]
    x, y, t = (Poly.variable(i, 3) for i in range(3))
    xc, tc = Poly.variable(0, 2), Poly.variable(1, 2)
    tp = Poly.variable(0, 1)
    gap = x * x + y * y
    cubic_witness = tc * tc * Q(-2, 3) - tc * xc * Q(1, 3) + Q(4, 3)
    cases = (
        ("stage5 gap", s5, gap, t * Q(1, 2), 1),
        ("stage5 squared gap", s5, gap * gap * 4, t * gap * 2, 1),
        ("stage5 without a gap", s5, Poly.constant(1, 3), t * Q(1, 2), 0),
        ("stage5 perturbed witness", s5, gap, t * (Q(1, 2) + Q(1, 10 ** 20)), 1),
        ("stage5 wrong exponent", s5, gap, t * Q(1, 2), 2),
        ("stage5 unreduced witness", s5, gap, t * Q(1, 2) + t * t * t, 1),
        ("stage5 zero localizer", s5, Poly.constant(0, 3), t * Q(1, 2), 1),
        ("cubic off the discriminant", cu, xc * xc - 4, cubic_witness, 1),
        ("cubic without a gap", cu, Poly.constant(1, 2), cubic_witness, 0),
        ("jordan without a gap", jo, Poly.constant(1, 1), Poly.constant(1, 1), 0),
        ("jordan shifted witness", jo, Poly.constant(1, 1), tp - 2, 0),
    )
    out = []
    for label, subject, localizer, witness, exponent in cases:
        name = next(n for n, s in table.items() if s is subject)
        chi = er.propose_spectral(subject).characteristic
        chart = er.Subject(subject.context, er.Chart(f"chart:{name}", "1", chi, localizer))
        report = er.verify_chart(chart, er.ChartCertificate(chart, witness, exponent))
        failed = [c.code for c in report.checks if c.status != "pass"]
        m = len(subject.context.variables)
        out.append({"label": label, "spectrum": name,
                    "localizer": encode_poly(localizer, m) if er.is_base(localizer) else None,
                    "localizerWithFiber": encode_poly(localizer, m + 1),
                    "witness": encode_poly(witness, m + 1), "exponent": exponent,
                    "accepted": report.accepted, "failure": failed[0] if failed else None})
    return out


# Branch points of a finite chart: (p, t) with g(p) != 0 and chi(p, t) = 0.
def branch_case(label, name, subject, localizer, point, value):
    candidate = er.propose_spectral(subject)
    chi, arity = candidate.characteristic, subject.context.arity
    full = tuple(point) + (value,)
    g = evaluate(localizer, full)
    on_chart = g != 0 and evaluate(chi, full) == 0
    case = {"label": label, "spectrum": name, "point": encode_rationals(point),
            "eigenvalue": encode_rational(Q(value)), "onChart": on_chart,
            "projector": None, "differential": None}
    if not on_chart:
        return case
    slope = evaluate(chi.derivative(arity - 1), full)
    assert slope != 0, label
    adjugate = evaluate_matrix(candidate.adjugate, full)
    projector = tuple(tuple(entry / slope for entry in row) for row in adjugate)
    rank = len(projector)
    assert rational_product(projector, projector) == projector, label
    assert sum(projector[i][i] for i in range(rank)) == 1, label
    h = evaluate_matrix(subject.matrix, full)
    assert rational_product(h, projector) == tuple(tuple(Q(value) * e for e in row) for row in projector), label
    differential = []
    for i in range(arity - 1):
        implicit = -evaluate(chi.derivative(i), full) / slope
        derivative = evaluate_matrix(er.entrywise(subject.matrix, lambda e: e.derivative(i)), full)
        hellmann = sum(rational_product(projector, derivative)[j][j] for j in range(rank))
        assert implicit == hellmann, (label, i)
        differential.append(implicit)
    case["projector"] = encode_rational_matrix(projector)
    case["differential"] = encode_rationals(differential)
    return case


def branch_cases(table):
    x, y = Poly.variable(0, 3), Poly.variable(1, 3)
    gap = x * x + y * y
    xc = Poly.variable(0, 2)
    s5, cu = table["stage5"], table["cubic"]
    return [
        branch_case("stage5 (3, 4), 5", "stage5", s5, gap, (3, 4), 5),
        branch_case("stage5 (3, 4), -5", "stage5", s5, gap, (3, 4), -5),
        branch_case("stage5 (1, 0), 1", "stage5", s5, gap, (1, 0), 1),
        branch_case("stage5 (1, 0), -1", "stage5", s5, gap, (1, 0), -1),
        branch_case("stage5 (0, 1), 1", "stage5", s5, gap, (0, 1), 1),
        branch_case("stage5 (3, 4), 4 is no eigenvalue", "stage5", s5, gap, (3, 4), 4),
        branch_case("stage5 origin, 0 is off the chart", "stage5", s5, gap, (0, 0), 0),
        branch_case("cubic 0, 0", "cubic", cu, xc * xc - 4, (0,), 0),
        branch_case("cubic 2, 1 is off the chart", "cubic", cu, xc * xc - 4, (2,), 1),
    ]


# Module actions over QQ: f(H) for elements f of QQ[t].
def module_cases():
    frame = fs.Frame("reference:environment:1", "QQ", "V", "e1,e2")
    t = fs.T
    elements = {"t": t, "t - 2": t - 2, "(t - 2)^2": (t - 2) ** 2, "t^2": t * t}
    cases = []
    for name, rows in (("zero", ((0, 0), (0, 0))), ("nilpotent", ((0, 1), (0, 0))),
                       ("scalar", ((2, 0), (0, 2))), ("jordan", ((2, 1), (0, 2)))):
        subject = fs.Subject(f"map:{name}", "1", frame, frame, rows)
        fs.verify(subject, fs.propose(subject))
        chi = fs.characteristic_polynomial(subject.h)
        actions = []
        for label, element in elements.items():
            value = fs.evaluate_at(element, subject.h)
            actions.append({"element": label, "elementPoly": encode_poly(element, 1),
                            "action": encode_rational_matrix(value),
                            "annihilates": value == fs.ZERO_MATRIX})
        cases.append({"name": name, "characteristic": encode_poly(chi, 1), "actions": actions})
    return cases


def fixture():
    table = subjects()
    return {
        "order": "degLex",
        "spectra": [spectrum_case(name, subject) for name, subject in table.items()],
        "charts": chart_cases(table),
        "branchPoints": branch_cases(table),
        "modules": module_cases(),
    }


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument("--check", action="store_true")
    group.add_argument("--write", action="store_true")
    args = parser.parse_args(argv)
    expected = json.dumps(fixture(), indent=2) + "\n"
    if args.write:
        FIXTURE.write_text(expected)
        return 0
    if not FIXTURE.is_file() or FIXTURE.read_text() != expected:
        print(f"{FIXTURE} differs from the reference models", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
