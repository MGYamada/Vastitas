"""Exact two-dimensional fixture for the Stage 3 smooth runtime.

This is a Python reference fixture writer, not a Lean proof and not the
compiler's implementation. It adds no mathematics: it drives the independent
references `metric_free_reference.py` (cotangent pullbacks along polynomial
maps of the real plane, differentials of plane functions) and
`metric_reference.py` (nondegeneracy and Riemannian evidence, flat and sharp)
on fixed inputs, and serializes their results to `tests/fixtures/
smooth-differential.json`. The kernel regression
`VastitasAlgebraTest.SmoothReferenceRegression` checks that `SmoothRuntime`
and `SmoothDeclarations` compute the same values. The references cover only
the real plane: maps R^2 -> R^2, functions R^2 -> R and 2 by 2 Gram matrices.

Polynomials use the encoding of `algebra-bases.json`: arity-2 terms
`[exponents, "num/den"]` in strictly decreasing degLex order, coordinate 0
most significant. A pullback whose seed does not lie over the map's output is
recorded as `null`, the reference's SEED_BASEPOINT_MISMATCH. Metric failures
record the reference's error code.

Run `python3 scripts/smooth_differential_reference.py --check` to compare the
fixture with the references, or `--write` to regenerate it.
"""

import argparse
import json
import sys
from dataclasses import replace
from fractions import Fraction as Q
from pathlib import Path

import metric_free_reference as mf
import metric_reference as mr
from affine_algebra_reference import encode_rational, key

FIXTURE = Path(__file__).resolve().parent.parent / "tests" / "fixtures" / "smooth-differential.json"
ARITY = 2

BASE = mf.Frame("smooth:environment", "smooth:source", "smooth:real-base", "chart:xy",
                "frame:xy", "dual:xy", "model:real-plane", "1", ("x", "y"))
SOURCE, MIDDLE, TARGET = (replace(BASE, object_id=f"smooth:{name}")
                          for name in ("source", "middle", "target"))
METRIC_POINT = (Q(1, 2), -3)

X, Y = mf.X, mf.Y
SHEAR_A = (X + Y, Y)
SHEAR_B = (X, X + Y)
SQUARE = (X ** 2, X * Y + Y)
RATIONAL = (Q(3, 4) * X ** 2 - Q(2, 5) * Y, Q(1, 3) * X * Y ** 2 + Q(7, 2))
CUBE = (X ** 3 - 3 * X * Y ** 2, 3 * X ** 2 * Y - Y ** 3)

# Reference codes that are fixture results. Any other Invalid is a bug here.
NONDEGENERATE_FAILURES = {"SINGULAR"}
RIEMANNIAN_FAILURES = {"SINGULAR", "NOT_POSITIVE_DEFINITE"}
METRIC_FAILURES = {"NOT_SYMMETRIC"}


def encode_poly(value):
    """Arity-2 terms of a reference polynomial, in strictly decreasing degLex."""
    mf.audit_polynomial(value)
    terms = [(powers[:ARITY], coefficient) for powers, coefficient in value.terms]
    return [[list(m), encode_rational(c)] for m, c in sorted(terms, key=lambda t: key(t[0]), reverse=True)]


def encode_vector(values):
    return [encode_rational(value) for value in mf.vector(tuple(values))]


def encode_matrix(rows):
    return [encode_vector(row) for row in mf.matrix(tuple(tuple(row) for row in rows))]


def compose(after, before):
    """The reference's substitution of `before`'s images into `after`'s."""
    return tuple(mf.substitute(expression, before) for expression in after)


def pullback_inputs():
    """(name, images, point, seed, seed point or None for the actual output,
    (after, before) for a composite or None)."""
    origin, dx = (0, 0), (1, 0)
    b_after_a, a_after_b = compose(SHEAR_B, SHEAR_A), compose(SHEAR_A, SHEAR_B)
    return [
        ("shear A at the origin", SHEAR_A, origin, dx, None, None),
        ("shear B at the origin", SHEAR_B, origin, dx, None, None),
        ("B after A at the origin", b_after_a, origin, dx, None, (SHEAR_B, SHEAR_A)),
        ("A after B at the origin", a_after_b, origin, dx, None, (SHEAR_A, SHEAR_B)),
        ("B after A at a rational point", b_after_a, (Q(1, 2), Q(-2, 3)), (Q(3, 5), -1), None,
         (SHEAR_B, SHEAR_A)),
        ("square map at (1, 2)", SQUARE, (1, 2), (3, -2), None, None),
        ("square map at a rational point", SQUARE, (Q(1, 2), Q(-1, 3)), (Q(2, 5), 7), None, None),
        ("square map at a negative point", SQUARE, (-3, Q(5, 4)), (Q(-1, 2), Q(1, 3)), None, None),
        ("square map at the origin", SQUARE, origin, (1, 1), None, None),
        ("rational coefficients", RATIONAL, (Q(2, 3), Q(-3, 2)), (Q(5, 6), -4), None, None),
        ("cube of z", CUBE, (Q(1, 2), Q(1, 3)), (1, -1), None, None),
        ("square after rational coefficients", compose(SQUARE, RATIONAL), (1, -1), (Q(1, 2), 2), None,
         (SQUARE, RATIONAL)),
        ("seed over the wrong output", SQUARE, (1, 2), (3, -2), (1, 5), None),
        ("seed over the input point", SQUARE, (2, 3), (1, 0), (2, 3), None),
        ("shear seed over the wrong output", SHEAR_A, origin, dx, (0, 1), None),
        ("composite seed over the inner output", b_after_a, (1, 1), dx, (2, 1), (SHEAR_B, SHEAR_A)),
    ]


def pullback(images, point, seed, seed_point=None):
    """The reference's output point, seed and pullback; the pullback is None
    exactly when the reference reports SEED_BASEPOINT_MISMATCH."""
    mapping = mf.PolynomialMap(SOURCE, TARGET, images)
    source = mf.Point(SOURCE, point)
    over = mapping.at(source) if seed_point is None else mf.Point(TARGET, seed_point)
    covector = mf.Cotangent(over, seed)
    try:
        return source, covector, mf.cotangent_pullback(mapping, source, covector)
    except mf.Invalid as error:
        if error.code != "SEED_BASEPOINT_MISMATCH":
            raise
        return source, covector, None


def pullback_case(name, images, point, seed, seed_point, composite):
    source, covector, value = pullback(images, point, seed, seed_point)
    entry = {
        "name": name,
        "map": [encode_poly(p) for p in images],
        "point": encode_vector(source.coordinates),
        "seed": encode_vector(covector.components),
        "expected": None if value is None else encode_vector(value.components),
        "seedPoint": encode_vector(covector.point.coordinates),
    }
    if composite is not None:
        after, before = composite
        entry["composite"] = {"after": [encode_poly(p) for p in after],
                              "before": [encode_poly(p) for p in before]}
    return entry


def differential_inputs():
    """(name, function, point)."""
    return [
        ("x^2 + y at (1, 2)", X ** 2 + Y, (1, 2)),
        ("x^2 + xy + 3y^2 at (1, 2)", X ** 2 + X * Y + 3 * Y ** 2, (1, 2)),
        ("rational cubic at a rational point", Q(2, 3) * X ** 3 - Q(5, 7) * X * Y ** 2 + Q(11, 13),
         (Q(3, 2), Q(-2, 5))),
        ("higher degree at a negative point", X ** 3 * Y ** 2 - 4 * Y ** 4 + X, (-1, Q(1, 2))),
        ("affine function at the origin", 3 * X - Q(1, 2) * Y + 4, (0, 0)),
        ("constant function", mf.Poly.constant(Q(-2, 3)), (Q(3, 2), Q(-2, 5))),
        ("zero function", mf.ZERO, (5, -7)),
    ]


def differential_case(name, function, point):
    source = mf.Point(SOURCE, point)
    value = mf.differential(mf.ScalarPolynomial(SOURCE, function), source)
    return {"name": name, "function": encode_poly(function),
            "point": encode_vector(source.coordinates), "expected": encode_vector(value.components)}


def metric_inputs():
    """(name, Gram matrix, covector to raise, vector to lower)."""
    return [
        ("Euclid", ((1, 0), (0, 1)), (3, -2), (Q(1, 2), 5)),
        ("Skew", ((2, 1), (1, 1)), (1, 0), (1, 2)),
        ("Lorentz", ((1, 0), (0, -1)), (Q(2, 3), 4), (1, 1)),
        ("Degenerate", ((1, 0), (0, 0)), (1, 1), (2, 3)),
        ("rational positive definite", ((Q(1, 2), Q(1, 3)), (Q(1, 3), Q(1, 4))), (Q(1, 6), -1), (6, -4)),
        ("hyperbolic plane", ((0, 1), (1, 0)), (2, -5), (Q(-1, 2), 3)),
        ("rational negative definite", ((Q(-3, 2), Q(1, 2)), (Q(1, 2), Q(-1, 4))), (1, 1),
         (Q(2, 3), Q(-1, 5))),
        ("indefinite with positive corner", ((1, 2), (2, 1)), (0, 1), (1, 1)),
        ("rational singular", ((Q(2, 3), 1), (1, Q(3, 2))), (1, 0), (3, -2)),
        ("not symmetric", ((1, 2), (0, 1)), (1, 0), (1, 0)),
    ]


def metric_case(name, gram, covector, tangent):
    entry = {"name": name, "point": encode_vector(METRIC_POINT), "gram": encode_matrix(gram)}
    try:
        metric = mr.Metric(SOURCE, f"metric:{name}", "1", gram)
    except mf.Invalid as error:
        if error.code not in METRIC_FAILURES:
            raise
        return entry | {"nondegenerate": error.code, "riemannian": error.code}
    subject = mr.FiberMetric(metric, mf.Point(SOURCE, METRIC_POINT))
    try:
        evidence = mr.certify_nondegenerate(subject)
        entry["nondegenerate"] = encode_matrix(evidence.inverse_gram)
    except mf.Invalid as error:
        if error.code not in NONDEGENERATE_FAILURES:
            raise
        evidence = None
        entry["nondegenerate"] = error.code
    try:
        mr.certify_riemannian(subject)
        entry["riemannian"] = "ok"
    except mf.Invalid as error:
        if error.code not in RIEMANNIAN_FAILURES:
            raise
        entry["riemannian"] = error.code
    if evidence is not None:
        alpha = mf.Cotangent(subject.point, covector)
        entry["sharp"] = {"covector": encode_vector(alpha.components),
                          "expected": encode_vector(mr.sharp(subject, alpha, evidence).value.components)}
    vector = mf.Tangent(subject.point, tangent)
    entry["flat"] = {"vector": encode_vector(vector.components),
                     "expected": encode_vector(mr.flat(subject, vector).value.components)}
    return entry


def fixture():
    return {
        "order": "degLex",
        "pullbacks": [pullback_case(*case) for case in pullback_inputs()],
        "differentials": [differential_case(*case) for case in differential_inputs()],
        "metrics": [metric_case(*case) for case in metric_inputs()],
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
    if FIXTURE.read_text() != expected:
        print(f"{FIXTURE} differs from the reference model", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
