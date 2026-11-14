"""Independent exact Gröbner-basis reference for the Stage 2 affine profile.

This is a Python reference model, not a Lean proof and not the compiler's
implementation. It computes reduced, monic Gröbner bases over QQ in the
degree-lexicographic order (total degree first, then lexicographic with
coordinate 0 most significant), plus normal forms. `tests/fixtures/
algebra-bases.json` records its results. The kernel regression
`VastitasAlgebraTest.BasisRegression` checks that the Lean kernel computes
the same bases and normal forms.

Run `python3 scripts/affine_algebra_reference.py --check` to compare the
fixture with this model, or `--write` to regenerate it.
"""

import argparse
import json
import sys
from fractions import Fraction
from itertools import combinations
from pathlib import Path

FIXTURE = Path(__file__).resolve().parent.parent / "tests" / "fixtures" / "algebra-bases.json"


class Invalid(ValueError):
    """Malformed input, never a mathematical result."""


def key(monomial):
    """degLex sort key: larger keys are larger monomials."""
    return (sum(monomial), monomial)


def check_monomial(monomial, arity):
    if type(monomial) is not tuple or len(monomial) != arity:
        raise Invalid(f"expected {arity} exponents")
    for exponent in monomial:
        if type(exponent) is not int or exponent < 0:
            raise Invalid("exponents must be nonnegative integers")


def poly(terms, arity):
    """Build a polynomial (dict monomial -> nonzero Fraction) from pairs."""
    result = {}
    for monomial, coefficient in terms:
        monomial = tuple(monomial)
        check_monomial(monomial, arity)
        if type(coefficient) not in (int, Fraction):
            raise Invalid("coefficients must be exact")
        result[monomial] = result.get(monomial, Fraction(0)) + Fraction(coefficient)
        if result[monomial] == 0:
            del result[monomial]
    return result


def leading(p):
    return max(p, key=key)


def add(p, q, scale=Fraction(1)):
    result = dict(p)
    for monomial, coefficient in q.items():
        value = result.get(monomial, Fraction(0)) + scale * coefficient
        if value == 0:
            result.pop(monomial, None)
        else:
            result[monomial] = value
    return result


def times_term(p, monomial, coefficient):
    return {tuple(a + b for a, b in zip(m, monomial)): c * coefficient for m, c in p.items()}


def divides(a, b):
    return all(x <= y for x, y in zip(a, b))


def normal_form(p, basis):
    """Full reduction of every term, dividing by the first applicable element."""
    rest = dict(p)
    remainder = {}
    while rest:
        monomial = leading(rest)
        coefficient = rest[monomial]
        for g in basis:
            lead = leading(g)
            if divides(lead, monomial):
                quotient = tuple(a - b for a, b in zip(monomial, lead))
                rest = add(rest, times_term(g, quotient, coefficient / g[lead]), Fraction(-1))
                break
        else:
            remainder[monomial] = coefficient
            del rest[monomial]
    return remainder


def s_polynomial(g, h):
    lg, lh = leading(g), leading(h)
    lcm = tuple(max(a, b) for a, b in zip(lg, lh))
    left = times_term(g, tuple(a - b for a, b in zip(lcm, lg)), 1 / g[lg])
    right = times_term(h, tuple(a - b for a, b in zip(lcm, lh)), 1 / h[lh])
    return add(left, right, Fraction(-1))


def groebner(relations):
    """Plain Buchberger over all pairs, then minimize, interreduce and normalize."""
    basis = [dict(f) for f in relations if f]
    queue = list(combinations(range(len(basis)), 2))
    while queue:
        i, j = queue.pop(0)
        remainder = normal_form(s_polynomial(basis[i], basis[j]), basis)
        if remainder:
            basis.append(remainder)
            queue.extend((k, len(basis) - 1) for k in range(len(basis) - 1))
    minimal = []
    for index, g in enumerate(basis):
        lead = leading(g)
        if not any(
            other is not g and divides(leading(other), lead)
            and (leading(other) != lead or position < index)
            for position, other in enumerate(basis)
        ):
            minimal.append(g)
    reduced = []
    for g in minimal:
        others = [h for h in minimal if h is not g]
        r = normal_form(g, others)
        lead = leading(r)
        reduced.append({m: c / r[lead] for m, c in r.items()})
    return sorted(reduced, key=lambda g: key(leading(g)), reverse=True)


def encode_rational(value):
    value = Fraction(value)
    return str(value.numerator) if value.denominator == 1 else f"{value.numerator}/{value.denominator}"


def decode_rational(text):
    if type(text) is not str:
        raise Invalid("coefficients are encoded as strings")
    return Fraction(text)


def encode_poly(p):
    return [[list(m), encode_rational(p[m])] for m in sorted(p, key=key, reverse=True)]


def x(arity, index, power=1):
    return tuple(power if position == index else 0 for position in range(arity))


def one(arity):
    return tuple(0 for _ in range(arity))


def cases():
    """Fixture inputs: (name, arity, relations, normal-form probes)."""
    t, s = Fraction(3, 5), Fraction(-7, 2)
    return [
        ("dual numbers", 1, [poly([(x(1, 0, 2), 1)], 1)],
         [poly([(x(1, 0, 3), 1), (x(1, 0), 2), (one(1), 1)], 1)]),
        ("square root family", 2, [poly([(x(2, 1, 2), 1), (x(2, 0), -1)], 2)],
         [poly([(x(2, 1, 5), 1)], 2), poly([(x(2, 1, 3), 1), (x(2, 0, 2), 1)], 2)]),
        ("fiber over zero", 2, [poly([(x(2, 1, 2), 1), (x(2, 0), -1)], 2), poly([(x(2, 0), 1)], 2)],
         [poly([(x(2, 1, 3), 1), (x(2, 0), 4)], 2)]),
        ("principal open", 2, [poly([((1, 1), 1), (one(2), -1)], 2)],
         [poly([((2, 3), 1)], 2)]),
        ("twisted cubic", 3, [
            poly([(x(3, 1), 1), (x(3, 0, 2), -1)], 3),
            poly([(x(3, 2), 1), (x(3, 0, 3), -1)], 3)],
         [poly([(x(3, 0, 4), 1), (x(3, 2, 2), 1)], 3)]),
        ("unit ideal", 1, [poly([(x(1, 0), 1)], 1), poly([(x(1, 0), 1), (one(1), -1)], 1)],
         [poly([(x(1, 0, 2), 5)], 1)]),
        ("non-basis generators", 2, [
            poly([(x(2, 0, 2), 1), (x(2, 1), -1)], 2),
            poly([((1, 1), 1), (one(2), -1)], 2)],
         [poly([(x(2, 0, 3), 1)], 2)]),
        ("rational coefficients", 2, [
            poly([(x(2, 0, 2), 2), (x(2, 1), t)], 2),
            poly([((1, 1), s), (one(2), 1)], 2)],
         [poly([(x(2, 1, 2), 1)], 2)]),
        ("zero ideal", 2, [], [poly([((2, 1), Fraction(1, 3))], 2)]),
        ("localized family", 3, [
            poly([(x(3, 1, 2), 1), (x(3, 0), -1)], 3),
            poly([((1, 0, 1), 1), (one(3), -1)], 3)],
         [poly([(x(3, 1, 4), 1), (x(3, 2), 1)], 3)]),
    ]


def fixture():
    entries = []
    for name, arity, relations, probes in cases():
        basis = groebner(relations)
        entries.append({
            "name": name,
            "arity": arity,
            "relations": [encode_poly(f) for f in relations],
            "basis": [encode_poly(g) for g in basis],
            "normalForms": [[encode_poly(p), encode_poly(normal_form(p, basis))] for p in probes],
        })
    return {"order": "degLex", "cases": entries}


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
