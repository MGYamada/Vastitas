"""Exact, incomplete reference verifier for #211; NOT compiler/Lean acceptance.

Only Q[x0,x1,x2,x3] two-forms on R^4 or D(1+q1), with inverse witnesses
N/(1+q1)^k. Standard library only. No expression parser, CAS or numeric sampling
is used in acceptance. See docs/symplectic-reference.md for semantics and gaps.
"""

from __future__ import annotations

import argparse
import json
from dataclasses import asdict, dataclass, fields
from fractions import Fraction
from itertools import combinations
from pathlib import Path


DIM = 4
COORDINATES = ("q1", "p1", "q2", "p2")
TRIPLES = tuple(combinations(range(DIM), 3))
SCALAR_PROFILE = "Q-to-R-polynomial/v1"


class Invalid(ValueError):
    """Malformed or unsupported input, never a mathematical acceptance."""

    def __init__(self, code, message):
        self.code = code
        super().__init__(message)


def natural(value, name):
    if type(value) is not int or value < 0:
        raise Invalid("INVALID_SCHEMA", f"{name} must be a nonnegative integer")


def identifier(value, name):
    if type(value) is not str or not value:
        raise Invalid("INVALID_SCHEMA", f"{name} must be a nonempty identifier")


@dataclass(frozen=True)
class Poly:
    """Canonical sparse polynomial: sorted (exponents, nonzero Fraction) pairs."""

    terms: tuple

    def __post_init__(self):
        if type(self.terms) is not tuple:
            raise Invalid("INVALID_SCHEMA", "polynomial terms must be immutable")
        previous = None
        for term in self.terms:
            if type(term) is not tuple or len(term) != 2:
                raise Invalid("INVALID_SCHEMA", "expected exponent/coefficient pair")
            powers, coefficient = term
            if type(powers) is not tuple or len(powers) != DIM:
                raise Invalid("INVALID_SCHEMA", "expected four exponents")
            for power in powers:
                natural(power, "exponent")
            if type(coefficient) is not Fraction or coefficient == 0:
                raise Invalid("INVALID_SCHEMA", "expected nonzero exact rational")
            if previous is not None and powers <= previous:
                raise Invalid("INVALID_SCHEMA", "terms must be sorted and unique")
            previous = powers

    @staticmethod
    def from_terms(terms):
        """Trusted arithmetic constructor; merge like monomials exactly."""
        result = {}
        for powers, coefficient in terms:
            if type(coefficient) not in (int, Fraction):
                raise Invalid("INVALID_SCHEMA", "no floating point coefficients")
            result[powers] = result.get(powers, Fraction(0)) + coefficient
        return Poly(tuple((p, Fraction(c)) for p, c in sorted(result.items()) if c))

    @staticmethod
    def constant(value):
        return Poly.from_terms([((0,) * DIM, value)])

    @staticmethod
    def variable(index):
        natural(index, "variable index")
        if index >= DIM:
            raise Invalid("INVALID_SCHEMA", "variable index out of range")
        return Poly.from_terms([(tuple(int(i == index) for i in range(DIM)), 1)])

    def __add__(self, other):
        if type(other) is int:
            other = Poly.constant(other)
        if type(other) is not Poly:
            return NotImplemented
        return Poly.from_terms(self.terms + other.terms)

    __radd__ = __add__

    def __neg__(self):
        return Poly.from_terms((p, -c) for p, c in self.terms)

    def __sub__(self, other):
        return self + (-other)

    def __mul__(self, other):
        if type(other) in (int, Fraction):
            other = Poly.constant(other)
        if type(other) is not Poly:
            return NotImplemented
        return Poly.from_terms(
            (tuple(a + b for a, b in zip(p, q)), c * d)
            for p, c in self.terms for q, d in other.terms
        )

    __rmul__ = __mul__

    def __pow__(self, exponent):
        natural(exponent, "power")
        result, base = Poly.constant(1), self
        while exponent:
            if exponent % 2:
                result = result * base
            base = base * base
            exponent //= 2
        return result

    def derivative(self, index):
        natural(index, "derivative index")
        if index >= DIM:
            raise Invalid("INVALID_SCHEMA", "derivative index out of range")
        return Poly.from_terms(
            (tuple(n - int(i == index) for i, n in enumerate(p)), c * p[index])
            for p, c in self.terms if p[index]
        )


ZERO, ONE = Poly.constant(0), Poly.constant(1)


def matrix(rows):
    result = tuple(tuple(p if type(p) is Poly else Poly.constant(p) for p in row)
                   for row in rows)
    audit_matrix(result)
    return result


def audit_matrix(value):
    if (type(value) is not tuple or len(value) != DIM
            or any(type(row) is not tuple or len(row) != DIM for row in value)
            or any(type(p) is not Poly for row in value for p in row)):
        raise Invalid("INVALID_SCHEMA", "expected an immutable 4 by 4 polynomial matrix")


def multiply(left, right):
    audit_matrix(left)
    audit_matrix(right)
    return tuple(tuple(sum((left[i][k] * right[k][j] for k in range(DIM)), ZERO)
                       for j in range(DIM)) for i in range(DIM))


def transpose(value):
    audit_matrix(value)
    return tuple(zip(*value))


IDENTITY = matrix([[int(i == j) for j in range(DIM)] for i in range(DIM)])


@dataclass(frozen=True)
class Context:
    environment_id: str
    object_id: str
    base_id: str
    chart_id: str
    tangent_frame_id: str
    cotangent_frame_id: str
    model_id: str
    model_revision: str
    scalar_profile: str
    coordinates: tuple[str, ...]

    def __post_init__(self):
        for field in fields(self):
            if field.name != "coordinates":
                identifier(getattr(self, field.name), field.name)
        if self.scalar_profile != SCALAR_PROFILE:
            raise Invalid("UNSUPPORTED_PROFILE", "only exact Q coefficients evaluated in R")
        if (type(self.coordinates) is not tuple or len(self.coordinates) != DIM
                or any(type(c) is not str for c in self.coordinates)
                or set(self.coordinates) != set(COORDINATES)):
            raise Invalid("UNSUPPORTED_COORDINATES", "expected an ordering of q1,p1,q2,p2")

    def generator(self):
        return ONE + Poly.variable(self.coordinates.index("q1"))


@dataclass(frozen=True)
class Domain:
    kind: str
    generator: Poly | None = None

    def __post_init__(self):
        if self.kind == "all" and self.generator is None:
            return
        if self.kind == "principal_open" and type(self.generator) is Poly:
            return
        raise Invalid("UNSUPPORTED_DOMAIN", "use all or a polynomial principal_open")


@dataclass(frozen=True)
class Subject:
    context: Context
    domain: Domain
    form_id: str
    form_revision: str
    omega: tuple

    def __post_init__(self):
        if type(self.context) is not Context or type(self.domain) is not Domain:
            raise Invalid("INVALID_SCHEMA", "expected Context and Domain")
        identifier(self.form_id, "form_id")
        identifier(self.form_revision, "form_revision")
        audit_matrix(self.omega)
        if (self.domain.kind == "principal_open"
                and self.domain.generator != self.context.generator()):
            raise Invalid("UNSUPPORTED_DOMAIN", "only D(1+q1); other opens need more evidence")


@dataclass(frozen=True)
class InverseWitness:
    numerator: tuple
    denominator_power: int

    def __post_init__(self):
        audit_matrix(self.numerator)
        natural(self.denominator_power, "denominator_power")


@dataclass(frozen=True)
class Certificate:
    subject: Subject
    claimed_derivative: tuple
    inverse: InverseWitness

    def __post_init__(self):
        if type(self.subject) is not Subject or type(self.inverse) is not InverseWitness:
            raise Invalid("INVALID_SCHEMA", "expected Subject and InverseWitness")
        if (type(self.claimed_derivative) is not tuple
                or len(self.claimed_derivative) != len(TRIPLES)
                or any(type(p) is not Poly for p in self.claimed_derivative)):
            raise Invalid("INVALID_SCHEMA", "expected four polynomial 3-form coefficients")


@dataclass(frozen=True)
class Check:
    name: str
    status: str
    code: str
    detail: str


@dataclass(frozen=True)
class Report:
    subject: Subject
    checks: tuple[Check, ...]

    @property
    def accepted(self):
        return all(c.status == "pass" for c in self.checks)


def check_alternation(omega):
    audit_matrix(omega)
    valid = all(omega[i][i] == ZERO for i in range(DIM)) and all(
        omega[i][j] + omega[j][i] == ZERO for i, j in combinations(range(DIM), 2)
    )
    return Check("alternation", "pass" if valid else "fail",
                 "OK" if valid else "NOT_ALTERNATING", "diagonal zero and A + transpose(A) = 0")


def exterior_derivative(omega):
    """Increasing triples; A_ij is the coefficient of dx_i wedge dx_j (i<j)."""
    audit_matrix(omega)
    return tuple(omega[j][k].derivative(i) - omega[i][k].derivative(j)
                 + omega[i][j].derivative(k) for i, j, k in TRIPLES)


def check_closedness(omega, claimed):
    computed = exterior_derivative(omega)
    if computed != claimed:
        return Check("exterior_derivative", "fail", "DERIVATIVE_WITNESS_MISMATCH",
                     "claimed coefficients differ from the computed exterior derivative")
    valid = all(p == ZERO for p in computed)
    return Check("exterior_derivative", "pass" if valid else "fail",
                 "OK" if valid else "NOT_CLOSED", f"exact coefficients in triple order {TRIPLES}")


def check_inverse(subject, witness):
    """Check denominator jurisdiction BEFORE clearing it; never infer an open."""
    if witness.denominator_power and subject.domain.kind != "principal_open":
        return Check("domain_inverse", "fail", "DENOMINATOR_NOT_JUSTIFIED",
                     "1+q1 vanishes on R^4; D(1+q1) evidence cannot extend to all")
    denominator = subject.context.generator() ** witness.denominator_power
    expected = tuple(tuple(denominator * p for p in row) for row in IDENTITY)
    left = multiply(subject.omega, witness.numerator)
    right = multiply(witness.numerator, subject.omega)
    valid = left == expected and right == expected
    return Check("domain_inverse", "pass" if valid else "fail",
                 "OK" if valid else "INVERSE_IDENTITY_FAILED",
                 "both A*N = h^k I and N*A = h^k I, on the declared domain")


def verify(expected, certificate):
    """expected is independently supplied, never taken from certificate.subject.

    The result contains the exact subject, not a reusable unindexed success bit.
    Matching nominal tags here is NOT authentication by a compiler environment.
    """
    if type(expected) is not Subject or type(certificate) is not Certificate:
        raise Invalid("INVALID_SCHEMA", "expected Subject and Certificate")
    if expected != certificate.subject:
        changed = [f.name for f in fields(Subject)
                   if getattr(expected, f.name) != getattr(certificate.subject, f.name)]
        return Report(expected, (
            Check("binding", "fail", "SUBJECT_MISMATCH", "different " + ", ".join(changed)),
            *(Check(name, "not_checked", "BINDING_REQUIRED", "subject mismatch")
              for name in ("alternation", "exterior_derivative", "domain_inverse")),
        ))
    alternating = check_alternation(expected.omega)
    closed = (check_closedness(expected.omega, certificate.claimed_derivative)
              if alternating.status == "pass" else
              Check("exterior_derivative", "not_checked", "ALTERNATION_REQUIRED",
                    "the supplied bilinear matrix is not a 2-form"))
    return Report(expected, (
        Check("binding", "pass", "OK", "full subject equality, including all coefficients"),
        alternating, closed, check_inverse(expected, certificate.inverse),
    ))


# Strict data-only JSON interface. No eval/sympify, opaque nonzero flags or samples.
def record(value, keys):
    if type(value) is not dict or set(value) != set(keys):
        raise Invalid("INVALID_SCHEMA", f"expected exactly these fields: {', '.join(keys)}")
    return value


def poly_from_data(value):
    if type(value) is not list:
        raise Invalid("INVALID_SCHEMA", "polynomial must be a list of sparse terms")
    terms, seen = [], set()
    for term in value:
        record(term, ("powers", "coefficient"))
        powers, coefficient = term["powers"], term["coefficient"]
        if type(powers) is not list or len(powers) != DIM:
            raise Invalid("INVALID_SCHEMA", "expected four exponents")
        for power in powers:
            natural(power, "exponent")
        if (type(coefficient) is not list or len(coefficient) != 2
                or any(type(c) is not int for c in coefficient) or coefficient[1] <= 0):
            raise Invalid("INVALID_SCHEMA", "coefficient must be [integer, positive integer]")
        powers = tuple(powers)
        if powers in seen:
            raise Invalid("INVALID_SCHEMA", "duplicate monomial")
        seen.add(powers)
        terms.append((powers, Fraction(*coefficient)))
    return Poly.from_terms(terms)


def poly_data(poly):
    return [{"powers": list(p), "coefficient": [c.numerator, c.denominator]}
            for p, c in poly.terms]


def matrix_from_data(value):
    if (type(value) is not list or len(value) != DIM
            or any(type(row) is not list or len(row) != DIM for row in value)):
        raise Invalid("INVALID_SCHEMA", "expected a 4 by 4 matrix")
    return tuple(tuple(poly_from_data(p) for p in row) for row in value)


def matrix_data(value):
    return [[poly_data(p) for p in row] for row in value]


def subject_from_data(value):
    record(value, ("context", "domain", "form_id", "form_revision", "omega"))
    context = record(value["context"], tuple(f.name for f in fields(Context)))
    if type(context["coordinates"]) is not list:
        raise Invalid("INVALID_SCHEMA", "coordinates must be an ordered list")
    context = Context(**(context | {"coordinates": tuple(context["coordinates"])}))
    raw = value["domain"]
    if type(raw) is not dict:
        raise Invalid("UNSUPPORTED_DOMAIN", "a string is not a domain proof")
    if raw.get("kind") == "all":
        record(raw, ("kind",))
        domain = Domain("all")
    elif raw.get("kind") == "principal_open":
        record(raw, ("kind", "generator"))
        domain = Domain("principal_open", poly_from_data(raw["generator"]))
    else:
        raise Invalid("UNSUPPORTED_DOMAIN", "only all and D(1+q1) are supported")
    return Subject(context, domain, value["form_id"], value["form_revision"],
                   matrix_from_data(value["omega"]))


def subject_data(subject):
    domain = {"kind": subject.domain.kind}
    if subject.domain.generator is not None:
        domain["generator"] = poly_data(subject.domain.generator)
    context = asdict(subject.context)
    context["coordinates"] = list(subject.context.coordinates)
    return {"context": context, "domain": domain, "form_id": subject.form_id,
            "form_revision": subject.form_revision, "omega": matrix_data(subject.omega)}


def certificate_from_data(value):
    record(value, ("subject", "claimed_derivative", "inverse"))
    inverse = record(value["inverse"], ("numerator", "denominator_power"))
    derivative = value["claimed_derivative"]
    if type(derivative) is not list or len(derivative) != len(TRIPLES):
        raise Invalid("INVALID_SCHEMA", "expected four derivative coefficients")
    return Certificate(subject_from_data(value["subject"]),
                       tuple(poly_from_data(p) for p in derivative),
                       InverseWitness(matrix_from_data(inverse["numerator"]),
                                      inverse["denominator_power"]))


def certificate_data(certificate):
    return {"subject": subject_data(certificate.subject),
            "claimed_derivative": [poly_data(p) for p in certificate.claimed_derivative],
            "inverse": {"numerator": matrix_data(certificate.inverse.numerator),
                        "denominator_power": certificate.inverse.denominator_power}}


def report_data(report):
    return {"status": "accepted_reference" if report.accepted else "rejected_reference",
            "subject": subject_data(report.subject),
            "checks": [asdict(c) for c in report.checks]}


def load_json(path):
    def unique_record(pairs):
        result = {}
        for key, value in pairs:
            if key in result:
                raise Invalid("INVALID_SCHEMA", f"duplicate JSON key: {key}")
            result[key] = value
        return result

    def reject_constant(value):
        raise Invalid("INVALID_SCHEMA", f"not an exact JSON value: {value}")

    return json.loads(Path(path).read_text(encoding="utf-8"), object_pairs_hook=unique_record,
                      parse_constant=reject_constant)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("request", help="independent expected subject JSON")
    parser.add_argument("certificate", help="untrusted certificate JSON")
    args = parser.parse_args()
    try:
        expected = subject_from_data(load_json(args.request))
        certificate = certificate_from_data(load_json(args.certificate))
        report = verify(expected, certificate)
    except (Invalid, OSError, UnicodeError, json.JSONDecodeError) as error:
        print(json.dumps({"status": "invalid_reference_input",
                          "code": getattr(error, "code", "INPUT_ERROR"),
                          "detail": str(error)}))
        return 2
    print(json.dumps(report_data(report), indent=2))
    return 0 if report.accepted else 1


if __name__ == "__main__":
    raise SystemExit(main())
