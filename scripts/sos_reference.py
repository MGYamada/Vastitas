"""Exact SOS cover reference for #244/#237; NOT Lean or Vastitas acceptance.

Check supplied QQ-polynomial Gram/LDL^T certificates on all real affine space.
No search, eigenvalue computation, sampling, tolerance or general cover decision.
See docs/sos-reference.md for the fixed interpretation and remaining obligations.
"""

from __future__ import annotations

import argparse
import json
from dataclasses import asdict, dataclass, fields
from fractions import Fraction
from pathlib import Path

from rational_polynomial_reference import Invalid, Poly, exponents


SCALAR_PROFILE = "QQ-to-R-polynomial/v1"
SITE = "real-cozero/v1"
PERMUTATION_CONVENTION = "P[i,p[i]]=1;P*G*P^T=L*diag(d)*L^T"
MATH_CHECKS = ("polynomial_identity", "gram_symmetry", "ldl_structure",
               "ldl_identity", "diagonal_nonnegative", "positive_delta")


def identifier(value, name):
    if type(value) is not str or not value:
        raise Invalid("INVALID_SCHEMA", f"{name} must be a nonempty identifier")


def exact(value):
    if type(value) is not Fraction:
        raise Invalid("INVALID_SCHEMA", "expected Fraction, never float or bool")


@dataclass(frozen=True)
class Context:
    environment_id: str
    object_id: str
    base_id: str
    chart_id: str
    model_id: str
    model_revision: str
    scalar_profile: str
    site: str
    variables: tuple[str, ...]

    def __post_init__(self):
        for field in fields(self):
            if field.name != "variables":
                identifier(getattr(self, field.name), field.name)
        if self.scalar_profile != SCALAR_PROFILE or self.site != SITE:
            raise Invalid("UNSUPPORTED_PROFILE", "only QQ polynomials on real cozero space")
        if (type(self.variables) is not tuple or not self.variables
                or any(type(v) is not str or not v for v in self.variables)
                or len(set(self.variables)) != len(self.variables)):
            raise Invalid("INVALID_VARIABLE_ORDER", "expected distinct ordered variable IDs")


@dataclass(frozen=True)
class Domain:
    domain_id: str
    kind: str
    dimension: int

    def __post_init__(self):
        identifier(self.domain_id, "domain_id")
        if self.kind != "all_real":
            raise Invalid("UNSUPPORTED_DOMAIN", "only all R^n; no constrained-domain certificates")
        if type(self.dimension) is not int or self.dimension <= 0:
            raise Invalid("INVALID_SCHEMA", "domain dimension must be a positive integer")


@dataclass(frozen=True)
class Generator:
    function_id: str
    revision: str
    polynomial: Poly

    def __post_init__(self):
        identifier(self.function_id, "function_id")
        identifier(self.revision, "revision")
        if type(self.polynomial) is not Poly:
            raise Invalid("INVALID_SCHEMA", "expected a polynomial generator")


@dataclass(frozen=True)
class Subject:
    context: Context
    domain: Domain
    generators: tuple[Generator, ...]
    monomials: tuple[tuple[int, ...], ...]
    delta: Fraction

    def __post_init__(self):
        if type(self.context) is not Context or type(self.domain) is not Domain:
            raise Invalid("INVALID_SCHEMA", "expected Context and Domain")
        arity = len(self.context.variables)
        if self.domain.dimension != arity:
            raise Invalid("DOMAIN_DIMENSION_MISMATCH", "variables must match the real domain")
        if (type(self.generators) is not tuple or not self.generators
                or any(type(g) is not Generator or g.polynomial.arity != arity
                       for g in self.generators)):
            raise Invalid("INVALID_SCHEMA", "expected nonempty generators in the declared ring")
        if len({g.function_id for g in self.generators}) != len(self.generators):
            raise Invalid("INVALID_SCHEMA", "function IDs must be distinct")
        if type(self.monomials) is not tuple or not self.monomials:
            raise Invalid("INVALID_SCHEMA", "expected a nonempty ordered monomial vector")
        for powers in self.monomials:
            exponents(powers, arity)
        if len(set(self.monomials)) != len(self.monomials):
            raise Invalid("INVALID_SCHEMA", "duplicate basis monomial")
        exact(self.delta)  # Its sign is a separate mathematical check.


def audit_matrix(value, size):
    if (type(value) is not tuple or len(value) != size
            or any(type(row) is not tuple or len(row) != size for row in value)):
        raise Invalid("INVALID_MATRIX_SHAPE", f"expected an immutable {size} by {size} matrix")
    for row in value:
        for entry in row:
            exact(entry)


@dataclass(frozen=True)
class Certificate:
    subject: Subject
    gram: tuple
    permutation: tuple[int, ...]
    lower: tuple
    diagonal: tuple[Fraction, ...]
    convention: str = PERMUTATION_CONVENTION

    def __post_init__(self):
        if type(self.subject) is not Subject:
            raise Invalid("INVALID_SCHEMA", "expected a bound Subject")
        size = len(self.subject.monomials)
        audit_matrix(self.gram, size)
        audit_matrix(self.lower, size)
        if (type(self.permutation) is not tuple or len(self.permutation) != size
                or any(type(p) is not int for p in self.permutation)
                or set(self.permutation) != set(range(size))):
            raise Invalid("INVALID_PERMUTATION", "p must permute 0..m-1 exactly once")
        if self.convention != PERMUTATION_CONVENTION:
            raise Invalid("UNSUPPORTED_PERMUTATION_CONVENTION", PERMUTATION_CONVENTION)
        # D is represented ONLY by its diagonal; no hidden off-diagonal entries.
        if type(self.diagonal) is not tuple or len(self.diagonal) != size:
            raise Invalid("INVALID_MATRIX_SHAPE", "expected m diagonal entries")
        for value in self.diagonal:
            exact(value)


@dataclass(frozen=True)
class Check:
    name: str
    status: str
    code: str
    detail: str


@dataclass(frozen=True)
class Report:
    subject: Subject
    certificate: Certificate
    checks: tuple[Check, ...]

    @property
    def accepted(self):
        return all(check.status == "pass" for check in self.checks)


def checked(name, valid, failure, detail):
    return Check(name, "pass" if valid else "fail", "OK" if valid else failure, detail)


def gram_polynomial(subject, gram):
    """Reconstruct every coefficient, including both off-diagonal contributions."""
    audit_matrix(gram, len(subject.monomials))
    return Poly.from_terms(
        ((tuple(a + b for a, b in zip(p, q)), gram[i][j])
         for i, p in enumerate(subject.monomials)
         for j, q in enumerate(subject.monomials)), len(subject.context.variables),
    )


def check_polynomial_identity(subject, gram):
    target = sum((g.polynomial ** 2 for g in subject.generators),
                 Poly.constant(0, len(subject.context.variables))) - subject.delta
    return checked("polynomial_identity", target == gram_polynomial(subject, gram),
                   "POLYNOMIAL_IDENTITY_MISMATCH", "sum(f_i^2)-delta = v^T G v coefficientwise")


def check_ldl(certificate):
    """Verify a supplied factorization, never find pivots or divide by them.

    P[i,p[i]]=1, so (P G P^T)[i,j]=G[p[i],p[j]] and w=P v.
    Then v^T G v = sum_k d[k] * ((L^T w)[k])^2, including d[k]=0.
    """
    g, p, lower, d = (certificate.gram, certificate.permutation,
                      certificate.lower, certificate.diagonal)
    size = len(p)
    symmetric = all(g[i][j] == g[j][i] for i in range(size) for j in range(size))
    unit_lower = all(lower[i][i] == 1 for i in range(size)) and all(
        lower[i][j] == 0 for i in range(size) for j in range(i + 1, size)
    )
    factorization = all(
        g[p[i]][p[j]] == sum((lower[i][k] * d[k] * lower[j][k] for k in range(size)),
                            Fraction(0))
        for i in range(size) for j in range(size)
    )
    return (
        checked("gram_symmetry", symmetric, "GRAM_NOT_SYMMETRIC", "G = G^T exactly"),
        checked("ldl_structure", unit_lower, "NOT_UNIT_LOWER_TRIANGULAR", "L is unit lower triangular"),
        checked("ldl_identity", factorization, "LDL_IDENTITY_MISMATCH", PERMUTATION_CONVENTION),
        checked("diagonal_nonnegative", all(value >= 0 for value in d),
                "NEGATIVE_DIAGONAL", "every d_i >= 0; zero pivots are allowed"),
    )


def check_positive_delta(delta):
    exact(delta)
    return checked("positive_delta", delta > 0, "DELTA_NOT_POSITIVE", "exact rational delta > 0")


def verify(expected, certificate):
    """Bind to an INDEPENDENT request and retain the exact candidate in the report.

    Nominal labels are synthetic reference data, not authenticated Core identities.
    Failed certificates say nothing about whether a different proof can succeed.
    """
    if type(expected) is not Subject or type(certificate) is not Certificate:
        raise Invalid("INVALID_SCHEMA", "expected Subject and Certificate")
    if expected != certificate.subject:
        changed = [f.name for f in fields(Subject)
                   if getattr(expected, f.name) != getattr(certificate.subject, f.name)]
        return Report(expected, certificate, (
            Check("binding", "fail", "SUBJECT_MISMATCH", "different " + ", ".join(changed)),
            *(Check(name, "not_checked", "BINDING_REQUIRED", "subject mismatch")
              for name in MATH_CHECKS),
        ))
    return Report(expected, certificate, (
        checked("binding", True, "SUBJECT_MISMATCH", "full subject, order and coefficient equality"),
        check_polynomial_identity(expected, certificate.gram),
        *check_ldl(certificate),
        check_positive_delta(expected.delta),
    ))


# Strict data-only wire format: rationals are [numerator, positive denominator].
def record(value, keys):
    if type(value) is not dict or set(value) != set(keys):
        raise Invalid("INVALID_SCHEMA", f"expected exactly these fields: {', '.join(keys)}")
    return value


def sequence(value):
    if type(value) is not list:
        raise Invalid("INVALID_SCHEMA", "expected a JSON list")
    return value


def rational_from_data(value):
    if (type(value) is not list or len(value) != 2
            or any(type(x) is not int for x in value) or value[1] <= 0):
        raise Invalid("INVALID_SCHEMA", "rational must be [integer, positive integer]")
    return Fraction(*value)


def rational_data(value):
    return [value.numerator, value.denominator]


def poly_from_data(value, arity):
    terms, seen = [], set()
    for term in sequence(value):
        record(term, ("powers", "coefficient"))
        powers = tuple(sequence(term["powers"]))
        exponents(powers, arity)
        if powers in seen:
            raise Invalid("INVALID_SCHEMA", "duplicate monomial")
        seen.add(powers)
        terms.append((powers, rational_from_data(term["coefficient"])))
    return Poly.from_terms(terms, arity)


def poly_data(poly):
    return [{"powers": list(p), "coefficient": rational_data(c)} for p, c in poly.terms]


def matrix_from_data(value):
    return tuple(tuple(rational_from_data(x) for x in sequence(row)) for row in sequence(value))


def matrix_data(value):
    return [[rational_data(x) for x in row] for row in value]


def subject_from_data(value):
    record(value, ("context", "domain", "generators", "monomials", "delta"))
    raw = record(value["context"], tuple(f.name for f in fields(Context)))
    context = Context(**(raw | {"variables": tuple(sequence(raw["variables"]))}))
    domain = Domain(**record(value["domain"], tuple(f.name for f in fields(Domain))))
    arity = len(context.variables)
    generators = []
    for generator in sequence(value["generators"]):
        record(generator, ("function_id", "revision", "polynomial"))
        generators.append(Generator(generator["function_id"], generator["revision"],
                                    poly_from_data(generator["polynomial"], arity)))
    return Subject(context, domain, tuple(generators),
                   tuple(tuple(sequence(p)) for p in sequence(value["monomials"])),
                   rational_from_data(value["delta"]))


def subject_data(subject):
    context = asdict(subject.context)
    context["variables"] = list(subject.context.variables)
    return {"context": context, "domain": asdict(subject.domain),
            "generators": [{"function_id": g.function_id, "revision": g.revision,
                            "polynomial": poly_data(g.polynomial)} for g in subject.generators],
            "monomials": [list(p) for p in subject.monomials], "delta": rational_data(subject.delta)}


def certificate_from_data(value):
    record(value, ("subject", "gram", "permutation", "lower", "diagonal", "convention"))
    return Certificate(subject_from_data(value["subject"]), matrix_from_data(value["gram"]),
                       tuple(sequence(value["permutation"])), matrix_from_data(value["lower"]),
                       tuple(rational_from_data(d) for d in sequence(value["diagonal"])),
                       value["convention"])


def certificate_data(certificate):
    return {"subject": subject_data(certificate.subject), "gram": matrix_data(certificate.gram),
            "permutation": list(certificate.permutation), "lower": matrix_data(certificate.lower),
            "diagonal": [rational_data(d) for d in certificate.diagonal],
            "convention": certificate.convention}


def report_data(report):
    return {"status": "accepted_reference" if report.accepted else "rejected_reference",
            "scope": "real cozero cover sufficient condition; Python reference only",
            "subject": subject_data(report.subject), "certificate": certificate_data(report.certificate),
            "checks": [asdict(c) for c in report.checks]}


def load_json(path):
    def unique_record(pairs):
        result = {}
        for key, value in pairs:
            if key in result:
                raise Invalid("INVALID_SCHEMA", f"duplicate JSON key: {key}")
            result[key] = value
        return result

    def reject_inexact(value):
        raise Invalid("INVALID_SCHEMA", f"not an exact JSON number: {value}")

    return json.loads(Path(path).read_text(encoding="utf-8"), object_pairs_hook=unique_record,
                      parse_constant=reject_inexact, parse_float=reject_inexact)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("request", help="independently supplied expected subject JSON")
    parser.add_argument("certificate", help="untrusted certificate JSON")
    args = parser.parse_args()
    try:
        expected = subject_from_data(load_json(args.request))
        certificate = certificate_from_data(load_json(args.certificate))
        report = verify(expected, certificate)
    except (Invalid, OSError, UnicodeError, ValueError, RecursionError) as error:
        print(json.dumps({"status": "invalid_input", "code": getattr(error, "code", "INPUT_ERROR"),
                          "detail": str(error)}))
        return 2
    print(json.dumps(report_data(report), indent=2))
    return 0 if report.accepted else 1


if __name__ == "__main__":
    raise SystemExit(main())
