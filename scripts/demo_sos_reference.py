"""Reproducible, hand-supplied SOS candidates; no certificate search or Vastitas IR."""

import argparse
import json
from dataclasses import replace
from fractions import Fraction as Q
from pathlib import Path

import sos_reference as sr


def matrix(rows):
    if any(type(x) not in (int, Q) for row in rows for x in row):
        raise sr.Invalid("INVALID_SCHEMA", "demo matrix entries must be exact")
    return tuple(tuple(Q(x) for x in row) for row in rows)


def examples():
    context = sr.Context("reference:environment:1", "reference:real-line", "reference:R",
                         "reference:global-chart", "reference:polynomial-model", "1",
                         sr.SCALAR_PROFILE, sr.SITE, ("x",))
    x, one = sr.Poly.variable(0, 1), sr.Poly.constant(1, 1)
    subject = sr.Subject(context, sr.Domain("reference:all-real-line", "all_real", 1),
                         (sr.Generator("f1", "1", x), sr.Generator("f2", "1", one - x)),
                         ((0,), (1,)), Q(1, 2))
    certificate = sr.Certificate(subject, matrix([[Q(1, 2), -1], [-1, 2]]), (0, 1),
                                 matrix([[1, 0], [-2, 1]]), (Q(1, 2), Q(0)))
    tiny_gram = matrix([[Q(1, 2) - Q(1, 10**20), -1], [-1, 2]])
    false_subject = replace(subject, generators=(sr.Generator("f1", "1", x),
                                                 sr.Generator("f2", "1", x)), delta=Q(0))
    false_cert = sr.Certificate(false_subject, matrix([[0, 0], [0, 2]]), (0, 1),
                               matrix([[1, 0], [0, 1]]), (Q(0), Q(2)))
    positive_delta = replace(false_subject, delta=Q(1, 2))
    leading_zero = replace(subject, generators=(sr.Generator("f1", "1", one),
                                                sr.Generator("f2", "1", x)), delta=Q(1))
    foreign_domain = replace(subject, domain=replace(subject.domain, domain_id="reference:other-domain"))
    return {
        "singular_cover": (subject, certificate),
        "permuted_singular_cover": (subject, replace(certificate, permutation=(1, 0),
                                    lower=matrix([[1, 0], [Q(-1, 2), 1]]), diagonal=(Q(2), Q(0)))),
        "leading_zero_cover": (leading_zero, sr.Certificate(
            leading_zero, matrix([[0, 0], [0, 1]]), (0, 1), matrix([[1, 0], [0, 1]]), (Q(0), Q(1)))),
        "tiny_gram_tamper": (subject, replace(certificate, gram=tiny_gram)),
        "false_cover_zero_delta": (false_subject, false_cert),
        "false_cover_positive_delta": (positive_delta, replace(false_cert, subject=positive_delta)),
        "false_cover_indefinite": (positive_delta, replace(
            false_cert, subject=positive_delta, gram=matrix([[Q(-1, 2), 0], [0, 2]]),
            diagonal=(Q(-1, 2), Q(2)))),
        "foreign_domain": (foreign_domain, certificate),
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write-dir", type=Path, help="write independent request/certificate JSON pairs")
    args = parser.parse_args()
    output = {"scope": "Python reference only; no Lean proof or compiler acceptance", "cases": {}}
    for name, (subject, certificate) in examples().items():
        report = sr.verify(subject, certificate)
        output["cases"][name] = {"accepted": report.accepted,
                                  "checks": {c.name: c.code for c in report.checks}}
        if args.write_dir:
            args.write_dir.mkdir(parents=True, exist_ok=True)
            for kind, data in (("request", sr.subject_data(subject)),
                               ("certificate", sr.certificate_data(certificate))):
                (args.write_dir / f"{name}.{kind}.json").write_text(
                    json.dumps(data, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(output, indent=2))


if __name__ == "__main__":
    main()
