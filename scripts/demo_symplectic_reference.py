"""Issue #211 examples; these are synthetic reference inputs, not Vastitas IR."""

import argparse
import json
from dataclasses import replace
from pathlib import Path

import symplectic_reference as sr


def examples():
    context = sr.Context(
        "reference:snapshot:1", "reference:R4:A", "reference:real-base:A",
        "reference:global-chart:A", "reference:coordinate-frame:A",
        "reference:dual-coordinate-frame:A", "reference:polynomial-model:A",
        "revision:1", sr.SCALAR_PROFILE, sr.COORDINATES,
    )
    q1, _, _, p2 = (sr.Poly.variable(i) for i in range(sr.DIM))
    h = sr.ONE + q1
    good = sr.matrix([
        [0, 1, -p2, 0], [-1, 0, 0, 0], [p2, 0, 0, h], [0, 0, -h, 0],
    ])
    bad = sr.matrix([
        [0, 1, 0, 0], [-1, 0, 0, 0], [0, 0, 0, h], [0, 0, -h, 0],
    ])
    good_inverse = sr.InverseWitness(sr.matrix([
        [0, -h, 0, 0], [h, 0, 0, -p2], [0, 0, 0, -1], [0, p2, 1, 0],
    ]), 1)
    bad_inverse = sr.InverseWitness(sr.matrix([
        [0, -h, 0, 0], [h, 0, 0, 0], [0, 0, 0, -1], [0, 0, 1, 0],
    ]), 1)
    subject = sr.Subject(context, sr.Domain("principal_open", h), "omega:good", "1", good)
    certificate = sr.Certificate(subject, (sr.ZERO,) * 4, good_inverse)
    bad_subject = replace(subject, form_id="omega:bad", omega=bad)
    # Honest derivative: d(omega_bad) has coefficient +1 at (0,2,3).
    bad_certificate = sr.Certificate(bad_subject, (sr.ZERO, sr.ZERO, sr.ONE, sr.ZERO),
                                     bad_inverse)
    global_subject = replace(subject, domain=sr.Domain("all"))
    return {
        "good_U": (subject, certificate),
        "bad_U": (bad_subject, bad_certificate),
        "bad_forged_closedness": (bad_subject, replace(bad_certificate,
                                                       claimed_derivative=(sr.ZERO,) * 4)),
        "global_stale_evidence": (global_subject, certificate),
        "global_relabelled_evidence": (global_subject, replace(certificate,
                                                              subject=global_subject)),
        "same_determinant_replay": (bad_subject, certificate),
        "same_determinant_relabelled": (bad_subject, replace(certificate,
                                                            subject=bad_subject)),
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write-dir", type=Path, help="write request/certificate pairs for the CLI")
    args = parser.parse_args()
    output = {"scope": "Python reference only; no Lean proof or compiler acceptance", "cases": {}}
    for name, (subject, certificate) in examples().items():
        report = sr.verify(subject, certificate)
        output["cases"][name] = {
            "accepted": report.accepted,
            "checks": {c.name: c.code for c in report.checks},
        }
        if args.write_dir:
            args.write_dir.mkdir(parents=True, exist_ok=True)
            for kind, data in (("request", sr.subject_data(subject)),
                               ("certificate", sr.certificate_data(certificate))):
                path = args.write_dir / f"{name}.{kind}.json"
                path.write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(output, indent=2))


if __name__ == "__main__":
    main()
