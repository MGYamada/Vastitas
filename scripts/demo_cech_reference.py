"""Reproduce #265's finite Cech example and independent rejection reasons."""

import json
from dataclasses import asdict, replace

import cech_reference as ref


def examples():
    subject = ref.six_point_subject()
    good = ref.propose(subject)
    data = good.cover_data
    fake = replace(good, cover_data=replace(
        data,
        overlaps=data.overlaps[:-1] + (ref.Overlap((0, 1, 2), frozenset({"e01"})),),
        bases=data.bases[:-1] + ((ref.Slot((0, 1, 2), frozenset({"e01"})),),)),
        complex=replace(good.complex, ranks=(3, 3, 1), differentials=(ref.D0, ref.Q)))
    bad_sign = replace(good, complex=replace(good.complex, differentials=(
        ref.matrix(((-1, -1, 0), (-1, 0, 1), (0, -1, 1))), ref.zero(0, 3))))
    cases = {"correct": (subject, good), "fake_triple": (subject, fake),
             "wrong_sign_with_zero_square": (subject, bad_sign)}
    for field in ("cover_id", "coefficient_id", "site_id"):
        changed = replace(subject, context=replace(subject.context, **{field: "another:" + field}))
        cases["stale_" + field] = (changed, good)
    return cases


def main():
    cases = examples()
    good = cases["correct"][1]
    fake = cases["fake_triple"][1]
    output = {
        "status": "tested Python reference; no Lean proof or accepted-Core attachment",
        "open_count": len(good.subject.opens),
        "abel_input": asdict(good.complex),
        "cover_provenance": asdict(good.cover_data),
        "cases": {name: {"accepted_reference": (report := ref.verify(s, c)).accepted,
                         "checks": [asdict(check) for check in report.checks]}
                  for name, (s, c) in cases.items()},
        "integer_witnesses": {"correct": ref.triangle_integral_witness(good.complex),
                              "fake_complex_algebra_only": ref.triangle_integral_witness(fake.complex)},
        "additional_obligations": ["overlap acyclicity for these coefficients",
                                   "comparison map and theorem under explicit hypotheses",
                                   "Lean checker soundness and actual returned-Core bridge"],
    }
    print(json.dumps(output, indent=2, default=lambda value: sorted(value)))


if __name__ == "__main__":
    main()
