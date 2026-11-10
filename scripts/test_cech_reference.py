"""Finite geometry, provenance and integral-lattice regressions for #265."""

import json
import subprocess
import sys
import unittest
from dataclasses import fields, replace
from itertools import permutations, product
from pathlib import Path
from unittest.mock import patch

import cech_reference as ref
from demo_cech_reference import examples


class CechTests(unittest.TestCase):
    def setUp(self):
        self.subject = ref.six_point_subject()
        self.good = ref.propose(self.subject)

    def check(self, candidate=None, subject=None):
        report = ref.verify(subject or self.subject, candidate or self.good)
        return report, {c.name: c for c in report.checks}

    def small_subject(self, points, opens, cover):
        return replace(self.subject, points=points, opens=tuple(map(frozenset, opens)),
                       cover=tuple(map(frozenset, cover)),
                       cover_labels=tuple(f"U{i}" for i in range(len(cover))))

    def test_six_point_space_and_actual_intersections(self):
        self.assertEqual(len(self.subject.opens), 18)
        self.assertTrue(ref.is_topology(self.subject))
        self.assertTrue(ref.is_cover(self.subject))
        overlaps = {o.indices: o.points for o in self.good.cover_data.overlaps}
        self.assertEqual(overlaps[(0, 1)], frozenset({"e01"}))
        self.assertEqual(overlaps[(0, 2)], frozenset({"e02"}))
        self.assertEqual(overlaps[(1, 2)], frozenset({"e12"}))
        self.assertEqual(overlaps[(0, 1, 2)], frozenset())
        self.assertEqual(self.good.complex.ranks, (3, 3, 0))
        self.assertEqual(self.good.complex.differentials, (ref.D0, ref.zero(0, 3)))
        report, checks = self.check()
        self.assertTrue(report.accepted)
        self.assertIs(report.returned, self.good)
        self.assertTrue(all(c.status == "pass" for c in checks.values()))

    def test_fake_triple_is_algebraically_valid_but_geometrically_rejected(self):
        fake = examples()["fake_triple"][1]
        report, checks = self.check(fake)
        self.assertFalse(report.accepted)
        self.assertIsNone(report.returned)
        self.assertEqual(checks["overlaps"].code, "INTERSECTION_MISMATCH")
        self.assertEqual(checks["sections"].code, "SECTION_BASIS_MISMATCH")
        self.assertEqual(checks["d_squared"].status, "pass")
        self.assertEqual(checks["endpoints"].status, "pass")
        witness = ref.triangle_integral_witness(fake.complex)
        self.assertEqual(witness["H1"], "0")
        self.assertEqual(witness["H1_quotient"], "ker(q)/im(D) = 0")

    def test_fake_intersection_table_rejected_even_with_correct_complex(self):
        fake = examples()["fake_triple"][1]
        candidate = replace(self.good, cover_data=replace(
            self.good.cover_data, overlaps=fake.cover_data.overlaps))
        report, checks = self.check(candidate)
        self.assertFalse(report.accepted)
        self.assertEqual(checks["overlaps"].status, "fail")
        self.assertEqual(checks["orientation"].status, "pass")

    def test_missing_duplicate_and_reversed_overlap_entries(self):
        overlaps = self.good.cover_data.overlaps
        for changed in (overlaps[:-1], overlaps + overlaps[:1], tuple(reversed(overlaps))):
            with self.subTest(changed=changed):
                candidate = replace(self.good, cover_data=replace(self.good.cover_data, overlaps=changed))
                report, checks = self.check(candidate)
                self.assertFalse(report.accepted)
                self.assertEqual(checks["overlaps"].status, "fail")

    def test_noncover_open_family_is_not_accepted(self):
        subject = replace(self.subject, cover=self.subject.cover[:2], cover_labels=("U0", "U1"))
        report, checks = self.check(replace(self.good, subject=subject), subject)
        self.assertFalse(report.accepted)
        self.assertEqual(checks["cover"].code, "NOT_AN_OPEN_COVER")
        self.assertEqual(checks["overlaps"].status, "not_checked")

    def test_set_cover_by_nonopens_is_not_accepted(self):
        subject = replace(self.subject, cover=(frozenset({"v0", "v1", "v2"}),
                          frozenset({"e01", "e02", "e12"})), cover_labels=("vertices", "edges"))
        report, checks = self.check(replace(self.good, subject=subject), subject)
        self.assertFalse(report.accepted)
        self.assertEqual(checks["cover"].code, "NOT_AN_OPEN_COVER")

    def test_topology_axioms_are_checked_before_reconstruction(self):
        # Empty and whole are present, but {a,b} intersection {b,c} is missing.
        subject = self.small_subject(("a", "b", "c"),
                                     ((), ("a", "b", "c"), ("a", "b"), ("b", "c")),
                                     (("a", "b", "c"),))
        for opens in (subject.opens, subject.opens[1:], subject.opens + (frozenset({"alien"}),),
                      subject.opens + subject.opens[:1]):
            changed = replace(subject, opens=opens)
            report, checks = self.check(replace(self.good, subject=changed), changed)
            self.assertFalse(report.accepted)
            self.assertEqual(checks["topology"].code, "INVALID_FINITE_TOPOLOGY")

    def test_wrong_sign_rejected_when_square_is_vacuously_zero(self):
        report, checks = self.check(examples()["wrong_sign_with_zero_square"][1])
        self.assertFalse(report.accepted)
        self.assertEqual(checks["orientation"].status, "fail")
        self.assertEqual(checks["d_squared"].status, "pass")

    def test_real_nonempty_triple_and_nonzero_square(self):
        subject = self.small_subject(("x",), ((), ("x",)), (("x",),) * 3)
        good = ref.propose(subject)
        self.assertTrue(ref.verify(subject, good).accepted)
        self.assertEqual(good.complex.differentials, (ref.D0, ref.Q))
        bad = replace(good, complex=replace(good.complex,
                      differentials=(ref.D0, ref.matrix(((1, 1, 1),)))))
        report, checks = self.check(bad, subject)
        self.assertFalse(report.accepted)
        self.assertEqual(checks["overlaps"].status, "pass")
        self.assertEqual(checks["orientation"].status, "fail")
        self.assertEqual(checks["d_squared"].code, "D_SQUARED_NONZERO")

    def test_consistent_global_sign_is_not_the_declared_orientation(self):
        negative = ref.matrix(tuple(-n for n in row) for row in ref.D0.entries)
        candidate = replace(self.good, complex=replace(self.good.complex,
                            differentials=(negative, ref.zero(0, 3))))
        report, checks = self.check(candidate)
        self.assertFalse(report.accepted)
        self.assertEqual(checks["d_squared"].status, "pass")
        self.assertEqual(checks["orientation"].status, "fail")

    def test_restriction_semantics_are_stronger_than_functor_laws(self):
        restrictions = tuple(replace(r, matrix=ref.zero(r.matrix.rows, r.matrix.cols))
                             if r.source != r.target else r
                             for r in self.good.cover_data.restrictions)
        candidate = replace(self.good, cover_data=replace(self.good.cover_data, restrictions=restrictions))
        report, checks = self.check(candidate)
        self.assertFalse(report.accepted)
        self.assertEqual(checks["restrictions"].status, "fail")
        self.assertEqual(checks["restriction_laws"].status, "pass")
        self.assertEqual(checks["d_squared"].status, "pass")

    def test_restriction_composition_on_nested_opens(self):
        subject = self.small_subject(("a", "b", "c"),
                                     ((), ("c",), ("b", "c"), ("a", "b", "c")),
                                     (("a", "b", "c"), ("b", "c"), ("c",)))
        good = ref.propose(subject)
        self.assertTrue(ref.verify(subject, good).accepted)
        restrictions = tuple(replace(r, matrix=ref.matrix(((2,),)))
                             if len(r.source) == 3 and len(r.target) == 1 else r
                             for r in good.cover_data.restrictions)
        bad = replace(good, cover_data=replace(good.cover_data, restrictions=restrictions))
        report, checks = self.check(bad, subject)
        self.assertFalse(report.accepted)
        self.assertEqual(checks["restriction_laws"].code, "RESTRICTION_LAWS_FAILED")

    def test_missing_or_wrongly_typed_restrictions_are_not_checked_as_lawful(self):
        original = self.good.cover_data.restrictions
        for restrictions in (original[:-1], original + original[:1],
                             (replace(original[0], matrix=ref.zero(2, 2)),) + original[1:]):
            candidate = replace(self.good, cover_data=replace(self.good.cover_data, restrictions=restrictions))
            report, checks = self.check(candidate)
            self.assertFalse(report.accepted)
            self.assertEqual(checks["restriction_laws"].status, "not_checked")

    def test_disconnected_opens_use_componentwise_sections(self):
        subject = self.small_subject(("a", "b"), ((), ("a",), ("b",), ("a", "b")),
                                     (("a", "b"), ("a", "b")))
        good = ref.propose(subject)
        self.assertTrue(ref.verify(subject, good).accepted)
        self.assertEqual(good.complex.ranks, (4, 2))
        self.assertEqual(good.complex.differentials,
                         (ref.matrix(((-1, 0, 1, 0), (0, -1, 0, 1))),))

    def test_empty_member_contributes_zero_sections(self):
        subject = replace(self.subject, cover=(frozenset(self.subject.points), frozenset()),
                          cover_labels=("X", "empty"))
        good = ref.propose(subject)
        self.assertTrue(ref.verify(subject, good).accepted)
        self.assertEqual(good.complex.ranks, (1, 0))
        self.assertEqual(good.complex.differentials, (ref.zero(0, 1),))

    def test_four_identical_opens_exercise_degree_two_differential(self):
        subject = self.small_subject(("x",), ((), ("x",)), (("x",),) * 4)
        good = ref.propose(subject)
        self.assertTrue(ref.verify(subject, good).accepted)
        self.assertEqual(good.complex.ranks, (4, 6, 4, 1))
        self.assertEqual(good.complex.differentials[-1], ref.matrix(((-1, 1, -1, 1),)))

    def test_all_cover_orderings_rebuild_but_do_not_borrow_evidence(self):
        for order in permutations(range(3)):
            changed = replace(self.subject, cover=tuple(self.subject.cover[i] for i in order),
                              cover_labels=tuple(self.subject.cover_labels[i] for i in order))
            self.assertTrue(ref.verify(changed, ref.propose(changed)).accepted)
            if order != (0, 1, 2):
                self.assertFalse(ref.verify(changed, self.good).accepted)

    def test_every_context_identity_is_bound(self):
        for field in fields(ref.Context):
            with self.subTest(field=field.name):
                subject = replace(self.subject, context=replace(
                    self.subject.context, **{field.name: "different:" + field.name}))
                report, checks = self.check(subject=subject)
                self.assertFalse(report.accepted)
                self.assertEqual(checks["binding"].code, "SUBJECT_MISMATCH")

    def test_changed_cover_contents_with_same_ids_are_bound(self):
        subject = replace(self.subject, cover=(frozenset(self.subject.points),) * 3)
        report, checks = self.check(subject=subject)
        self.assertFalse(report.accepted)
        self.assertEqual(checks["binding"].code, "SUBJECT_MISMATCH")
        # Retagging a stale candidate is insufficient: reconstruction still runs.
        report, checks = self.check(replace(self.good, subject=subject), subject)
        self.assertFalse(report.accepted)
        self.assertEqual(checks["binding"].status, "pass")
        self.assertEqual(checks["overlaps"].status, "fail")

    def test_same_points_different_topology_is_bound(self):
        discrete = tuple(frozenset(x for i, x in enumerate(self.subject.points) if mask & (1 << i))
                         for mask in range(64))
        subject = replace(self.subject, opens=discrete)
        self.assertFalse(ref.verify(subject, self.good).accepted)
        report, checks = self.check(replace(self.good, subject=subject), subject)
        self.assertFalse(report.accepted)
        self.assertEqual(checks["sections"].status, "fail")

    def test_unimplemented_site_or_coefficient_profile_is_unsupported(self):
        for key, value in (("site_profile", "etale"), ("coefficient_profile", "Q")):
            subject = replace(self.subject, context=replace(self.subject.context, **{key: value}))
            report, checks = self.check(replace(self.good, subject=subject), subject)
            self.assertFalse(report.accepted)
            self.assertEqual(checks["profile"].status, "unsupported")

    def test_complex_coefficient_identity_and_endpoints_are_checked(self):
        wrong_coefficient = replace(self.good.complex, coefficient_id="other-Z")
        self.assertFalse(self.check(replace(self.good, complex=wrong_coefficient))[0].accepted)
        for data in (replace(self.good.complex, ranks=(3, 3, 1)),
                     replace(self.good.complex, differentials=()),
                     replace(self.good.complex, differentials=(ref.D0, ref.zero(3, 0)))):
            report, checks = self.check(replace(self.good, complex=data))
            self.assertFalse(report.accepted)
            self.assertEqual(checks["endpoints"].status, "fail")
            self.assertEqual(checks["d_squared"].status, "not_checked")

    def test_integral_unimodular_witness_and_splitting(self):
        witness = ref.triangle_integral_witness(self.good.complex)
        self.assertEqual(witness["smith_diagonal"], (1, 1, 0))
        self.assertEqual(witness["H0"], "Z")
        self.assertEqual(witness["H1"], "Z")
        # Independent concrete evaluations of the all-integer splitting formula.
        for a, b, c in product(range(-3, 4), repeat=3):
            y = ref.matrix(((a,), (b,), (c,)))
            image = ref.multiply(ref.D0, ref.matrix(((0,), (a,), (b,))))
            q = a - b + c
            self.assertEqual(tuple(r[0] for r in image.entries), (a, b, b - a))
            self.assertEqual((a, b, image.entries[2][0] + q), (a, b, c))
            self.assertEqual(ref.multiply(ref.Q, y).entries, ((q,),))

    def test_same_rational_rank_cannot_reuse_integer_witness(self):
        doubled = ref.matrix(tuple(2 * x for x in row) for row in ref.D0.entries)
        data = replace(self.good.complex, differentials=(doubled, ref.zero(0, 3)))
        self.assertTrue(ref.d_squared(data))
        # b1=(1,0,-1) is in im(D0), but not im(2D0): its first entry is odd.
        witness = ref.triangle_integral_witness(self.good.complex)
        self.assertEqual(ref.multiply(ref.multiply(ref.matrix(witness["U"]), doubled),
                                      ref.matrix(witness["V"])),
                         ref.matrix(((2, 0, 0), (0, 2, 0), (0, 0, 0))))
        with self.assertRaises(ref.Invalid):
            ref.triangle_integral_witness(data)
        self.assertFalse(self.check(replace(self.good, complex=data))[0].accepted)

    def test_no_candidate_producer_or_integer_result_is_trusted_by_verify(self):
        with patch.object(ref, "propose", side_effect=AssertionError("trusted producer")), \
             patch.object(ref, "triangle_integral_witness", side_effect=AssertionError("trusted H1")):
            self.assertTrue(ref.verify(self.subject, self.good).accepted)

    def test_single_open_cover_does_not_compute_derived_cohomology(self):
        subject = replace(self.subject, cover=(frozenset(self.subject.points),), cover_labels=("X",))
        good = ref.propose(subject)
        self.assertTrue(ref.verify(subject, good).accepted)
        self.assertEqual(good.complex.ranks, (1,))
        # This cover's positive-degree Cech terms are zero; no comparison follows.
        self.assertEqual(good.complex.differentials, ())
        with self.assertRaises(ref.Invalid):
            ref.triangle_integral_witness(good.complex)

    def test_inexact_mutable_and_malformed_data_rejected(self):
        for x in (True, 1.0, "1"):
            with self.assertRaises(ref.Invalid):
                ref.matrix(((x,),))
        for bad in (((1,), (1, 2)),):
            with self.assertRaises(ref.Invalid):
                ref.matrix(bad)
        with self.assertRaises(ref.Invalid):
            replace(self.subject, opens=list(self.subject.opens))
        with self.assertRaises(ref.Invalid):
            ref.Overlap((True,), frozenset())
        with self.assertRaises(ref.Invalid):
            ref.zero(True, 1)

    def test_demo_is_reproducible_json(self):
        result = subprocess.run([sys.executable, str(Path(__file__).with_name("demo_cech_reference.py"))],
                                check=True, text=True, capture_output=True)
        data = json.loads(result.stdout)
        self.assertEqual(data["open_count"], 18)
        self.assertTrue(data["cases"]["correct"]["accepted_reference"])
        self.assertTrue(all(not case["accepted_reference"] for name, case in data["cases"].items()
                            if name != "correct"))


if __name__ == "__main__":
    unittest.main()
