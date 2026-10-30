"""Exact exhaustive F5 laws, independent table oracle, and #253 boundary mutations."""

from dataclasses import replace
from fractions import Fraction as Q
from itertools import product
import json
from pathlib import Path
import subprocess
import sys
import unittest
from unittest.mock import patch

import elliptic_reference as e
from demo_elliptic_reference import (
    example, isolated_zero_torsion_mutant, report, slope_only_mutant,
)


ROOT = Path(__file__).resolve().parents[1]
FIXTURE = ROOT / "tests/fixtures/elliptic/f5-y2-x3-minus-x.json"

# Independent group-table oracle: coordinates of i*G+j*H for G=(2,1), H=(1,0).
# Derive the eight coordinates from the four chord/tangent identities documented
# in docs/elliptic-reference.md. The expected table uses integer C4 x C2 addition,
# never the implementation's affine formulas, inverse, enumeration or audit.
COORDINATES = (None, (0, 0), (1, 0), (2, 1), (2, 4), (3, 2), (3, 3), (4, 0))
GROUP_INDICES = ((0, 0), (2, 0), (0, 1), (1, 0), (3, 0), (3, 1), (1, 1), (2, 1))


class EllipticTests(unittest.TestCase):
    def setUp(self):
        self.model = example()
        self.qmodel = example("QQ")
        self.p = e.point(self.model, 0, 0)
        self.g = e.point(self.model, 2, 1)
        self.o = e.zero(self.model)

    def reject(self, code, action):
        with self.assertRaises(e.Invalid) as raised:
            action()
        self.assertEqual(raised.exception.code, code)

    def test_exact_fields_keep_zero_inverse_total(self):
        field = self.model.field
        self.assertEqual(tuple(field.inv0(i) for i in range(5)), (0, 1, 3, 2, 4))
        for i in range(1, 5):
            self.assertEqual(field.scalar(i * field.inv0(i)), 1)
        self.assertEqual(field.inv0(5), 0)
        qfield = self.qmodel.field
        self.assertEqual(qfield.inv0(Q(0)), Q(0))
        self.assertIs(type(qfield.inv0(0)), Q)
        self.assertEqual(qfield.inv0(Q(-2, 3)), Q(-3, 2))
        for model in (self.model, self.qmodel):
            self.reject("ZERO_SLOPE_DENOMINATOR", lambda: e.slope_inverse(model.field, 0))
            self.assertEqual(model.field.inv0(0), 0)
        self.reject("ZERO_SLOPE_DENOMINATOR", lambda: e.slope_inverse(field, 5))

    def test_only_requested_fields_and_exact_inputs_are_admitted(self):
        for name in ("F2", "F3", "F7", "ZZ", "RR", "general-ring", 5):
            self.reject("UNSUPPORTED_FIELD", lambda: e.Field(name, "test"))
        for value in (0.0, True, "0", None):
            for model in (self.model, self.qmodel):
                self.reject("INEXACT_SCALAR", lambda: e.point(model, value, 0))
        self.reject("INEXACT_SCALAR", lambda: e.point(self.model, Q(0), 0))
        self.assertEqual(e.point(self.model, 5, -5), self.p)
        self.reject("NONCANONICAL_SCALAR", lambda: e.check_point(
            self.model, e.Point(self.model, (5, 0))))
        self.reject("NONCANONICAL_SCALAR", lambda: e.check_point(
            self.qmodel, e.Point(self.qmodel, (0, 0))))
        self.reject("UNSUPPORTED_ENUMERATION", lambda: e.f5_points(self.qmodel))

    def test_model_discriminants_and_subject_bound_evidence(self):
        for model, delta in ((self.model, 4), (self.qmodel, Q(64))):
            evidence = e.certify_model(model)
            self.assertEqual(evidence.discriminant, delta)
            self.assertEqual(e.check_model_evidence(model, evidence), evidence)
            self.reject("DISCRIMINANT_MISMATCH", lambda: e.check_model_evidence(
                model, replace(evidence, discriminant=model.field.scalar(0))))
            self.reject("NONCANONICAL_SCALAR", lambda: e.check_model_evidence(
                model, replace(evidence, discriminant=False)))

    def test_all_eight_points_and_independent_projective_enumeration(self):
        points = e.f5_points(self.model)
        self.assertEqual(tuple(p.coordinates for p in points), COORDINATES)
        # Enumerate nonzero homogeneous triples; each F5 projective point has
        # four representatives. O is the unique point with Z=0, not (0,0,0).
        representatives = []
        normalized = set()
        for x, y, z in product(range(5), repeat=3):
            if (x, y, z) == (0, 0, 0) or (y*y*z - x*x*x + x*z*z) % 5:
                continue
            representatives.append((x, y, z))
            if z == 0:
                self.assertEqual(x, 0)
                self.assertNotEqual(y, 0)
                normalized.add(None)
            else:
                normalized.add((x * pow(z, -1, 5) % 5, y * pow(z, -1, 5) % 5))
        self.assertEqual(len(representatives), 32)
        self.assertEqual(normalized, set(COORDINATES))

    def test_off_curve_and_malformed_points_are_rejected(self):
        self.reject("OFF_CURVE", lambda: e.point(self.model, 0, 1))
        self.reject("OFF_CURVE", lambda: e.point(self.qmodel, Q(1, 2), Q(0)))
        for coordinates in ([0, 0], (0,), (0, 0, 0), "O"):
            self.reject("INVALID_COORDINATES", lambda: e.check_point(
                self.model, e.Point(self.model, coordinates)))
        bad = e.Point(self.model, (1, 1))
        for action in (lambda: e.add(self.model, self.o, bad),
                       lambda: e.add(self.model, bad, self.o),
                       lambda: e.neg(self.model, bad),
                       lambda: e.certify_membership(self.model, bad)):
            self.reject("OFF_CURVE", action)

    def test_all_six_branches_and_formula_conditions(self):
        h = e.point(self.model, 1, 0)
        cases = (
            (self.o, self.g, "left_identity", self.g, None, None),
            (self.g, self.o, "right_identity", self.g, None, None),
            (self.p, self.p, "double_y_zero", self.o, None, None),
            (self.g, e.neg(self.model, self.g), "inverse_pair", self.o, None, None),
            (self.g, self.g, "tangent", self.p, 2, 3),
            (self.g, h, "chord", e.point(self.model, 3, 3), 4, 1),
        )
        for left, right, branch, result, denominator, slope in cases:
            with self.subTest(branch=branch):
                actual = e.addition(self.model, left, right)
                self.assertEqual((actual.branch, actual.result, actual.denominator, actual.slope),
                                 (branch, result, denominator, slope))
                self.assertEqual(e.check_addition_evidence(self.model, left, right, actual), actual)
        self.assertEqual(e.add(self.model, self.o, self.o), self.o)

    def test_exception_branches_never_evaluate_an_inverse(self):
        for model in (self.model, self.qmodel):
            o, p = e.zero(model), e.point(model, 0, 0)
            pairs = [(o, o), (o, p), (p, o), (p, p)]
            if model.field.kind == "F5":
                g = e.point(model, 2, 1)
                pairs.append((g, e.neg(model, g)))
            with patch.object(e.Field, "inv0", side_effect=AssertionError("unexpected inverse")):
                for left, right in pairs:
                    e.add(model, left, right)

    def test_QQ_two_torsion_boundary_uses_exact_rationals(self):
        model = self.qmodel
        o = e.zero(model)
        for x in (-1, 0, 1):
            p = e.point(model, Q(x), Q(0))
            self.assertEqual(e.neg(model, p), p)
            self.assertEqual(e.add(model, p, p), o)
            self.assertEqual(e.add(model, o, p), p)
            self.assertEqual(e.add(model, p, o), p)
            self.assertEqual(e.add(model, p, e.neg(model, p)), o)
        # A nonzero chord denominator in the same small rational boundary set.
        p, h = e.point(model, 0, 0), e.point(model, 1, 0)
        proof = e.addition(model, p, h)
        self.assertEqual(proof.result, e.point(model, -1, 0))
        self.assertEqual((proof.branch, proof.denominator, proof.slope), ("chord", Q(1), Q(0)))
        self.assertIs(type(proof.denominator), Q)

    def test_full_table_matches_independent_C4_times_C2_oracle(self):
        points = e.f5_points(self.model)
        by_index = dict(zip(GROUP_INDICES, COORDINATES))
        for i, j in product(range(8), repeat=2):
            a, b = GROUP_INDICES[i], GROUP_INDICES[j]
            expected = by_index[((a[0] + b[0]) % 4, (a[1] + b[1]) % 2)]
            self.assertEqual(e.add(self.model, points[i], points[j]).coordinates, expected)

    def test_all_group_laws_are_exhaustive_not_sampled(self):
        audit = e.check_f5_group(self.model)
        self.assertTrue(audit.passed)
        totals = {"closure": 64, "left_identity": 8, "right_identity": 8,
                  "left_inverse": 8, "right_inverse": 8, "commutativity": 64,
                  "associativity": 512}
        self.assertEqual({law: check.checked for law, check in audit.checks.items()}, totals)
        self.assertTrue(all(c.failures == 0 and c.witness is None for c in audit.checks.values()))
        self.assertIs(audit.model, self.model)
        for p, q in product(audit.points, repeat=2):
            claim = e.addition(self.model, p, q)
            e.check_addition_evidence(self.model, p, q, claim)
            if claim.branch in ("chord", "tangent"):
                self.assertNotEqual(claim.denominator, 0)

    def test_naive_formula_passes_membership_but_fails_inverse_at_P(self):
        for model in (self.model, self.qmodel):
            p = e.point(model, 0, 0)
            wrong = slope_only_mutant(model, p, p)
            self.assertEqual(wrong, p)
            self.assertEqual(e.check_point(model, wrong), wrong)
            e.check_membership_evidence(model, wrong, e.certify_membership(model, wrong))
            self.assertNotEqual(wrong, e.zero(model))
            self.reject("ADDITION_MISMATCH", lambda: e.check_addition_evidence(
                model, p, p, replace(e.addition(model, p, p), result=wrong)))
        # Do not falsely claim the unrestricted naive mutation preserves closure.
        h = e.point(self.model, 1, 0)
        self.reject("OFF_CURVE", lambda: e.check_point(
            self.model, slope_only_mutant(self.model, h, h)))

    def test_isolated_slope_mutation_passes_every_membership_but_fails_laws(self):
        audit = e.audit_f5_group(self.model, isolated_zero_torsion_mutant)
        self.assertEqual(audit.checks["closure"], e.LawCheck(64, 0, None))
        self.assertEqual(audit.checks["left_inverse"].failures, 1)
        self.assertEqual(audit.checks["right_inverse"].failures, 1)
        self.assertEqual(audit.checks["associativity"].checked, 512)
        self.assertGreater(audit.checks["associativity"].failures, 0)
        self.reject("GROUP_LAW_FAILURE", lambda: e.check_f5_group(
            self.model, isolated_zero_torsion_mutant))
        # Concrete associativity witness using only on-curve intermediates.
        h = e.point(self.model, 1, 0)
        op = lambda p, q: isolated_zero_torsion_mutant(self.model, p, q)
        self.assertEqual(op(op(self.p, self.p), h), e.point(self.model, 4, 0))
        self.assertEqual(op(self.p, op(self.p, h)), h)

    def test_field_curve_and_model_handles_are_not_coordinate_equality(self):
        curve = self.model.curve
        # Same labels and coefficients remain distinct nominal declarations.
        foreign_models = (
            e.Model(curve, self.model.name),
            e.Model(e.Curve(curve.field, curve.name), self.model.name),
            e.Model(e.Curve(e.Field("F5", curve.field.name), curve.name), self.model.name),
            self.qmodel,
        )
        for model in foreign_models:
            p, o = e.point(model, 0, 0), e.zero(model)
            for action in (lambda: e.add(self.model, self.p, p),
                           lambda: e.add(self.model, self.o, p),
                           lambda: e.add(self.model, p, self.o),
                           lambda: e.add(self.model, self.p, o),
                           lambda: e.neg(self.model, p)):
                self.reject("POINT_SUBJECT", action)
            self.reject("EVIDENCE_SUBJECT", lambda: e.check_model_evidence(
                self.model, e.certify_model(model)))
            self.reject("EVIDENCE_SUBJECT", lambda: e.check_membership_evidence(
                self.model, self.p, e.certify_membership(model, p)))
            self.reject("EVIDENCE_SUBJECT", lambda: e.check_addition_evidence(
                self.model, self.p, self.p, e.addition(model, p, p)))

    def test_membership_evidence_cannot_change_point_or_residual(self):
        evidence = e.certify_membership(self.model, self.p)
        self.reject("EVIDENCE_SUBJECT", lambda: e.check_membership_evidence(
            self.model, self.g, evidence))
        self.reject("MEMBERSHIP_MISMATCH", lambda: e.check_membership_evidence(
            self.model, self.p, replace(evidence, residual=1)))
        self.reject("NONCANONICAL_SCALAR", lambda: e.check_membership_evidence(
            self.model, self.p, replace(evidence, residual=False)))
        # Python considers False == 0; equality cannot replace payload auditing.
        self.reject("NONCANONICAL_SCALAR", lambda: e.check_membership_evidence(
            self.model, self.p, replace(evidence, point=e.Point(self.model, (False, 0)))))

    def test_addition_evidence_binds_inputs_result_branch_and_denominator(self):
        proof = e.addition(self.model, self.g, self.g)
        for forged in (replace(proof, result=self.g), replace(proof, branch="chord"),
                       replace(proof, denominator=0), replace(proof, denominator=None),
                       replace(proof, slope=0), replace(proof, slope=None)):
            self.reject("ADDITION_MISMATCH", lambda: e.check_addition_evidence(
                self.model, self.g, self.g, forged))
        self.reject("NONCANONICAL_SCALAR", lambda: e.check_addition_evidence(
            self.model, self.g, self.g, replace(proof, slope=True)))
        foreign = example()
        self.reject("POINT_SUBJECT", lambda: e.check_addition_evidence(
            self.model, self.g, self.g, replace(proof, result=e.point(foreign, 0, 0))))
        chord = e.addition(self.model, self.p, self.g)
        self.reject("EVIDENCE_SUBJECT", lambda: e.check_addition_evidence(
            self.model, self.g, self.p, chord))
        proof = e.addition(self.model, self.p, self.p)
        for side in ("left", "right"):
            forged = replace(proof, **{side: e.Point(self.model, (0.0, 0))})
            self.reject("NONCANONICAL_SCALAR", lambda: e.check_addition_evidence(
                self.model, self.p, self.p, forged))

    def test_group_auditor_rejects_foreign_and_off_curve_outputs(self):
        foreign = example()
        self.reject("POINT_SUBJECT", lambda: e.audit_f5_group(
            self.model, lambda model, p, q: e.zero(foreign)))
        self.reject("OFF_CURVE", lambda: e.audit_f5_group(
            self.model, lambda model, p, q: e.Point(model, (0, 1))))
        self.reject("OFF_CURVE", lambda: e.audit_f5_group(self.model, slope_only_mutant))

    def test_checked_in_report_and_cli_preserve_full_table_and_failures(self):
        expected = json.loads(FIXTURE.read_text())
        self.assertEqual(json.loads(json.dumps(report())), expected)
        process = subprocess.run([sys.executable, "scripts/demo_elliptic_reference.py", "--json"],
                                 cwd=ROOT, capture_output=True, text=True, check=True)
        self.assertEqual(json.loads(process.stdout), expected)


if __name__ == "__main__":
    unittest.main()
