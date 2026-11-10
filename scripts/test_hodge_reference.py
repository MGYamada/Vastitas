"""Independent sign tables, wedge checks, exact actions and rejected premises."""

import itertools
import json
import subprocess
import sys
import unittest
from dataclasses import fields, replace
from fractions import Fraction as Q
from pathlib import Path

import hodge_reference as h
from demo_hodge_reference import diagonal, example


class HodgeTests(unittest.TestCase):
    def setUp(self):
        self.g, self.e, self.o = example(3)
        self.m, self.me, self.mo = example(4)
        self.xy = h.basis_form(self.g.frame, (0, 1))

    def reject(self, code, action):
        with self.assertRaises(h.Invalid) as raised:
            action()
        self.assertEqual(raised.exception.code, code)

    def test_euclidean_full_basis_table_and_orientation(self):
        table = {(): ((0, 1, 2), 1), (0,): ((1, 2), 1), (1,): ((0, 2), -1),
                 (2,): ((0, 1), 1), (0, 1): ((2,), 1), (0, 2): ((1,), -1),
                 (1, 2): ((0,), 1), (0, 1, 2): ((), 1)}
        for blade, (complement, sign) in table.items():
            a = h.basis_form(self.g.frame, blade)
            expected = h.scale(h.basis_form(self.g.frame, complement), sign)
            self.assertEqual(h.star(self.g, a, self.e, self.o), expected)
            self.assertEqual(h.star(self.g, a, self.e, replace(self.o, sign=-1)), h.scale(expected, -1))
            self.assertEqual(h.verify_star(self.g, a, self.e, expected, orientation=self.o), expected)

    def test_lorentz_six_two_form_signs_independent_table(self):
        # t,x,y,z; signature (-,+,+,+); not computed using implementation helpers.
        table = {(0, 1): ((2, 3), -1), (0, 2): ((1, 3), 1), (0, 3): ((1, 2), -1),
                 (1, 2): ((0, 3), 1), (1, 3): ((0, 2), -1), (2, 3): ((0, 1), 1)}
        for blade, (complement, sign) in table.items():
            a = h.basis_form(self.m.frame, blade)
            expected = h.scale(h.basis_form(self.m.frame, complement), sign)
            self.assertEqual(h.star(self.m, a, self.me, self.mo), expected)
            h.verify_star(self.m, a, self.me, expected, orientation=self.mo)

    def test_all_degrees_square_law_and_sign_line_square(self):
        for metric, evidence, orientation, q in ((*example(3), 0), (*example(4), 1)):
            n = metric.frame.dimension
            for k in range(n + 1):
                for blade in h.indices(metric.frame, k):
                    a = h.basis_form(metric.frame, blade)
                    expected = h.scale(a, (-1) ** (k * (n - k) + q))
                    for sign in (-1, 1):
                        o = replace(orientation, sign=sign)
                        self.assertEqual(h.star(metric, h.star(metric, a, evidence, o), evidence, o), expected)
                    twisted = h.star_twisted(metric, a, evidence)
                    self.assertEqual(twisted.line, h.OrientationLine(metric.frame))
                    h.verify_star(metric, a, evidence, twisted, orientation=None)
                    self.assertEqual(h.star_twisted(metric, twisted, evidence), expected)
                    h.verify_star(metric, twisted, evidence, expected, orientation=None)

    def test_reject_euclidean_lorentz_substitution_and_global_sign_mutation(self):
        # Euclidean square is +1 for k=2,n=4. Applying those signs to Minkowski
        # fails the defining identity, even though dimensions and types agree.
        for blade, comp, euclidean_sign in (((0, 1), (2, 3), 1), ((0, 2), (1, 3), -1), ((0, 3), (1, 2), 1)):
            a = h.basis_form(self.m.frame, blade)
            bad = h.scale(h.basis_form(self.m.frame, comp), euclidean_sign)
            self.reject("HODGE_IDENTITY_FAILED", lambda: h.verify_star(self.m, a, self.me, bad, orientation=self.mo))
        a = h.basis_form(self.m.frame, (2, 3))
        self.assertNotEqual(h.star(self.m, h.star(self.m, a, self.me, self.mo), self.me, self.mo), a)
        # Negating the entire operator preserves its square; the definition must
        # still reject it. A square-only checker would miss this mutation.
        bad = h.scale(h.star(self.m, a, self.me, self.mo), -1)
        self.reject("HODGE_IDENTITY_FAILED", lambda: h.verify_star(self.m, a, self.me, bad, orientation=self.mo))

    def test_plus_minus_minus_minus_profile_is_separately_certified(self):
        entries = (1, -1, -1, -1)
        g = replace(self.m, metric_id="mostly-minus", gram=diagonal(entries))
        e = h.HodgeEvidence(h.NondegenerateEvidence(g, g.gram),
                            h.SignatureEvidence(g, diagonal((1, 1, 1, 1)), entries, 3), h.VolumeEvidence(g, Q(1)))
        for k in range(5):
            for blade in h.indices(g.frame, k):
                a = h.basis_form(g.frame, blade)
                self.assertEqual(h.star(g, h.star(g, a, e, self.mo), e, self.mo), h.scale(a, (-1) ** (k * (4 - k) + 3)))
        self.reject("SIGNATURE_MISMATCH", lambda: h.check_hodge(g, replace(e, signature=replace(e.signature, negative_count=1))))

    def test_dense_rational_forms_zero_and_linearity(self):
        for g, e, o in (example(3), example(4)):
            for k in range(g.frame.dimension + 1):
                a = h.Form(g.frame, k, tuple(Q(i - 3, i + 2) for i, _ in enumerate(h.indices(g.frame, k))), None)
                result = h.star(g, a, e, o)
                h.verify_star(g, a, e, result, orientation=o)
                self.assertEqual(h.star(g, h.scale(a, Q(-3, 7)), e, o), h.scale(result, Q(-3, 7)))
                self.assertEqual(h.star(g, h.scale(a, 0), e, o), h.scale(result, 0))
                bad = replace(result, components=tuple(x + int(i == 0) for i, x in enumerate(result.components)))
                self.reject("HODGE_IDENTITY_FAILED", lambda: h.verify_star(g, a, e, bad, orientation=o))

    def test_cross_is_flat_wedge_star_sharp_with_axial_type(self):
        f = self.g.frame
        ex, ey, ez = (h.PolarVector(f, row) for row in diagonal((1, 1, 1)))
        self.assertEqual(h.cross_twisted(self.g, ex, ey, self.e), h.AxialVector(f, (0, 0, 1)))
        self.assertEqual(h.cross_twisted(self.g, ey, ex, self.e), h.AxialVector(f, (0, 0, -1)))
        self.assertEqual(h.cross_twisted(self.g, ex, ex, self.e), h.AxialVector(f, (0, 0, 0)))
        for a, b, expected in ((ey, ez, (1, 0, 0)), (ez, ex, (0, 1, 0))):
            self.assertEqual(h.cross_twisted(self.g, a, b, self.e).components, expected)
        a, b = h.PolarVector(f, (Q(1, 2), -2, 3)), h.PolarVector(f, (4, Q(2, 3), -1))
        cross = h.cross_twisted(self.g, a, b, self.e)
        self.assertEqual(cross.components, (0, Q(25, 2), Q(25, 3)))
        self.assertEqual(cross, h.sharp(self.g, h.star_twisted(self.g, h.wedge(h.flat(self.g, a), h.flat(self.g, b)), self.e), self.e.nondegenerate))

    def test_orientation_reversal_preserves_twisted_object(self):
        twisted = h.star_twisted(self.g, self.xy, self.e)
        positive = h.display_twisted(twisted, self.o)
        negative = h.display_twisted(twisted, replace(self.o, sign=-1))
        self.assertEqual(negative, tuple(-x for x in positive))
        self.assertEqual(h.star_twisted(self.g, self.xy, self.e), twisted)
        self.assertEqual(twisted.line, h.OrientationLine(self.g.frame))
        self.reject("MISSING_ORIENTATION", lambda: h.display_twisted(twisted, None))
        self.reject("TWIST_MISMATCH", lambda: h.star(self.g, twisted, self.e, self.o))
        axial = h.AxialVector(self.g.frame, (0, 0, 1))
        self.assertIs(type(h.display_twisted(axial, self.o)), tuple)
        self.reject("POLAR_REQUIRED", lambda: h.cross_twisted(self.g, axial, h.PolarVector(self.g.frame, (1, 0, 0)), self.e))

    def test_all_48_signed_permutations_preserve_twisted_equivariance(self):
        f = self.g.frame
        a, b = h.PolarVector(f, (Q(1, 2), 2, -3)), h.PolarVector(f, (2, -1, Q(3, 5)))
        axial = h.cross_twisted(self.g, a, b, self.e)
        for permutation in itertools.permutations(range(3)):
            parity = (-1) ** sum(permutation[i] > permutation[j] for i in range(3) for j in range(i + 1, 3))
            for signs in itertools.product((-1, 1), repeat=3):
                matrix = tuple(tuple(signs[i] if j == permutation[i] else 0 for j in range(3)) for i in range(3))
                action = h.FrameAutomorphism(f, matrix, tuple(zip(*matrix)))
                h.check_isometry(self.g, action)
                expected = tuple(parity * signs[0] * signs[1] * signs[2] * signs[i] * axial.components[permutation[i]] for i in range(3))
                self.assertEqual(action.act(axial).components, expected)
                self.assertEqual(h.cross_twisted(self.g, action.act(a), action.act(b), self.e), action.act(axial))
                for k in range(4):
                    form = h.Form(f, k, tuple(Q(i + 1, 3) for i, _ in enumerate(h.indices(f, k))), None)
                    self.assertEqual(h.star_twisted(self.g, action.act(form), self.e), action.act(h.star_twisted(self.g, form, self.e)))

    def test_reflection_rejects_polar_transformation_of_axial_result(self):
        action = h.FrameAutomorphism(self.g.frame, diagonal((-1, 1, 1)), diagonal((-1, 1, 1)))
        axial = h.AxialVector(self.g.frame, (0, 0, 1))
        self.assertEqual(action.act(axial).components, (0, 0, -1))
        self.assertEqual(action.act(h.PolarVector(self.g.frame, (0, 0, 1))).components, (0, 0, 1))
        transformed = action.act(self.xy)
        wrong = action.act(h.star(self.g, self.xy, self.e, self.o))
        self.reject("HODGE_IDENTITY_FAILED", lambda: h.verify_star(self.g, transformed, self.e, wrong, orientation=self.o))

    def test_rational_rotation_and_lorentz_boost_naturality(self):
        rotation = ((Q(3, 5), Q(-4, 5), 0), (Q(4, 5), Q(3, 5), 0), (0, 0, 1))
        boost = ((Q(5, 4), Q(-3, 4), 0, 0), (Q(-3, 4), Q(5, 4), 0, 0), (0, 0, 1, 0), (0, 0, 0, 1))
        inverse_boost = ((Q(5, 4), Q(3, 4), 0, 0), (Q(3, 4), Q(5, 4), 0, 0), (0, 0, 1, 0), (0, 0, 0, 1))
        for g, e, matrix, inverse in ((self.g, self.e, rotation, tuple(zip(*rotation))), (self.m, self.me, boost, inverse_boost)):
            action = h.FrameAutomorphism(g.frame, matrix, inverse)
            h.check_isometry(g, action)
            for k in range(g.frame.dimension + 1):
                for blade in h.indices(g.frame, k):
                    a = h.basis_form(g.frame, blade)
                    self.assertEqual(h.star_twisted(g, action.act(a), e), action.act(h.star_twisted(g, a, e)))
        euclidean_rotation = ((0, -1, 0, 0), (1, 0, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1))
        action = h.FrameAutomorphism(self.m.frame, euclidean_rotation, tuple(zip(*euclidean_rotation)))
        self.reject("NOT_ISOMETRIC", lambda: h.check_isometry(self.m, action))

    def test_nonorthonormal_rational_volume_and_musical_maps(self):
        g = replace(self.g, metric_id="scaled", gram=diagonal((4, 1, 1)))
        e = h.HodgeEvidence(h.NondegenerateEvidence(g, diagonal((Q(1, 4), 1, 1))),
                            h.SignatureEvidence(g, diagonal((1, 1, 1)), (4, 1, 1), 0), h.VolumeEvidence(g, Q(2)))
        self.assertEqual(h.star(g, self.xy, e, self.o).components, (0, 0, Q(1, 2)))
        ex, ey = h.PolarVector(g.frame, (1, 0, 0)), h.PolarVector(g.frame, (0, 1, 0))
        self.assertEqual(h.cross_twisted(g, ex, ey, e).components, (0, 0, 2))
        for vector in (ex, h.AxialVector(g.frame, (Q(2, 3), 4, -5))):
            self.assertEqual(h.sharp(g, h.flat(g, vector), e.nondegenerate), vector)
        for k in range(4):
            for blade in h.indices(g.frame, k):
                a = h.basis_form(g.frame, blade)
                result = h.star(g, a, e, self.o)
                h.verify_star(g, a, e, result, orientation=self.o)
                self.assertEqual(h.star(g, result, e, self.o), a)
        # Omitting metric volume and merely keeping the sign line is wrong.
        wrong = h.scale(h.star(g, self.xy, e, self.o), Q(1, 2))
        self.reject("HODGE_IDENTITY_FAILED", lambda: h.verify_star(g, self.xy, e, wrong, orientation=self.o))

    def test_off_diagonal_metrics_and_zero_diagonal_lorentz(self):
        shear = ((1, 1, 0), (1, 2, 0), (0, 0, 1))
        inverse = ((2, -1, 0), (-1, 1, 0), (0, 0, 1))
        g = replace(self.g, metric_id="shear", gram=shear)
        e = h.HodgeEvidence(h.NondegenerateEvidence(g, inverse),
                            h.SignatureEvidence(g, ((1, -1, 0), (0, 1, 0), (0, 0, 1)), (1, 1, 1), 0), h.VolumeEvidence(g, Q(1)))
        self.assertEqual(h.star(g, h.basis_form(g.frame, (0,)), e, self.o).components, (0, 1, 2))
        # Lorentz Gram matrix with zero first diagonal entry; signature is not
        # inferred from diagonal entries, a leading-pivot test, or det alone.
        gram = ((0, 1, 0, 0), (1, 0, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1))
        m = replace(self.m, metric_id="null-coordinates", gram=gram)
        me = h.HodgeEvidence(h.NondegenerateEvidence(m, gram), h.SignatureEvidence(m,
                             ((1, 1, 0, 0), (1, -1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1)), (2, -2, 1, 1), 1), h.VolumeEvidence(m, Q(1)))
        for metric, evidence, o in ((g, e, self.o), (m, me, self.mo)):
            for k in range(metric.frame.dimension + 1):
                for blade in h.indices(metric.frame, k):
                    a = h.basis_form(metric.frame, blade)
                    result = h.star(metric, a, evidence, o)
                    h.verify_star(metric, a, evidence, result, orientation=o)
                    expected = (-1) ** (k * (metric.frame.dimension - k) + evidence.signature.negative_count)
                    self.assertEqual(h.star(metric, result, evidence, o), h.scale(a, expected))

    def test_missing_premises_and_orientation_rejected(self):
        self.reject("MISSING_METRIC", lambda: h.star(None, self.xy, self.e, self.o))
        self.reject("MISSING_HODGE_EVIDENCE", lambda: h.star(self.g, self.xy, None, self.o))
        for field, code in (("nondegenerate", "MISSING_NONDEGENERACY"), ("signature", "MISSING_SIGNATURE"), ("volume", "MISSING_VOLUME")):
            self.reject(code, lambda: h.star(self.g, self.xy, replace(self.e, **{field: None}), self.o))
        self.reject("MISSING_ORIENTATION", lambda: h.star(self.g, self.xy, self.e, None))
        self.reject("MISSING_FRAME", lambda: replace(self.g, frame=None))
        self.reject("UNSUPPORTED_DIMENSION", lambda: replace(self.g.frame, dimension=None))
        self.reject("INVALID_BASIS", lambda: replace(self.g.frame, basis=None))
        self.reject("INVALID_SCHEMA", lambda: replace(self.g.frame, coefficient_id=None))
        self.reject("INVALID_SCHEMA", lambda: replace(self.g.frame, dual_basis_id=None))

    def test_all_nominal_frame_indices_and_evidence_subjects_bound(self):
        for f in fields(self.g.frame):
            if f.name in ("dimension", "scalar_profile"):
                continue
            value = tuple(reversed(self.g.frame.basis)) if f.name == "basis" else getattr(self.g.frame, f.name) + ":other"
            frame = replace(self.g.frame, **{f.name: value})
            metric = replace(self.g, frame=frame)
            with self.subTest(index=f.name):
                self.reject("EVIDENCE_SUBJECT_MISMATCH", lambda: h.check_hodge(metric, self.e))
                self.reject("FIBER_MISMATCH", lambda: h.star(self.g, replace(self.xy, frame=frame), self.e, self.o))
                self.reject("ORIENTATION_MISMATCH", lambda: h.star(self.g, self.xy, self.e, replace(self.o, frame=frame)))
        for metric in (replace(self.g, metric_id="same-matrix-twin"), replace(self.g, revision="2"), replace(self.g, gram=diagonal((4, 1, 1)))):
            self.reject("EVIDENCE_SUBJECT_MISMATCH", lambda: h.check_hodge(metric, self.e))
        twin = replace(self.g, metric_id="twin")
        for f in fields(self.e):
            evidence = replace(getattr(self.e, f.name), subject=twin)
            self.reject("EVIDENCE_SUBJECT_MISMATCH", lambda: h.check_hodge(self.g, replace(self.e, **{f.name: evidence})))

    def test_forged_inverse_signature_and_degenerate_metric_rejected(self):
        for gram in (diagonal((1, 0, 1)), diagonal((2, 1, 1))):
            g = replace(self.g, gram=gram)
            self.reject("INVALID_INVERSE", lambda: h.check_nondegenerate(g, h.NondegenerateEvidence(g, diagonal((1, 1, 1)))))
        for sig in (replace(self.e.signature, diagonal=(2, 1, 1)),
                    replace(self.e.signature, diagonalizer=diagonal((0, 1, 1)))):
            self.reject("INVALID_SIGNATURE_WITNESS", lambda: h.check_hodge(self.g, replace(self.e, signature=sig)))
        for q in (1, True):
            self.reject("SIGNATURE_MISMATCH", lambda: h.check_hodge(self.g, replace(self.e, signature=replace(self.e.signature, negative_count=q))))
        self.reject("NOT_SYMMETRIC", lambda: replace(self.g, gram=((1, 1, 0), (0, 1, 0), (0, 0, 1))))
        # A Euclidean 4-space cannot be smuggled into the admitted Lorentz profile.
        g = replace(self.m, gram=diagonal((1, 1, 1, 1)))
        e = h.HodgeEvidence(h.NondegenerateEvidence(g, g.gram), h.SignatureEvidence(g, g.gram, (1, 1, 1, 1), 0), h.VolumeEvidence(g, Q(1)))
        self.reject("UNSUPPORTED_SIGNATURE", lambda: h.check_hodge(g, e))

    def test_volume_magnitude_and_coefficient_extension_rejections(self):
        for magnitude in (0, -1, 2):
            self.reject("VOLUME_MISMATCH", lambda: h.check_hodge(self.g, replace(self.e, volume=replace(self.e.volume, magnitude=magnitude))))
        g = replace(self.g, gram=diagonal((2, 1, 1)))
        e = h.HodgeEvidence(h.NondegenerateEvidence(g, diagonal((Q(1, 2), 1, 1))),
                            h.SignatureEvidence(g, diagonal((1, 1, 1)), (2, 1, 1), 0), h.VolumeEvidence(g, Q(1)))
        for magnitude in (Q(1), Q(7, 5), Q(99, 70)):
            self.reject("COEFFICIENT_EXTENSION_REQUIRED", lambda: h.star_twisted(g, self.xy, replace(e, volume=replace(e.volume, magnitude=magnitude))))

    def test_wrong_result_type_degree_fiber_and_twist_rejected(self):
        good = h.star(self.g, self.xy, self.e, self.o)
        bads = (None, self.xy, replace(good, frame=replace(good.frame, coefficient_id="QQ-twin")),
                replace(good, line=h.OrientationLine(good.frame)))
        for bad in bads:
            self.reject("RESULT_TYPE_MISMATCH", lambda: h.verify_star(self.g, self.xy, self.e, bad, orientation=self.o))
        self.reject("RESULT_TYPE_MISMATCH", lambda: h.verify_star(self.g, self.xy, self.e, good, orientation=None))
        self.reject("LINE_MISMATCH", lambda: replace(good, line=h.OrientationLine(replace(good.frame, fiber_id="other-point"))))
        self.reject("VARIANCE_MISMATCH", lambda: h.flat(self.g, self.xy))
        self.reject("VARIANCE_MISMATCH", lambda: h.sharp(self.g, self.xy, self.e.nondegenerate))

    def test_strict_exact_schema_no_shape_or_float_inference(self):
        for value in (1.0, True, "1"):
            self.reject("INEXACT_INPUT", lambda: replace(self.xy, components=(value, 0, 0)))
            self.reject("INEXACT_INPUT", lambda: h.check_hodge(self.g, replace(self.e, volume=replace(self.e.volume, magnitude=value))))
        for dimension in (True, 2, 5):
            self.reject("UNSUPPORTED_DIMENSION", lambda: replace(self.g.frame, dimension=dimension))
        for degree in (True, -1, 4):
            self.reject("INVALID_DEGREE", lambda: h.indices(self.g.frame, degree))
        for sign in (True, 0, 1.0):
            self.reject("INVALID_ORIENTATION", lambda: replace(self.o, sign=sign))
        for blade in ((True,), (0, 0), (1, 0), (3,)):
            self.reject("INVALID_BLADE", lambda: h.basis_form(self.g.frame, blade))
        self.reject("INVALID_SHAPE", lambda: replace(self.g, gram=((1, 0), (0, 1))))
        self.reject("INVALID_BASIS", lambda: replace(self.g.frame, basis=("x", "x", "z")))
        self.reject("UNSUPPORTED_COEFFICIENTS", lambda: replace(self.g.frame, scalar_profile="float64"))
        self.reject("INVALID_INVERSE", lambda: h.FrameAutomorphism(self.g.frame, diagonal((2, 1, 1)), diagonal((1, 1, 1))))

    def test_demo_executes_and_reports_reference_scope(self):
        demo = Path(__file__).with_name("demo_hodge_reference.py")
        result = subprocess.run([sys.executable, str(demo)], capture_output=True, text=True, check=True)
        report = json.loads(result.stdout)
        self.assertTrue(all(c["passed"] for c in report["checks"].values()))
        self.assertIn("no Lean proof", report["scope"])
        self.assertEqual(report["checks"]["reject_euclidean_sign"]["actual"], "HODGE_IDENTITY_FAILED")


if __name__ == "__main__":
    unittest.main()
