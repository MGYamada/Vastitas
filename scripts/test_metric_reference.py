"""Independent exact examples, variance failures and nominal evidence mutations."""

import itertools
import json
import subprocess
import sys
import unittest
from dataclasses import fields, replace
from fractions import Fraction as Q
from pathlib import Path

import metric_free_reference as mf
import metric_reference as mr
from demo_metric_reference import example


ROOT = Path(__file__).resolve().parents[1]


class MetricTests(unittest.TestCase):
    def setUp(self):
        self.f, self.p, self.u, self.change, self.g, self.h = example()
        self.alpha = mf.differential(self.f, self.p)
        self.subject = mr.FiberMetric(self.g, self.p)
        self.evidence = mr.certify_nondegenerate(self.subject)

    def reject(self, code, action):
        with self.assertRaises(mf.Invalid) as raised:
            action()
        self.assertEqual(raised.exception.code, code)

    def grad(self, metric, alpha=None):
        alpha = self.alpha if alpha is None else alpha
        subject = mr.FiberMetric(metric, alpha.point)
        return mr.sharp(subject, alpha, mr.certify_nondegenerate(subject))

    def test_known_differential_and_two_selected_gradients(self):
        self.assertEqual(self.alpha.components, (4, 13))
        self.assertEqual(self.grad(self.g).value.components, (2, Q(13, 3)))
        self.assertEqual(self.grad(self.h).value.components, (Q(-5, 3), Q(22, 3)))
        self.assertIs(self.grad(self.g).subject.metric, self.g)
        self.assertIs(self.grad(self.h).subject.metric, self.h)
        self.assertEqual(mr.gradient(self.f, self.p, using=self.g, evidence=self.evidence), self.grad(self.g))

    def test_rational_coefficients_higher_powers_and_rational_basepoint(self):
        f = mf.ScalarPolynomial(self.p.frame, Q(2, 3) * mf.X ** 3 - Q(5, 7) * mf.X * mf.Y ** 2 + mf.Poly.constant(Q(11, 13)))
        p = mf.Point(self.p.frame, (Q(3, 2), Q(-2, 5)))
        self.assertEqual(mf.differential(f, p).components, (Q(307, 70), Q(6, 7)))
        constant = mf.ScalarPolynomial(self.p.frame, mf.Poly.constant(Q(-2, 3)))
        self.assertEqual(mf.differential(constant, p).components, (0, 0))

    def test_metric_free_import_in_fresh_process(self):
        result = subprocess.run([sys.executable, "-c",
                                 "import sys; import metric_free_reference; "
                                 "print('metric_reference' in sys.modules)"],
                                cwd=ROOT / "scripts", capture_output=True, text=True, check=True)
        self.assertEqual(result.stdout.strip(), "False")

    def test_nonlinear_pullback_is_unchanged_by_adding_or_swapping_metrics(self):
        target = replace(self.p.frame, object_id="other:R2", chart_id="other:chart")
        mapping = mf.PolynomialMap(self.p.frame, target, (mf.X ** 2 + mf.Y, mf.Y ** 2 + mf.X))
        output = mapping.at(self.p)
        self.assertEqual(output.coordinates, (3, 5))
        seed = mf.Cotangent(output, (3, -2))
        baseline = mf.cotangent_pullback(mapping, self.p, seed)
        self.assertEqual(baseline.components, (4, -5))
        for metric in (self.g, self.h, replace(self.g, metric_id="singular", gram=((1, 0), (0, 0)))):
            # A metric on either endpoint does not enter the differential/pullback path.
            target_metric = replace(metric, frame=target)
            self.assertEqual(target_metric.frame, output.frame)
            self.assertEqual(mf.differential(self.f, self.p), self.alpha)
            self.assertEqual(mf.cotangent_pullback(mapping, self.p, seed), baseline)

    def test_polynomial_chain_rule_at_actual_output_basepoint(self):
        target = replace(self.p.frame, object_id="target:R2")
        mapping = mf.PolynomialMap(self.p.frame, target, (mf.X ** 2 + mf.Y, mf.Y ** 2 + mf.X))
        outer = replace(self.f, frame=target)
        seed = mf.differential(outer, mapping.at(self.p))
        composite = mf.ScalarPolynomial(self.p.frame, mf.substitute(outer.expression, mapping.expressions))
        pulled = mf.cotangent_pullback(mapping, self.p, seed)
        self.assertEqual(pulled.components, (55, 143))
        self.assertEqual(pulled, mf.differential(composite, self.p))

    def test_pullback_composition_and_linearity(self):
        middle = replace(self.p.frame, object_id="middle:R2")
        target = replace(self.p.frame, object_id="target:R2")
        first = mf.PolynomialMap(self.p.frame, middle, (mf.X ** 2 + mf.Y, mf.X * mf.Y))
        second = mf.PolynomialMap(middle, target, (mf.X * mf.Y, mf.X + mf.Y ** 2))
        composite = mf.PolynomialMap(self.p.frame, target,
                                     tuple(mf.substitute(p, first.expressions) for p in second.expressions))
        seed = mf.Cotangent(composite.at(self.p), (Q(2, 3), Q(-7, 5)))
        direct = mf.cotangent_pullback(composite, self.p, seed)
        staged = mf.cotangent_pullback(first, self.p,
                                       mf.cotangent_pullback(second, first.at(self.p), seed))
        self.assertEqual(direct, staged)
        scale = Q(-9, 7)
        scaled = replace(seed, components=tuple(scale * x for x in seed.components))
        self.assertEqual(mf.cotangent_pullback(composite, self.p, scaled).components,
                         tuple(scale * x for x in direct.components))

    def test_pullback_rejects_wrong_seed_point_object_and_variance(self):
        mapping = self.change.as_map()
        for point in (replace(self.p, coordinates=(1, 3)),
                      replace(self.p, frame=replace(self.p.frame, object_id="different:R2")),
                      replace(self.p, frame=replace(self.p.frame, cotangent_frame_id="different:dual"))):
            self.reject("SEED_BASEPOINT_MISMATCH",
                        lambda: mf.cotangent_pullback(mapping, self.u, replace(self.alpha, point=point)))
        self.reject("VARIANCE_MISMATCH", lambda: mf.cotangent_pullback(mapping, self.u, mf.Tangent(self.p, (4, 13))))

    def test_three_coordinate_laws_separately(self):
        alpha_u = mf.differential(self.change.reexpress(self.f), self.u)
        self.assertEqual(alpha_u.components, (4, 17))
        self.assertEqual(mf.check_cotangent_transport(self.change, self.u, self.alpha, alpha_u), alpha_u)
        g_u = mr.Metric(self.u.frame, self.g.metric_id, self.g.revision, ((2, 2), (2, 5)))
        self.assertEqual(mr.check_metric_transport(self.change, self.g, g_u), g_u)
        grad_u = self.grad(g_u, alpha_u)
        self.assertEqual(grad_u.value.components, (Q(-7, 3), Q(13, 3)))
        self.assertEqual(self.change.push_tangent(grad_u.value), self.grad(self.g).value)
        self.assertEqual(mr.check_gradient_transport(self.change, self.u, self.g, self.alpha,
                                                     self.grad(self.g), grad_u), grad_u)

    def test_nonorthogonal_df_as_vector_fails_value_and_pairing(self):
        wrong = mf.Cotangent(self.u, mf.matvec(mf.inverse(self.change.forward), self.alpha.components))
        self.assertEqual(wrong.components, (-9, 13))
        self.reject("COTANGENT_TRANSPORT_MISMATCH",
                    lambda: mf.check_cotangent_transport(self.change, self.u, self.alpha, wrong))
        v = mf.Tangent(self.u, (0, 1))
        true = mf.cotangent_pullback(self.change.as_map(), self.u, self.alpha)
        self.assertEqual(mf.pairing(self.alpha, self.change.push_tangent(v)), 17)
        self.assertEqual(mf.pairing(true, v), 17)
        self.assertEqual(mf.pairing(wrong, v), 13)
        self.reject("VARIANCE_MISMATCH", lambda: self.change.reexpress_tangent(self.u, self.alpha))
        self.reject("VARIANCE_MISMATCH", lambda: self.change.push_tangent(self.alpha))

    def test_metric_and_gradient_transport_reject_independently(self):
        g_u = mr.reexpress_metric(self.change, self.g)
        for bad in (replace(g_u, metric_id="another-metric"), replace(g_u, gram=self.g.gram)):
            self.reject("METRIC_TRANSPORT_MISMATCH", lambda: mr.check_metric_transport(self.change, self.g, bad))
        alpha_u = mf.cotangent_pullback(self.change.as_map(), self.u, self.alpha)
        good = self.grad(g_u, alpha_u)
        bad = replace(good, value=mf.Tangent(self.u, alpha_u.components))
        self.reject("GRADIENT_MISMATCH", lambda: mr.check_gradient_transport(self.change, self.u,
                    self.g, self.alpha, self.grad(self.g), bad))
        twin = replace(g_u, metric_id="same-matrix-another-metric")
        self.reject("EVIDENCE_SUBJECT_MISMATCH", lambda: mr.check_gradient_transport(self.change, self.u,
                    self.g, self.alpha, self.grad(self.g), self.grad(twin, alpha_u)))

    def test_flat_sharp_both_inverse_laws_and_retained_selection(self):
        for metric in (self.g, self.h, replace(self.g, gram=((1, 0), (0, -1)))):
            subject = mr.FiberMetric(metric, self.p)
            evidence = mr.certify_nondegenerate(subject)
            v = mf.Tangent(self.p, (Q(7, 11), Q(-13, 5)))
            lowered = mr.flat(subject, v)
            self.assertIs(lowered.subject, subject)
            self.assertEqual(mr.sharp(subject, lowered.value, evidence).value, v)
            raised = mr.sharp(subject, self.alpha, evidence)
            self.assertIs(raised.evidence, evidence)
            self.assertEqual(mr.flat(subject, raised.value).value, self.alpha)

    def test_singular_flat_is_valid_but_has_no_sharp(self):
        singular = mr.FiberMetric(replace(self.g, gram=((1, 0), (0, 0))), self.p)
        kernel = mf.Tangent(self.p, (0, 1))
        self.assertEqual(mr.flat(singular, kernel).value.components, (0, 0))
        self.reject("SINGULAR", lambda: mr.certify_nondegenerate(singular))
        forged = mr.NondegenerateEvidence(singular, mf.IDENTITY)
        self.reject("INVALID_INVERSE", lambda: mr.sharp(singular, self.alpha, forged))

    def test_indefinite_is_nondegenerate_but_not_riemannian(self):
        indefinite = mr.FiberMetric(replace(self.g, gram=((1, 0), (0, -1))), self.p)
        evidence = mr.certify_nondegenerate(indefinite)
        self.assertEqual(mr.sharp(indefinite, self.alpha, evidence).value.components, (4, -13))
        self.reject("NOT_POSITIVE_DEFINITE", lambda: mr.certify_riemannian(indefinite))
        self.reject("MISSING_POSITIVITY", lambda: mr.check_riemannian(indefinite, evidence))

    def test_positive_determinant_does_not_prove_positivity(self):
        negative = mr.FiberMetric(replace(self.g, gram=((-1, 0), (0, -1))), self.p)
        self.assertEqual(mf.determinant(negative.metric.gram), 1)
        mr.certify_nondegenerate(negative)
        self.reject("NOT_POSITIVE_DEFINITE", lambda: mr.certify_riemannian(negative))

    def test_positive_definite_evidence_has_separate_checked_minors(self):
        for metric, expected in ((self.g, (2, 6)), (self.h, (2, 3))):
            subject = mr.FiberMetric(metric, self.p)
            evidence = mr.certify_riemannian(subject)
            self.assertEqual(evidence.leading_minors, expected)
            self.assertEqual(mr.check_riemannian(subject, evidence), evidence)
            self.reject("MINOR_MISMATCH", lambda: mr.check_riemannian(subject, replace(evidence, leading_minors=(1, 1))))
        indefinite = mr.FiberMetric(replace(self.g, gram=((1, 0), (0, -1))), self.p)
        fake = mr.RiemannianEvidence(indefinite, mr.certify_nondegenerate(indefinite), (1, 1))
        self.reject("MINOR_MISMATCH", lambda: mr.check_riemannian(indefinite, fake))

    def test_equal_matrix_distinct_metric_and_stale_revision_rejected(self):
        for metric in (replace(self.g, metric_id="g-twin"), replace(self.g, revision="2"),
                       replace(self.g, gram=((3, 0), (0, 2)))):
            subject = mr.FiberMetric(metric, self.p)
            self.reject("EVIDENCE_SUBJECT_MISMATCH", lambda: mr.sharp(subject, self.alpha, self.evidence))

    def test_all_context_indices_bound_even_with_same_matrix_and_point_numbers(self):
        for field in fields(self.p.frame):
            if field.name == "scalar_profile":
                continue  # unsupported profiles are rejected at construction
            changed = (("y", "x") if field.name == "coordinates"
                       else getattr(self.p.frame, field.name) + ":different")
            frame = replace(self.p.frame, **{field.name: changed})
            point = replace(self.p, frame=frame)
            subject = mr.FiberMetric(replace(self.g, frame=frame), point)
            with self.subTest(index=field.name):
                self.reject("EVIDENCE_SUBJECT_MISMATCH", lambda: mr.check_nondegenerate(subject, self.evidence))

    def test_basepoint_evidence_and_arguments_are_bound(self):
        point = replace(self.p, coordinates=(2, 1))
        subject = mr.FiberMetric(self.g, point)
        self.reject("EVIDENCE_SUBJECT_MISMATCH", lambda: mr.check_nondegenerate(subject, self.evidence))
        self.reject("FIBER_MISMATCH", lambda: mr.sharp(subject, self.alpha, mr.certify_nondegenerate(subject)))
        self.reject("FIBER_MISMATCH", lambda: mf.pairing(self.alpha, mf.Tangent(point, (1, 2))))
        self.reject("FIBER_MISMATCH", lambda: mr.FiberMetric(self.g, self.u))
        self.reject("FIBER_MISMATCH", lambda: mf.differential(self.f, self.u))

    def test_positivity_cannot_borrow_another_metrics_inverse(self):
        good = mr.certify_riemannian(self.subject)
        twin = mr.FiberMetric(replace(self.g, metric_id="twin"), self.p)
        self.reject("EVIDENCE_SUBJECT_MISMATCH", lambda: mr.check_riemannian(twin, good))
        fake = replace(good, nondegenerate=mr.certify_nondegenerate(twin))
        self.reject("EVIDENCE_SUBJECT_MISMATCH", lambda: mr.check_riemannian(self.subject, fake))

    def test_inverse_certificate_rechecked_and_not_trusted(self):
        fake = replace(self.evidence, inverse_gram=mf.IDENTITY)
        self.reject("INVALID_INVERSE", lambda: mr.sharp(self.subject, self.alpha, fake))
        self.reject("MISSING_NONDEGENERACY", lambda: mr.sharp(self.subject, self.alpha, None))
        self.reject("MISSING_METRIC", lambda: mr.sharp(None, self.alpha, self.evidence))
        self.reject("MISSING_METRIC", lambda: mr.gradient(self.f, self.p, using=None, evidence=self.evidence))

    def test_no_implicit_vector_covector_coercion(self):
        v = mf.Tangent(self.p, self.alpha.components)
        self.reject("VARIANCE_MISMATCH", lambda: mr.flat(self.subject, self.alpha))
        self.reject("VARIANCE_MISMATCH", lambda: mr.sharp(self.subject, v, self.evidence))
        self.reject("VARIANCE_MISMATCH", lambda: mf.pairing(v, v))

    def test_coordinate_change_requires_invertibility_and_same_object(self):
        self.reject("SINGULAR", lambda: replace(self.change, forward=((1, 1), (1, 1))))
        for field in ("object_id", "base_id", "environment_id", "model_id", "model_revision"):
            source = replace(self.u.frame, **{field: "another"})
            self.reject("COORDINATE_OBJECT_MISMATCH", lambda: replace(self.change, source=source))
        self.reject("INVALID_FRAME", lambda: replace(self.change, source=self.p.frame))

    def test_unchecked_map_is_not_a_coordinate_change(self):
        mapping = self.change.as_map()
        self.reject("UNSUPPORTED_COORDINATE_CHANGE", lambda: mr.reexpress_metric(mapping, self.g))
        self.reject("UNSUPPORTED_COORDINATE_CHANGE",
                    lambda: mf.check_cotangent_transport(mapping, self.u, self.alpha, self.alpha))
        self.reject("UNSUPPORTED_COORDINATE_CHANGE",
                    lambda: mr.check_gradient_transport(mapping, self.u, self.g, self.alpha, None, None))

    def test_gradient_record_cannot_supply_its_own_subject_or_argument(self):
        g_u = mr.reexpress_metric(self.change, self.g)
        alpha_u = mf.cotangent_pullback(self.change.as_map(), self.u, self.alpha)
        good = self.grad(g_u, alpha_u)
        for bad in (replace(good, subject=self.subject),
                    replace(good, argument=replace(alpha_u, components=(4, 18))),
                    replace(good, value=replace(good.value, point=self.p))):
            self.reject("GRADIENT_MISMATCH", lambda: mr.check_gradient_transport(
                self.change, self.u, self.g, self.alpha, self.grad(self.g), bad))

    def test_reject_unsupported_inexact_or_malformed_inputs(self):
        for number in (0.5, True, "1/2"):
            self.reject("INEXACT_INPUT", lambda: mf.Point(self.p.frame, (number, 0)))
            self.reject("INEXACT_INPUT", lambda: replace(self.g, gram=((number, 0), (0, 1))))
            self.reject("INEXACT_INPUT", lambda: replace(self.change, forward=((1, number), (0, 1))))
            self.reject("INVALID_SCHEMA", lambda: mf.Poly.constant(number))
        self.reject("INVALID_SHAPE", lambda: mf.Point(self.p.frame, (1, 2, 3)))
        self.reject("NOT_SYMMETRIC", lambda: replace(self.g, gram=((1, 1), (0, 1))))
        self.reject("UNSUPPORTED_POLYNOMIAL", lambda: replace(self.f, expression=mf.Poly.variable(2)))
        self.reject("UNSUPPORTED_POLYNOMIAL", lambda: mf.PolynomialMap(self.p.frame, self.p.frame, (mf.X, mf.Poly.variable(3))))
        self.reject("UNSUPPORTED_PROFILE", lambda: replace(self.p.frame, scalar_profile="Float64"))
        self.reject("INVALID_FRAME", lambda: replace(self.p.frame, coordinates=("x", "x")))

    def test_symbolic_chain_rule_and_finite_rational_coordinate_grid(self):
        transforms = (((1, 1), (0, 1)), ((0, 1), (1, 0)), ((2, -1), (1, 3)),
                      ((Q(1, 2), Q(-2, 3)), (Q(3, 5), Q(7, 4))),
                      ((1, 0), (0, 1)))
        expressions = (self.f.expression, mf.X ** 3 * mf.Y + Q(2, 7) * mf.Y ** 4,
                       mf.Poly.constant(Q(3, 11)))
        points = ((-1, 2), (0, 0), (Q(2, 3), Q(-5, 7)))
        metrics = (self.g, self.h, replace(self.g, metric_id="indefinite", gram=((1, 0), (0, -1))))
        for a, expression in itertools.product(transforms, expressions):
            change = replace(self.change, forward=a)
            f = replace(self.f, expression=expression)
            f_u = change.reexpress(f)
            # Polynomial identity, not a finite-difference/numeric derivative oracle.
            for i in range(2):
                chain = sum((a[j][i] * mf.substitute(expression.derivative(j), change.as_map().expressions)
                             for j in range(2)), mf.ZERO)
                self.assertEqual(f_u.expression.derivative(i), chain)
            for coordinates, metric in itertools.product(points, metrics):
                with self.subTest(A=a, point=coordinates, metric=metric.metric_id):
                    u = mf.Point(change.source, coordinates)
                    p = change.at(u)
                    alpha = mf.differential(f, p)
                    alpha_u = mf.differential(f_u, u)
                    mf.check_cotangent_transport(change, u, alpha, alpha_u)
                    g_u = mr.reexpress_metric(change, metric)
                    grad = self.grad(metric, alpha)
                    grad_u = self.grad(g_u, alpha_u)
                    mr.check_gradient_transport(change, u, metric, alpha, grad, grad_u)
                    v = mf.Tangent(u, (Q(3, 2), Q(-7, 3)))
                    flat_x = mr.flat(mr.FiberMetric(metric, p), change.push_tangent(v)).value
                    flat_u = mr.flat(mr.FiberMetric(g_u, u), v).value
                    mf.check_cotangent_transport(change, u, flat_x, flat_u)
                    self.assertEqual(mf.pairing(alpha_u, v), mf.pairing(alpha, change.push_tangent(v)))

    def test_demo_runs_and_reports_exact_values_and_scope(self):
        result = subprocess.run([sys.executable, str(ROOT / "scripts/demo_metric_reference.py")],
                                capture_output=True, text=True, check=True)
        report = json.loads(result.stdout)
        self.assertIn("no Lean proof or accepted Core", report["scope"])
        self.assertEqual(report["gradient_g_in_uv"], ["-7/3", "13/3"])
        self.assertTrue(all(check["passed"] for check in report["checks"].values()))


if __name__ == "__main__":
    unittest.main()
