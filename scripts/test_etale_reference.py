"""Chart, self-overlap descent and spectral-chart regressions for #765."""

import json
import subprocess
import sys
import unittest
from dataclasses import replace
from fractions import Fraction as Q
from itertools import islice, product
from pathlib import Path
from unittest.mock import patch

import etale_reference as ref
from demo_etale_reference import context, cubic, descent, examples, number_fields, stage5
from rational_polynomial_calculus import evaluate
from rational_polynomial_reference import Invalid, Poly


TINY = Q(1, 10 ** 20)


def by_name(report):
    return {check.name: check for check in report.checks}


def failures(report):
    return tuple(c.code for c in report.checks if c.status in ("fail", "unsupported"))


def at(matrix, point):
    return tuple(tuple(evaluate(entry, point) for entry in row) for row in matrix)


def product_q(left, right):
    size = range(len(left))
    return tuple(tuple(sum(left[i][k] * right[k][j] for k in size) for j in size) for i in size)


class ChartTests(unittest.TestCase):
    def setUp(self):
        self.s5, self.cu, self.nf = stage5(), cubic(), number_fields()

    def test_demo_expectations(self):
        for name, (verifier, arguments, accepted, codes) in examples().items():
            with self.subTest(name=name):
                report = verifier(*arguments)
                self.assertEqual(report.accepted, accepted)
                self.assertEqual(failures(report), codes)
                self.assertEqual(report.returned is not None, accepted)

    def test_finite_and_simple_root_charts_are_different_charts(self):
        self.assertTrue(ref.is_finite(self.s5["finite"].chart))
        self.assertFalse(ref.is_finite(self.s5["simple"].subject.chart))
        self.assertFalse(ref.is_finite(self.cu["simple"].subject.chart))
        self.assertTrue(ref.is_finite(self.nf["sqrt2"].chart))
        report = ref.verify_chart(self.s5["finite"], self.s5["certificate"])
        self.assertIs(report.returned, self.s5["certificate"])

    def test_unit_witness_mutations(self):
        chart, good = self.s5["finite"], self.s5["certificate"]
        t = Poly.variable(2, 3)
        for changed in (replace(good, witness=good.witness + TINY),
                        replace(good, witness=good.witness * -1),
                        replace(good, exponent=0), replace(good, exponent=2)):
            with self.subTest(changed=changed.exponent):
                report = ref.verify_chart(chart, changed)
                self.assertFalse(report.accepted)
                self.assertEqual(failures(report), ("UNIT_WITNESS_MISMATCH",))
        moved = replace(chart, chart=replace(chart.chart, localizer=self.s5["gap"] + 1))
        self.assertEqual(failures(ref.verify_chart(moved, replace(good, subject=moved))),
                         ("UNIT_WITNESS_MISMATCH",))
        # An unreduced witness denotes the same element; it is rejected, not reduced silently.
        unreduced = replace(good, witness=good.witness + chart.chart.relation * t)
        checks = by_name(ref.verify_chart(chart, unreduced))
        self.assertEqual(checks["reduced_presentation"].code, "NOT_REDUCED")
        self.assertEqual(checks["unit_witness"].status, "pass")

    def test_relation_must_be_monic_of_positive_degree(self):
        chart, good = self.s5["finite"], self.s5["certificate"]
        x, t = Poly.variable(0, 3), Poly.variable(2, 3)
        for relation in (t * t * 2 - x, x * t * t - 1, x * x + 1, Poly.constant(0, 3),
                         t ** (ref.MAX_DEGREE + 1) - x):
            subject = replace(chart, chart=replace(chart.chart, relation=relation))
            with self.subTest(relation=relation.terms):
                report = ref.verify_chart(subject, replace(good, subject=subject))
                checks = by_name(report)
                self.assertFalse(report.accepted)
                self.assertEqual(checks["monic_relation"].code, "RELATION_NOT_MONIC")
                self.assertEqual(checks["unit_witness"].status, "not_checked")

    def test_zero_localizer_is_an_empty_chart_not_a_unit(self):
        chart = self.s5["finite"]
        zero = Poly.constant(0, 3)
        empty = replace(chart, chart=replace(chart.chart, localizer=zero))
        report = ref.verify_chart(empty, ref.ChartCertificate(empty, zero, 1))
        checks = by_name(report)
        self.assertFalse(report.accepted)
        self.assertEqual(checks["nonzero_localizer"].code, "EMPTY_CHART")
        self.assertEqual(checks["unit_witness"].status, "pass")

    def test_cubic_has_no_global_unit_witness(self):
        relation = self.cu["relation"]
        # At x = 2 the root t = 1 is double: p and p' vanish together, so no
        # identity W p' = 1 + U p can hold after this specialization.
        self.assertEqual(evaluate(relation, (Q(2), Q(1))), 0)
        self.assertEqual(evaluate(relation.derivative(1), (Q(2), Q(1))), 0)
        self.assertNotEqual(evaluate(relation.derivative(1), (Q(2), Q(-2))), 0)
        x, t = Poly.variable(0, 2), Poly.variable(1, 2)
        everywhere = self.cu["everywhere"]
        for c0, c1, c2 in product((Q(0), Q(1), Q(-1, 3), x), repeat=3):
            witness = t * t * c2 + t * c1 + c0
            for exponent in (0, 1):
                report = ref.verify_chart(everywhere, ref.ChartCertificate(everywhere, witness, exponent))
                self.assertEqual(failures(report), ("UNIT_WITNESS_MISMATCH",))
        self.assertTrue(ref.verify_chart(self.cu["finite"], self.cu["certificate"]).accepted)
        self.assertTrue(ref.verify_chart(self.cu["simple"].subject, self.cu["simple"]).accepted)

    def test_number_field_charts(self):
        ctx, t = self.nf["context"], Poly.variable(0, 1)
        zeta8 = ref.Subject(ctx, ref.Chart("chart:zeta8", "1", t ** 4 + 1, Poly.constant(1, 1)))
        self.assertTrue(ref.verify_chart(zeta8, ref.ChartCertificate(zeta8, t * Q(-1, 4), 0)).accepted)
        # t^2 is inseparable over QQ: its derivative 2t is nilpotent in QQ[t]/(t^2).
        double = ref.Subject(ctx, ref.Chart("chart:double", "1", t * t, Poly.constant(1, 1)))
        for witness in (t * Q(1, 2), Poly.constant(1, 1), t + 1, Poly.constant(0, 1)):
            report = ref.verify_chart(double, ref.ChartCertificate(double, witness, 0))
            self.assertEqual(failures(report), ("UNIT_WITNESS_MISMATCH",))

    def test_binding_blocks_every_mathematical_check(self):
        chart, good = self.s5["finite"], self.s5["certificate"]
        stale = (replace(chart, chart=replace(chart.chart, revision="2")),
                 replace(chart, chart=replace(chart.chart, chart_id="chart:other")),
                 replace(chart, context=replace(chart.context, model_revision="2")),
                 replace(chart, context=replace(chart.context, variables=("y", "x"))),
                 replace(chart, context=replace(chart.context, fiber="s")))
        for expected in stale:
            with self.subTest(expected=expected.chart.revision):
                report = ref.verify_chart(expected, good)
                self.assertFalse(report.accepted)
                self.assertIsNone(report.returned)
                self.assertEqual(report.checks[0].code, "SUBJECT_MISMATCH")
                self.assertTrue(all(c.status == "not_checked" for c in report.checks[1:]))

    def test_unsupported_profiles_and_malformed_contexts(self):
        ctx = self.s5["context"]
        for field, value in (("site", "zariski-principal/v1"), ("site", "real-cozero/v1"),
                             ("site", "fppf"), ("scalar_profile", "Float64"),
                             ("scalar_profile", "QQ-to-R-polynomial/v1")):
            with self.subTest(value=value), self.assertRaises(Invalid) as raised:
                replace(ctx, **{field: value})
            self.assertEqual(raised.exception.code, "UNSUPPORTED_PROFILE")
        for field, value in (("variables", ("x", "x")), ("variables", ["x", "y"]),
                             ("variables", ("x", "t")), ("variables", ("a", "b", "c", "d", "e")),
                             ("variables", ("x", "")), ("fiber", ""), ("environment_id", 7)):
            with self.subTest(value=value), self.assertRaises(Invalid):
                replace(ctx, **{field: value})

    def test_schema_rejections(self):
        chart, good = self.s5["finite"], self.s5["certificate"]
        wrong_ring = Poly.variable(0, 2)
        with self.assertRaises(Invalid):
            replace(chart, chart=replace(chart.chart, relation=wrong_ring))
        with self.assertRaises(Invalid):
            replace(chart, chart=replace(chart.chart, localizer="x^2+y^2"))
        with self.assertRaises(Invalid):
            replace(good, witness=wrong_ring)
        for exponent in (True, -1, 1.0, ref.MAX_EXPONENT + 1):
            with self.subTest(exponent=exponent), self.assertRaises(Invalid):
                replace(good, exponent=exponent)
        with self.assertRaises(Invalid):
            Poly.from_terms([((0, 0, 1), 0.5)], 3)
        with self.assertRaises(Invalid):
            ref.verify_chart(chart, chart)


class ArithmeticTests(unittest.TestCase):
    def test_reduction_agrees_with_specialization_on_the_curve(self):
        x, t = Poly.variable(0, 2), Poly.variable(1, 2)
        square, relation = t * t - x, cubic()["relation"]
        samples = (t ** 5, t ** 4 * x - t * 3 + 1, (t + x) ** 3, t ** 7 * Q(2, 3) + x * x)
        for value in samples:
            reduced = ref.reduce(value, square)
            self.assertLess(ref.degree(reduced, 1), 2)
            cubic_reduced = ref.reduce(value, relation)
            self.assertLess(ref.degree(cubic_reduced, 1), 3)
            for a in (Q(0), Q(1), Q(-2), Q(3, 7)):
                self.assertEqual(evaluate(value, (a * a, a)), evaluate(reduced, (a * a, a)))
                on_cubic = (3 * a - a ** 3, a)
                self.assertEqual(evaluate(value, on_cubic), evaluate(cubic_reduced, on_cubic))

    def test_reduction_refuses_a_relation_that_is_not_monic(self):
        x, t = Poly.variable(0, 2), Poly.variable(1, 2)
        for relation in (t * t * 2 - x, x * t - 1, x, Poly.variable(0, 3)):
            with self.subTest(relation=relation.terms), self.assertRaises(Invalid) as raised:
                ref.reduce(t ** 3, relation)
            self.assertEqual(raised.exception.code, "RELATION_NOT_MONIC")

    def test_trace_satisfies_newton_identities(self):
        x, t = Poly.variable(0, 2), Poly.variable(1, 2)
        relation = cubic()["relation"]  # e1 = 0, e2 = -3, e3 = -x
        self.assertEqual(ref.trace(Poly.constant(1, 2), relation), Poly.constant(3, 2))
        self.assertEqual(ref.trace(t, relation), Poly.constant(0, 2))
        self.assertEqual(ref.trace(t * t, relation), Poly.constant(6, 2))
        self.assertEqual(ref.trace(t ** 3, relation), x * -3)
        self.assertEqual(ref.trace(t ** 4, relation), Poly.constant(18, 2))
        self.assertEqual(ref.trace(t * x + 5, relation), Poly.constant(15, 2))
        self.assertEqual(ref.trace(t * t * x, relation), x * 6)

    def test_trace_of_powers_equals_matrix_invariants_without_a_gap(self):
        for fixture in (stage5(), cubic()):
            subject, chi = fixture["subject"], fixture["candidate"].characteristic
            arity = subject.context.arity
            t, power = Poly.variable(arity - 1, arity), ref.identity(len(subject.matrix), arity)
            for k in range(1, 6):
                power = ref.multiply(power, subject.matrix)
                self.assertEqual(ref.trace(t ** k, chi), ref.matrix_trace(power))

    def test_divided_difference_factors_the_self_overlap(self):
        for relation in (cubic()["relation"], stage5()["candidate"].characteristic):
            arity = relation.arity + 1
            quotient = ref.divided_difference(relation)
            t, s = Poly.variable(arity - 2, arity), Poly.variable(arity - 1, arity)
            self.assertEqual(ref.first(relation) - ref.second(relation), (t - s) * quotient)
            derivative = relation.derivative(relation.arity - 1)
            for point in product((Q(-1), Q(2), Q(1, 3)), repeat=relation.arity):
                self.assertEqual(evaluate(quotient, point + point[-1:]), evaluate(derivative, point))


class DescentTests(unittest.TestCase):
    def setUp(self):
        self.s5, self.cu, self.nf = stage5(), cubic(), number_fields()

    def test_a_section_descends_exactly_when_both_pullbacks_agree(self):
        x3, t3 = Poly.variable(0, 3), Poly.variable(2, 3)
        x2, t2 = Poly.variable(0, 2), Poly.variable(1, 2)
        cases = ((self.s5["finite"], self.s5["certificate"], (Q(0), Q(1), x3), t3, 2),
                 (self.cu["finite"], self.cu["certificate"], (Q(0), Q(2), x2), t2, 3))
        for chart, certificate, choices, t, top in cases:
            for coefficients in product(choices, repeat=top):
                numerator = sum((t ** k * c for k, c in enumerate(coefficients)),
                                Poly.constant(0, t.arity))
                agrees = not ref.overlap_difference(numerator, chart.chart.relation).terms
                self.assertEqual(agrees, ref.is_base(numerator))
                report = ref.verify_descent(*descent(chart, certificate, numerator))
                self.assertEqual(report.accepted, ref.is_base(numerator))

    def test_self_overlap_and_restriction_are_separate_obligations(self):
        chart, certificate, gap = self.s5["finite"], self.s5["certificate"], self.s5["gap"]
        subject, good = descent(chart, certificate, gap)
        wrong = replace(good, descended=gap + 1)
        checks = by_name(ref.verify_descent(subject, wrong))
        self.assertEqual(checks["self_overlap"].status, "pass")
        self.assertEqual(checks["restriction"].code, "RESTRICTION_MISMATCH")
        # A branch value offered as its own descent still fails: it is not in A.
        branch_subject, branch = descent(chart, certificate, Poly.variable(2, 3))
        self.assertEqual(failures(ref.verify_descent(branch_subject, branch)),
                         ("SELF_OVERLAP_DISAGREEMENT", "RESTRICTION_MISMATCH"))

    def test_descent_replays_the_chart_certificate(self):
        chart, certificate, gap = self.s5["finite"], self.s5["certificate"], self.s5["gap"]
        subject, good = descent(chart, certificate, gap)
        forged = replace(good, chart_certificate=replace(certificate, exponent=0))
        report = ref.verify_descent(subject, forged)
        checks = by_name(report)
        self.assertFalse(report.accepted)
        self.assertEqual(checks["chart"].code, "CHART_NOT_VERIFIED")
        self.assertEqual(checks["self_overlap"].status, "not_checked")
        other = replace(good, chart_certificate=self.cu["certificate"])
        self.assertEqual(by_name(ref.verify_descent(subject, other))["chart"].code,
                         "CHART_NOT_VERIFIED")

    def test_descent_binding(self):
        subject, good = descent(self.s5["finite"], self.s5["certificate"], self.s5["gap"])
        for expected in (replace(subject, section=replace(subject.section, revision="2")),
                         replace(subject, section=replace(subject.section, exponent=1)),
                         replace(subject, chart=self.s5["simple"].subject)):
            report = ref.verify_descent(expected, good)
            self.assertEqual(report.checks[0].code, "SUBJECT_MISMATCH")
            self.assertTrue(all(c.status == "not_checked" for c in report.checks[1:]))
        with self.assertRaises(Invalid):
            replace(subject, section=replace(subject.section, numerator=Poly.variable(0, 2)))

    def test_number_field_elements(self):
        t = Poly.variable(0, 1)
        for chart, certificate in ((self.nf["sqrt2"], self.nf["sqrt2_certificate"]),
                                   (self.nf["zeta3"], self.nf["zeta3_certificate"])):
            self.assertTrue(ref.verify_descent(
                *descent(chart, certificate, Poly.constant(Q(3, 7), 1))).accepted)
            for numerator in (t, t + 1, t * Q(1, 10 ** 20) + 2):
                report = ref.verify_descent(*descent(chart, certificate, numerator))
                self.assertEqual(by_name(report)["self_overlap"].code, "SELF_OVERLAP_DISAGREEMENT")


class SpectralTests(unittest.TestCase):
    def setUp(self):
        self.s5, self.cu = stage5(), cubic()

    def test_stage5_values(self):
        x, y, t = (Poly.variable(i, 3) for i in range(3))
        candidate = self.s5["candidate"]
        self.assertEqual(candidate.characteristic, t * t - x * x - y * y)
        self.assertEqual(candidate.adjugate, ((t + x, y), (y, t - x)))
        self.assertEqual(self.s5["simple"].subject.chart.localizer, t * 2)
        self.assertEqual(self.cu["candidate"].characteristic, self.cu["relation"])

    def test_verifier_does_not_call_the_producer(self):
        subject, candidate = self.s5["subject"], self.s5["candidate"]
        with patch.object(ref, "propose_spectral", side_effect=AssertionError("producer called")):
            self.assertTrue(ref.verify_spectral(subject, candidate).accepted)
        wrong = replace(candidate, characteristic=candidate.characteristic + 1)
        with patch.object(ref, "propose_spectral", return_value=wrong):
            self.assertFalse(ref.verify_spectral(subject, ref.propose_spectral(subject)).accepted)

    def test_two_computation_routes_agree_on_a_family(self):
        ctx = self.s5["context"]
        x, y = Poly.variable(0, 3), Poly.variable(1, 3)
        entries = (Poly.constant(0, 3), Poly.constant(1, 3), x, y * -1)
        for a, b, c, d in product(entries, repeat=4):
            subject = ref.SpectralSubject(ctx, "map:family", "1", ((a, b), (c, d)))
            self.assertTrue(ref.verify_spectral(subject, ref.propose_spectral(subject)).accepted)
        for flat in islice(product(entries[1:], repeat=9), 0, 3 ** 9, 997):
            subject = ref.SpectralSubject(ctx, "map:family", "1", (flat[:3], flat[3:6], flat[6:]))
            self.assertTrue(ref.verify_spectral(subject, ref.propose_spectral(subject)).accepted)
        zero, one = entries[0], entries[1]
        companion = ((zero, zero, zero, x), (one, zero, zero, y), (zero, one, zero, one),
                     (zero, zero, one, zero))
        subject = ref.SpectralSubject(ctx, "map:quartic", "1", companion)
        candidate = ref.propose_spectral(subject)
        self.assertTrue(ref.verify_spectral(subject, candidate).accepted)
        t = Poly.variable(2, 3)
        self.assertEqual(candidate.characteristic, t ** 4 - t * t - t * y - x)
        rank_one = ref.SpectralSubject(ctx, "map:scalar", "1", ((x,),))
        self.assertTrue(ref.verify_spectral(rank_one, ref.propose_spectral(rank_one)).accepted)

    def test_specialized_adjugate_is_an_eigenprojector(self):
        subject, candidate = self.s5["subject"], self.s5["candidate"]
        derivative = candidate.characteristic.derivative(2)
        for x, y, t in ((3, 4, 5), (3, 4, -5), (5, 12, 13), (0, -2, 2), (Q(3, 5), Q(4, 5), -1)):
            point = (Q(x), Q(y), Q(t))
            self.assertEqual(evaluate(candidate.characteristic, point), 0)
            scale = evaluate(derivative, point)
            h, adjugate = at(subject.matrix, point), at(candidate.adjugate, point)
            projector = tuple(tuple(entry / scale for entry in row) for row in adjugate)
            self.assertEqual(product_q(projector, projector), projector)
            self.assertEqual(projector[0][0] + projector[1][1], 1)
            self.assertEqual(product_q(h, projector),
                             tuple(tuple(point[2] * entry for entry in row) for row in projector))
        # Neither diagonal entry alone is nonzero on the whole chart; their sum chi' is.
        self.assertEqual(at(candidate.adjugate, (Q(3), Q(0), Q(-3)))[0][0], 0)
        self.assertEqual(at(candidate.adjugate, (Q(3), Q(0), Q(3)))[1][1], 0)

    def test_branch_projectors_resolve_the_identity_at_a_rational_point(self):
        subject, candidate = self.s5["subject"], self.s5["candidate"]
        total = moved = ((Q(0), Q(0)), (Q(0), Q(0)))
        for t in (Q(5), Q(-5)):
            adjugate = at(candidate.adjugate, (Q(3), Q(4), t))
            projector = tuple(tuple(entry / (2 * t) for entry in row) for row in adjugate)
            total = tuple(tuple(a + b for a, b in zip(r, s)) for r, s in zip(total, projector))
            moved = tuple(tuple(a + t * b for a, b in zip(r, s)) for r, s in zip(moved, projector))
        self.assertEqual(total, ((1, 0), (0, 1)))
        self.assertEqual(moved, at(subject.matrix, (Q(3), Q(4), Q(0))))

    def test_degenerate_fibers_keep_the_identities_and_the_module(self):
        ctx = context((), "point")
        zero, one, t = Poly.constant(0, 1), Poly.constant(1, 1), Poly.variable(0, 1)
        scalar = ref.SpectralSubject(ctx, "map:zero", "1", ((zero, zero), (zero, zero)))
        jordan = ref.SpectralSubject(ctx, "map:jordan", "1", ((zero, one), (zero, zero)))
        candidates = {}
        for subject in (scalar, jordan):
            candidates[subject.map_id] = candidate = ref.propose_spectral(subject)
            self.assertTrue(ref.verify_spectral(subject, candidate).accepted)
            self.assertEqual(candidate.characteristic, t * t)
            simple = ref.simple_root_chart(candidate, "chart:simple-root", "1")
            # The chart D(2t) of Spec QQ[t]/(t^2) is empty: it is etale and covers nothing.
            self.assertTrue(ref.verify_chart(simple.subject, simple).accepted)
            report = ref.verify_resolution(subject, simple.subject, candidate, simple)
            self.assertEqual(failures(report), ("UNSUPPORTED_CHART",))
        self.assertEqual(candidates["map:zero"].adjugate, ((t, zero), (zero, t)))
        self.assertEqual(candidates["map:jordan"].adjugate, ((t, one), (zero, t)))
        swapped = replace(candidates["map:zero"], adjugate=candidates["map:jordan"].adjugate)
        self.assertIn("ADJUGATE_MISMATCH", failures(ref.verify_spectral(scalar, swapped)))

    def test_projector_of_minus_h_passes_the_symmetric_checks(self):
        _, (subject, wrong_sign), _, _ = examples()["stage5_projector_of_minus_H"]
        checks = by_name(ref.verify_spectral(subject, wrong_sign))
        for name in ("characteristic", "jacobi_trace", "idempotent", "rank_one"):
            self.assertEqual(checks[name].status, "pass")
        for name in ("adjugate", "eigen_columns", "divided_difference"):
            self.assertEqual(checks[name].status, "fail")

    def test_candidate_mutations(self):
        subject, candidate = self.s5["subject"], self.s5["candidate"]
        t = Poly.variable(2, 3)
        # A changed constant term cancels in chi(t) - chi(s); the other checks see it.
        shifted = replace(candidate, characteristic=candidate.characteristic + TINY)
        self.assertEqual(failures(ref.verify_spectral(subject, shifted)),
                         ("CHARACTERISTIC_MISMATCH", "EIGEN_COLUMN_MISMATCH",
                          "PROJECTOR_NOT_IDEMPOTENT", "RANK_ONE_MINOR_NONZERO"))
        rows = candidate.adjugate
        entry = replace(candidate, adjugate=((rows[0][0] + TINY, rows[0][1]), rows[1]))
        self.assertEqual(failures(ref.verify_spectral(subject, entry))[:2],
                         ("ADJUGATE_MISMATCH", "JACOBI_TRACE_MISMATCH"))
        transposed = replace(self.cu["candidate"],
                             adjugate=tuple(zip(*self.cu["candidate"].adjugate)))
        codes = failures(ref.verify_spectral(self.cu["subject"], transposed))
        self.assertIn("ADJUGATE_MISMATCH", codes)
        self.assertIn("EIGEN_COLUMN_MISMATCH", codes)
        self.assertNotIn("JACOBI_TRACE_MISMATCH", codes)
        doubled = replace(candidate, characteristic=candidate.characteristic * 2)
        checks = by_name(ref.verify_spectral(subject, doubled))
        self.assertEqual(checks["eigen_columns"].code, "RELATION_NOT_MONIC")
        self.assertEqual(checks["idempotent"].status, "not_checked")
        self.assertEqual(checks["adjugate"].status, "pass")
        unrelated = replace(candidate, characteristic=t * t)
        self.assertIn("CHARACTERISTIC_MISMATCH", failures(ref.verify_spectral(subject, unrelated)))

    def test_spectral_binding_and_shapes(self):
        subject, candidate = self.s5["subject"], self.s5["candidate"]
        x, t = Poly.variable(0, 3), Poly.variable(2, 3)
        for expected in (replace(subject, revision="2"), replace(subject, map_id="map:other"),
                         replace(subject, matrix=ref.scale(subject.matrix, -1)),
                         replace(subject, context=replace(subject.context, base_id="Spec-ZZ"))):
            report = ref.verify_spectral(expected, candidate)
            self.assertIsNone(report.returned)
            self.assertEqual(report.checks[0].code, "SUBJECT_MISMATCH")
            self.assertTrue(all(c.status == "not_checked" for c in report.checks[1:]))
        for matrix in (((x, x), (x,)), ((x, t), (x, x)), (), [[x]], ((x,) * 5,) * 5,
                       ((Poly.variable(0, 2),),)):
            with self.subTest(matrix=len(matrix)), self.assertRaises(Invalid):
                replace(subject, matrix=matrix)
        with self.assertRaises(Invalid):
            replace(candidate, adjugate=candidate.adjugate[:1])
        with self.assertRaises(Invalid):
            replace(candidate, adjugate=ref.identity(3, 3))

    def test_resolution_requires_each_prerequisite(self):
        subject, candidate = self.s5["subject"], self.s5["candidate"]
        chart, certificate = self.s5["finite"], self.s5["certificate"]
        arguments = (subject, chart, candidate, certificate)
        self.assertIs(ref.verify_resolution(*arguments).returned, candidate)
        bad_candidate = replace(candidate, characteristic=candidate.characteristic + 1)
        self.assertEqual(failures(ref.verify_resolution(subject, chart, bad_candidate, certificate)),
                         ("SPECTRAL_NOT_VERIFIED",))
        foreign = replace(chart, chart=replace(chart.chart, relation=Poly.variable(2, 3) ** 2 - 1))
        self.assertEqual(failures(ref.verify_resolution(
            subject, foreign, candidate, replace(certificate, subject=foreign))),
            ("CHART_RELATION_MISMATCH",))
        other_context = replace(chart, context=replace(chart.context, model_revision="2"))
        self.assertEqual(failures(ref.verify_resolution(
            subject, other_context, candidate, replace(certificate, subject=other_context))),
            ("CHART_RELATION_MISMATCH",))
        forged = replace(certificate, exponent=2)
        self.assertEqual(failures(ref.verify_resolution(subject, chart, candidate, forged)),
                         ("CHART_NOT_VERIFIED",))
        stale = replace(subject, revision="2")
        self.assertEqual(failures(ref.verify_resolution(stale, chart, candidate, certificate)),
                         ("SUBJECT_MISMATCH",))

    def test_resolution_uses_the_witness_of_the_chart(self):
        # A larger localizer with its own witness is another valid finite chart.
        subject, candidate, gap = self.s5["subject"], self.s5["candidate"], self.s5["gap"]
        chart = self.s5["finite"]
        wider = replace(chart, chart=replace(chart.chart, chart_id="chart:gap-squared",
                                             localizer=gap * gap * 4))
        certificate = ref.ChartCertificate(wider, Poly.variable(2, 3) * gap * 2, 1)
        self.assertTrue(ref.verify_chart(wider, certificate).accepted)
        self.assertTrue(ref.verify_resolution(subject, wider, candidate, certificate).accepted)


class DemoTests(unittest.TestCase):
    def test_demo_reports_every_expectation(self):
        script = Path(__file__).with_name("demo_etale_reference.py")
        result = subprocess.run([sys.executable, str(script)], capture_output=True, text=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        output = json.loads(result.stdout)
        self.assertEqual(output["site"], ref.SITE)
        self.assertEqual(set(output["cases"]), set(examples()))
        self.assertTrue(all(case["expected"] for case in output["cases"].values()))
        self.assertEqual(output["stage5"]["trace_of_t_squared"],
                         output["stage5"]["matrix_trace_of_H_squared"])


if __name__ == "__main__":
    unittest.main()
