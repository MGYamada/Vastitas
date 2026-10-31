"""Exact semantic, binding, mutation and wire regressions for #293."""

import copy
import itertools
import json
import subprocess
import sys
import tempfile
import unittest
from dataclasses import replace
from fractions import Fraction as Q
from pathlib import Path

import integral_reference as ir
from demo_integral_reference import cell, examples, interval
from rational_polynomial_reference import Poly


ROOT = Path(__file__).resolve().parents[1]


def failures(report):
    return {check.code for check in report.checks if check.status != "pass"}


class IntegralTests(unittest.TestCase):
    def setUp(self):
        self.examples = examples()
        self.request, self.coarse = self.examples["coarse_goal_unmet"]
        self.target = self.request.target
        self.refined = self.examples["refined_goal_met"][1]
        self.x = Poly.variable(0, 1)

    def reject(self, certificate, code, request=None):
        report = ir.verify(self.request if request is None else request, certificate)
        self.assertFalse(report.accepted)
        self.assertIsNone(report.artifact)
        self.assertEqual(report.goal_status, "NotEvaluated")
        self.assertIn(code, failures(report))
        self.assertIsNone(ir.report_data(report)["artifact"])
        return report

    def test_required_positive_enclosures_and_separate_goal(self):
        expected = {
            "coarse_goal_unmet": (Q(1, 2), Q(1, 4), interval(Q(1, 4), Q(3, 4)), "GoalUnmet"),
            "refined_goal_met": (Q(3, 8), Q(1, 16), interval(Q(5, 16), Q(7, 16)), "GoalMet"),
            "exact_singleton": (Q(1, 3), Q(0), interval(Q(1, 3), Q(1, 3)), "GoalMet"),
        }
        for name, (q, error, enclosure, goal) in expected.items():
            with self.subTest(name=name):
                request, certificate = self.examples[name]
                report = ir.verify(request, certificate)
                self.assertTrue(report.accepted)
                self.assertEqual(report.goal_status, goal)
                self.assertEqual((report.artifact.totals.q, report.artifact.totals.error,
                                  report.artifact.totals.enclosure), (q, error, enclosure))
                self.assertLessEqual(enclosure.lower, Q(1, 3))
                self.assertGreaterEqual(enclosure.upper, Q(1, 3))

    def test_goal_does_not_change_the_integral_or_enclosure(self):
        for radius, goal in ((None, "NotRequested"), (Q(1, 2), "GoalMet"),
                             (Q(1, 4), "GoalMet"), (Q(1, 4) - Q(1, 10**20), "GoalUnmet")):
            with self.subTest(radius=radius):
                report = ir.verify(replace(self.request, absolute_radius=radius), self.coarse)
                self.assertTrue(report.accepted)
                self.assertEqual(report.goal_status, goal)
                self.assertEqual(report.artifact.totals, self.coarse.claimed)

    def test_false_delta_rejected_even_with_correct_totals_and_goal(self):
        request, certificate = self.examples["false_delta"]
        report = self.reject(certificate, "LOCAL_BOUND_FALSE", replace(request, absolute_radius=Q(1)))
        self.assertEqual(report.recomputed, certificate.claimed)
        witness = next(c for c in report.checks if c.name == "local_error[0]")
        self.assertIn("x = 1/2", witness.detail)

    def test_endpoint_samples_cannot_prove_a_uniform_bound(self):
        request, certificate = self.examples["endpoint_only"]
        f = request.target.function.polynomial
        self.assertEqual((ir.evaluate(f, Q(0)), ir.evaluate(f, Q(1))), (Q(0), Q(0)))
        self.assertEqual(ir.integrate_polynomial(f, interval(0, 1)), Q(8, 15))
        self.reject(certificate, "UNSUPPORTED_PROOF_FORM", request)
        lied = replace(certificate, cells=(replace(certificate.cells[0], proof_form=ir.LOCAL_PROOF),))
        self.reject(lied, "UNSUPPORTED_DIFFERENCE_DEGREE", request)

    def test_degree_limit_is_on_difference_not_target_or_approximation(self):
        p = 7 * self.x ** 9 - 3 * self.x ** 4 + Q(2, 3)
        target = replace(self.target, function=replace(self.target.function, polynomial=p))
        exact_q = Q(7, 10) - Q(3, 5) + Q(2, 3)
        cert = ir.Certificate(target, (cell(0, 1, p, 0),),
                              ir.Totals((exact_q,), exact_q, Q(0), interval(exact_q, exact_q)))
        self.assertTrue(ir.verify(ir.Request(target), cert).accepted)
        cert = replace(cert, cells=(cell(0, 1, p - self.x ** 2, 1),),
                       claimed=ir.Totals((exact_q - Q(1, 3),), exact_q - Q(1, 3), Q(1),
                                         interval(exact_q - Q(4, 3), exact_q + Q(2, 3))))
        self.assertTrue(ir.verify(ir.Request(target), cert).accepted)

    def test_every_unsupported_proof_is_rejected_even_when_delta_is_valid(self):
        for form in ("endpoint-samples/v1", "finite-samples/v1", "SOS/v1", "Taylor/v1",
                     "interval-extension/v1", "native-float/v1", "quadratic-extrema/v2"):
            with self.subTest(form=form):
                c = replace(self.coarse.cells[0], proof_form=form)
                self.reject(replace(self.coarse, cells=(c,)), "UNSUPPORTED_PROOF_FORM")

    def test_negative_delta_is_not_cancelled_by_aggregation(self):
        cells = (cell(0, Q(1, 2), self.x ** 2, -1), cell(Q(1, 2), 1, self.x ** 2, 2))
        actual = ir.recompute_totals(cells)
        self.assertGreater(actual.error, 0)
        self.reject(replace(self.coarse, cells=cells, claimed=actual), "NEGATIVE_DELTA")

    def test_tiny_invalid_bound_cannot_disappear_through_float_conversion(self):
        delta = Q(1, 4) - Q(1, 10**20)
        self.assertEqual(float(delta), float(Q(1, 4)))
        cells = (replace(self.coarse.cells[0], delta=delta),)
        self.reject(replace(self.coarse, cells=cells, claimed=ir.recompute_totals(cells)), "LOCAL_BOUND_FALSE")

    def test_smaller_proof_region_rejected(self):
        c = replace(self.coarse.cells[0], delta=Q(0), proof_interval=interval(0, 0))
        self.reject(replace(self.coarse, cells=(c,)), "LOCAL_DOMAIN_MISMATCH")

    def test_relabelled_smaller_region_is_rechecked_on_actual_cell(self):
        c = replace(self.coarse.cells[0], delta=Q(0), proof_interval=interval(0, 1))
        self.reject(replace(self.coarse, cells=(c,)), "LOCAL_BOUND_FALSE")

    def test_partition_gaps_overlaps_order_and_missing_endpoints(self):
        cases = (
            (((0, Q(1, 3)), (Q(1, 2), 1)), "PARTITION_GAP"),
            (((0, Q(3, 4)), (Q(1, 2), 1)), "PARTITION_OVERLAP_OR_ORDER"),
            (((Q(1, 2), 1), (0, Q(1, 2))), "PARTITION_GAP"),
            (((Q(1, 4), 1),), "PARTITION_GAP"),
            (((0, Q(3, 4)),), "PARTITION_END_MISMATCH"),
            (((-1, 1),), "PARTITION_OVERLAP_OR_ORDER"),
            (((0, 2),), "PARTITION_END_MISMATCH"),
            (((0, 1), (0, 1)), "PARTITION_OVERLAP_OR_ORDER"),
        )
        for endpoints, code in cases:
            with self.subTest(endpoints=endpoints):
                cells = tuple(cell(a, b, self.x ** 2, 0) for a, b in endpoints)
                # All local bounds and totals are valid: coverage still has to fail.
                report = self.reject(replace(self.coarse, cells=cells, claimed=ir.recompute_totals(cells)), code)
                self.assertEqual({c.code for c in report.checks if c.name.startswith("local_error")}, {"OK"})

    def test_empty_partition_for_positive_length_rejected(self):
        self.reject(replace(self.coarse, cells=(), claimed=ir.recompute_totals(())), "EMPTY_PARTITION")

    def test_zero_length_target_has_only_empty_partition_and_zero_totals(self):
        request, certificate = self.examples["zero_length"]
        report = ir.verify(request, certificate)
        self.assertTrue(report.accepted)
        self.assertEqual(report.goal_status, "GoalMet")
        self.assertEqual(report.artifact.totals, ir.Totals((), Q(0), Q(0), interval(0, 0)))
        c = cell(Q(3, 7), Q(3, 7), self.x ** 2, 0)
        self.reject(replace(certificate, cells=(c,)), "NONEMPTY_ZERO_PARTITION", request)
        self.reject(replace(certificate, claimed=replace(certificate.claimed, q=Q(1))), "Q_MISMATCH", request)
        self.reject(replace(certificate, claimed=replace(certificate.claimed, error=Q(1))),
                    "ERROR_MISMATCH", request)
        self.reject(replace(certificate, claimed=replace(certificate.claimed, enclosure=interval(-1, 1))),
                    "ENCLOSURE_MISMATCH", request)

    def test_zero_length_cell_in_positive_partition_rejected(self):
        cells = (cell(0, 0, self.x ** 2, 0), cell(0, 1, self.x ** 2, 0))
        self.reject(replace(self.coarse, cells=cells, claimed=ir.recompute_totals(cells)), "NONPOSITIVE_CELL")

    def test_reversed_target_is_not_silently_reoriented(self):
        target = replace(self.target, interval=interval(1, 0))
        report = self.reject(replace(self.coarse, target=target), "REVERSED_INTERVAL", ir.Request(target))
        self.assertIsNone(report.recomputed)

    def test_reversed_cell_does_not_receive_totals_or_acceptance(self):
        report = self.reject(replace(self.coarse, cells=(cell(1, 0, self.x, Q(1, 4)),)), "NONPOSITIVE_CELL")
        self.assertIsNone(report.recomputed)
        self.assertIn("REVERSED_CELL", failures(report))

    def test_shared_endpoints_and_certificate_preserving_subdivision(self):
        cells = tuple(cell(a, b, self.x, Q(1, 4)) for a, b in
                      ((0, Q(1, 7)), (Q(1, 7), Q(2, 3)), (Q(2, 3), 1)))
        cert = replace(self.coarse, cells=cells, claimed=ir.recompute_totals(cells))
        report = ir.verify(self.request, cert)
        self.assertTrue(report.accepted)
        self.assertEqual((report.artifact.totals.q, report.artifact.totals.error,
                          report.artifact.totals.enclosure),
                         (Q(1, 2), Q(1, 4), self.coarse.claimed.enclosure))
        self.assertEqual(report.goal_status, "GoalUnmet")

    def test_unequal_lengths_weight_local_errors(self):
        zero = Poly.constant(0, 1)
        target = replace(self.target, interval=interval(-1, 2),
                         function=replace(self.target.function, polynomial=zero))
        cells = (cell(-1, 0, zero, 1), cell(0, 2, zero, 3))
        cert = ir.Certificate(target, cells, ir.Totals((Q(0), Q(0)), Q(0), Q(7), interval(-7, 7)))
        self.assertTrue(ir.verify(ir.Request(target), cert).accepted)
        self.reject(replace(cert, claimed=replace(cert.claimed, error=Q(4))), "ERROR_MISMATCH", ir.Request(target))

    def test_each_claimed_total_checked_independently(self):
        cases = (("local_integrals", (Q(7),), "LOCAL_INTEGRALS_MISMATCH"),
                 ("q", Q(7), "Q_MISMATCH"), ("error", Q(7), "ERROR_MISMATCH"),
                 ("enclosure", interval(Q(1, 3), Q(1, 3)), "ENCLOSURE_MISMATCH"))
        for field, value, code in cases:
            with self.subTest(field=field):
                forged = replace(self.coarse.claimed, **{field: value})
                report = self.reject(replace(self.coarse, claimed=forged), code)
                self.assertEqual(failures(report), {code})

    def test_compensating_local_integral_forgery_preserves_sum_but_fails(self):
        forged = replace(self.refined.claimed, local_integrals=(Q(5, 16), Q(1, 16)))
        report = self.reject(replace(self.refined, claimed=forged), "LOCAL_INTEGRALS_MISMATCH")
        self.assertEqual(failures(report), {"LOCAL_INTEGRALS_MISMATCH"})

    def test_self_consistent_forged_totals_cannot_drive_verifier(self):
        fake = ir.Totals((Q(0),), Q(0), Q(0), interval(0, 0))
        report = self.reject(replace(self.coarse, claimed=fake), "Q_MISMATCH")
        self.assertEqual(failures(report),
                         {"LOCAL_INTEGRALS_MISMATCH", "Q_MISMATCH", "ERROR_MISMATCH", "ENCLOSURE_MISMATCH"})

    def test_changed_local_polynomial_and_delta_are_recomputed(self):
        cases = ((replace(self.coarse.cells[0], polynomial=self.x + 1), "LOCAL_BOUND_FALSE"),
                 (replace(self.coarse.cells[0], delta=Q(1, 3)), "ERROR_MISMATCH"))
        for c, code in cases:
            with self.subTest(code=code):
                self.reject(replace(self.coarse, cells=(c,)), code)

    def test_full_target_binding_includes_definition_not_only_tags(self):
        targets = [replace(self.target, **{field: value}) for field, value in
                   (("environment_id", "other"), ("domain_id", "other"), ("variable_id", "y"),
                    ("interval", interval(0, 2)), ("measure", "counting"), ("scalar_profile", "Float64"))]
        targets += [replace(self.target, function=replace(self.target.function, **changes)) for changes in
                    ({"revision": "2"}, {"function_id": "other"}, {"polynomial": self.x ** 2 + 1})]
        for target in targets:
            with self.subTest(target=target):
                report = self.reject(replace(self.coarse, target=target), "TARGET_MISMATCH")
                self.assertIsNone(report.recomputed)
                self.assertTrue(all(c.status == "not_checked" for c in report.checks[3:]))
                self.reject(self.coarse, "TARGET_MISMATCH", replace(self.request, target=target))

    def test_coordinated_measure_or_scalar_relabel_is_still_unsupported(self):
        for field, value in (("measure", "counting"), ("measure", "weighted-lebesgue"),
                             ("scalar_profile", "QQ-to-C"), ("scalar_profile", "Float64")):
            with self.subTest(field=field, value=value):
                target = replace(self.target, **{field: value})
                self.reject(replace(self.coarse, target=target), "UNSUPPORTED_PROFILE", ir.Request(target))

    def test_returned_artifact_retains_exact_request_cells_and_recomputed_data(self):
        report = ir.verify(self.request, self.refined)
        self.assertIs(report.artifact.target, self.request.target)
        self.assertIs(report.artifact.cells, self.refined.cells)
        self.assertIs(report.artifact.totals, report.recomputed)
        self.assertIsNot(report.artifact.totals, self.refined.claimed)


class ArithmeticTests(unittest.TestCase):
    def setUp(self):
        self.x = Poly.variable(0, 1)

    def test_reuses_shared_poly_and_requires_explicit_arity_one(self):
        self.assertIs(ir.Poly, Poly)
        for p in (Poly.constant(0), Poly.variable(0, 2), Poly.constant(1, 0)):
            with self.subTest(arity=p.arity), self.assertRaises(ir.Invalid):
                ir.integrate_polynomial(p, interval(0, 1))

    def test_exact_integration_constants_high_degree_and_negative_endpoints(self):
        p = Q(2, 7) * self.x ** 5 - 3 * self.x + Q(5, 11)
        # [x^6/21 - 3*x^2/2 + 5*x/11]_-2^1 = -3 + 9/2 + 15/11.
        self.assertEqual(ir.integrate_polynomial(p, interval(-2, 1)), Q(63, 22))
        for constant in (Q(0), Q(-5, 3), Q(7, 11)):
            self.assertEqual(ir.integrate_polynomial(Poly.constant(constant, 1), interval(-2, 1)), 3 * constant)
        self.assertEqual(ir.integrate_polynomial(self.x ** 20, interval(0, 1)), Q(1, 21))

    def test_primitive_derivative_and_finite_additivity(self):
        for coefficients in itertools.product((-2, 0, Q(1, 3)), repeat=4):
            p = Poly.from_terms((((i,), c) for i, c in enumerate(coefficients)), arity=1)
            self.assertEqual(ir.antiderivative(p).derivative(0), p)
            self.assertEqual(ir.integrate_polynomial(p, interval(-1, 2)),
                             ir.integrate_polynomial(p, interval(-1, Q(2, 3)))
                             + ir.integrate_polynomial(p, interval(Q(2, 3), 2)))

    def test_zero_length_and_reversed_polynomial_integrals(self):
        self.assertEqual(ir.integrate_polynomial(self.x ** 12 + 1, interval(3, 3)), Q(0))
        with self.assertRaises(ir.Invalid):
            ir.integrate_polynomial(self.x, interval(3, 2))

    def test_extrema_constant_linear_both_curvatures_and_vertex_outside(self):
        cases = ((Poly.constant(-3, 1), interval(0, 1), ((Q(0), Q(-3)), (Q(1), Q(-3)))),
                 (2 * self.x - 1, interval(0, 1), ((Q(0), Q(-1)), (Q(1), Q(1)))),
                 (self.x ** 2 - self.x, interval(0, 1), ((Q(0), Q(0)), (Q(1, 2), Q(-1, 4)), (Q(1), Q(0)))),
                 (-self.x ** 2 + self.x, interval(0, 1), ((Q(0), Q(0)), (Q(1, 2), Q(1, 4)), (Q(1), Q(0)))),
                 (self.x ** 2 + self.x, interval(0, 1), ((Q(0), Q(0)), (Q(1), Q(2)))),
                 (self.x ** 2, interval(0, 1), ((Q(0), Q(0)), (Q(1), Q(1)))))
        for p, domain, expected in cases:
            with self.subTest(p=p):
                self.assertEqual(ir.quadratic_extrema(p, domain), expected)

    def test_signed_bound_requires_both_sides(self):
        target = ir.PolynomialFunction("zero", "1", Poly.constant(0, 1))
        for p in (self.x - self.x ** 2, self.x ** 2 - self.x):
            with self.subTest(p=p):
                self.assertEqual(ir.check_local_error(target, cell(0, 1, p, Q(1, 8))).code, "LOCAL_BOUND_FALSE")
                self.assertEqual(ir.check_local_error(target, cell(0, 1, p, Q(1, 4))).status, "pass")

    def test_generated_quadratic_enclosures_against_independent_simpson_identity(self):
        # Simpson is exact for these quadratics, used ONLY as a test oracle.
        a, b = Q(-1, 3), Q(5, 4)
        bound_x = max(abs(a), abs(b))
        for c0, c1, c2 in itertools.product((-2, 0, 1), repeat=3):
            p = c0 + c1 * self.x + c2 * self.x ** 2
            delta = abs(c0) + abs(c1) * bound_x + abs(c2) * bound_x ** 2
            f = ir.PolynomialFunction("family", "1", p)
            target = ir.Target("env", "R", "x", f, interval(a, b))
            error = (b - a) * delta
            cert = ir.Certificate(target, (cell(a, b, Poly.constant(0, 1), delta),),
                                  ir.Totals((Q(0),), Q(0), error, interval(-error, error)))
            report = ir.verify(ir.Request(target), cert)
            self.assertTrue(report.accepted)
            def value(x):
                return c0 + c1 * x + c2 * x * x
            integral = (b - a) * (value(a) + 4 * value((a + b) / 2) + value(b)) / 6
            self.assertLessEqual(report.artifact.totals.enclosure.lower, integral)
            self.assertLessEqual(integral, report.artifact.totals.enclosure.upper)


class InputTests(unittest.TestCase):
    def setUp(self):
        self.request, self.cert = examples()["coarse_goal_unmet"]

    def test_nonpolynomial_functions_cannot_gain_integrability_from_tags(self):
        for value in (lambda x: x, "continuous", {"expression": "sin(x)", "continuous": True},
                      {"kind": "polynomial", "integrable": True}):
            with self.subTest(value=value), self.assertRaises(ir.Invalid):
                ir.PolynomialFunction("f", "1", value)
        for tag in ("continuous", "integrable", "integral_value", "kind"):
            raw = ir.request_data(self.request)
            raw["target"]["function"][tag] = True
            with self.subTest(tag=tag), self.assertRaises(ir.Invalid):
                ir.request_from_data(raw)
        raw = ir.request_data(self.request)
        del raw["target"]["function"]["polynomial"]
        with self.assertRaises(ir.Invalid):
            ir.request_from_data(raw)

    def test_zero_interval_does_not_bypass_function_or_profile_validation(self):
        request, cert = examples()["zero_length"]
        target = replace(request.target, measure="Dirac")
        self.assertFalse(ir.verify(ir.Request(target), replace(cert, target=target)).accepted)
        raw = ir.request_data(request)
        raw["target"]["function"]["polynomial"] = "nonpolynomial but continuous"
        with self.assertRaises(ir.Invalid):
            ir.request_from_data(raw)

    def test_round_trip_preserves_binding_and_artifact(self):
        for request, cert in examples().values():
            decoded_request = ir.request_from_data(json.loads(json.dumps(ir.request_data(request))))
            decoded_cert = ir.certificate_from_data(json.loads(json.dumps(ir.certificate_data(cert))))
            self.assertEqual((decoded_request, decoded_cert), (request, cert))
            self.assertEqual(ir.verify(decoded_request, decoded_cert), ir.verify(request, cert))
            json.dumps(ir.report_data(ir.verify(request, cert)))

    def test_invalid_goals_exact_fields_and_immutable_cells(self):
        for radius in (Q(0), Q(-1), 0.01, True, 1):
            with self.subTest(radius=radius), self.assertRaises(ir.Invalid):
                replace(self.request, absolute_radius=radius)
        for value in (0.0, True, 1):
            with self.subTest(value=value), self.assertRaises(ir.Invalid):
                replace(self.cert.cells[0], delta=value)
        with self.assertRaises(ir.Invalid):
            replace(self.cert, cells=list(self.cert.cells))

    def test_strict_wire_rejects_extra_missing_and_malformed_fields(self):
        raw = ir.certificate_data(self.cert)
        mutations = []
        for field in ("accepted", "goal_status", "native_success", "continuity"):
            value = copy.deepcopy(raw)
            value[field] = True
            mutations.append(value)
        for delta in (0.25, [True, 4], [1, 0], [1, -4], [1.0, 4]):
            value = copy.deepcopy(raw)
            value["cells"][0]["delta"] = delta
            mutations.append(value)
        for powers in ([-1], [True], [1, 0], [0.5]):
            value = copy.deepcopy(raw)
            value["cells"][0]["polynomial"][0]["powers"] = powers
            mutations.append(value)
        for field in ("proof_form", "proof_interval"):
            value = copy.deepcopy(raw)
            del value["cells"][0][field]
            mutations.append(value)
        duplicate = copy.deepcopy(raw)
        duplicate["cells"][0]["polynomial"] *= 2
        mutations.append(duplicate)
        extra_sample = copy.deepcopy(raw)
        extra_sample["cells"][0]["samples"] = [[0, 0], [1, 0]]
        mutations.append(extra_sample)
        for index, value in enumerate(mutations):
            with self.subTest(index=index), self.assertRaises(ir.Invalid):
                ir.certificate_from_data(value)

    def test_duplicate_keys_float_literals_and_nonfinite_json_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "input.json"
            for text in ('{"x":1,"x":2}', '[0.0]', '[NaN]', '[Infinity]', '[-Infinity]'):
                path.write_text(text)
                with self.subTest(text=text), self.assertRaises(ir.Invalid):
                    ir.load_json(path)

    def test_cli_exit_codes_keep_goal_unmet_distinct_from_rejection(self):
        with tempfile.TemporaryDirectory() as directory:
            request_path, cert_path = Path(directory) / "request.json", Path(directory) / "cert.json"
            for name, status, code in (("coarse_goal_unmet", "accepted_reference", 0),
                                       ("refined_goal_met", "accepted_reference", 0),
                                       ("false_delta", "rejected_reference", 1),
                                       ("endpoint_only", "rejected_reference", 1)):
                request, cert = examples()[name]
                request_path.write_text(json.dumps(ir.request_data(request)))
                cert_path.write_text(json.dumps(ir.certificate_data(cert)))
                result = subprocess.run([sys.executable, str(ROOT / "scripts/integral_reference.py"),
                                         str(request_path), str(cert_path)], capture_output=True, text=True)
                with self.subTest(name=name):
                    self.assertEqual(result.returncode, code, result.stderr)
                    output = json.loads(result.stdout)
                    self.assertEqual(output["status"], status)
                    self.assertEqual(output["artifact"] is not None, code == 0)
                    if name == "coarse_goal_unmet":
                        self.assertEqual(output["goal_status"], "GoalUnmet")
            cert_path.write_text('{"continuous": true}')
            result = subprocess.run([sys.executable, str(ROOT / "scripts/integral_reference.py"),
                                     str(request_path), str(cert_path)], capture_output=True, text=True)
            self.assertEqual(result.returncode, 2)
            self.assertIsNone(json.loads(result.stdout)["artifact"])


if __name__ == "__main__":
    unittest.main()
