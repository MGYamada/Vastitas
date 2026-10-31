import itertools
import json
from pathlib import Path
import subprocess
import sys
import unittest
from dataclasses import replace
from fractions import Fraction as Q
from unittest.mock import patch

import variational_reference as vr
from rational_polynomial_calculus import evaluate, substitute
from rational_polynomial_reference import Invalid, Poly


t, q, v = (Poly.variable(i, arity=3) for i in range(3))
T = vr.T
FIXED_ETA = T * (1 + -T)


def subject(expression=q * v, path=T, variation=T, mode="unrestricted"):
    return vr.Subject(vr.Lagrangian("example:L", "1", ("t", "q", "v"), expression),
                      path, variation, mode)


class VariationalTests(unittest.TestCase):
    def reject(self, code, operation):
        with self.assertRaises(Invalid) as caught:
            operation()
        self.assertEqual(caught.exception.code, code)

    def checked(self, request):
        result = vr.verify(request, vr.propose(request))
        self.assertIs(result.subject, request)
        self.assertEqual(result.direct.first_variation, result.parts.first_variation)
        return result

    def test_total_derivative_zero_bulk_nonzero_boundary(self):
        result = self.checked(subject())
        self.assertEqual(result.parts.euler_lagrange, Poly.constant(0, 1))
        self.assertEqual(result.parts.bulk, 0)
        self.assertEqual(result.parts.boundary_at_endpoints, (0, 1))
        self.assertEqual(result.parts.boundary, 1)
        self.assertEqual(result.direct.first_variation, 1)
        epsilon = Poly.variable(0, arity=1)
        self.assertEqual(result.direct.action_in_epsilon,
                         Q(1, 2) * (1 + epsilon) ** 2)

    def test_total_derivative_fixed_endpoints_recomputed(self):
        request = subject(variation=FIXED_ETA, mode="fixed_endpoints")
        result = self.checked(request)
        self.assertEqual(result.variation_at_endpoints, (0, 0))
        self.assertEqual(result.parts.boundary_at_endpoints, (0, 0))
        self.assertEqual(result.direct.first_variation, 0)
        self.assertEqual(result.parts.boundary, 0)
        # Fixed endpoint variations do not require the path endpoints to be zero.
        self.assertEqual(evaluate(request.path, (Q(1),)), 1)

    def test_harmonic_example_and_whole_action(self):
        result = self.checked(subject(Q(1, 2) * (v ** 2 - q ** 2),
                                      variation=FIXED_ETA, mode="fixed_endpoints"))
        self.assertEqual(result.parts.euler_lagrange, -T)
        self.assertEqual(result.parts.bulk, Q(-1, 12))
        self.assertEqual(result.parts.boundary, 0)
        epsilon = Poly.variable(0, arity=1)
        self.assertEqual(result.direct.action_in_epsilon,
                         Q(1, 3) + Q(-1, 12) * epsilon + Q(3, 20) * epsilon ** 2)

    def test_both_boundary_endpoints_and_orientation(self):
        result = self.checked(subject(path=T + 2, variation=Poly.constant(1, 1)))
        self.assertEqual(result.parts.boundary_at_endpoints, (2, 3))
        self.assertEqual(result.parts.boundary, 1)

    def test_explicit_time_derivative_is_retained(self):
        result = self.checked(subject(t * v, variation=FIXED_ETA, mode="fixed_endpoints"))
        self.assertEqual(result.parts.euler_lagrange, Poly.constant(-1, 1))
        self.assertEqual(result.parts.bulk, Q(-1, 6))

    def test_acceleration_term_is_retained(self):
        result = self.checked(subject(Q(1, 2) * v ** 2, path=T ** 2,
                                      variation=FIXED_ETA, mode="fixed_endpoints"))
        self.assertEqual(result.parts.euler_lagrange, Poly.constant(-2, 1))
        self.assertEqual(result.direct.first_variation, Q(-1, 3))

    def test_constant_linear_and_zero_variations(self):
        for expression, expected in ((Poly.constant(7, 3), Q(0)), (q, Q(1, 2)), (v, Q(1))):
            self.assertEqual(self.checked(subject(expression)).direct.first_variation, expected)
        result = self.checked(subject(t * q ** 3 * v ** 2, variation=Poly.constant(0, 1),
                                      mode="fixed_endpoints"))
        self.assertEqual(result.direct.first_variation, 0)

    def test_exact_tiny_boundary_is_never_rounded_away(self):
        tiny = Q(1, 10**30)
        result = self.checked(subject(variation=tiny * T))
        self.assertEqual(result.parts.boundary, tiny)

    def test_finite_nonlinear_family_two_independent_routes(self):
        lagrangians = (q * v, t * v, Q(1, 2) * (v ** 2 - q ** 2),
                       t ** 2 * q ** 3 * v ** 2 + Q(2, 7) * q ** 5 + v ** 3,
                       q * v ** 2 + Q(-3, 11) * t * q ** 2 * v + t ** 4)
        paths = (T, T + 2, T ** 2, Q(1, 3) + Q(-2, 5) * T + T ** 3)
        variations = (T, Poly.constant(1, 1), FIXED_ETA, Q(7, 13) * T ** 3 + -2)
        count = 0
        for expression, path, eta in itertools.product(lagrangians, paths, variations):
            with self.subTest(expression=expression, path=path, eta=eta):
                self.checked(subject(expression, path, eta))
                count += 1
        self.assertEqual(count, 80)

    def test_first_variation_is_rational_linear_in_eta(self):
        request = subject(t * q ** 3 * v ** 2 + v ** 3, path=T ** 2 + 1)
        alpha, beta = Q(-2, 7), Q(5, 11)
        eta, xi = T ** 2 + 1, FIXED_ETA
        for route in (vr.direct_first_variation, vr.bulk_boundary_first_variation):
            actual = route(replace(request, variation=alpha * eta + beta * xi)).first_variation
            expected = (alpha * route(replace(request, variation=eta)).first_variation
                        + beta * route(replace(request, variation=xi)).first_variation)
            self.assertEqual(actual, expected)

    def test_total_derivative_family_uses_endpoint_action(self):
        for potential in (q ** 2, t * q ** 3 + Q(2, 7) * q, t ** 2 * q ** 2 + t ** 3):
            expression = potential.derivative(0) + potential.derivative(1) * v
            for path, eta in ((T + 2, T + 1), (T ** 3, FIXED_ETA)):
                result = self.checked(subject(expression, path, eta))
                def endpoint(x):
                    return (evaluate(potential.derivative(1), (x, evaluate(path, (x,)), Q(0)))
                            * evaluate(eta, (x,)))
                self.assertEqual(result.parts.euler_lagrange, Poly.constant(0, 1))
                self.assertEqual(result.direct.first_variation, endpoint(Q(1)) - endpoint(Q(0)))

    def test_variable_permutations_work_when_expression_is_reindexed(self):
        request = subject(t * q ** 2 * v + Q(2, 3) * v ** 2, path=T ** 2, variation=T + 1)
        expected = self.checked(request).parts
        for order in itertools.permutations(("t", "q", "v")):
            coordinates = tuple(Poly.variable(order.index(name), arity=3)
                                for name in ("t", "q", "v"))
            lagrangian = replace(request.lagrangian, variables=order,
                                 expression=substitute(request.lagrangian.expression, coordinates))
            self.assertEqual(self.checked(replace(request, lagrangian=lagrangian)).parts, expected)

    def test_direct_and_bulk_boundary_routes_do_not_call_each_other(self):
        request = subject()
        with patch.object(vr, "bulk_boundary_first_variation", side_effect=AssertionError("wrong route")):
            self.assertEqual(vr.direct_first_variation(request).first_variation, 1)
        with patch.object(vr, "direct_first_variation", side_effect=AssertionError("wrong route")):
            self.assertEqual(vr.bulk_boundary_first_variation(request).first_variation, 1)

    def test_missing_boundary_and_wrong_boundary_sign_rejected(self):
        request = subject()
        evidence = vr.propose(request)
        for bad_boundary in (Q(0), Q(-1)):
            parts = replace(evidence.parts, boundary=bad_boundary, first_variation=bad_boundary)
            self.reject("BOUNDARY_MISMATCH", lambda: vr.verify(request, replace(evidence, parts=parts)))

    def test_lower_endpoint_sign_and_endpoint_swap_rejected(self):
        request = subject(path=T + 2, variation=Poly.constant(1, 1))
        evidence = vr.propose(request)
        parts = replace(evidence.parts, boundary=Q(5), first_variation=Q(5))
        self.reject("BOUNDARY_MISMATCH", lambda: vr.verify(request, replace(evidence, parts=parts)))
        parts = replace(evidence.parts, boundary_at_endpoints=(Q(3), Q(2)))
        self.reject("BOUNDARY_ENDPOINT_MISMATCH", lambda: vr.verify(request, replace(evidence, parts=parts)))

    def test_wrong_el_sign_and_individually_forged_totals_rejected(self):
        request = subject(Q(1, 2) * (v ** 2 - q ** 2), variation=FIXED_ETA)
        evidence = vr.propose(request)
        mutations = (
            ("EULER_LAGRANGE_MISMATCH", replace(evidence.parts, euler_lagrange=T)),
            ("BULK_MISMATCH", replace(evidence.parts, bulk=Q(1, 12))),
            ("FIRST_VARIATION_MISMATCH", replace(evidence.parts, first_variation=Q(1, 12))),
            # An unchanged total cannot hide compensating bulk/boundary errors.
            ("BULK_MISMATCH", replace(evidence.parts, bulk=evidence.parts.bulk + 1,
                                      boundary=evidence.parts.boundary - 1)),
        )
        for code, parts in mutations:
            self.reject(code, lambda: vr.verify(request, replace(evidence, parts=parts)))

    def test_direct_route_detects_an_incorrect_recomputed_decomposition(self):
        request = subject()
        evidence = vr.propose(request)
        wrong = replace(evidence.parts, boundary=Q(0), first_variation=Q(0))
        with patch.object(vr, "bulk_boundary_first_variation", return_value=wrong):
            self.reject("VARIATION_IDENTITY_MISMATCH",
                        lambda: vr.verify(request, replace(evidence, parts=wrong)))

    def test_wrong_el_with_the_same_integrated_pairing_is_rejected(self):
        request = subject()
        evidence = vr.propose(request)
        # eta=t and integral_0^1 (3t-2)*t = 0, just like the true zero EL.
        # Equality of scalar totals cannot establish the entire EL polynomial.
        parts = replace(evidence.parts, euler_lagrange=3 * T + -2)
        self.reject("EULER_LAGRANGE_MISMATCH", lambda: vr.verify(request, replace(evidence, parts=parts)))

    def test_fixed_endpoint_tag_rejected_at_both_endpoints(self):
        for eta in (T, 1 + -T, Poly.constant(1, 1), T * Q(1, 10**30)):
            request = subject(variation=eta, mode="fixed_endpoints")
            for operation in (vr.check_admissibility, vr.direct_first_variation,
                              vr.bulk_boundary_first_variation, vr.propose):
                self.reject("INADMISSIBLE_VARIATION", lambda: operation(request))

    def test_zero_boundary_does_not_establish_fixed_endpoint_admissibility(self):
        request = subject(path=Poly.constant(1, 1), variation=Poly.constant(1, 1))
        self.assertEqual(self.checked(request).parts.boundary, 0)
        fixed = replace(request, admissible_variations="fixed_endpoints")
        forged = replace(vr.propose(request), subject=fixed, variation_at_endpoints=(Q(0), Q(0)))
        self.reject("INADMISSIBLE_VARIATION", lambda: vr.verify(fixed, forged))

    def test_forged_endpoint_values_and_variation_space_replay_rejected(self):
        request = subject()
        evidence = vr.propose(request)
        self.reject("ENDPOINT_EVIDENCE_MISMATCH", lambda: vr.verify(request,
                    replace(evidence, variation_at_endpoints=(Q(0), Q(0)))))
        request = subject(variation=FIXED_ETA)
        evidence = vr.propose(request)
        self.reject("EVIDENCE_SUBJECT_MISMATCH", lambda: vr.verify(
                    replace(request, admissible_variations="fixed_endpoints"), evidence))

    def test_lagrangian_identity_revision_expression_and_order_replay_rejected(self):
        request = subject()
        evidence = vr.propose(request)
        for lagrangian in (replace(request.lagrangian, definition_id="twin:L"),
                           replace(request.lagrangian, revision="2"),
                           replace(request.lagrangian, expression=q * v + 1),
                           replace(request.lagrangian, variables=("t", "v", "q"))):
            # Several mutations retain exactly the same first variation.
            changed = replace(request, lagrangian=lagrangian)
            self.reject("EVIDENCE_SUBJECT_MISMATCH", lambda: vr.verify(changed, evidence))

    def test_interval_replay_and_relabelled_unsupported_interval_rejected(self):
        request = subject()
        evidence = vr.propose(request)
        for interval in ((Q(0), Q(2)), (Q(1), Q(0)), (Q(0), Q(1, 2)), (Q(0), Q(0))):
            changed = replace(request, interval=interval)
            self.reject("EVIDENCE_SUBJECT_MISMATCH", lambda: vr.verify(changed, evidence))
            self.reject("UNSUPPORTED_PROFILE", lambda: vr.verify(changed, replace(evidence, subject=changed)))

    def test_path_variation_and_environment_replay_rejected(self):
        request = subject()
        evidence = vr.propose(request)
        for change in (dict(path=T + 1), dict(variation=T ** 2),
                       dict(environment_id="other-env"), dict(configuration_id="other-space"),
                       dict(scalar_profile="complex"), dict(ruleset="future-rule")):
            self.reject("EVIDENCE_SUBJECT_MISMATCH", lambda: vr.verify(replace(request, **change), evidence))
        # Relabelling with an eta that has the same endpoint traces still needs
        # recomputation of its interior contribution, not just endpoint checks.
        request = subject(q, variation=FIXED_ETA)
        evidence = vr.propose(request)
        changed = replace(request, variation=2 * FIXED_ETA)
        self.reject("BULK_MISMATCH", lambda: vr.verify(changed, replace(evidence, subject=changed)))

    def test_malformed_inexact_or_unsupported_inputs_rejected(self):
        request = subject()
        evidence = vr.propose(request)
        for bad in (0.0, True, 0):
            self.reject("INEXACT_INPUT", lambda: replace(evidence.parts, boundary=bad))
            self.reject("INEXACT_INPUT", lambda: replace(request, interval=(bad, Q(1))))
        self.reject("INVALID_POLYNOMIAL", lambda: replace(request, path=Poly.constant(0, 2)))
        self.reject("INVALID_POLYNOMIAL", lambda: replace(request.lagrangian, expression=Poly.constant(0, 4)))
        self.reject("UNSUPPORTED_VARIABLES", lambda: replace(request.lagrangian, variables=("t", "q", "q")))
        self.reject("UNSUPPORTED_VARIATIONS", lambda: replace(request, admissible_variations="compact_support"))
        self.reject("INVALID_SCHEMA", lambda: vr.verify(request, None))
        self.reject("INVALID_SCHEMA", lambda: vr.verify(request, {"verified": True}))

    def test_demo_runs_without_optional_packages(self):
        demo = Path(__file__).with_name("demo_variational_reference.py")
        completed = subprocess.run([sys.executable, "-S", str(demo)],
                                   check=True, text=True, capture_output=True)
        report = json.loads(completed.stdout)
        self.assertEqual([case["epsilon_coefficient"] for case in report["positive"]],
                         ["1", "0", "-1/12"])
        self.assertEqual([case["bulk_plus_boundary"] for case in report["positive"]],
                         ["1", "0", "-1/12"])
        self.assertEqual([case["boundary"] for case in report["positive"]], ["1", "0", "0"])
        self.assertEqual([case["code"] for case in report["negative"]],
                         ["BOUNDARY_MISMATCH", "BOUNDARY_MISMATCH", "INADMISSIBLE_VARIATION",
                          "EVIDENCE_SUBJECT_MISMATCH", "EVIDENCE_SUBJECT_MISMATCH",
                          "EVIDENCE_SUBJECT_MISMATCH"])


if __name__ == "__main__":
    unittest.main()
