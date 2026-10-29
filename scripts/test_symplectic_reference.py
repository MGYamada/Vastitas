"""Exact semantic, mutation and wire regressions; no CAS is trusted by acceptance."""

import copy
import itertools
import json
import subprocess
import sys
import tempfile
import unittest
from dataclasses import fields, replace
from fractions import Fraction
from pathlib import Path

import symplectic_reference as sr
from demo_symplectic_reference import examples


ROOT = Path(__file__).resolve().parents[1]


def determinant(value):
    """Test-only Leibniz formula, never used by the verifier."""
    result = sr.ZERO
    for permutation in itertools.permutations(range(len(value))):
        inversions = sum(permutation[i] > permutation[j]
                         for i, j in itertools.combinations(range(len(value)), 2))
        term = sr.Poly.constant((-1) ** inversions)
        for i, j in enumerate(permutation):
            term = term * value[i][j]
        result = result + term
    return result


def substitute(poly, coordinates):
    """Test-only polynomial substitution (including symbolic hyperplanes)."""
    result = sr.ZERO
    for powers, coefficient in poly.terms:
        term = sr.Poly.constant(coefficient)
        for coordinate, power in zip(coordinates, powers):
            term = term * coordinate ** power
        result = result + term
    return result


def evaluate_matrix(value, coordinates):
    return tuple(tuple(substitute(p, coordinates) for p in row) for row in value)


def changed_entry(value, i, j, replacement):
    rows = [list(row) for row in value]
    rows[i][j] = replacement
    return sr.matrix(rows)


def codes(report):
    return {check.name: check.code for check in report.checks}


class SymplecticTests(unittest.TestCase):
    def setUp(self):
        self.cases = examples()
        self.good, self.cert = self.cases["good_U"]
        self.bad, self.bad_cert = self.cases["bad_U"]
        self.x = tuple(sr.Poly.variable(i) for i in range(4))
        self.h = sr.ONE + self.x[0]

    def test_good_accepted_on_exact_open(self):
        report = sr.verify(self.good, self.cert)
        self.assertTrue(report.accepted)
        self.assertIs(report.subject, self.good)
        self.assertEqual(set(codes(report).values()), {"OK"})

    def test_bad_fails_only_closedness_with_honest_witness(self):
        report = sr.verify(self.bad, self.bad_cert)
        self.assertFalse(report.accepted)
        self.assertEqual(codes(report), {"binding": "OK", "alternation": "OK",
                                        "exterior_derivative": "NOT_CLOSED", "domain_inverse": "OK"})
        self.assertEqual(sr.exterior_derivative(self.bad.omega),
                         (sr.ZERO, sr.ZERO, sr.ONE, sr.ZERO))

    def test_forged_zero_derivative_not_trusted(self):
        report = sr.verify(*self.cases["bad_forged_closedness"])
        self.assertEqual(codes(report)["exterior_derivative"], "DERIVATIVE_WITNESS_MISMATCH")
        self.assertFalse(report.accepted)

    def test_jacobian_pullback_recovers_cross_term_and_sign(self):
        q1, p1, q2, p2 = self.x
        mapping = (q1, p1, q2, self.h * p2)
        jacobian = tuple(tuple(p.derivative(i) for i in range(4)) for p in mapping)
        standard = sr.matrix([[0, 1, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 1], [0, 0, -1, 0]])
        pullback = sr.multiply(sr.multiply(sr.transpose(jacobian), standard), jacobian)
        self.assertEqual(pullback, self.good.omega)
        self.assertEqual(pullback[0][2], -p2)
        self.assertEqual(determinant(jacobian), self.h)

    def test_determinant_and_origin_do_not_determine_closedness(self):
        self.assertEqual(determinant(self.good.omega), self.h ** 2)
        self.assertEqual(determinant(self.bad.omega), self.h ** 2)
        self.assertEqual(evaluate_matrix(self.good.omega, (sr.ZERO,) * 4),
                         evaluate_matrix(self.bad.omega, (sr.ZERO,) * 4))
        self.assertNotEqual(sr.exterior_derivative(self.good.omega),
                            sr.exterior_derivative(self.bad.omega))

    def test_rank_two_on_entire_hyperplane_not_just_a_sample(self):
        coordinates = (sr.Poly.constant(-1), *self.x[1:])
        for subject in (self.good, self.bad):
            value = evaluate_matrix(subject.omega, coordinates)
            self.assertEqual(determinant(tuple(row[:2] for row in value[:2])), sr.ONE)
            for rows in itertools.combinations(range(4), 3):
                for cols in itertools.combinations(range(4), 3):
                    minor = tuple(tuple(value[i][j] for j in cols) for i in rows)
                    self.assertEqual(determinant(minor), sr.ZERO)

    def test_global_extension_catches_stale_and_relabelled_evidence(self):
        stale = sr.verify(*self.cases["global_stale_evidence"])
        self.assertEqual(codes(stale)["binding"], "SUBJECT_MISMATCH")
        relabelled = sr.verify(*self.cases["global_relabelled_evidence"])
        self.assertEqual(codes(relabelled)["exterior_derivative"], "OK")
        self.assertEqual(codes(relabelled)["domain_inverse"], "DENOMINATOR_NOT_JUSTIFIED")
        self.assertFalse(relabelled.accepted)

    def test_same_determinant_cannot_replay_even_after_relabelling(self):
        stale = sr.verify(*self.cases["same_determinant_replay"])
        self.assertEqual(codes(stale)["binding"], "SUBJECT_MISMATCH")
        relabelled = sr.verify(*self.cases["same_determinant_relabelled"])
        self.assertEqual(codes(relabelled)["exterior_derivative"], "DERIVATIVE_WITNESS_MISMATCH")
        self.assertEqual(codes(relabelled)["domain_inverse"], "INVERSE_IDENTITY_FAILED")

    def test_same_form_id_and_determinant_with_changed_coefficients_rejected(self):
        changed = replace(self.good, omega=self.bad.omega)
        self.assertEqual(changed.form_id, self.good.form_id)
        self.assertEqual(codes(sr.verify(changed, self.cert))["binding"], "SUBJECT_MISMATCH")

    def test_same_determinant_and_closedness_still_do_not_identify_inverse(self):
        negative = sr.matrix([[-p for p in row] for row in self.good.omega])
        self.assertEqual(determinant(negative), determinant(self.good.omega))
        subject = replace(self.good, omega=negative)
        report = sr.verify(subject, replace(self.cert, subject=subject))
        self.assertEqual(codes(report)["exterior_derivative"], "OK")
        self.assertEqual(codes(report)["domain_inverse"], "INVERSE_IDENTITY_FAILED")
        self.assertFalse(report.accepted)

    def test_each_nominal_binding_field_and_revision_is_significant(self):
        for field in fields(sr.Context):
            if field.name in ("scalar_profile", "coordinates"):
                continue
            with self.subTest(field=field.name):
                changed = replace(self.good.context, **{field.name: "other:same-dimension"})
                report = sr.verify(replace(self.good, context=changed), self.cert)
                self.assertEqual(codes(report)["binding"], "SUBJECT_MISMATCH")
        for field in ("form_id", "form_revision"):
            report = sr.verify(replace(self.good, **{field: "changed"}), self.cert)
            self.assertEqual(codes(report)["binding"], "SUBJECT_MISMATCH")

    def test_coordinate_reorder_cannot_replay_certificate(self):
        # Leave q1 in slot zero so the same domain polynomial is still well-formed.
        context = replace(self.good.context, coordinates=("q1", "q2", "p1", "p2"))
        self.assertEqual(codes(sr.verify(replace(self.good, context=context), self.cert))["binding"],
                         "SUBJECT_MISMATCH")

    def test_reordered_coordinates_require_reindexed_generator(self):
        context = replace(self.good.context, coordinates=("p1", "q1", "q2", "p2"))
        with self.assertRaises(sr.Invalid) as caught:
            replace(self.good, context=context)
        self.assertEqual(caught.exception.code, "UNSUPPORTED_DOMAIN")

    def test_non_alternating_invertible_matrix_is_not_a_two_form(self):
        subject = replace(self.good, omega=sr.IDENTITY, domain=sr.Domain("all"))
        certificate = replace(self.cert, subject=subject, inverse=sr.InverseWitness(sr.IDENTITY, 0))
        report = sr.verify(subject, certificate)
        self.assertEqual(codes(report)["alternation"], "NOT_ALTERNATING")
        self.assertEqual(codes(report)["exterior_derivative"], "ALTERNATION_REQUIRED")
        self.assertEqual(codes(report)["domain_inverse"], "OK")
        self.assertFalse(report.accepted)

    def test_wrong_lower_triangle_rejected_even_with_closed_upper_triangle(self):
        subject = replace(self.good, omega=changed_entry(self.good.omega, 1, 0, sr.ZERO))
        report = sr.verify(subject, replace(self.cert, subject=subject))
        self.assertEqual(codes(report)["alternation"], "NOT_ALTERNATING")

    def test_closed_zero_form_fails_inverse(self):
        zero = sr.matrix([[0] * 4 for _ in range(4)])
        subject = replace(self.good, omega=zero)
        report = sr.verify(subject, replace(self.cert, subject=subject))
        self.assertEqual(codes(report)["exterior_derivative"], "OK")
        self.assertEqual(codes(report)["domain_inverse"], "INVERSE_IDENTITY_FAILED")

    def test_constant_standard_form_accepted_globally(self):
        standard = evaluate_matrix(self.good.omega, (sr.ZERO,) * 4)
        inverse = sr.matrix([[-p for p in row] for row in standard])
        subject = replace(self.good, omega=standard, domain=sr.Domain("all"))
        certificate = replace(self.cert, subject=subject, inverse=sr.InverseWitness(inverse, 0))
        self.assertTrue(sr.verify(subject, certificate).accepted)

    def test_denominator_checks_precede_cancellation(self):
        standard = evaluate_matrix(self.good.omega, (sr.ZERO,) * 4)
        numerator = sr.matrix([[-self.h * p for p in row] for row in standard])
        subject = replace(self.good, omega=standard, domain=sr.Domain("all"))
        certificate = replace(self.cert, subject=subject, inverse=sr.InverseWitness(numerator, 1))
        # Though cancellation could produce a global inverse, this witness is out of scope.
        self.assertEqual(codes(sr.verify(subject, certificate))["domain_inverse"],
                         "DENOMINATOR_NOT_JUSTIFIED")

    def test_higher_common_denominator_is_checked_exactly(self):
        numerator = sr.matrix([[self.h ** 2 * p for p in row] for row in self.cert.inverse.numerator])
        certificate = replace(self.cert, inverse=sr.InverseWitness(numerator, 3))
        self.assertTrue(sr.verify(self.good, certificate).accepted)

    def test_each_inverse_entry_mutation_is_rejected(self):
        for i, j in itertools.product(range(4), repeat=2):
            numerator = self.cert.inverse.numerator
            changed = changed_entry(numerator, i, j, numerator[i][j] + sr.ONE)
            certificate = replace(self.cert, inverse=sr.InverseWitness(changed, 1))
            with self.subTest(i=i, j=j):
                self.assertEqual(codes(sr.verify(self.good, certificate))["domain_inverse"],
                                 "INVERSE_IDENTITY_FAILED")

    def test_h_not_nonzero_on_arbitrary_or_string_domains(self):
        for raw in ("q1 != -1", {"kind": "sampled", "points": [[0, 0, 0, 0]]},
                    {"kind": "all", "nonzero": "1+q1 != 0"},
                    {"kind": "principal_open", "generator": sr.poly_data(self.x[0])},
                    {"kind": "principal_open", "generator": sr.poly_data(sr.ONE + self.x[0] ** 2)}):
            data = sr.subject_data(self.good)
            data["domain"] = raw
            with self.subTest(domain=raw), self.assertRaises(sr.Invalid):
                sr.subject_from_data(data)

    def test_nonconstant_global_positive_determinant_needs_more_evidence(self):
        # This form really is symplectic on R^4: its first coefficient depends only on q1.
        positive = sr.ONE + self.x[0] ** 2
        form = sr.matrix([[0, positive, 0, 0], [-positive, 0, 0, 0],
                          [0, 0, 0, 1], [0, 0, -1, 0]])
        self.assertEqual(sr.exterior_derivative(form), (sr.ZERO,) * 4)
        subject = replace(self.good, domain=sr.Domain("all"), omega=form)
        raw = sr.certificate_data(replace(self.cert, subject=subject))
        raw["inverse"]["denominator"] = sr.poly_data(positive)
        raw["inverse"]["positive"] = True
        with self.assertRaises(sr.Invalid):
            sr.certificate_from_data(raw)


class PolynomialAndWireTests(unittest.TestCase):
    def test_exact_rational_arithmetic_and_mixed_partial_cancellation(self):
        x, y, z, t = (sr.Poly.variable(i) for i in range(4))
        poly = Fraction(1, 3) * x ** 3 * y + Fraction(2, 7) * z ** 2 * t
        self.assertEqual(poly.derivative(0), x ** 2 * y)
        self.assertEqual(poly.derivative(0).derivative(1), poly.derivative(1).derivative(0))
        self.assertEqual(poly - poly, sr.ZERO)
        self.assertEqual(sr.poly_from_data(sr.poly_data(poly)), poly)

    def test_exterior_derivative_all_triple_signs(self):
        for i, j, k in sr.TRIPLES:
            for row, col, derivative, sign in ((j, k, i, 1), (i, k, j, -1), (i, j, k, 1)):
                omega = sr.matrix([[0] * 4 for _ in range(4)])
                coefficient = sr.Poly.variable(derivative)
                omega = changed_entry(omega, row, col, coefficient)
                omega = changed_entry(omega, col, row, -coefficient)
                expected = tuple(sr.Poly.constant(sign if triple == (i, j, k) else 0)
                                 for triple in sr.TRIPLES)
                with self.subTest(triple=(i, j, k), pair=(row, col)):
                    self.assertEqual(sr.exterior_derivative(omega), expected)

    def test_exact_one_form_derivatives_are_closed(self):
        # Coordinate d(d alpha), exercising mixed partials and all four triples.
        x = tuple(sr.Poly.variable(i) for i in range(4))
        alpha = (x[1] ** 3 * x[2], x[0] * x[2] * x[3],
                 Fraction(2, 3) * x[0] ** 2 * x[3], x[1] * x[2] ** 2)
        omega = sr.matrix([[alpha[j].derivative(i) - alpha[i].derivative(j)
                            for j in range(4)] for i in range(4)])
        self.assertEqual(sr.check_alternation(omega).code, "OK")
        self.assertEqual(sr.exterior_derivative(omega), (sr.ZERO,) * 4)

    def test_polynomial_rejects_inexact_and_malformed_inputs(self):
        term = {"powers": [1, 0, 0, 0], "coefficient": [1, 2]}
        malformed = ["q1", 1.0, [{"powers": [1, 0, 0, 0], "coefficient": [1.0, 2]}],
                     [{"powers": [-1, 0, 0, 0], "coefficient": [1, 2]}],
                     [{"powers": [True, 0, 0, 0], "coefficient": [1, 2]}],
                     [{"powers": [1, 0, 0, 0], "coefficient": [1, 0]}],
                     [{"powers": [1, 0, 0, 0], "coefficient": [True, 1]}],
                     [term, term], [{"powers": [1, 0, 0], "coefficient": [1, 2]}]]
        for raw in malformed:
            with self.subTest(raw=raw), self.assertRaises(sr.Invalid):
                sr.poly_from_data(raw)
        for value in (0.5, True, "1/2"):
            with self.subTest(value=value), self.assertRaises(sr.Invalid):
                sr.Poly.constant(value)

    def test_round_trip_all_cases_without_changing_outcomes(self):
        for name, (subject, certificate) in examples().items():
            expected = sr.subject_from_data(json.loads(json.dumps(sr.subject_data(subject))))
            decoded = sr.certificate_from_data(json.loads(json.dumps(sr.certificate_data(certificate))))
            with self.subTest(name=name):
                self.assertEqual(expected, subject)
                self.assertEqual(decoded, certificate)
                self.assertEqual(sr.verify(expected, decoded), sr.verify(subject, certificate))

    def test_invalid_certificate_envelopes_rejected(self):
        _, certificate = examples()["good_U"]
        original = sr.certificate_data(certificate)
        mutations = []
        for power in (-1, True, 1.0, "1"):
            data = copy.deepcopy(original)
            data["inverse"]["denominator_power"] = power
            mutations.append(data)
        data = copy.deepcopy(original)
        data["claimed_derivative"] = []
        mutations.append(data)
        for path in ("subject", "inverse"):
            data = copy.deepcopy(original)
            data[path]["verified"] = True
            mutations.append(data)
        data = copy.deepcopy(original)
        data["subject"]["omega"] = []
        mutations.append(data)
        for data in mutations:
            with self.subTest(data=data), self.assertRaises(sr.Invalid):
                sr.certificate_from_data(data)

    def test_wrong_scalar_profile_and_duplicate_coordinates_rejected(self):
        subject, _ = examples()["good_U"]
        for field, value in (("scalar_profile", "Float64"),
                             ("coordinates", ["q1", "q1", "q2", "p2"])):
            data = sr.subject_data(subject)
            data["context"][field] = value
            with self.subTest(field=field), self.assertRaises(sr.Invalid):
                sr.subject_from_data(data)

    def test_json_duplicate_keys_and_nonfinite_constants_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "invalid.json"
            for content in ('{"kind":"all","kind":"principal_open"}', '{"x":NaN}',
                            '{"x":Infinity}', '{"x":-Infinity}'):
                path.write_text(content, encoding="utf-8")
                with self.subTest(content=content), self.assertRaises(sr.Invalid):
                    sr.load_json(path)

    def test_cli_accept_reject_and_invalid_exit_codes(self):
        with tempfile.TemporaryDirectory() as directory:
            demo = subprocess.run([sys.executable, str(ROOT / "scripts/demo_symplectic_reference.py"),
                                   "--write-dir", directory], capture_output=True, text=True, check=True)
            self.assertTrue(json.loads(demo.stdout)["cases"]["good_U"]["accepted"])
            for name, expected_code in (("good_U", 0), ("bad_U", 1),
                                        ("global_relabelled_evidence", 1), ("same_determinant_replay", 1)):
                request = Path(directory) / f"{name}.request.json"
                certificate = Path(directory) / f"{name}.certificate.json"
                command = [sys.executable, str(ROOT / "scripts/symplectic_reference.py"),
                           str(request), str(certificate)]
                result = subprocess.run(command, capture_output=True, text=True)
                self.assertEqual(result.returncode, expected_code, result.stderr)
                self.assertEqual(json.loads(result.stdout)["status"],
                                 "accepted_reference" if expected_code == 0 else "rejected_reference")
            certificate.write_text('{"subject":NaN}', encoding="utf-8")
            result = subprocess.run(command, capture_output=True, text=True)
            self.assertEqual(result.returncode, 2)
            self.assertEqual(json.loads(result.stdout)["code"], "INVALID_SCHEMA")
            certificate.write_bytes(b"\xff")
            result = subprocess.run(command, capture_output=True, text=True)
            self.assertEqual(result.returncode, 2)
            self.assertEqual(json.loads(result.stdout)["code"], "INPUT_ERROR")


if __name__ == "__main__":
    unittest.main()
