"""Exact semantic, binding and malformed-input regressions for #244/#237."""

import copy
import itertools
import json
import subprocess
import sys
import tempfile
import unittest
from dataclasses import fields, replace
from fractions import Fraction as Q
from pathlib import Path

import sos_reference as sr
import symplectic_reference as sym
from demo_sos_reference import examples, matrix
from demo_symplectic_reference import examples as symplectic_examples
from rational_polynomial_reference import Poly


ROOT = Path(__file__).resolve().parents[1]


def codes(report):
    return {c.name: c.code for c in report.checks}


def failed(report):
    return {c.code for c in report.checks if c.status == "fail"}


def changed_entry(value, i, j, replacement):
    rows = [list(row) for row in value]
    rows[i][j] = replacement
    return tuple(tuple(row) for row in rows)


class SOSTests(unittest.TestCase):
    def setUp(self):
        self.cases = examples()
        self.subject, self.cert = self.cases["singular_cover"]

    def test_singular_cover_exact_identity_and_zero_pivot(self):
        report = sr.verify(self.subject, self.cert)
        self.assertTrue(report.accepted)
        self.assertIs(report.subject, self.subject)
        self.assertIs(report.certificate, self.cert)
        self.assertEqual(set(codes(report).values()), {"OK"})
        x = Poly.variable(0, 1)
        self.assertEqual(sr.gram_polynomial(self.subject, self.cert.gram),
                         2 * (x - Q(1, 2)) ** 2)
        self.assertEqual(self.cert.diagonal, (Q(1, 2), Q(0)))
        self.assertEqual(self.cert.gram[0][0] * self.cert.gram[1][1]
                         - self.cert.gram[0][1] ** 2, 0)

    def test_leading_zero_and_permuted_singular_cover(self):
        for name in ("permuted_singular_cover", "leading_zero_cover"):
            with self.subTest(name=name):
                self.assertTrue(sr.verify(*self.cases[name]).accepted)

    def test_zero_gram_with_positive_delta_is_valid(self):
        # f=1, delta=1 proves a cover, although the residual SOS has rank zero.
        subject = replace(self.subject, generators=(sr.Generator("one", "1", Poly.constant(1, 1)),),
                          monomials=((0,),), delta=Q(1))
        cert = sr.Certificate(subject, matrix([[0]]), (0,), matrix([[1]]), (Q(0),))
        self.assertTrue(sr.verify(subject, cert).accepted)

    def test_noninvolutive_permutations_use_declared_direction(self):
        # Independent diagonal example, v=(1,x,y), f=(1,x,2y), delta=1/2.
        # All 6 permutations include the two distinct 3-cycles p != inverse(p).
        x, y = Poly.variable(0, 2), Poly.variable(1, 2)
        subject = replace(self.subject, context=replace(self.subject.context, variables=("x", "y")),
                          domain=replace(self.subject.domain, dimension=2),
                          generators=(sr.Generator("one", "1", Poly.constant(1, 2)),
                                      sr.Generator("x", "1", x), sr.Generator("y2", "1", 2 * y)),
                          monomials=((0, 0), (1, 0), (0, 1)))
        diagonal = (Q(1, 2), Q(1), Q(4))
        gram = matrix([[diagonal[i] if i == j else 0 for j in range(3)] for i in range(3)])
        identity = matrix([[int(i == j) for j in range(3)] for i in range(3)])
        for p in itertools.permutations(range(3)):
            cert = sr.Certificate(subject, gram, p, identity, tuple(diagonal[i] for i in p))
            with self.subTest(p=p):
                self.assertTrue(sr.verify(subject, cert).accepted)
                if p != tuple(p.index(i) for i in range(3)):
                    wrong = replace(cert, diagonal=tuple(diagonal[p.index(i)] for i in range(3)))
                    self.assertEqual(failed(sr.verify(subject, wrong)), {"LDL_IDENTITY_MISMATCH"})

    def test_tiny_rational_tamper_is_invisible_to_float_but_rejected(self):
        subject, cert = self.cases["tiny_gram_tamper"]
        self.assertEqual([[float(x) for x in row] for row in cert.gram],
                         [[float(x) for x in row] for row in self.cert.gram])
        self.assertEqual(cert.gram[0][0] * cert.gram[1][1] - cert.gram[0][1] ** 2,
                         Q(-2, 10**20))
        self.assertEqual(failed(sr.verify(subject, cert)),
                         {"POLYNOMIAL_IDENTITY_MISMATCH", "LDL_IDENTITY_MISMATCH"})
        # Even a repaired exact LDL does not make the perturbed matrix PSD.
        a = cert.gram[0][0]
        exact_factor = replace(cert, lower=matrix([[1, 0], [-1 / a, 1]]),
                               diagonal=(a, 2 - 1 / a))
        report = sr.verify(subject, exact_factor)
        self.assertEqual(codes(report)["ldl_identity"], "OK")
        self.assertEqual(codes(report)["diagonal_nonnegative"], "NEGATIVE_DIAGONAL")

    def test_multivariate_higher_degree_sos_with_three_cycle_and_singular_gram(self):
        # Substitute h=x^2+y into the original identity. Nontrivial L and P are
        # checked together with two zero diagonal weights; the original Gram
        # basis is (1,x^2,y).
        x, y = Poly.variable(0, 2), Poly.variable(1, 2)
        h = x ** 2 + y
        subject = replace(self.subject, context=replace(self.subject.context, variables=("x", "y")),
                          domain=replace(self.subject.domain, dimension=2),
                          generators=(sr.Generator("h", "1", h),
                                      sr.Generator("one-h", "1", Poly.constant(1, 2) - h)),
                          monomials=((0, 0), (2, 0), (0, 1)))
        gram = matrix([[Q(1, 2), -1, -1], [-1, 2, 2], [-1, 2, 2]])
        cert = sr.Certificate(subject, gram, (1, 2, 0),
                              matrix([[1, 0, 0], [1, 1, 0], [Q(-1, 2), 0, 1]]),
                              (Q(2), Q(0), Q(0)))
        self.assertEqual(sr.gram_polynomial(subject, gram),
                         Poly.from_terms([((0, 0), Q(1, 2)), ((2, 0), -2), ((0, 1), -2),
                                          ((4, 0), 2), ((2, 1), 4), ((0, 2), 2)], 2))
        self.assertTrue(sr.verify(subject, cert).accepted)
        self.assertEqual(failed(sr.verify(subject, replace(cert, permutation=(2, 0, 1)))),
                         {"LDL_IDENTITY_MISMATCH"})

    def test_false_cover_distinguishes_psd_identity_and_strict_bound(self):
        expected = {"false_cover_zero_delta": {"DELTA_NOT_POSITIVE"},
                    "false_cover_positive_delta": {"POLYNOMIAL_IDENTITY_MISMATCH"},
                    "false_cover_indefinite": {"NEGATIVE_DIAGONAL"}}
        for name, errors in expected.items():
            report = sr.verify(*self.cases[name])
            with self.subTest(name=name):
                self.assertFalse(report.accepted)
                self.assertEqual(failed(report), errors)
                self.assertEqual(codes(report)["ldl_identity"], "OK")

    def test_negative_delta_fails_even_with_valid_positive_gram(self):
        subject = replace(self.subject, delta=Q(-1))
        cert = replace(self.cert, subject=subject, gram=matrix([[2, -1], [-1, 2]]),
                       lower=matrix([[1, 0], [Q(-1, 2), 1]]), diagonal=(Q(2), Q(3, 2)))
        self.assertEqual(failed(sr.verify(subject, cert)), {"DELTA_NOT_POSITIVE"})

    def test_wrong_factor_and_non_unit_lower_are_distinct(self):
        wrong = replace(self.cert, lower=matrix([[1, 0], [-1, 1]]))
        self.assertEqual(failed(sr.verify(self.subject, wrong)), {"LDL_IDENTITY_MISMATCH"})
        # Last column is multiplied by a zero pivot; the product still agrees.
        for lower in (matrix([[1, 1], [-2, 1]]), matrix([[1, 0], [-2, 2]])):
            report = sr.verify(self.subject, replace(self.cert, lower=lower))
            self.assertEqual(failed(report), {"NOT_UNIT_LOWER_TRIANGULAR"})

    def test_asymmetric_gram_cannot_hide_in_quadratic_form(self):
        # Antisymmetric perturbation cancels in v^T G v, but is not a PSD witness.
        gram = matrix([[Q(1, 2), -2], [0, 2]])
        report = sr.verify(self.subject, replace(self.cert, gram=gram))
        self.assertEqual(codes(report)["polynomial_identity"], "OK")
        self.assertEqual(failed(report), {"GRAM_NOT_SYMMETRIC", "LDL_IDENTITY_MISMATCH"})

    def test_every_gram_and_lower_entry_tamper_is_rejected(self):
        for field in ("gram", "lower"):
            for i, j in itertools.product(range(2), repeat=2):
                value = getattr(self.cert, field)
                mutated = changed_entry(value, i, j, value[i][j] + Q(1, 10**20))
                with self.subTest(field=field, i=i, j=j):
                    self.assertFalse(sr.verify(self.subject, replace(self.cert, **{field: mutated})).accepted)

    def test_context_function_domain_and_delta_replay_rejected(self):
        subjects = [replace(self.subject, domain=replace(self.subject.domain, domain_id="other")),
                    replace(self.subject, delta=Q(1, 3))]
        for field in fields(sr.Context):
            if field.name in ("variables", "scalar_profile", "site"):
                continue
            subjects.append(replace(self.subject, context=replace(
                self.subject.context, **{field.name: "different"})))
        generator = self.subject.generators[0]
        for change in ({"function_id": "other"}, {"revision": "2"},
                       {"polynomial": generator.polynomial + Q(1, 10**20)}):
            subjects.append(replace(self.subject, generators=(replace(generator, **change),
                                                              self.subject.generators[1])))
        for subject in subjects:
            with self.subTest(subject=subject):
                report = sr.verify(subject, self.cert)
                self.assertEqual(failed(report), {"SUBJECT_MISMATCH"})
                self.assertTrue(all(c.status == "not_checked" for c in report.checks[1:]))

    def test_relabelling_changed_coefficients_cannot_repair_identity(self):
        generator = self.subject.generators[1]
        subject = replace(self.subject, generators=(self.subject.generators[0], replace(
            generator, polynomial=generator.polynomial - Q(1, 10**20))))
        self.assertEqual(failed(sr.verify(subject, replace(self.cert, subject=subject))),
                         {"POLYNOMIAL_IDENTITY_MISMATCH"})

    def test_variable_order_replay_and_incorrect_reindexing(self):
        x, y = Poly.variable(0, 2), Poly.variable(1, 2)
        subject = replace(self.subject, context=replace(self.subject.context, variables=("x", "y")),
                          domain=replace(self.subject.domain, dimension=2),
                          generators=(sr.Generator("f1", "1", x),
                                      sr.Generator("f2", "1", Poly.constant(1, 2) - x)),
                          monomials=((0, 0), (1, 0)))
        cert = replace(self.cert, subject=subject)
        self.assertTrue(sr.verify(subject, cert).accepted)
        reordered = replace(subject, context=replace(subject.context, variables=("y", "x")))
        self.assertEqual(failed(sr.verify(reordered, cert)), {"SUBJECT_MISMATCH"})
        # Correctly reindex f_i but forget to reindex the monomial vector.
        reordered = replace(reordered, generators=(sr.Generator("f1", "1", y),
                            sr.Generator("f2", "1", Poly.constant(1, 2) - y)))
        self.assertEqual(failed(sr.verify(reordered, replace(cert, subject=reordered))),
                         {"POLYNOMIAL_IDENTITY_MISMATCH"})
        fixed = replace(reordered, monomials=((0, 0), (0, 1)))
        self.assertTrue(sr.verify(fixed, replace(cert, subject=fixed)).accepted)

    def test_monomial_order_is_not_silently_sorted(self):
        reordered = replace(self.subject, monomials=tuple(reversed(self.subject.monomials)))
        self.assertEqual(failed(sr.verify(reordered, self.cert)), {"SUBJECT_MISMATCH"})
        self.assertEqual(failed(sr.verify(reordered, replace(self.cert, subject=reordered))),
                         {"POLYNOMIAL_IDENTITY_MISMATCH"})
        cert = replace(self.cert, subject=reordered, gram=matrix([[2, -1], [-1, Q(1, 2)]]),
                       lower=matrix([[1, 0], [Q(-1, 2), 1]]), diagonal=(Q(2), Q(0)))
        self.assertTrue(sr.verify(reordered, cert).accepted)


class PolynomialAndWireTests(unittest.TestCase):
    def test_shared_polynomials_generalize_without_weakening_symplectic(self):
        self.assertIs(sr.Poly, sym.Poly)
        for n in (1, 2, 5):
            x = Poly.variable(n - 1, n)
            self.assertEqual(((x + 1) * (x - 1)).derivative(n - 1), 2 * x)
            self.assertEqual((x + 1) * (x - 1), x ** 2 - 1)
            self.assertEqual(Poly.from_terms([((0,) * n, Q(1, 2)), ((0,) * n, Q(-1, 2))], n),
                             Poly.constant(0, n))
        self.assertNotEqual(Poly.constant(0, 1), Poly.constant(0, 4))
        for operation in (lambda: Poly.constant(0, 1) + Poly.constant(0, 4),
                          lambda: Poly.variable(0, 1) * Poly.variable(0, 4)):
            with self.assertRaises(sr.Invalid):
                operation()
        subject, certificate = symplectic_examples()["good_U"]
        foreign_zero = Poly.constant(0, 1)
        for operation in (lambda: sym.matrix([[foreign_zero] * 4] * 4),
                          lambda: sym.Domain("principal_open", foreign_zero),
                          lambda: replace(certificate, claimed_derivative=(foreign_zero,) * 4)):
            with self.assertRaises(sr.Invalid):
                operation()
        self.assertTrue(sym.verify(subject, certificate).accepted)

    def test_bad_zero_terms_cannot_hide_malformed_exponents(self):
        for powers in ((-1,), (True,), (0, 0), (0.0,)):
            with self.subTest(powers=powers), self.assertRaises(sr.Invalid):
                Poly.from_terms([(powers, 0)], 1)

    def test_multivariate_cross_terms_and_coefficient_identity(self):
        # Independent expansion, not just comparison with the same Gram routine.
        x, y = Poly.variable(0, 2), Poly.variable(1, 2)
        subject, _ = examples()["singular_cover"]
        subject = replace(subject, context=replace(subject.context, variables=("x", "y")),
                          domain=replace(subject.domain, dimension=2),
                          generators=(sr.Generator("f", "1", x + y + 1),),
                          monomials=((0, 0), (1, 0), (0, 1)), delta=Q(0))
        self.assertEqual(sr.gram_polynomial(subject, matrix([[1] * 3] * 3)),
                         Poly.from_terms([((0, 0), 1), ((1, 0), 2), ((0, 1), 2),
                                          ((2, 0), 1), ((1, 1), 2), ((0, 2), 1)], 2))

    def test_round_trip_preserves_exact_inputs_and_results(self):
        for name, (subject, certificate) in examples().items():
            expected = sr.subject_from_data(json.loads(json.dumps(sr.subject_data(subject))))
            decoded = sr.certificate_from_data(json.loads(json.dumps(sr.certificate_data(certificate))))
            with self.subTest(name=name):
                self.assertEqual(expected, subject)
                self.assertEqual(decoded, certificate)
                self.assertEqual(sr.verify(expected, decoded), sr.verify(subject, certificate))

    def test_invalid_certificate_shapes_permutations_and_convention(self):
        _, cert = examples()["singular_cover"]
        changes = [("gram", []), ("gram", [[[1, 1]]]), ("lower", []),
                   ("diagonal", []), ("diagonal", [[[1, 1], [0, 1]], [[0, 1], [0, 1]]]),
                   ("convention", "P^T*G*P=L*D*L^T"), ("convention", None)]
        changes += [("permutation", p) for p in ([0, 0], [0], [-1, 0], [1, 2], [False, 1], [0.0, 1])]
        for field, value in changes:
            raw = sr.certificate_data(cert)
            raw[field] = value
            with self.subTest(field=field, value=value), self.assertRaises(sr.Invalid):
                sr.certificate_from_data(raw)

    def test_rationals_and_polynomials_reject_inexact_or_ambiguous_data(self):
        for value in (0.5, "1/2", True, [1, 0], [1, -2], [True, 2], [1.0, 2], [1, 2, 3]):
            with self.subTest(value=value), self.assertRaises(sr.Invalid):
                sr.rational_from_data(value)
        term = {"powers": [1], "coefficient": [1, 2]}
        bad_terms = ["x", [term, term], [{"powers": [-1], "coefficient": [0, 1]}],
                     [{"powers": [True], "coefficient": [1, 2]}],
                     [{"powers": [1, 0], "coefficient": [1, 2]}]]
        for raw in bad_terms:
            with self.subTest(raw=raw), self.assertRaises(sr.Invalid):
                sr.poly_from_data(raw, 1)
        self.assertEqual(sr.rational_from_data([2, 4]), Q(1, 2))

    def test_float_residual_or_eigenvalue_flag_is_never_evidence(self):
        _, cert = examples()["singular_cover"]
        for field, value in (("residual", 0.0), ("psd", True), ("min_eigenvalue", 1e-20)):
            raw = sr.certificate_data(cert)
            raw[field] = value
            with self.subTest(field=field), self.assertRaises(sr.Invalid):
                sr.certificate_from_data(raw)
        for field in ("gram", "lower", "diagonal"):
            raw = sr.certificate_data(cert)
            raw[field][0] = [0.5, 0.0] if field != "diagonal" else 0.5
            with self.subTest(field=field), self.assertRaises(sr.Invalid):
                sr.certificate_from_data(raw)

    def test_unsupported_domains_sites_and_coefficients_even_after_relabelling(self):
        subject, cert = examples()["singular_cover"]
        mutations = [("context", "scalar_profile", value) for value in ("Float64", "QQ-to-C", "cyclotomic")]
        mutations += [("context", "site", value) for value in ("Zariski", "complex", "analytic-bumps")]
        mutations += [("domain", "kind", value) for value in ("interval", "semialgebraic", "principal_open")]
        for area, field, value in mutations:
            request, candidate = sr.subject_data(subject), sr.certificate_data(cert)
            request[area][field] = value
            candidate["subject"] = copy.deepcopy(request)
            with self.subTest(value=value):
                with self.assertRaises(sr.Invalid):
                    sr.subject_from_data(request)
                with self.assertRaises(sr.Invalid):
                    sr.certificate_from_data(candidate)

    def test_subject_shapes_are_audited(self):
        subject, _ = examples()["singular_cover"]
        for area, field, value in (("context", "variables", []), ("context", "variables", ["x", "x"]),
                                   ("domain", "dimension", 2), ("domain", "dimension", True)):
            raw = sr.subject_data(subject)
            raw[area][field] = value
            with self.subTest(field=field, value=value), self.assertRaises(sr.Invalid):
                sr.subject_from_data(raw)
        for field, value in (("generators", []), ("monomials", []), ("monomials", [[0], [0]]),
                             ("monomials", [[-1]]), ("delta", 0.5), ("delta", [1, 0])):
            raw = sr.subject_data(subject)
            raw[field] = value
            with self.subTest(field=field, value=value), self.assertRaises(sr.Invalid):
                sr.subject_from_data(raw)

    def test_duplicate_json_keys_and_all_inexact_numbers_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "input.json"
            for content in ('{"x":1,"x":2}', '{"x":NaN}', '{"x":Infinity}',
                            '{"x":-Infinity}', '{"x":0.0}', '{"x":1e-20}'):
                path.write_text(content, encoding="utf-8")
                with self.subTest(content=content), self.assertRaises(sr.Invalid):
                    sr.load_json(path)

    def test_cli_reports_and_exit_codes(self):
        with tempfile.TemporaryDirectory() as directory:
            demo = subprocess.run([sys.executable, str(ROOT / "scripts/demo_sos_reference.py"),
                                   "--write-dir", directory], capture_output=True, text=True, check=True)
            summary = json.loads(demo.stdout)
            for name, (subject, cert) in examples().items():
                command = [sys.executable, str(ROOT / "scripts/sos_reference.py"),
                           str(Path(directory) / f"{name}.request.json"),
                           str(Path(directory) / f"{name}.certificate.json")]
                result = subprocess.run(command, capture_output=True, text=True)
                report = sr.verify(subject, cert)
                with self.subTest(name=name):
                    self.assertEqual(summary["cases"][name]["accepted"], report.accepted)
                    self.assertEqual(result.returncode, 0 if report.accepted else 1, result.stderr)
                    self.assertEqual(json.loads(result.stdout), sr.report_data(report))
            for raw in (b'{"gram":NaN}', b'{"gram":0.0}', b'{"gram":', b'\xff'):
                Path(command[-1]).write_bytes(raw)
                result = subprocess.run(command, capture_output=True, text=True)
                self.assertEqual(result.returncode, 2, result.stderr)
                self.assertEqual(json.loads(result.stdout)["status"], "invalid_input")
            Path(command[-1]).unlink()
            result = subprocess.run(command, capture_output=True, text=True)
            self.assertEqual(result.returncode, 2)


if __name__ == "__main__":
    unittest.main()
