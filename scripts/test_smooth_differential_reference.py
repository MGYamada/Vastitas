import unittest
from fractions import Fraction as Q

import affine_algebra_reference as algebra
import metric_free_reference as mf
import smooth_differential_reference as ref


def vector(values):
    return tuple(Q(value) for value in values)


class SmoothDifferentialReference(unittest.TestCase):
    def setUp(self):
        fixture = ref.fixture()
        self.pullbacks = {case["name"]: case for case in fixture["pullbacks"]}
        self.differentials = {case["name"]: case for case in fixture["differentials"]}
        self.metrics = {case["name"]: case for case in fixture["metrics"]}

    def polynomials(self):
        for case in self.pullbacks.values():
            yield from case["map"]
            if "composite" in case:
                yield from case["composite"]["after"]
                yield from case["composite"]["before"]
        for case in self.differentials.values():
            yield case["function"]

    def test_polynomials_use_the_kernel_deglex_order(self):
        encoded = ref.encode_poly(mf.X ** 2 + mf.X * mf.Y + mf.Y ** 2 + mf.X + 1)
        self.assertEqual([m for m, _ in encoded], [[2, 0], [1, 1], [0, 2], [1, 0], [0, 0]])
        self.assertEqual(ref.encode_poly(Q(-3, 4) * mf.Y), [[[0, 1], "-3/4"]])
        self.assertEqual(ref.encode_poly(mf.ZERO), [])

    def test_every_fixture_polynomial_is_canonical(self):
        for terms in self.polynomials():
            monomials = [tuple(m) for m, _ in terms]
            for monomial, coefficient in terms:
                self.assertEqual(len(monomial), 2)
                self.assertTrue(all(type(e) is int and e >= 0 for e in monomial))
                self.assertNotEqual(algebra.decode_rational(coefficient), 0)
            keys = [algebra.key(m) for m in monomials]
            self.assertEqual(keys, sorted(keys, reverse=True))
            self.assertEqual(len(set(keys)), len(keys))

    def test_shears_and_their_composites(self):
        dx_pullbacks = {name: self.pullbacks[name]["expected"] for name in (
            "shear A at the origin", "shear B at the origin",
            "B after A at the origin", "A after B at the origin")}
        self.assertEqual(dx_pullbacks, {
            "shear A at the origin": ["1", "1"], "shear B at the origin": ["1", "0"],
            "B after A at the origin": ["1", "1"], "A after B at the origin": ["2", "1"]})
        self.assertEqual(self.pullbacks["B after A at the origin"]["map"],
                         [ref.encode_poly(mf.X + mf.Y), ref.encode_poly(mf.X + 2 * mf.Y)])
        self.assertEqual(self.pullbacks["A after B at the origin"]["map"],
                         [ref.encode_poly(2 * mf.X + mf.Y), ref.encode_poly(mf.X + mf.Y)])

    def test_composites_follow_the_two_step_chain_rule(self):
        composites = [case for case in ref.pullback_inputs() if case[5] is not None and case[4] is None]
        self.assertGreaterEqual(len(composites), 4)
        for name, _, point, seed, _, (after, before) in composites:
            with self.subTest(name):
                inner = mf.PolynomialMap(ref.SOURCE, ref.MIDDLE, before)
                outer = mf.PolynomialMap(ref.MIDDLE, ref.TARGET, after)
                source = mf.Point(ref.SOURCE, point)
                middle = inner.at(source)
                alpha = mf.cotangent_pullback(outer, middle, mf.Cotangent(outer.at(middle), seed))
                beta = mf.cotangent_pullback(inner, source, alpha)
                self.assertEqual(ref.encode_vector(beta.components), self.pullbacks[name]["expected"])

    def test_known_nonlinear_pullbacks(self):
        case = self.pullbacks["square map at (1, 2)"]
        self.assertEqual((case["seedPoint"], case["expected"]), (["1", "4"], ["2", "-4"]))
        case = self.pullbacks["square map at a rational point"]
        self.assertEqual(case["expected"], ["-29/15", "21/2"])

    def test_seed_basepoint_mismatches_are_null(self):
        mismatches = [case for case in ref.pullback_inputs() if case[4] is not None]
        self.assertGreaterEqual(len(mismatches), 2)
        for name, images, point, seed, seed_point, _ in mismatches:
            with self.subTest(name):
                mapping = mf.PolynomialMap(ref.SOURCE, ref.TARGET, images)
                source = mf.Point(ref.SOURCE, point)
                with self.assertRaises(mf.Invalid) as raised:
                    mf.cotangent_pullback(mapping, source, mf.Cotangent(mf.Point(ref.TARGET, seed_point), seed))
                self.assertEqual(raised.exception.code, "SEED_BASEPOINT_MISMATCH")
                self.assertIsNone(self.pullbacks[name]["expected"])
                self.assertNotEqual(vector(self.pullbacks[name]["seedPoint"]), mapping.at(source).coordinates)
        for name, *_, seed_point, _ in ref.pullback_inputs():
            if seed_point is None:
                self.assertIsNotNone(self.pullbacks[name]["expected"], name)

    def test_known_differentials(self):
        self.assertEqual(self.differentials["x^2 + y at (1, 2)"]["expected"], ["2", "1"])
        self.assertEqual(self.differentials["rational cubic at a rational point"]["expected"], ["307/70", "6/7"])
        self.assertEqual(self.differentials["zero function"]["function"], [])

    def test_known_metrics(self):
        def outcome(name):
            case = self.metrics[name]
            return case["nondegenerate"], case["riemannian"]

        self.assertEqual(outcome("Euclid"), ([["1", "0"], ["0", "1"]], "ok"))
        self.assertEqual(outcome("Skew"), ([["1", "-1"], ["-1", "2"]], "ok"))
        self.assertEqual(outcome("Lorentz"), ([["1", "0"], ["0", "-1"]], "NOT_POSITIVE_DEFINITE"))
        self.assertEqual(outcome("Degenerate"), ("SINGULAR", "SINGULAR"))
        self.assertEqual(outcome("rational positive definite"), ([["18", "-24"], ["-24", "36"]], "ok"))
        self.assertEqual(outcome("not symmetric"), ("NOT_SYMMETRIC", "NOT_SYMMETRIC"))
        self.assertNotIn("sharp", self.metrics["Degenerate"])

    def test_flat_undoes_sharp(self):
        for name, case in self.metrics.items():
            if "sharp" not in case:
                continue
            with self.subTest(name):
                gram = tuple(vector(row) for row in case["gram"])
                raised = vector(case["sharp"]["expected"])
                self.assertEqual(mf.matvec(gram, raised), vector(case["sharp"]["covector"]))

    def test_invalid_inputs_are_not_fixture_results(self):
        with self.assertRaises(mf.Invalid):
            ref.encode_poly(mf.Poly.variable(2))
        with self.assertRaises(mf.Invalid):
            ref.metric_case("not square", ((1, 0),), (1, 0), (1, 0))
        with self.assertRaises(mf.Invalid):
            ref.metric_case("inexact", ((1.0, 0), (0, 1)), (1, 0), (1, 0))

    def test_fixture_is_current(self):
        self.assertEqual(ref.main(["--check"]), 0)


if __name__ == "__main__":
    unittest.main()
