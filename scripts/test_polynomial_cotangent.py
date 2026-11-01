"""Independent witnesses for the Lean polynomial cotangent regressions.

Reuse the existing sparse polynomial/metric-free reference. These tests check
exact witness values, not Lean proofs or any accepted-Core correspondence.
"""

from dataclasses import replace
from fractions import Fraction as Q
import unittest

import metric_free_reference as mf


class PolynomialCotangentWitnessTests(unittest.TestCase):
    def setUp(self):
        self.a = mf.Frame("361", "A", "real-base", "chart", "tangent", "cotangent",
                          "polynomial", "v1", ("x", "y"))
        self.b = replace(self.a, object_id="B")
        self.c = replace(self.a, object_id="C")

    @staticmethod
    def compose(g, f):
        # Test helper only; production/reference APIs are unchanged.
        if f.target != g.source:
            raise ValueError("incompatible nominal endpoints")
        return mf.PolynomialMap(f.source, g.target,
                                tuple(mf.substitute(p, f.expressions) for p in g.expressions))

    def test_identity_and_well_typed_noncommuting_order(self):
        p = mf.Point(self.a, (0, 0))
        seed = mf.Cotangent(p, (1, 0))
        identity = mf.PolynomialMap(self.a, self.a, (mf.X, mf.Y))
        f = mf.PolynomialMap(self.a, self.a, (mf.X + mf.Y, mf.Y))
        g = mf.PolynomialMap(self.a, self.a, (mf.X, mf.X + mf.Y))
        self.assertEqual(f.at(p), p)
        self.assertEqual(g.at(p), p)
        self.assertEqual(mf.cotangent_pullback(identity, p, seed), seed)
        correct = mf.cotangent_pullback(f, p, mf.cotangent_pullback(g, p, seed))
        reversed_order = mf.cotangent_pullback(g, p, mf.cotangent_pullback(f, p, seed))
        self.assertEqual(correct.components, (1, 1))
        self.assertEqual(reversed_order.components, (2, 1))
        self.assertEqual(correct.point, reversed_order.point)
        self.assertNotEqual(correct, reversed_order)
        self.assertEqual(mf.cotangent_pullback(self.compose(g, f), p, seed), correct)

    def test_nonlinear_chain_at_actual_intermediate_point(self):
        f = mf.PolynomialMap(self.a, self.b, (mf.X ** 2 + mf.Y, mf.X * mf.Y))
        g = mf.PolynomialMap(self.b, self.c, (mf.X + mf.Y ** 2, mf.X * mf.Y))
        p = mf.Point(self.a, (2, 3))
        gf = self.compose(g, f)
        self.assertEqual(f.at(p).coordinates, (7, 6))
        self.assertEqual(gf.at(p).coordinates, (43, 42))
        seed = mf.Cotangent(gf.at(p), (3, 5))
        staged = mf.cotangent_pullback(f, p, mf.cotangent_pullback(g, f.at(p), seed))
        self.assertEqual(staged.components, (345, 175))
        self.assertEqual(mf.cotangent_pullback(gf, p, seed), staged)
        wrong = mf.Cotangent(mf.Point(self.b, (2, 3)), (3, 5))
        with self.assertRaises(mf.Invalid) as raised:
            mf.cotangent_pullback(f, p, wrong)
        self.assertEqual(raised.exception.code, "SEED_BASEPOINT_MISMATCH")
        foreign = mf.Cotangent(mf.Point(self.c, (7, 6)), (3, 5))
        with self.assertRaises(mf.Invalid) as raised:
            mf.cotangent_pullback(f, p, foreign)
        self.assertEqual(raised.exception.code, "SEED_BASEPOINT_MISMATCH")

    def test_rational_coefficients_point_and_seed(self):
        f = mf.PolynomialMap(self.a, self.b, (Q(1, 2) * mf.X ** 2, mf.Y))
        p = mf.Point(self.a, (Q(2, 3), Q(3, 4)))
        seed = mf.Cotangent(f.at(p), (Q(3, 2), Q(-1, 3)))
        self.assertEqual(mf.cotangent_pullback(f, p, seed).components, (1, Q(-1, 3)))


if __name__ == "__main__":
    unittest.main()
