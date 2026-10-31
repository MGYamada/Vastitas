"""Shared arithmetic and legacy consumer boundaries for the Poly extraction."""

import unittest
from fractions import Fraction as Q

import metric_free_reference as metric
import symplectic_reference as symplectic
from rational_polynomial_reference import Invalid, Poly


class PolynomialCompatibilityTests(unittest.TestCase):
    def test_four_variable_arithmetic_and_wire_format_are_preserved(self):
        self.assertIs(Poly, symplectic.Poly)
        self.assertIs(Poly, metric.Poly)
        x, y, z, w = (Poly.variable(i) for i in range(4))
        p = (x + y) ** 2 - x ** 2 - y ** 2 + Q(2, 3) * z * w
        expected = [
            {"powers": [0, 0, 1, 1], "coefficient": [2, 3]},
            {"powers": [1, 1, 0, 0], "coefficient": [2, 1]},
        ]
        self.assertEqual(p.arity, 4)
        self.assertEqual(symplectic.poly_data(p), expected)
        self.assertEqual(symplectic.poly_from_data(expected), p)
        self.assertEqual(p.derivative(0), 2 * y)
        self.assertEqual(p.derivative(3), Q(2, 3) * z)
        self.assertEqual(p - p, Poly(()))
        self.assertEqual(symplectic.poly_data(p - p), [])
        self.assertEqual(symplectic.poly_from_data([]), Poly.constant(0))

    def test_arity_survives_zero_and_legacy_consumers_reject_wrong_ring(self):
        self.assertEqual(Poly.constant(0).arity, 4)
        metric.audit_polynomial(Poly.constant(0))
        symplectic.audit_matrix(tuple((Poly.constant(0),) * 4 for _ in range(4)))
        for arity in (0, 1, 2, 3, 5):
            zero = Poly.constant(0, arity)
            self.assertNotEqual(zero, Poly.constant(0))
            with self.subTest(arity=arity), self.assertRaises(Invalid):
                metric.audit_polynomial(zero)
            with self.subTest(arity=arity), self.assertRaises(Invalid):
                symplectic.audit_matrix(tuple((zero,) * 4 for _ in range(4)))


if __name__ == "__main__":
    unittest.main()
