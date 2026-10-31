import unittest
from fractions import Fraction as Q

from rational_polynomial_reference import Invalid, Poly
from rational_polynomial_calculus import evaluate, integrate, substitute


class PolynomialCalculusTests(unittest.TestCase):
    def test_exact_integrals_and_no_endpoint_sampling(self):
        t = Poly.variable(0, arity=1)
        for expression, expected in (
            (Poly.constant(0, 1), Q(0)),
            (Poly.constant(3, 1), Q(3)),
            (t ** 2, Q(1, 3)),
            (16 * t ** 2 * (1 + -t) ** 2, Q(8, 15)),
            (Q(1, 10**20) * t ** 7, Q(1, 8 * 10**20)),
        ):
            self.assertEqual(evaluate(integrate(expression, 0, 0, 1), ()), expected)

    def test_fundamental_theorem_for_rational_polynomial_family(self):
        t = Poly.variable(0, arity=1)
        for degree in range(1, 10):
            p = Q(-7, 3) * t ** degree + Q(2, 11) * t + 5
            for lower, upper in ((Q(0), Q(1)), (Q(-2, 3), Q(5, 7)), (Q(4), Q(4))):
                self.assertEqual(evaluate(integrate(p.derivative(0), 0, lower, upper), ()),
                                 evaluate(p, (upper,)) - evaluate(p, (lower,)))

    def test_parameter_ring_order_survives_each_integration_axis(self):
        x, y, z = (Poly.variable(i, arity=3) for i in range(3))
        p = x * y ** 2 + Q(3, 7) * z
        a, b = (Poly.variable(i, arity=2) for i in range(2))
        self.assertEqual(integrate(p, 0, 0, 1), Q(1, 2) * a ** 2 + Q(3, 7) * b)
        self.assertEqual(integrate(p, 1, 0, 1), Q(1, 3) * a + Q(3, 7) * b)
        self.assertEqual(integrate(p, 2, 0, 1), a * b ** 2 + Q(3, 14))
        self.assertEqual(integrate(p, 1, 1, 0), -integrate(p, 1, 0, 1))

    def test_composition_commutes_with_evaluation(self):
        x, y = (Poly.variable(i, arity=2) for i in range(2))
        t = Poly.variable(0, arity=1)
        p = x ** 3 * y + Q(2, 7) * y ** 2 + 11
        coordinates = (t ** 2 + 1, 3 * t + -1)
        for point in (Q(-3, 2), Q(0), Q(1, 3), Q(1)):
            self.assertEqual(evaluate(substitute(p, coordinates), (point,)),
                             evaluate(p, tuple(evaluate(c, (point,)) for c in coordinates)))

    def test_malformed_and_inexact_arithmetic_inputs_rejected(self):
        t = Poly.variable(0, arity=1)
        for bad in (0.0, True, "0"):
            with self.assertRaises(Invalid):
                integrate(t, 0, bad, 1)
            with self.assertRaises(Invalid):
                evaluate(t, (bad,))
        for index in (-1, 1, True):
            with self.assertRaises(Invalid):
                integrate(t, index, 0, 1)
        for coordinates in ((), [t], (t, t)):
            with self.assertRaises(Invalid):
                substitute(t, coordinates)
        x = Poly.variable(0, arity=2)
        with self.assertRaises(Invalid):
            substitute(x, (t, x))
        with self.assertRaises(Invalid):
            t + x


if __name__ == "__main__":
    unittest.main()
