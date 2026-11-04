import unittest
from fractions import Fraction
from itertools import combinations, permutations

import affine_algebra_reference as ref


def p(arity, *terms):
    return ref.poly(terms, arity)


class AffineAlgebraReference(unittest.TestCase):
    def test_deglex_compares_degree_then_coordinate_zero(self):
        self.assertGreater(ref.key((0, 2)), ref.key((1, 0)))
        self.assertGreater(ref.key((2, 0)), ref.key((1, 1)))
        self.assertGreater(ref.key((1, 0, 0)), ref.key((0, 1, 0)))

    def test_known_reduced_bases(self):
        self.assertEqual(ref.groebner([p(1, ((2,), 1))]), [p(1, ((2,), 1))])
        fiber = ref.groebner([p(2, ((0, 2), 1), ((1, 0), -1)), p(2, ((1, 0), 1))])
        self.assertEqual(fiber, [p(2, ((0, 2), 1)), p(2, ((1, 0), 1))])
        self.assertEqual(ref.groebner([p(1, ((1,), 1)), p(1, ((1,), 1), ((0,), -1))]), [p(1, ((0,), 1))])
        self.assertEqual(ref.groebner([]), [])

    def test_twisted_cubic_matches_hand_computation(self):
        basis = ref.groebner([p(3, ((0, 1, 0), 1), ((2, 0, 0), -1)), p(3, ((0, 0, 1), 1), ((3, 0, 0), -1))])
        self.assertEqual(basis, [
            p(3, ((0, 3, 0), 1), ((0, 0, 2), -1)),
            p(3, ((2, 0, 0), 1), ((0, 1, 0), -1)),
            p(3, ((1, 1, 0), 1), ((0, 0, 1), -1)),
            p(3, ((1, 0, 1), 1), ((0, 2, 0), -1)),
        ])

    def test_every_fixture_basis_satisfies_buchberger_and_is_reduced(self):
        for name, arity, relations, _ in ref.cases():
            with self.subTest(name):
                basis = ref.groebner(relations)
                for g, h in combinations(basis, 2):
                    self.assertEqual(ref.normal_form(ref.s_polynomial(g, h), basis), {})
                for f in relations:
                    self.assertEqual(ref.normal_form(f, basis), {})
                for g in basis:
                    self.assertEqual(g[ref.leading(g)], 1)
                    for h in basis:
                        if h is not g:
                            self.assertFalse(any(ref.divides(ref.leading(h), m) for m in g))

    def test_normal_forms_do_not_depend_on_divisor_order(self):
        for name, arity, relations, probes in ref.cases():
            basis = ref.groebner(relations)
            for probe in probes:
                expected = ref.normal_form(probe, basis)
                for order in permutations(basis):
                    with self.subTest(name):
                        self.assertEqual(ref.normal_form(probe, list(order)), expected)

    def test_dual_number_epsilon_is_nonzero_and_squares_to_zero(self):
        basis = ref.groebner([p(1, ((2,), 1))])
        self.assertEqual(ref.normal_form(p(1, ((1,), 1)), basis), p(1, ((1,), 1)))
        self.assertEqual(ref.normal_form(p(1, ((2,), 1)), basis), {})

    def test_rational_coefficients_stay_exact(self):
        basis = ref.groebner([p(1, ((1,), Fraction(3, 5)), ((0,), Fraction(-7, 2)))])
        self.assertEqual(basis, [p(1, ((1,), 1), ((0,), Fraction(-35, 6)))])

    def test_invalid_inputs_are_rejected(self):
        with self.assertRaises(ref.Invalid):
            ref.poly([((1,), 1)], 2)
        with self.assertRaises(ref.Invalid):
            ref.poly([((-1,), 1)], 1)
        with self.assertRaises(ref.Invalid):
            ref.poly([((1,), 0.5)], 1)
        with self.assertRaises(ref.Invalid):
            ref.decode_rational(3)

    def test_fixture_is_current(self):
        self.assertEqual(ref.main(["--check"]), 0)


if __name__ == "__main__":
    unittest.main()
