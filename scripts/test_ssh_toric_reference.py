"""Exact SSH scheme regressions; these do not run or certify .vast/Lean code."""

import json
import subprocess
import sys
import unittest
from dataclasses import replace
from fractions import Fraction as Q
from pathlib import Path

import ssh_toric_reference as sr


ROOT = Path(__file__).resolve().parents[1]


def multiply2(left, right):
    return tuple(tuple(sum(left[i][k] * right[k][j] for k in range(2))
                       for j in range(2)) for i in range(2))


def scalar_value(poly, v, w, energy, z):
    """Independent direct exact evaluation, without the specialization API."""
    return sum((c * Q(v) ** p[0] * Q(w) ** p[1] * Q(energy) ** p[2] * Q(z) ** p[3]
                for p, c in poly.terms), Q(0))


class LaurentTests(unittest.TestCase):
    def test_canonical_finite_support_and_negative_characters(self):
        poly = sr.Laurent.from_terms([((0, 0, 0, -2), Q(1, 3)),
                                     ((0, 0, 0, -2), Q(2, 3)),
                                     ((1, 0, 0, 0), 1), ((1, 0, 0, 0), -1)])
        self.assertEqual(poly, sr.Laurent.character(-2))
        self.assertEqual(poly * sr.Z ** 2, sr.ONE)
        self.assertEqual(sr.Z * sr.Z_INV, sr.ONE)

    def test_reject_inexact_and_invalid_support_before_cancellation(self):
        for value in (0.5, True, "1/2"):
            with self.subTest(value=value), self.assertRaises(ValueError):
                sr.Laurent.constant(value)
            with self.subTest(value=value), self.assertRaises(ValueError):
                sr.ONE - value
        for powers in ((-1, 0, 0, 0), (0, -1, 0, 0), (0, 0, -1, 0),
                       (0, 0, 0, Q(1, 2)), (0, 0, 0, True), (0, 0, 1)):
            with self.subTest(powers=powers), self.assertRaises(ValueError):
                sr.Laurent.from_terms([(powers, 0)])
        with self.assertRaises(ValueError):
            sr.Laurent((((0, 0, 0, 0), Q(1)), ((0, 0, 0, 0), Q(2))))
        with self.assertRaises(ValueError):
            (sr.Z + 1) ** -1

    def test_rational_specialization_must_respect_localization(self):
        self.assertEqual(sr.Z_INV.specialize(z=Q(2, 3)), sr.Laurent.constant(Q(3, 2)))
        for poly in (sr.Z_INV, sr.Z, sr.ONE, sr.ZERO):
            with self.subTest(poly=poly), self.assertRaises(ValueError):
                poly.specialize(z=0)
        for values in ({"v": 1.0}, {"w": True}, {"unknown": 1}):
            with self.subTest(values=values), self.assertRaises(ValueError):
                sr.ONE.specialize(**values)


class SSHFamilyTests(unittest.TestCase):
    def setUp(self):
        self.h = sr.ssh_hamiltonian()
        self.family = sr.ssh_bloch_family()

    def test_symbolic_determinant_and_monic_energy_degree(self):
        expected = sr.Laurent.from_terms([
            ((0, 0, 2, 0), 1), ((2, 0, 0, 0), -1), ((0, 2, 0, 0), -1),
            ((1, 1, 0, 1), -1), ((1, 1, 0, -1), -1),
        ])
        self.assertEqual(self.family.equation, expected)
        energy_terms = [(p, c) for p, c in expected.terms if p[2]]
        self.assertEqual(energy_terms, [((0, 0, 2, 0), Q(1))])
        self.assertEqual(sr.characteristic2(((2, 3), (5, 7))), sr.E ** 2 - 9 * sr.E - 1)

    def test_specialize_matrix_before_or_after_determinant(self):
        for v in (0, 1, -1, 2, Q(2, 3)):
            for w in (0, 1, -1, Q(3, 2)):
                with self.subTest(v=v, w=w):
                    after = self.family.equation.specialize(v=v, w=w)
                    before = sr.characteristic2(sr.specialize_matrix(self.h, v=v, w=w))
                    self.assertEqual(before, after)
                    for energy in (0, Q(1, 2)):
                        for z in (-1, 2, Q(1, 3)):
                            expected = Q(energy) ** 2 - (Q(v) + Q(w) * z) * (Q(v) + Q(w) / z)
                            self.assertEqual(scalar_value(after, 0, 0, energy, z), expected)

    def test_zero_energy_and_parameter_base_changes_commute(self):
        for v, w in ((1, 1), (0, 0), (0, 1), (1, 0), (2, 1), (Q(1, 3), -2)):
            with self.subTest(v=v, w=w):
                energy_first = self.family.specialize(E=0).target.specialize(v=v, w=w)
                params_first = self.family.specialize(v=v, w=w).target.specialize(E=0)
                together = self.family.specialize(v=v, w=w, E=0)
                separate = self.family.specialize(w=w).target.specialize(v=v).target.specialize(E=0)
                self.assertEqual(energy_first.target, params_first.target)
                self.assertEqual(energy_first.target, together.target)
                self.assertEqual(separate.target, together.target)
                self.assertEqual(together.target.coordinates, ("z",))

    def test_presentation_and_maps_retain_actual_equations_and_endpoints(self):
        fiber = self.family.specialize(v=1, w=1, E=0)
        self.assertEqual(fiber.source, self.family)
        self.assertEqual(fiber.assignments, (("v", Q(1)), ("w", Q(1)), ("E", Q(0))))
        self.assertEqual(fiber.target.equation, -sr.Z_INV * (sr.Z + 1) ** 2)
        with self.assertRaises(ValueError):
            replace(fiber, target=sr.TorusPresentation(("z",), sr.Z + 1))
        with self.assertRaises(ValueError):
            replace(fiber, assignments=(("v", Q(1)), ("v", Q(1))))
        with self.assertRaises(ValueError):
            sr.TorusPresentation(("z",), sr.V)
        with self.assertRaises(ValueError):
            fiber.target.specialize(v=1)
        with self.assertRaises(ValueError):
            self.family.specialize(z=-1)

    def test_degenerate_hoppings_not_silently_divided_out(self):
        for v, w, expected in ((0, 0, sr.ZERO), (0, 1, -sr.ONE), (1, 0, -sr.ONE)):
            with self.subTest(v=v, w=w):
                fiber = self.family.specialize(v=v, w=w, E=0).target
                self.assertEqual(fiber.equation, expected)  # whole torus / empty scheme
                with self.assertRaises(ValueError):
                    sr.require_ssh_double_point(fiber)
        distinct = self.family.specialize(v=2, w=1, E=0).target
        self.assertEqual(distinct.equation.specialize(z=-2), sr.ZERO)
        self.assertEqual(distinct.equation.specialize(z=Q(-1, 2)), sr.ZERO)
        with self.assertRaises(ValueError):
            sr.require_ssh_double_point(distinct)

    def test_minimal_denominator_representatives_need_not_commute_with_specialization(self):
        k, family_numerator = sr.clear_z_denominator(self.family.equation)
        specialized = self.family.equation.specialize(v=0, w=0)
        after_k, after_numerator = sr.clear_z_denominator(specialized)
        before_numerator = family_numerator.specialize(v=0, w=0)
        self.assertEqual((k, after_k), (1, 0))
        self.assertNotEqual(before_numerator, after_numerator)
        self.assertEqual(sr.Laurent.character(-k) * before_numerator,
                         sr.Laurent.character(-after_k) * after_numerator)
        # Saturation of the specialized numerator removes the extra boundary z.
        self.assertEqual(sr.saturate_principal_z(before_numerator).generator, sr.E ** 2)

    def test_unsupported_hamiltonians_rejected(self):
        with self.assertRaises(ValueError):
            sr.characteristic2(((sr.E, 0), (0, 0)))
        with self.assertRaises(ValueError):
            sr.characteristic2(((1, 2, 3), (4, 5, 6)))


class DoublePointTests(unittest.TestCase):
    def setUp(self):
        self.fiber = sr.ssh_bloch_family().specialize(v=1, w=1, E=0).target

    def test_nonzero_nilpotent_and_invertible_z(self):
        self.assertEqual(sr.require_ssh_double_point(self.fiber), (sr.Dual(1), sr.EPSILON))
        self.assertNotEqual(sr.EPSILON, sr.Dual())
        self.assertEqual(sr.EPSILON ** 2, sr.Dual())
        self.assertEqual(sr.DUAL_Z.inverse(), sr.Dual(-1, -1))
        self.assertEqual(sr.DUAL_Z * sr.DUAL_Z.inverse(), sr.Dual(1))
        self.assertEqual(sr.DUAL_Z.inverse() * sr.DUAL_Z, sr.Dual(1))
        self.assertEqual(sr.in_double_point(self.fiber.equation), sr.Dual())
        self.assertEqual(sr.in_double_point(sr.Z + 1), sr.EPSILON)
        self.assertEqual(sr.in_double_point(sr.Z_INV), sr.Dual(-1, -1))

    def test_regular_representation_retains_length_two(self):
        nilpotent = sr.EPSILON.multiplication_matrix()
        identity = sr.Dual(1).multiplication_matrix()
        zero = ((Q(0), Q(0)), (Q(0), Q(0)))
        self.assertEqual(nilpotent, ((0, 0), (1, 0)))
        self.assertNotEqual(nilpotent, zero)
        self.assertEqual(multiply2(nilpotent, nilpotent), zero)
        self.assertEqual(multiply2(sr.DUAL_Z.multiplication_matrix(),
                                   sr.DUAL_Z.inverse().multiplication_matrix()), identity)
        # Faithfulness: the first column of multiplication by a+b*epsilon is (a,b).
        for element in (sr.Dual(2, Q(3, 2)), sr.EPSILON, sr.DUAL_Z):
            self.assertEqual(tuple(row[0] for row in element.multiplication_matrix()),
                             (element.a, element.b))

    def test_laurent_quotient_agrees_with_independent_first_order_remainder(self):
        for n in range(-9, 10):
            with self.subTest(n=n):
                # Taylor remainder mod (z+1)^2, with exact negative powers too.
                expected = sr.Dual(Q(-1) ** n, n * Q(-1) ** (n - 1))
                self.assertEqual(sr.in_double_point(sr.Laurent.character(n)), expected)
        p = 3 * sr.Z ** 4 - 2 * sr.Z_INV + Q(1, 2) * sr.Laurent.character(-3)
        q = sr.Z ** 3 + 7 * sr.Z_INV
        self.assertEqual(sr.in_double_point(p * q), sr.in_double_point(p) * sr.in_double_point(q))
        self.assertEqual(sr.in_double_point(p + q), sr.in_double_point(p) + sr.in_double_point(q))
        self.assertEqual(sr.in_double_point(p + q * (sr.Z + 1) ** 2), sr.in_double_point(p))

    def test_reducing_to_points_loses_multiplicity(self):
        reduced, doubled = sr.Z + 1, (sr.Z + 1) ** 2
        self.assertEqual(reduced.specialize(z=-1), sr.ZERO)
        self.assertEqual(doubled.specialize(z=-1), sr.ZERO)
        self.assertNotEqual(sr.in_double_point(reduced), sr.Dual())
        self.assertEqual(sr.in_double_point(doubled), sr.Dual())
        # The reduction map a+b*epsilon -> a collapses distinct elements.
        self.assertNotEqual(sr.Dual(3, 1), sr.Dual(3, 0))
        self.assertEqual(sr.Dual(3, 1).a, sr.Dual(3, 0).a)
        for equation in (reduced, reduced ** 3):
            with self.subTest(equation=equation), self.assertRaises(ValueError):
                sr.require_ssh_double_point(sr.TorusPresentation(("z",), equation))

    def test_ssh_matrix_on_double_point_is_not_its_reduced_value(self):
        h = sr.specialize_matrix(sr.ssh_hamiltonian(), v=1, w=1)
        self.assertEqual(sr.in_double_point(h[0][1]), -sr.EPSILON)
        self.assertEqual(sr.in_double_point(h[1][0]), sr.EPSILON)
        self.assertEqual(sr.specialize_matrix(h, z=-1), sr.matrix2(((0, 0), (0, 0))))

    def test_nonunits_and_unspecialized_expressions_rejected(self):
        for element in (sr.Dual(), sr.EPSILON):
            with self.subTest(element=element), self.assertRaises(ValueError):
                element.inverse()
        with self.assertRaises(ValueError):
            sr.in_double_point(sr.V + sr.Z)
        for value in (True, 0.5):
            with self.subTest(value=value), self.assertRaises(ValueError):
                sr.Dual(1) - value


class BoundaryAndJordanTests(unittest.TestCase):
    def setUp(self):
        self.p = sr.ssh_bloch_family().specialize(v=1, w=1).target.equation
        self.f = sr.Z * sr.E ** 2 - (sr.Z + 1) ** 2

    def test_extra_denominator_clearing_adds_an_entire_affine_component(self):
        self.assertEqual(sr.clear_z_denominator(self.p), (1, self.f))
        bad = sr.Z * self.f
        self.assertEqual(sr.polynomial_boundary_at_z_zero(bad), sr.ZERO)  # all E
        self.assertEqual(sr.polynomial_boundary_at_z_zero(self.f), -sr.ONE)
        self.assertNotEqual(self.f, bad)
        self.assertEqual(sr.Z_INV * bad, self.f)  # a unit multiple on the torus
        with self.assertRaises(ValueError):
            sr.polynomial_boundary_at_z_zero(self.p)

    def test_principal_saturation_recovers_f_and_keeps_double_multiplicity(self):
        for power in (0, 1, 2, 7):
            for generator in (self.f, (sr.Z + 1) ** 2):
                with self.subTest(power=power, generator=generator):
                    original = sr.Z ** power * generator
                    witness = sr.saturate_principal_z(original)
                    self.assertTrue(sr.check_principal_z_saturation(original, witness))
                    self.assertEqual(witness.removed_power, power)
                    self.assertEqual(witness.generator, generator)

    def test_forged_saturation_witnesses_fail(self):
        original = sr.Z * self.f
        witness = sr.saturate_principal_z(original)
        for changed in (replace(witness, removed_power=0), replace(witness, generator=self.f + 1),
                        replace(witness, original=self.f),
                        replace(witness, removed_power=0, generator=original)):
            with self.subTest(changed=changed):
                self.assertFalse(sr.check_principal_z_saturation(original, changed))
        doubled = sr.Z * (sr.Z + 1) ** 2
        radicalized = sr.PrincipalZSaturation(doubled, 1, sr.Z + 1)
        self.assertFalse(sr.check_principal_z_saturation(doubled, radicalized))

    def test_saturation_scope_is_not_general_ideal_membership(self):
        for value in (sr.ZERO, sr.V * self.f, sr.Z_INV, [self.f, sr.Z]):
            with self.subTest(value=value), self.assertRaises(ValueError):
                sr.saturate_principal_z(value)
        self.assertEqual(sr.saturate_principal_z(sr.Z ** 3).generator, sr.ONE)

    def test_same_characteristic_polynomial_does_not_determine_jordan_structure(self):
        zero_h = sr.specialize_matrix(sr.ssh_hamiltonian(), v=1, w=1, z=-1)
        jordan = sr.matrix2(((0, 1), (0, 0)))
        self.assertEqual(sr.characteristic2(zero_h), sr.E ** 2)
        self.assertEqual(sr.characteristic2(jordan), sr.E ** 2)
        self.assertEqual(sr.kernel_dimension2(zero_h), 2)
        self.assertEqual(sr.kernel_dimension2(jordan), 1)
        self.assertEqual(multiply2(((0, 1), (0, 0)), ((0, 1), (0, 0))), ((0, 0), (0, 0)))
        self.assertNotEqual(zero_h, jordan)
        self.assertEqual(sr.kernel_dimension2(((1, 0), (0, 1))), 0)
        with self.assertRaises(ValueError):
            sr.kernel_dimension2(sr.ssh_hamiltonian())


class DemoTests(unittest.TestCase):
    def test_demo_runs_without_optional_packages_and_reports_reference_status(self):
        result = subprocess.run([sys.executable, "-S", "scripts/demo_ssh_toric_reference.py"],
                                cwd=ROOT, text=True, capture_output=True, check=True)
        report = json.loads(result.stdout)
        self.assertEqual(report["status"], "external_exact_reference_only")
        self.assertFalse(report["vastitas_or_lean_acceptance"])
        self.assertTrue(all(report["checks"].values()))
        self.assertEqual(report["jordan_counterexample"]["kernel_dimensions"], [2, 1])


if __name__ == "__main__":
    unittest.main()
