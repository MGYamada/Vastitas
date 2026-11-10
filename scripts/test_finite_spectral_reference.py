"""Exact examples and independently mutated obligations for the finite pair."""

import itertools
import json
from dataclasses import replace
from fractions import Fraction as Q
from pathlib import Path
import subprocess
import sys
import unittest
from unittest.mock import patch

import finite_spectral_reference as fs
from metric_free_reference import determinant, inverse, matrix, matvec, multiply
from rational_polynomial_calculus import evaluate, substitute
from rational_polynomial_reference import Invalid, Poly


T, ONE, ZERO = fs.T, fs.ONE, fs.ZERO
I, O = fs.IDENTITY, fs.ZERO_MATRIX
J = matrix(((0, 1), (0, 0)))
SWAP = matrix(((0, 1), (1, 0)))
FRAME = fs.Frame("test-env", "QQ", "V", "e0,e1")


def subject(h, name="H", frame=FRAME):
    return fs.Subject(name, "1", frame, frame, h)


class FiniteSpectralTests(unittest.TestCase):
    def reject(self, code, call):
        with self.assertRaises(Invalid) as caught:
            call()
        self.assertEqual(caught.exception.code, code)

    def checked(self, h, name="H"):
        s = subject(h, name)
        e = fs.propose(s)
        self.assertEqual(fs.verify(s, e), e)
        return s, e

    def test_zero_and_jordan_have_same_scheme_but_different_action(self):
        s0, e0 = self.checked(O, "zero")
        sj, ej = self.checked(J, "jordan")
        self.assertEqual(e0.algebra, ej.algebra)
        self.assertEqual(e0.algebra.relation, T ** 2)
        self.assertEqual(fs.act(s0, e0, T, (0, 1)), (0, 0))
        self.assertEqual(fs.act(sj, ej, T, (0, 1)), (1, 0))
        for s, e in ((s0, e0), (sj, ej)):
            self.assertEqual(fs.act(s, e, T ** 2, (2, 3)), (0, 0))
            # The characteristic algebra stays nonreduced even when M is killed by t.
            self.assertEqual(e.algebra.reduce(T), T)
            self.assertEqual(e.algebra.reduce(T ** 2), ZERO)

    def test_shifted_repeated_rational_root_retains_epsilon(self):
        a = Q(3, 7)
        for h, expected in ((((a, 0), (0, a)), (0, 0)),
                            (((a, 1), (0, a)), (1, 0))):
            s, e = self.checked(h)
            self.assertEqual(e.algebra.relation, (T - a) ** 2)
            self.assertNotEqual(e.algebra.reduce(T - a), ZERO)
            self.assertEqual(e.algebra.reduce((T - a) ** 2), ZERO)
            self.assertEqual(fs.act(s, e, T - a, (0, 1)), expected)

    def test_exact_characteristic_known_nondiagonal_and_tiny_entries(self):
        s, e = self.checked(((Q(1, 2), Q(2, 3)), (Q(-3, 5), Q(7, 11))))
        self.assertEqual(e.algebra.relation, T ** 2 - Q(25, 22) * T + Q(79, 110))
        tiny = Q(1, 10 ** 60)
        s, e = self.checked(((0, tiny), (0, 0)))
        self.assertEqual(fs.act(s, e, T, (0, 1)), (tiny, 0))
        self.reject("RECOVERY_MISMATCH", lambda: fs.verify(s, replace(e, t_action=O)))

    def test_finite_rational_matrix_family_and_direct_ch_columns(self):
        for entries in itertools.product((Q(-2, 3), Q(0), Q(5, 7)), repeat=4):
            a, b, c, d = entries
            s, e = self.checked(((a, b), (c, d)))
            self.assertEqual(e.algebra.relation, (T - a) * (T - d) - b * c)
            for v in ((1, 0), (0, 1)):
                hv = (a * v[0] + b * v[1], c * v[0] + d * v[1])
                hhv = (a * hv[0] + b * hv[1], c * hv[0] + d * hv[1])
                self.assertEqual(tuple(hhv[i] - (a + d) * hv[i] + (a * d - b * c) * v[i]
                                       for i in range(2)), (0, 0))

    def test_producer_error_is_not_echoed_by_characteristic_check(self):
        s = subject(O)
        with patch.object(fs, "characteristic_polynomial", return_value=T ** 2 + T):
            e = fs.propose(s)
        # A wrong monic quadratic still annihilates this H: CH alone is insufficient.
        fs.check_cayley_hamilton(s, e.algebra)
        self.reject("CHARACTERISTIC_MISMATCH", lambda: fs.verify(s, e))

    def test_ch_and_quotient_action_fail_independently(self):
        s, e = self.checked(I)
        self.reject("CAYLEY_HAMILTON_FAILURE", lambda: fs.check_cayley_hamilton(
            s, fs.QuadraticAlgebra("t", T ** 2)))
        sj, ej = self.checked(J)
        self.reject("QUOTIENT_ACTION_FAILURE", lambda: fs.verify(sj, replace(ej, t_action=I)))
        self.reject("NONUNITAL_ACTION", lambda: fs.verify(sj, replace(ej, unit_action=O)))

    def test_nilpotent_erasure_passes_quotient_but_fails_recovery(self):
        s, e = self.checked(J)
        forged = replace(e, t_action=O)
        fs.check_quotient_action(forged)
        self.reject("RECOVERY_MISMATCH", lambda: fs.verify(s, forged))

    def test_singular_pushforward_cannot_hide_erased_action(self):
        s, e = self.checked(J)
        self.reject("INVALID_PUSHFORWARD", lambda: fs.verify(
            s, replace(e, t_action=O, pushforward=O)))

    def test_same_charpoly_payload_replay_and_relabel_both_rejected(self):
        s0, e0 = self.checked(O, "zero")
        sj, ej = self.checked(J, "jordan")
        self.reject("SUBJECT_MISMATCH", lambda: fs.verify(sj, e0))
        self.reject("RECOVERY_MISMATCH", lambda: fs.verify(sj, replace(e0, subject=sj)))
        self.reject("RECOVERY_MISMATCH", lambda: fs.verify(s0, replace(ej, subject=s0)))
        self.reject("INVALID_SCHEMA", lambda: fs.verify(sj, ej.algebra))

    def test_root_set_reduction_and_annihilator_substitution_rejected(self):
        for relation in (T, T - 2, ONE, ZERO, 2 * T ** 2, T ** 3):
            self.reject("NOT_MONIC_QUADRATIC", lambda: fs.QuadraticAlgebra("t", relation))
        s, e = self.checked(O)
        # ann(M_0)=(t) is smaller information than the characteristic ideal (t^2).
        self.assertEqual(fs.evaluate_at(T, s.h), O)
        self.assertNotEqual(e.algebra.reduce(T), ZERO)

    def test_regular_representation_is_jordan_only_with_explicit_isomorphism(self):
        sj, ej = self.checked(J)
        self.assertEqual(ej.algebra.regular_action(), ((0, 0), (1, 0)))
        self.assertEqual(fs.check_structure_sheaf_isomorphism(sj, ej, SWAP), SWAP)
        s0, e0 = self.checked(O)
        self.reject("NOT_REGULAR_MODULE", lambda: fs.check_structure_sheaf_isomorphism(s0, e0, I))
        self.reject("NOT_REGULAR_MODULE", lambda: fs.check_structure_sheaf_isomorphism(s0, e0, SWAP))
        self.reject("SINGULAR_COMPARISON", lambda: fs.check_structure_sheaf_isomorphism(s0, e0, O))
        # For H0 every candidate (v,Hv) has determinant zero: no cyclic generator.
        for v in ((1, 0), (0, 1), (Q(2, 3), Q(-5, 7))):
            self.assertEqual(determinant(tuple(zip(v, matvec(O, v)))), 0)

    def test_replacing_every_module_with_structure_sheaf_is_rejected(self):
        s, e = self.checked(O)
        fake = replace(e, t_action=e.algebra.regular_action())
        fs.check_quotient_action(fake)
        self.reject("RECOVERY_MISMATCH", lambda: fs.verify(s, fake))

    def test_quotient_representatives_and_module_laws(self):
        p, q = Q(2, 3) * T ** 5 - T + Q(7, 11), T ** 3 + 2 * T + 1
        for h in (O, J, ((1, 2), (3, 4)), ((0, 2), (1, 0))):
            s, e = self.checked(h)
            a = e.algebra
            v, w = (Q(2, 3), Q(-7, 5)), (Q(-1, 2), Q(4, 9))
            apply = lambda f, x: fs.act(s, e, f, x)
            self.assertEqual(a.reduce(p + a.relation * q), a.reduce(p))
            self.assertEqual(apply(p + a.relation * q, v), apply(p, v))
            self.assertEqual(apply(ONE, v), v)
            self.assertEqual(apply(ZERO, v), (0, 0))
            self.assertEqual(apply(p * q, v), apply(p, apply(q, v)))
            self.assertEqual(apply(p + q, v), tuple(x + y for x, y in zip(apply(p, v), apply(q, v))))
            self.assertEqual(apply(p, tuple(x + y for x, y in zip(v, w))),
                             tuple(x + y for x, y in zip(apply(p, v), apply(p, w))))
            # Direct unreduced evaluation uses matrix powers, not quotient reduction.
            self.assertEqual(apply(p, v), matvec(fs.evaluate_at(p, h), v))

    def test_regular_algebra_laws_and_nonreduced_basis(self):
        a = fs.QuadraticAlgebra("t", T ** 2 - 3 * T + 2)
        for p, q, r in itertools.product((ONE, T, 2 * T - 3), repeat=3):
            self.assertEqual(a.product(a.product(p, q), r), a.product(p, a.product(q, r)))
            self.assertEqual(a.product(p, q + r), a.reduce(a.product(p, q) + a.product(p, r)))
        double = fs.QuadraticAlgebra("epsilon", T ** 2)
        self.assertNotEqual(double.reduce(T), ZERO)
        self.assertEqual(double.product(T, T), ZERO)
        self.assertEqual(double.reduce(3 + 2 * T), 3 + 2 * T)

    def test_explicit_similarity_retains_distinct_frames_and_all_actions(self):
        s, e = self.checked(((1, 2), (3, 4)))
        u = matrix(((1, Q(2, 3)), (Q(-1, 2), 1)))
        other = replace(FRAME, basis_id="f0,f1")
        target = subject(multiply(multiply(inverse(u), s.h), u), "H-in-f", other)
        te = fs.propose(target)
        self.assertEqual(fs.check_similarity(s, target, e, te, u), u)
        self.assertNotEqual(s, target)
        self.assertEqual(e.algebra, te.algebra)
        for p in (T, T ** 2 + T + 3, Q(7, 9) * T ** 4):
            self.assertEqual(multiply(fs.evaluate_at(p, s.h), u), multiply(u, fs.evaluate_at(p, target.h)))

    def test_changed_private_module_coordinates_recover_original_h(self):
        s, e = self.checked(J)
        changed = replace(e, t_action=multiply(multiply(inverse(SWAP), s.h), SWAP), pushforward=SWAP)
        fs.verify(s, changed)
        for v in ((1, 0), (0, 1)):
            self.assertEqual(matvec(SWAP, fs.act(s, changed, T, v)), matvec(s.h, matvec(SWAP, v)))

    def test_false_similarity_direction_and_singular_intertwiners(self):
        s0, e0 = self.checked(O)
        sj, ej = self.checked(J)
        self.reject("NOT_INTERTWINING", lambda: fs.check_similarity(s0, sj, e0, ej, I))
        self.reject("SINGULAR_COMPARISON", lambda: fs.check_similarity(s0, sj, e0, ej, O))
        u = matrix(((2, 1), (0, 1)))
        right = subject(multiply(multiply(inverse(u), J), u))
        self.reject("NOT_INTERTWINING", lambda: fs.check_similarity(sj, right, ej, fs.propose(right), inverse(u)))

    def test_stale_nominal_data_and_coefficient_bases(self):
        s, e = self.checked(J)
        for altered in (replace(s, map_id="other"), replace(s, revision="2"), replace(s, h=O)):
            self.reject("SUBJECT_MISMATCH", lambda: fs.verify(altered, e))
        for field in ("environment_id", "coefficient_id", "space_id", "basis_id"):
            frame = replace(FRAME, **{field: "other"})
            altered = replace(s, source=frame, target=frame)
            self.reject("SUBJECT_MISMATCH", lambda: fs.verify(altered, e))
            if field in ("environment_id", "coefficient_id"):
                self.reject("COEFFICIENT_BASE_MISMATCH", lambda: fs.check_similarity(s, altered, e, fs.propose(altered), I))
        self.reject("ENDPOINT_MISMATCH", lambda: replace(s, target=replace(FRAME, basis_id="other")))
        self.reject("CHARACTERISTIC_MISMATCH", lambda: fs.verify(s, replace(e, algebra=replace(e.algebra, generator="energy-other"))))

    def test_unsupported_scalars_shapes_and_float_observations(self):
        for profile in ("F64", "noncommutative", "CC"):
            self.reject("UNSUPPORTED_SCALARS", lambda: replace(FRAME, scalar_profile=profile))
        for value in (0.0, 1.0, True, complex(1), "1/2"):
            self.reject("INEXACT_INPUT", lambda: subject(((value, 0), (0, 0))))
        self.reject("INVALID_SHAPE", lambda: subject(((0, 0, 0), (0, 0, 0))))
        self.reject("INVALID_POLYNOMIAL", lambda: fs.QuadraticAlgebra("t", Poly.variable(0, 2) ** 2))
        s, e = self.checked(J)
        self.reject("INEXACT_INPUT", lambda: replace(e, t_action=((0, 1.0), (0, 0))))
        self.reject("INEXACT_INPUT", lambda: fs.act(s, e, T, (True, 1)))

    def test_explicit_eigenvector_is_not_a_canonical_choice_at_degeneracy(self):
        s, e = self.checked(O)
        v = fs.check_eigenvector(s, e, 0, (1, 0), selection="explicit")
        # SWAP is an automorphism of H0 but moves the selected eigenline.
        fs.check_similarity(s, s, e, e, SWAP)
        self.assertNotEqual(matvec(SWAP, v), v)
        self.assertEqual(fs.check_eigenvector(s, e, 0, matvec(SWAP, v), selection="explicit"), (0, 1))
        for tag in ("canonical", "canonical-frame", "smooth-branch", "metric-normalized"):
            self.reject("UNSUPPORTED_CANONICAL_SELECTION", lambda: fs.check_eigenvector(s, e, 0, v, selection=tag))
        self.reject("INVALID_EIGENVECTOR", lambda: fs.check_eigenvector(s, e, 0, (0, 0), selection="explicit"))
        sj, ej = self.checked(J)
        self.reject("INVALID_EIGENVECTOR", lambda: fs.check_eigenvector(sj, ej, 0, (0, 1), selection="explicit"))
        self.reject("INEXACT_INPUT", lambda: fs.check_eigenvector(s, e, 0.0, v, selection="explicit"))

    def test_specialization_at_collision_does_not_diagonalize_jordan(self):
        parameter, energy = Poly.variable(0, 2), Poly.variable(1, 2)
        family_characteristic = (energy - parameter) * (energy + parameter)
        for value in (Q(-2), Q(-1, 3), Q(0), Q(2, 5), Q(7)):
            sd, ed = self.checked(((value, 0), (0, -value)), "diagonal-family")
            sj, ej = self.checked(((value, 1), (0, -value)), "triangular-family")
            specialized = substitute(family_characteristic, (Poly.constant(value, 1), T))
            self.assertEqual(ed.algebra.relation, specialized)
            self.assertEqual(ej.algebra.relation, specialized)
            if value:
                fs.check_similarity(sd, sj, ed, ej, ((1, 1 / (2 * value)), (0, 1)))
            else:
                self.assertEqual(ej.algebra.reduce(T ** 2), ZERO)
                self.assertNotEqual(ej.algebra.reduce(T), ZERO)
                self.assertNotEqual(ed.t_action, ej.t_action)
                self.reject("NOT_INTERTWINING", lambda: fs.check_similarity(sd, sj, ed, ej, I))

    def test_irreducible_quadratic_splits_after_exact_coefficient_extension(self):
        s, e = self.checked(((0, 2), (1, 0)))
        scalars = fs.QuadraticAlgebra("u=sqrt(2)", T ** 2 - 2)
        ext = fs.propose_scalar_extension(s, e, scalars)
        fs.check_scalar_extension(s, e, scalars, ext)
        self.assertEqual(ext.characteristic, (Poly.constant(-2, 1), ZERO, ONE))
        # v+=(u,1), v-=(-u,1), genuinely outside QQ^2.
        for sign in (-1, 1):
            v = (sign * T, ONE)
            actual = fs.extended_act(s, e, scalars, ext, ZERO, ONE, v)
            self.assertEqual(actual, tuple(scalars.product(sign * T, x) for x in v))
        # det[v+,v-]=2u is a unit: inverse u/4. No eigenvector solver used.
        self.assertEqual(scalars.product(2 * T, Q(1, 4) * T), ONE)

    def test_base_change_keeps_distinct_module_actions_and_nilpotents(self):
        for scalars in (fs.QuadraticAlgebra("sqrt2", T ** 2 - 2),
                        fs.QuadraticAlgebra("dual-u", T ** 2)):
            for h, output in ((O, (ZERO, ZERO)), (J, (T, ZERO))):
                s, e = self.checked(h)
                ext = fs.propose_scalar_extension(s, e, scalars)
                self.assertEqual(fs.extended_act(s, e, scalars, ext, ZERO, ONE, (ZERO, T)), output)
                self.assertEqual(fs.extended_act(s, e, scalars, ext, ZERO, ONE, output), (ZERO, ZERO))
                self.assertEqual(ext.characteristic, (ZERO, ZERO, ONE))
                self.assertNotEqual(scalars.reduce(T), ZERO)

    def test_base_change_action_laws_with_nonrational_coefficients(self):
        s, e = self.checked(((0, 2), (1, 0)))
        k = fs.QuadraticAlgebra("sqrt2", T ** 2 - 2)
        ext = fs.propose_scalar_extension(s, e, k)
        v = (T + 1, 2 * T - 3)
        a, b, c, d = T + 1, T - 2, 2 * T + 3, 3 * T - 1
        action = lambda x, y, v: fs.extended_act(s, e, k, ext, x, y, v)
        # (a+bt)(c+dt)=(ac+2bd)+(ad+bc)t in the extended spectral algebra.
        self.assertEqual(action(a, b, action(c, d, v)),
                         action(k.reduce(a * c + 2 * b * d), k.reduce(a * d + b * c), v))
        self.assertEqual(action(ONE, ZERO, v), v)

    def test_base_change_rejects_forged_characteristic_action_and_context(self):
        s, e = self.checked(J)
        k = fs.QuadraticAlgebra("sqrt2", T ** 2 - 2)
        ext = fs.propose_scalar_extension(s, e, k)
        self.reject("BASE_CHANGE_CHARACTERISTIC_MISMATCH", lambda: fs.check_scalar_extension(
            s, e, k, replace(ext, characteristic=(ONE, ZERO, ONE))))
        erased = replace(ext, action=((ZERO, ZERO), (ZERO, ZERO)))
        self.reject("BASE_CHANGE_ACTION_MISMATCH", lambda: fs.check_scalar_extension(s, e, k, erased))
        # Same determinant and CH, but a new nonrational off-diagonal is not scalar extension.
        forged = replace(ext, action=((ZERO, T), (ZERO, ZERO)))
        self.reject("BASE_CHANGE_ACTION_MISMATCH", lambda: fs.check_scalar_extension(s, e, k, forged))
        other = fs.QuadraticAlgebra("sqrt3", T ** 2 - 3)
        self.reject("BASE_CHANGE_SUBJECT_MISMATCH", lambda: fs.check_scalar_extension(s, e, other, ext))
        self.reject("BASE_CHANGE_SUBJECT_MISMATCH", lambda: fs.check_scalar_extension(s, e, k, replace(ext, subject=replace(s, revision="2"))))
        self.reject("NONCANONICAL_ELEMENT", lambda: replace(ext, action=((ZERO, T ** 2 - 1), (ZERO, ZERO))))

    def test_ssh_rational_torus_fibers_match_characteristic_consumer(self):
        # #247: clear only the invertible z denominator, in QQ[v,w,z,E].
        v, w, z, energy = (Poly.variable(i, 4) for i in range(4))
        cleared = z * energy ** 2 - (v * z + w) * (v + w * z)
        for vv, ww, zz in itertools.product((Q(0), Q(1), Q(2, 3)), (Q(-1), Q(1)), (Q(-2), Q(-1), Q(2, 5))):
            h = ((0, vv + ww / zz), (vv + ww * zz, 0))
            s, e = self.checked(h)
            at_z = substitute(cleared, (Poly.constant(vv, 1), Poly.constant(ww, 1), Poly.constant(zz, 1), T))
            self.assertEqual(at_z, zz * e.algebra.relation)
            self.assertEqual(evaluate(e.algebra.relation, (Q(0),)), -(vv + ww * zz) * (vv + ww / zz))

    def test_ssh_fermi_double_point_is_not_reduced_and_module_is_not_regular(self):
        v, w, z, energy = (Poly.variable(i, 4) for i in range(4))
        cleared = z * energy ** 2 - (v * z + w) * (v + w * z)
        fermi = substitute(cleared, (ONE, ONE, T, ZERO))
        self.assertEqual(fermi, -(T + 1) ** 2)
        a = fs.QuadraticAlgebra("z", -fermi)
        epsilon, z_inverse = T + 1, -T - 2
        self.assertEqual(a.product(T, z_inverse), ONE)
        self.assertNotEqual(a.reduce(epsilon), ZERO)
        self.assertEqual(a.product(epsilon, epsilon), ZERO)
        self.assertEqual(a.product(ONE + T, ONE + z_inverse), ZERO)
        # A different fiber: z=-1 first, leaving the energy coordinate t.
        s, e = self.checked(O, "SSH(v=w=1,z=-1)")
        self.assertEqual(e.algebra.relation, T ** 2)
        self.assertEqual(fs.act(s, e, T, (0, 1)), (0, 0))
        self.assertNotEqual(e.algebra.regular_action(), e.t_action)
        self.reject("NOT_REGULAR_MODULE", lambda: fs.check_structure_sheaf_isomorphism(s, e, I))

    def test_demo_executes_without_optional_packages(self):
        root = Path(__file__).resolve().parents[1]
        completed = subprocess.run([sys.executable, "-S", "scripts/demo_finite_spectral_reference.py"],
                                   cwd=root, text=True, capture_output=True, check=True)
        report = json.loads(completed.stdout)
        self.assertEqual(report["status"], "external exact reference; Lean/Core/native pending")
        self.assertEqual(report["same_characteristic"], True)
        self.assertEqual(report["epsilon_on_zero"], ["0", "0"])
        self.assertEqual(report["epsilon_on_jordan"], ["1", "0"])
        self.assertEqual(report["rejections"]["erase_jordan"], "RECOVERY_MISMATCH")
        self.assertEqual(report["rejections"]["false_structure_sheaf"], "NOT_REGULAR_MODULE")
        self.assertEqual(report["ssh_fermi_epsilon_nonzero"], True)


if __name__ == "__main__":
    unittest.main()
