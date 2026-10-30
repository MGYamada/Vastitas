"""Independent exact witnesses and rejection tests for the finite #301 profile."""

import json
import subprocess
import sys
import unittest
from dataclasses import fields, replace
from fractions import Fraction
from itertools import product
from pathlib import Path
from unittest.mock import patch

import car_reference as cr
import time_reversal_reference as tr


def fixture(model):
    coordinates = tr.reference_coordinates(model)
    # Expected target is supplied separately; never extract it from a candidate.
    target = tr.Selection(coordinates, model.profile)
    action = tr.Semilinear(coordinates, "T", model.reference_matrix, tr.ScalarAction.CONJUGATE)
    return target, action


def new_coordinates(source, b, name="complex basis"):
    return replace(source, basis=tr.Basis(name, source.model.model_id, ("new-0", "new-1"), b))


class SemilinearTests(unittest.TestCase):
    def setUp(self):
        self.target, self.t = fixture(tr.SPIN_HALF)

    def test_all_four_composition_profiles_and_coefficient_conjugation(self):
        a = cr.matrix([[cr.I, 0], [0, 1]])
        b = cr.matrix([[0, cr.I], [1, 0]])
        v = (cr.Qi(1, 2), cr.Qi(-3, 1))
        for left_sigma, right_sigma in product(tr.ScalarAction, repeat=2):
            with self.subTest(left=left_sigma, right=right_sigma):
                left = replace(self.t, entries=a, scalar_action=left_sigma)
                right = replace(self.t, entries=b, scalar_action=right_sigma)
                composite = tr.compose(left, right)
                expected = (cr.matrix([[0, -1], [1, 0]])
                            if left_sigma is tr.ScalarAction.IDENTITY else cr.X)
                self.assertEqual(composite.entries, expected)
                self.assertIs(composite.scalar_action,
                              tr.ScalarAction.IDENTITY if left_sigma is right_sigma
                              else tr.ScalarAction.CONJUGATE)
                self.assertEqual(tr.apply(composite, v), tr.apply(left, tr.apply(right, v)))
        # Ordinary multiplication is wrong when the OUTER action conjugates.
        self.assertNotEqual(cr.mul(a, b), cr.X)

    def test_associativity_and_identity_for_all_scalar_profiles(self):
        matrices = (cr.matrix([[cr.I, 0], [0, 1]]),
                    cr.matrix([[0, cr.I], [1, 0]]), cr.matrix([[1, cr.I], [0, 1]]))
        identity = replace(self.t, entries=cr.ID2, scalar_action=tr.ScalarAction.IDENTITY)
        for sigmas in product(tr.ScalarAction, repeat=3):
            a, b, c = [replace(self.t, entries=m, scalar_action=s) for m, s in zip(matrices, sigmas)]
            left, right = tr.compose(tr.compose(a, b), c), tr.compose(a, tr.compose(b, c))
            self.assertEqual((left.entries, left.scalar_action), (right.entries, right.scalar_action))
            for result in (tr.compose(identity, a), tr.compose(a, identity)):
                self.assertEqual((result.entries, result.scalar_action), (a.entries, a.scalar_action))

    def test_antilinearity_on_complex_vectors_and_additivity(self):
        v, w = (cr.Qi(1, 2), cr.Qi(-3, 1)), (cr.Qi(2, -1), cr.Qi(1, 4))
        self.assertEqual(tr.apply(self.t, tr.E0), (cr.ZERO, -cr.ONE))
        self.assertEqual(tr.apply(self.t, tr.vector_scale(cr.I, tr.E0)), (cr.ZERO, cr.I))
        for model in (tr.SPIN_HALF, tr.SPINLESS):
            _, t = fixture(model)
            for scalar in (cr.I, cr.Qi(Fraction(2, 3), Fraction(4, 5))):
                self.assertEqual(tr.apply(t, tr.vector_scale(scalar, v)),
                                 tr.vector_scale(scalar.conjugate(), tr.apply(t, v)))
            add = lambda a, b: tuple(x + y for x, y in zip(a, b))
            self.assertEqual(tr.apply(t, add(v, w)), add(tr.apply(t, v), tr.apply(t, w)))

    def test_antiunitarity_is_checked_separately_from_the_square(self):
        v, w = (cr.Qi(1, 2), cr.Qi(-3, 1)), (cr.Qi(2, -1), cr.Qi(1, 4))
        for model in (tr.SPIN_HALF, tr.SPINLESS):
            _, t = fixture(model)
            self.assertEqual(tr.inner(tr.apply(t, v), tr.apply(t, w)), tr.inner(v, w).conjugate())
        # A real, nonunitary matrix can still have A bar(A) = -I.
        bad = replace(self.t, entries=cr.matrix([[0, 2], [Fraction(-1, 2), 0]]))
        report = tr.observe_time_reversal(self.target, bad)
        self.assertEqual(report.square.entries, cr.scale(-cr.ONE, cr.ID2))
        self.assertFalse(next(r for r in report.matrix_relations if r.label == "unitarity").holds)
        with self.assertRaises(tr.Rejected):
            tr.check_time_reversal(self.target, bad)
        with self.assertRaises(tr.Rejected):
            tr.transform_operator(bad, cr.ID2)

    def test_spin_half_and_spinless_squares(self):
        for model, sign in ((tr.SPIN_HALF, -cr.ONE), (tr.SPINLESS, cr.ONE)):
            target, t = fixture(model)
            report = tr.check_time_reversal(target, t)
            self.assertTrue(report.all_hold)
            self.assertEqual(report.square.entries, cr.scale(sign, cr.ID2))
            self.assertIs(report.square.scalar_action, tr.ScalarAction.IDENTITY)
            for v in (tr.E0, tr.E1, (cr.Qi(1, 2), cr.I)):
                self.assertEqual(tr.apply(t, tr.apply(t, v)), tr.vector_scale(sign, v))

    def test_dropping_K_passes_the_original_square_but_fails_antilinearity(self):
        bad = replace(self.t, scalar_action=tr.ScalarAction.IDENTITY)
        report = tr.observe_time_reversal(self.target, bad)
        self.assertEqual(report.square.entries, cr.scale(-cr.ONE, cr.ID2))
        self.assertTrue(all(r.holds for r in report.matrix_relations))
        self.assertFalse(any(r.holds for r in report.vector_relations))
        self.assertFalse(report.all_hold)
        with self.assertRaisesRegex(tr.Rejected, "scalar action"):
            tr.check_time_reversal(self.target, bad)

    def test_global_phase_invariance_for_both_models(self):
        for model, phase in product((tr.SPIN_HALF, tr.SPINLESS),
                                    (cr.ONE, -cr.ONE, cr.I, -cr.I,
                                     cr.Qi(Fraction(3, 5), Fraction(4, 5)))):
            target, t = fixture(model)
            phased = tr.rephase(t, phase)
            report = tr.check_time_reversal(replace(target, phase=phase), phased)
            self.assertEqual(report.square.entries, cr.scale(model.profile.square, cr.ID2))
            self.assertEqual(tr.transform_operator(phased, cr.Y), tr.transform_operator(t, cr.Y))

    def test_ordinary_square_after_phase_i_has_the_wrong_sign(self):
        phased = tr.rephase(self.t, cr.I)
        target = replace(self.target, phase=cr.I)
        report = tr.check_time_reversal(target, phased)
        ordinary_square = cr.mul(phased.entries, phased.entries)
        self.assertEqual(ordinary_square, cr.ID2)
        self.assertEqual(report.square.entries, cr.scale(-cr.ONE, cr.ID2))
        wrong = replace(report, square=replace(report.square, entries=ordinary_square))
        with self.assertRaisesRegex(tr.Rejected, "altered"):
            tr.check_time_reversal(target, phased, wrong)
        with self.assertRaises(tr.Rejected):
            tr.check_time_reversal(target, replace(phased, scalar_action=tr.ScalarAction.IDENTITY))

    def test_T_i_T_inverse_and_explicit_operator_conjugation(self):
        self.assertEqual(tr.transform_operator(self.t, cr.scale(cr.I, cr.ID2)),
                         cr.scale(-cr.I, cr.ID2))
        for pauli in (cr.X, cr.Y, cr.Z):
            self.assertEqual(tr.transform_operator(self.t, pauli), cr.scale(-cr.ONE, pauli))


class BasisTransportTests(unittest.TestCase):
    def test_complex_basis_requires_conjugation_on_the_right(self):
        b = cr.matrix([[1, 0], [0, cr.I]])
        for model, expected in ((tr.SPIN_HALF, cr.matrix([[0, -cr.I], [cr.I, 0]])),
                                (tr.SPINLESS, cr.Z)):
            target, t = fixture(model)
            changed = new_coordinates(target.coordinates, b)
            new_target = replace(target, coordinates=changed)
            transported = tr.transport(t, changed)
            self.assertEqual(transported.entries, expected)
            tr.check_time_reversal(new_target, transported)
            for v in (tr.E0, tr.E1, (cr.Qi(2, 3), cr.Qi(1, -4))):
                self.assertEqual(tr.matvec(b, tr.apply(transported, v)),
                                 tr.apply(t, tr.matvec(b, v)))
            ordinary = cr.mul(cr.mul(cr.conjugate_transpose(b), t.entries), b)
            self.assertNotEqual(ordinary, expected)
            with self.assertRaises(tr.Rejected):
                tr.check_time_reversal(new_target, replace(transported, entries=ordinary))

    def test_mixed_basis_phase_and_round_trip(self):
        a, b = cr.Qi(Fraction(3, 5)), cr.Qi(Fraction(4, 5))
        change = cr.matrix([[a, b], [-cr.I * b, cr.I * a]])
        for model in (tr.SPIN_HALF, tr.SPINLESS):
            target, t = fixture(model)
            changed = new_coordinates(target.coordinates, change, "mixed complex basis")
            transported = tr.transport(t, changed)
            expected = (cr.scale(-cr.I, tr.SPIN_U) if model == tr.SPIN_HALF else
                        cr.matrix([[Fraction(-7, 25), Fraction(24, 25)],
                                   [Fraction(24, 25), Fraction(7, 25)]]))
            self.assertEqual(transported.entries, expected)
            tr.check_time_reversal(replace(target, coordinates=changed), transported)
            self.assertEqual(tr.transport(transported, target.coordinates), t)
            phase = cr.Qi(Fraction(3, 5), Fraction(4, 5))
            phased = tr.transport(tr.rephase(t, phase), changed)
            tr.check_time_reversal(replace(target, coordinates=changed, phase=phase), phased)
            self.assertEqual(phased.entries, cr.scale(phase, transported.entries))

    def test_transport_preserves_composition_for_all_scalar_profiles(self):
        target, t = fixture(tr.SPIN_HALF)
        changed = new_coordinates(target.coordinates, cr.matrix([[1, 0], [0, cr.I]]))
        for left_sigma, right_sigma in product(tr.ScalarAction, repeat=2):
            a = replace(t, entries=cr.Y, scalar_action=left_sigma)
            b = replace(t, entries=cr.matrix([[1, cr.I], [0, 1]]), scalar_action=right_sigma)
            left = tr.transport(tr.compose(a, b), changed)
            right = tr.compose(tr.transport(a, changed), tr.transport(b, changed))
            self.assertEqual(left, right)

    def test_gram_and_model_constraints_for_transport(self):
        target, t = fixture(tr.SPIN_HALF)
        for change in (cr.matrix([[1, 0], [0, 2]]), cr.matrix([[1, 1], [0, 0]])):
            with self.assertRaises(tr.Rejected):
                tr.transport(t, new_coordinates(target.coordinates, change))
        with self.assertRaises(tr.Rejected):
            tr.transport(t, tr.reference_coordinates(tr.SPINLESS))


class SelectionAndEvidenceTests(unittest.TestCase):
    def setUp(self):
        self.target, self.t = fixture(tr.SPIN_HALF)
        self.report = tr.check_time_reversal(self.target, self.t)

    def test_spinless_evidence_cannot_certify_spin_half(self):
        spinless_target, spinless = fixture(tr.SPINLESS)
        evidence = tr.check_time_reversal(spinless_target, spinless)
        self.assertEqual(spinless.name, self.t.name)  # Both are labeled T.
        with self.assertRaises(tr.Rejected):
            tr.check_time_reversal(self.target, self.t, evidence)
        with self.assertRaises(tr.Rejected):
            tr.check_time_reversal(self.target, spinless)
        # Relabeling the actual matrix and profile does not cure the wrong square.
        relabeled = replace(spinless, coordinates=self.target.coordinates)
        with self.assertRaises(tr.Rejected):
            tr.check_time_reversal(self.target, relabeled)
        with self.assertRaises(tr.Rejected):
            tr.check_time_reversal(replace(self.target, profile=spinless_target.profile), self.t)

    def test_names_neither_grant_authority_nor_choose_the_action(self):
        self.assertTrue(tr.check_time_reversal(self.target, replace(self.t, name="arbitrary label")).all_hold)
        with self.assertRaises(tr.Rejected):
            tr.check_time_reversal(self.target, replace(self.t, entries=cr.ID2))
        for fake in ("T", self.target.profile.profile_id, True, {"all_hold": True}):
            with self.subTest(fake=fake), self.assertRaises(tr.Rejected):
                tr.check_time_reversal(self.target, self.t, fake)

    def test_full_model_and_embedding_are_checked_even_when_names_match(self):
        c = self.target.coordinates
        for f in fields(tr.Model):
            if type(getattr(c.model, f.name)) is str:
                with self.subTest(field=f.name), self.assertRaises(tr.Rejected):
                    tr.audit_coordinates(replace(c, model=replace(c.model, **{f.name: "changed"})))
        for f in fields(tr.Coefficients):
            value = -cr.I if f.name == "generator_image" else cr.I if f.name == "conjugate_generator" else "changed"
            with self.subTest(field=f.name), self.assertRaises(tr.Rejected):
                tr.audit_coordinates(replace(c, coefficients=replace(c.coefficients, **{f.name: value})))
        for field, value in (("reference_matrix", cr.ID2), ("reference_basis", ("down", "up")),
                             ("profile", tr.SPINLESS.profile)):
            with self.subTest(field=field), self.assertRaises(tr.Rejected):
                tr.audit_coordinates(replace(c, model=replace(c.model, **{field: value})))

    def test_profile_payload_not_just_profile_id_is_checked(self):
        p = self.target.profile
        for field, value in (("profile_id", "other"), ("square", cr.ONE),
                             ("scalar_action", tr.ScalarAction.IDENTITY),
                             ("scalar_action", "conjugation"),
                             ("inner_product_id", "unspecified")):
            with self.subTest(field=field), self.assertRaises(tr.Rejected):
                tr.check_time_reversal(replace(self.target, profile=replace(p, **{field: value})), self.t)

    def test_basis_relabeling_or_matrix_change_requires_independent_selection(self):
        c = self.target.coordinates
        for basis in (replace(c.basis, ordered_labels=("down", "up")),
                      replace(c.basis, basis_id="different basis"),
                      replace(c.basis, to_reference=cr.matrix([[1, 0], [0, cr.I]]))):
            changed_action = replace(self.t, coordinates=replace(c, basis=basis))
            with self.assertRaises(tr.Rejected):
                tr.check_time_reversal(self.target, changed_action)
            with self.assertRaises(tr.Rejected):
                tr.compose(self.t, changed_action)
        # A deliberately selected new basis is valid, but old evidence stays bound.
        changed = new_coordinates(c, cr.ID2, "other nominal basis")
        other_target, other_t = replace(self.target, coordinates=changed), tr.transport(self.t, changed)
        with self.assertRaises(tr.Rejected):
            tr.check_time_reversal(other_target, other_t, self.report)

    def test_phase_is_explicit_and_old_observations_do_not_replay(self):
        phased = tr.rephase(self.t, cr.I)
        with self.assertRaises(tr.Rejected):
            tr.check_time_reversal(self.target, phased)
        with self.assertRaises(tr.Rejected):
            tr.check_time_reversal(replace(self.target, phase=cr.I), phased, self.report)
        for phase in (cr.ZERO, cr.Qi(2), 1, 1j, True):
            with self.subTest(phase=phase), self.assertRaises(tr.Rejected):
                tr.rephase(self.t, phase)

    def test_reports_are_recomputed_and_not_trusted_for_all_hold(self):
        wrong = replace(self.report, matrix_relations=(), vector_relations=())
        self.assertTrue(wrong.all_hold)
        with self.assertRaises(tr.Rejected):
            tr.check_time_reversal(self.target, self.t, wrong)
        with patch.object(tr, "compose", return_value=replace(self.report.square, entries=cr.ID2)):
            with self.assertRaises(tr.Rejected):
                tr.check_time_reversal(self.target, self.t)

    def test_exact_arithmetic_is_reused_and_inexact_inputs_fail(self):
        for name in ("Qi", "matrix", "mul", "scale", "conjugate_transpose"):
            self.assertIs(getattr(tr, name), getattr(cr, name))
        for sigma in (None, True, "conjugation", 1):
            with self.assertRaises(tr.Rejected):
                replace(self.t, scalar_action=sigma)
        for vector in ((1, 0), (1j, 0j), (True, False), [cr.ONE, cr.ZERO], (cr.ONE,)):
            with self.assertRaises(tr.Rejected):
                tr.apply(self.t, vector)


class InvarianceTests(unittest.TestCase):
    def setUp(self):
        self.target, self.t = fixture(tr.SPIN_HALF)
        c = self.target.coordinates
        self.h = tr.Subject(c, "H", tr.SubjectKind.HAMILTONIAN, cr.ID2)
        self.p = tr.Subject(c, "P-up", tr.SubjectKind.PURE_STATE_PROJECTOR, cr.matrix([[1, 0], [0, 0]]))

    def test_symmetric_H_does_not_make_each_ground_state_invariant(self):
        h = tr.check_invariance(self.target, self.t, self.h)
        p = tr.observe_invariance(self.target, self.t, self.p)
        self.assertTrue(h.holds)
        self.assertEqual(cr.mul(self.h.entries, self.p.entries), self.p.entries)
        self.assertEqual(p.transformed, cr.matrix([[0, 0], [0, 1]]))
        self.assertFalse(p.holds)
        with self.assertRaises(tr.Rejected):
            tr.check_invariance(self.target, self.t, self.p)
        with self.assertRaises(tr.Rejected):
            tr.check_invariance(self.target, self.t, self.p, h)

    def test_same_subject_name_and_forged_holds_do_not_authorize_replay(self):
        h = tr.check_invariance(self.target, self.t, self.h)
        same_name = replace(self.p, object_id=self.h.object_id)
        forged = replace(h, subject=same_name, transformed=same_name.entries)
        self.assertTrue(forged.holds)
        with self.assertRaises(tr.Rejected):
            tr.check_invariance(self.target, self.t, same_name, forged)

    def test_spinless_state_invariance_is_ray_not_vector_equality(self):
        target, t = fixture(tr.SPINLESS)
        state = replace(self.p, coordinates=target.coordinates)
        self.assertTrue(tr.check_invariance(target, t, state).holds)
        v = (cr.I, cr.ZERO)
        self.assertNotEqual(tr.apply(t, v), v)
        self.assertEqual(tr.apply(t, v), tr.vector_scale(-cr.ONE, v))
        complex_state = replace(state, entries=cr.scale(cr.Qi(Fraction(1, 2)),
                                                        cr.matrix([[1, -cr.I], [cr.I, 1]])))
        self.assertFalse(tr.observe_invariance(target, t, complex_state).holds)

    def test_operator_and_state_invariance_transport_covariantly(self):
        b = cr.matrix([[1, 0], [0, cr.I]])
        changed = new_coordinates(self.target.coordinates, b)
        t = tr.transport(self.t, changed)
        target = replace(self.target, coordinates=changed)
        for subject in (self.h, self.p, replace(self.h, entries=cr.Y)):
            original = tr.observe_invariance(self.target, self.t, subject)
            transported = replace(subject, coordinates=changed,
                                  entries=cr.mul(cr.mul(cr.conjugate_transpose(b), subject.entries), b))
            observed = tr.observe_invariance(target, t, transported)
            self.assertEqual(observed.holds, original.holds)
            self.assertEqual(observed.transformed,
                             cr.mul(cr.mul(cr.conjugate_transpose(b), original.transformed), b))
        v = (cr.Qi(1, 2), cr.Qi(3, -1))
        self.assertEqual(tr.apply(t, tr.transport_vector(v, self.target.coordinates, changed)),
                         tr.transport_vector(tr.apply(self.t, v), self.target.coordinates, changed))

    def test_invalid_or_cross_model_subjects_are_rejected(self):
        for bad in (replace(self.h, entries=cr.matrix([[0, 1], [0, 0]])),
                    replace(self.p, entries=cr.ID2), replace(self.p, entries=cr.scale(cr.Qi(2), self.p.entries)),
                    replace(self.p, coordinates=tr.reference_coordinates(tr.SPINLESS)),
                    replace(self.h, kind="Hamiltonian")):
            with self.subTest(subject=bad), self.assertRaises(tr.Rejected):
                tr.observe_invariance(self.target, self.t, bad)


class DemoTests(unittest.TestCase):
    def test_demo_is_executable_and_reports_exact_payloads(self):
        result = subprocess.run([sys.executable, str(Path(__file__).with_name("demo_time_reversal_reference.py"))],
                                check=True, capture_output=True, text=True)
        data = json.loads(result.stdout)
        self.assertFalse(data["lean_proof"])
        self.assertFalse(data["accepted_core_connection"])
        self.assertFalse(data["physical_identification_verified"])
        self.assertEqual(len(data["models"]), 2)
        self.assertEqual(len(data["expected_rejections"]), 5)
        spin = data["models"]["fixture:spin-half"]
        self.assertEqual(spin["candidate"]["scalar_action"], "conjugation")
        self.assertEqual(spin["square"]["entries"][0][0]["real"], {"numerator": -1, "denominator": 1})
        self.assertEqual(data["state_transformed"][1][1]["real"], {"numerator": 1, "denominator": 1})


if __name__ == "__main__":
    unittest.main()
