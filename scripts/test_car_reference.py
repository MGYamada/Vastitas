"""Finite physical examples, independent matrix witnesses and provenance mutations."""

import json
import subprocess
import sys
import unittest
from dataclasses import fields, replace
from fractions import Fraction
from pathlib import Path
from unittest.mock import patch

import car_reference as cr
import graph_reference as graph


class CARTests(unittest.TestCase):
    def test_all_three_one_mode_and_twelve_two_mode_relations(self):
        for n in (1, 2):
            operators = cr.annihilators(n)
            report = cr.observe_car(operators, operators[0].model.adjoint_profile)
            self.assertEqual(len(report.relations), 3 * n * n)
            self.assertEqual(report.operators, operators)
            self.assertTrue(report.all_hold)
            for relation in report.relations:
                with self.subTest(n=n, relation=relation.label):
                    self.assertEqual(relation.lhs, relation.rhs)
            for c, dagger in zip(operators, report.adjoints):
                self.assertEqual(dagger.model, c.model)
                self.assertEqual(dagger.degree, 1)
                self.assertEqual(cr.adjoint(dagger, report.model.adjoint_profile).entries, c.entries)

    def test_ordered_fock_basis_and_independent_jordan_wigner_matrices(self):
        one, = cr.annihilators(1)
        c1, c2 = cr.annihilators(2)
        self.assertEqual(one.entries, cr.R)
        self.assertEqual(one.model.basis, ((0,), (1,)))
        self.assertEqual(c1.model.basis, ((0, 0), (0, 1), (1, 0), (1, 1)))
        self.assertEqual(c1.model.basis_parity, (0, 1, 1, 0))
        self.assertEqual(c1.entries, cr.kron(cr.R, cr.ID2))
        self.assertEqual(c2.entries, cr.kron(cr.Z, cr.R))
        # Columns are inputs: c2|01> = |00>, c2|11> = -|10>.
        self.assertEqual(c2.entries, cr.matrix([[0, 1, 0, 0], [0, 0, 0, 0],
                                               [0, 0, 0, -1], [0, 0, 0, 0]]))

    def test_missing_z_preserves_single_modes_but_fails_cross_mode_car(self):
        c1, c2 = cr.annihilators(2)
        dropped = replace(c2, entries=cr.kron(cr.ID2, cr.R))
        report = cr.observe_car((c1, dropped), c1.model.adjoint_profile)
        self.assertFalse(report.all_hold)
        self.assertEqual(sum(not r.holds for r in report.relations), 6)
        for relation in report.relations:
            if relation.label.endswith(("[1,1]", "[2,2]")):
                self.assertTrue(relation.holds, relation.label)
        witness = next(r for r in report.relations if r.label == "cc[1,2]")
        self.assertEqual(witness.lhs, cr.scale(cr.Qi(2), cr.kron(cr.R, cr.R)))
        self.assertNotEqual(witness.lhs, witness.rhs)

    def test_every_nonzero_annihilator_entry_mutation_breaks_car(self):
        # Preserves shape and homogeneity, so this exercises algebra, not metadata rejection.
        for n in (1, 2):
            ops = cr.annihilators(n)
            for site, op in enumerate(ops):
                for i, row in enumerate(op.entries):
                    for j, value in enumerate(row):
                        if value == cr.ZERO:
                            continue
                        rows = [list(r) for r in op.entries]
                        rows[i][j] = value * cr.Qi(2)
                        changed = ops[:site] + (replace(op, entries=cr.matrix(rows)),) + ops[site + 1:]
                        with self.subTest(n=n, site=site, i=i, j=j):
                            self.assertFalse(cr.observe_car(changed, op.model.adjoint_profile).all_hold)

    def test_embedding_uses_existing_evaluator_for_exchange_coefficients(self):
        with patch.object(graph, "evaluate", wraps=graph.evaluate) as evaluator:
            cr.annihilators(2)
        self.assertEqual(evaluator.call_count, 4)
        self.assertTrue(all(call.args[0].profile == graph.FIXTURES["symmetric_sign"].key
                            for call in evaluator.call_args_list))
        # If the shared sign evaluator is broken, CAR must detect it. There is no
        # separate Jordan-Wigner sign implementation concealing that mutation.
        evaluate = graph.evaluate
        with patch.object(graph, "evaluate", side_effect=lambda w: replace(evaluate(w), scalar=Fraction(1))):
            ops = cr.annihilators(2)
        self.assertFalse(cr.observe_car(ops, ops[0].model.adjoint_profile).all_hold)

    def test_modes_outside_fragment_are_rejected(self):
        for n in (0, 3, -1, True, 2.0):
            for constructor in (cr.annihilators, cr.spin_x):
                with self.subTest(n=n, constructor=constructor), self.assertRaises(cr.Rejected):
                    constructor(n)


class SpinAndPauliTests(unittest.TestCase):
    def test_independent_spin_sites_use_ordinary_tensor(self):
        a, b = cr.spin_x()
        self.assertEqual(a.entries, cr.kron(cr.X, cr.ID2))
        self.assertEqual(b.entries, cr.kron(cr.ID2, cr.X))
        self.assertEqual(a.model.basis_parity, (0, 0, 0, 0))
        self.assertTrue(cr.observe_spins((a, b)).all_hold)
        self.assertTrue(cr.observe_spins(cr.spin_x(1)).all_hold)
        self.assertEqual(cr.mul(a.entries, b.entries), cr.kron(cr.X, cr.X))
        self.assertEqual(cr.mul(b.entries, a.entries), cr.kron(cr.X, cr.X))
        # Falsely demanding a fermionic exchange law gives a nonzero residual.
        residual = cr.add(cr.mul(a.entries, b.entries), cr.mul(b.entries, a.entries))
        self.assertEqual(residual, cr.scale(cr.Qi(2), cr.kron(cr.X, cr.X)))
        self.assertNotEqual(residual, cr.scale(cr.ZERO, cr.identity(4)))

    def test_accidental_fermionic_prefix_on_spin_site_is_detected(self):
        a, b = cr.spin_x()
        wrong = replace(b, entries=cr.kron(cr.Z, cr.X))
        report = cr.observe_spins((a, wrong))
        self.assertTrue(report.relations[0].holds)
        self.assertTrue(report.relations[1].holds)
        self.assertFalse(report.relations[2].holds)
        self.assertFalse(report.all_hold)

    def test_pauli_quadratic_relations_and_xyz(self):
        report = cr.observe_pauli()
        self.assertEqual(len(report.relations), 7)
        self.assertTrue(all(r.holds for r in report.relations))
        self.assertEqual(report.relations[-1].lhs, cr.scale(cr.I, cr.ID2))
        # Abstract Clifford generator parity is NOT spin exchange parity.
        self.assertEqual(report.abstract_generator_parity, (1, 1, 1))
        self.assertEqual(tuple(op.degree for op in report.operators), (0, 0, 0))

    def test_cl2_rank_four_and_cl3_nonfaithful_rank_four(self):
        report = cr.observe_pauli()
        self.assertEqual(cr.require_independent_images(report.cl2_images), 4)
        self.assertEqual(cr.span_rank(report.cl3_images), 4)
        with self.assertRaisesRegex(cr.Rejected, "rank 4 < 8"):
            cr.require_independent_images(report.cl3_images)
        # Nonzero formal PBW vector e123 - i*1 maps to zero. Image equality
        # cannot authorize identifying Cl3(C) and Mat2(C).
        coefficients = (-cr.I,) + (cr.ZERO,) * 6 + (cr.ONE,)
        image = cr.scale(cr.ZERO, cr.ID2)
        for coefficient, word_image in zip(coefficients, report.cl3_images):
            image = cr.add(image, cr.scale(coefficient, word_image))
        self.assertNotEqual(coefficients, (cr.ZERO,) * 8)
        self.assertEqual(image, cr.scale(cr.ZERO, cr.ID2))
        self.assertEqual(cr.span_rank((cr.ID2, cr.scale(cr.I, cr.ID2))), 1)

    def test_explicit_adjoint_conjugates_instead_of_only_transposing(self):
        model = cr.MODELS["spin", 1]
        y = cr.Operator(model, "Y", 0, cr.Y)
        self.assertEqual(cr.adjoint(y, model.adjoint_profile).entries, cr.Y)
        self.assertNotEqual(cr.matrix(zip(*cr.Y)), cr.Y)
        a = cr.Operator(model, "iX", 0, cr.scale(cr.I, cr.X))
        self.assertEqual(cr.adjoint(a, model.adjoint_profile).entries, cr.scale(-cr.I, cr.X))
        for bad in (None, "transpose", cr.MODELS["CAR", 1].adjoint_profile,
                    replace(model.adjoint_profile, involution_id="identity"),
                    replace(model.adjoint_profile, inner_product_id="unspecified")):
            with self.subTest(profile=bad), self.assertRaises(cr.Rejected):
                cr.adjoint(y, bad)


class ModelAndGraphBoundaryTests(unittest.TestCase):
    def test_every_model_identity_component_is_bound(self):
        model = cr.MODELS["CAR", 2]
        for field in fields(cr.Model):
            if type(getattr(model, field.name)) is str:
                with self.subTest(field=field.name), self.assertRaises(cr.Rejected):
                    cr.audit_model(replace(model, **{field.name: "other-or-stale"}))
        for bad in (
            replace(model, tensor_profile=cr.MODELS["spin", 2].tensor_profile),
            replace(model, basis=tuple(reversed(model.basis))),
            replace(model, basis_parity=(0, 0, 0, 0)),
            replace(model, local_basis_parity=(0, 0)),
            replace(model, adjoint_profile=cr.MODELS["CAR", 1].adjoint_profile),
            replace(model, sites=1), replace(model, sites=True),
            replace(model, basis_parity=(False, 1, 1, 0)),
            replace(model, basis=((False, 0),) + model.basis[1:]),
        ):
            with self.subTest(model=bad), self.assertRaises(cr.Rejected):
                cr.audit_model(bad)

    def test_unknown_or_wrong_operator_parity_is_rejected(self):
        c, = cr.annihilators(1)
        for degree in (None, 0, True, 1.0, 2):
            with self.subTest(degree=degree), self.assertRaises(cr.Rejected):
                replace(c, degree=degree)
        with self.assertRaises(cr.Rejected):
            replace(c, entries=cr.ID2)  # even matrix cannot be labeled odd
        for p in (None, True, 1.0, -1):
            with self.assertRaises(cr.Rejected):
                cr.exchange_word(c.model, p, 1)

    def test_different_models_cannot_share_a_family_or_adjoint(self):
        c1, c2 = cr.annihilators(2)
        spins = cr.spin_x()
        for ops in ((c1, spins[1]), spins, (c1,), ()):
            with self.subTest(operators=ops), self.assertRaises(cr.Rejected):
                cr.observe_car(ops, c1.model.adjoint_profile)
        with self.assertRaises(cr.Rejected):
            cr.observe_car((c1, c2), spins[0].model.adjoint_profile)
        with self.assertRaises(cr.Rejected):
            cr.observe_spins((c1, c2))

    def test_all_four_parity_exchanges_reuse_existing_profiles(self):
        for kind in ("CAR", "spin"):
            model = cr.MODELS[kind, 2]
            # Fixed expected truth table is independent of the implementation.
            expected = (1, 1, 1, -1) if kind == "CAR" else (1, 1, 1, 1)
            for (left, right), coefficient in zip(((0, 0), (0, 1), (1, 0), (1, 1)), expected):
                word = cr.exchange_word(model, left, right)
                self.assertEqual(graph.evaluate(word).scalar, Fraction(coefficient))
            double = cr.exchange_word(model, 1, 1, double=True)
            claim = graph.propose_rewrite(double, 0, graph.Rule.SYMMETRIC,
                                         graph.evidence_for(double.profile, graph.Rule.SYMMETRIC))
            returned = graph.check_rewrite(double, claim)
            self.assertEqual(returned.crossings, ())
            self.assertEqual(graph.evaluate(double).scalar, Fraction(1))

    def test_cross_profile_evidence_and_matrix_observation_are_rejected(self):
        car = cr.MODELS["CAR", 2]
        spin = cr.MODELS["spin", 2]
        for model, other in ((car, spin), (spin, car)):
            word = cr.exchange_word(model, 1, 1, double=True)
            with self.assertRaises(graph.Rejected):
                graph.propose_rewrite(word, 0, graph.Rule.SYMMETRIC,
                                      graph.evidence_for(other.tensor_profile, graph.Rule.SYMMETRIC))
        ops = cr.annihilators(2)
        report = cr.observe_car(ops, car.adjoint_profile)
        self.assertTrue(report.all_hold)
        with self.assertRaises(graph.Rejected):
            graph.propose_rewrite(word, 0, graph.Rule.SYMMETRIC, report)

    def test_single_symmetric_crossing_is_not_erasable(self):
        for kind in ("CAR", "spin"):
            word = cr.exchange_word(cr.MODELS[kind, 2], 1, 1)
            with self.assertRaises(graph.Rejected):
                graph.propose_rewrite(word, 0, graph.Rule.SYMMETRIC,
                                      graph.evidence_for(word.profile, graph.Rule.SYMMETRIC))

    def test_graph_rewrite_does_not_consult_matrix_or_sign_observations(self):
        word = cr.exchange_word(cr.MODELS["CAR", 2], 1, 1, double=True)
        evidence = graph.evidence_for(word.profile, graph.Rule.SYMMETRIC)
        with patch.object(cr, "observe_car", side_effect=AssertionError("matrix oracle used")), \
             patch.object(graph, "evaluate", side_effect=AssertionError("scalar oracle used")):
            claim = graph.propose_rewrite(word, 0, graph.Rule.SYMMETRIC, evidence)
            returned = graph.check_trace(word, (claim,), claim.after).returned
        self.assertEqual(returned.crossings, ())


class ArithmeticAndDemoTests(unittest.TestCase):
    def test_exact_field_and_matrix_operations(self):
        a = cr.Qi(Fraction(1, 3), Fraction(2, 5))
        b = cr.Qi(Fraction(-7, 11), Fraction(3, 2))
        self.assertEqual((a * b) / b, a)
        self.assertEqual(cr.I * cr.I, -cr.ONE)
        self.assertEqual(a * a.conjugate(), cr.Qi(Fraction(61, 225)))
        self.assertEqual(cr.conjugate_transpose(cr.mul(cr.X, cr.Y)),
                         cr.mul(cr.conjugate_transpose(cr.Y), cr.conjugate_transpose(cr.X)))
        with self.assertRaises(ZeroDivisionError):
            a / cr.ZERO
        for value in (0.0, 1j, True, "1/2"):
            with self.subTest(value=value), self.assertRaises(cr.Rejected):
                cr.matrix([[value]])
        with self.assertRaises(cr.Rejected):
            cr.mul(cr.ID2, cr.identity(4))

    def test_demo_runs_and_reports_exact_metadata_and_expected_negatives(self):
        root = Path(__file__).resolve().parent
        result = subprocess.run([sys.executable, str(root / "demo_car_reference.py")],
                                check=True, capture_output=True, text=True)
        data = json.loads(result.stdout)
        self.assertFalse(data["production_graph_authority"])
        self.assertEqual(data["car"]["1"]["relations_checked"], 3)
        self.assertEqual(data["car"]["2"]["relations_checked"], 12)
        self.assertTrue(data["car"]["2"]["all_hold"])
        self.assertEqual(data["car"]["2"]["observation"]["model"]["coefficient_id"], "QQ(i)")
        self.assertEqual(data["pauli"]["cl3_image_rank"], 4)
        self.assertEqual(len(data["expected_negatives"]), 4)


if __name__ == "__main__":
    unittest.main()
