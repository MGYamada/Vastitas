"""Independent finite oracles and mutation regressions for #294."""

from dataclasses import replace
from itertools import product
import json
from pathlib import Path
import subprocess
import sys
import unittest

import order_reference as r
from demo_order_reference import absolute_order, powerset_example


def chain(size=3):
    return r.Order("order-reference-v1", f"chain-{size}", "usual", "1",
                   tuple(str(x) for x in range(size)),
                   tuple(tuple(x <= y for y in range(size)) for x in range(size)))


def dual(order):
    return replace(order, name=order.name + "-dual", le=tuple(zip(*order.le)))


def change_cell(table, row, col, value):
    return tuple(tuple(value if (i, j) == (row, col) else x for j, x in enumerate(xs))
                 for i, xs in enumerate(table))


class ReferenceTests(unittest.TestCase):
    def verify(self, subject, law):
        return r.verify(subject, r.Claim(subject, law), law=law)

    def rejects(self, subject, law, code, candidate=None):
        with self.assertRaises(r.Invalid) as caught:
            r.verify(subject, candidate or r.Claim(subject, law), law=law)
        self.assertEqual(caught.exception.code, code)
        return caught.exception.witness

    def test_chain_and_powerset_acceptance_profiles(self):
        la, lb, _ = powerset_example()
        self.assertEqual(self.verify(lb.order, "linear_order"),
                         {"reflexivity": 2, "transitivity": 8, "antisymmetry": 4, "totality": 4})
        self.verify(la.order, "partial_order")
        self.assertEqual(self.rejects(la.order, "linear_order", "totality"), (1, 2))

    def test_absolute_preorder_does_not_identify_carrier_elements(self):
        order = absolute_order()
        self.verify(order, "preorder")
        self.assertNotEqual(order.elements[0], order.elements[2])
        self.assertTrue(order.le[0][2] and order.le[2][0])
        for law in ("partial_order", "linear_order"):
            self.assertEqual(self.rejects(order, law, "antisymmetry"), (0, 2))

    def test_divisibility_not_total(self):
        values = (1, 2, 3, 6)
        order = r.Order("order-reference-v1", "divisors-of-6", "divides", "1",
                        tuple(map(str, values)),
                        tuple(tuple(b % a == 0 for b in values) for a in values))
        self.verify(order, "partial_order")
        self.assertEqual(self.rejects(order, "linear_order", "totality"), (1, 2))

    def test_cyclic_comparator_and_strict_relation_rejected(self):
        cyclic = replace(chain(), le=((True, True, False), (False, True, True),
                                      (True, False, True)))
        self.rejects(cyclic, "preorder", "transitivity")
        self.rejects(replace(chain(2), le=((False, True), (False, False))),
                     "preorder", "reflexivity")

    def test_nan_comparison_table_is_not_reflexive(self):
        values = (0.0, float("nan"))
        order = replace(chain(2), elements=("0", "NaN"),
                        le=tuple(tuple(a <= b for b in values) for a in values))
        self.assertEqual(self.rejects(order, "linear_order", "reflexivity"), (1,))

    def test_empty_order_is_vacuously_linear_but_not_bounded_lattice(self):
        empty = chain(0)
        self.assertTrue(all(n == 0 for n in self.verify(empty, "linear_order").values()))
        with self.assertRaises(r.Invalid):
            r.Lattice(empty, (), (), 0, 0)

    def test_every_three_element_relation_against_set_composition_oracle(self):
        vertices = range(3)
        all_edges = tuple(product(vertices, repeat=2))
        diagonal = {(x, x) for x in vertices}
        totals = [0, 0, 0]
        for bits in product((False, True), repeat=9):
            edges = {edge for edge, present in zip(all_edges, bits) if present}
            composed = {(x, z) for x, y in edges for yy, z in edges if y == yy}
            converse = {(y, x) for x, y in edges}
            preorder = diagonal <= edges and composed <= edges
            partial = preorder and edges & converse <= diagonal
            linear = partial and edges | converse == set(all_edges)
            order = replace(chain(), le=tuple(tuple(bits[3*i:3*i+3]) for i in vertices))
            for i, (law, expected) in enumerate(zip(
                    ("preorder", "partial_order", "linear_order"), (preorder, partial, linear))):
                try:
                    self.verify(order, law)
                    accepted = True
                except r.Invalid:
                    accepted = False
                self.assertEqual(accepted, expected, (bits, law))
                totals[i] += accepted
        self.assertEqual(totals, [29, 19, 6])

    def test_both_lattices_by_universal_properties(self):
        la, lb, _ = powerset_example()
        self.assertEqual(self.verify(la, "bounded_lattice"),
                         {"join_universal": 64, "meet_universal": 64, "bottom": 4, "top": 4})
        self.verify(lb, "bounded_lattice")

    def test_swapped_operations_and_wrong_top_bottom(self):
        la, _, _ = powerset_example()
        self.rejects(replace(la, joins=la.meets, meets=la.joins),
                     "bounded_lattice", "join_universal")
        self.rejects(replace(la, bottom=3), "bounded_lattice", "bottom")
        self.rejects(replace(la, top=0), "bounded_lattice", "top")

    def test_upper_lower_bounds_alone_are_not_least_greatest(self):
        xs = range(3)
        lattice = r.Lattice(chain(), tuple(tuple(max(a, b) for b in xs) for a in xs),
                            tuple(tuple(min(a, b) for b in xs) for a in xs), 0, 2)
        sup = change_cell(lattice.joins, 0, 1, 2)  # Upper bound, not least.
        inf = change_cell(lattice.meets, 1, 2, 0)  # Lower bound, not greatest.
        self.rejects(replace(lattice, joins=sup), "bounded_lattice", "join_universal")
        self.rejects(replace(lattice, meets=inf), "bounded_lattice", "meet_universal")

    def test_missing_joins_meets_are_not_success_or_completeness(self):
        fork = replace(chain(), le=((True, True, True), (False, True, False),
                                    (False, False, True)))
        for order, law, code in ((fork, "binary_joins", "MISSING_JOIN"),
                                 (dual(fork), "binary_meets", "MISSING_MEET")):
            self.verify(order, "partial_order")
            mapping = r.Map("identity", "1", order, order, (0, 1, 2))
            self.rejects(mapping, law, code)

    def test_original_adjoint_example_all_eight_pairs_and_unit_counit(self):
        _, _, pair = powerset_example()
        self.assertEqual(self.verify(pair, "galois"),
                         {"lower_monotonicity": 16, "upper_monotonicity": 4,
                          "adjunction": 8, "unit": 4, "counit": 2})

    def test_correct_binary_and_all_subset_preservation(self):
        _, _, pair = powerset_example()
        for mapping, law, count in ((pair.lower, "binary_joins", 16),
                                    (pair.upper, "binary_meets", 4),
                                    (pair.lower, "all_joins", 16),
                                    (pair.upper, "all_meets", 4)):
            self.assertEqual(self.verify(mapping, law), {"preservation": count})

    def test_direct_image_does_not_preserve_meets(self):
        la, lb, pair = powerset_example()
        f = pair.lower.images
        self.assertEqual(f[la.meets[1][2]], 0)
        self.assertEqual(lb.meets[f[1]][f[2]], 1)
        self.assertEqual(self.rejects(pair.lower, "binary_meets", "preservation"),
                         ((1, 2), 0, 1))

    def test_right_adjoint_need_not_preserve_joins(self):
        la, lb, _ = powerset_example()
        # Diagonal into the square of the two-element chain is left adjoint
        # to binary meet. Here the upper map really fails join preservation.
        pair = r.Pair(r.Map("diagonal", "1", lb.order, la.order, (0, 3)),
                      r.Map("meet", "1", la.order, lb.order, (0, 0, 0, 1)))
        self.verify(pair, "galois")
        self.verify(pair.lower, "all_joins")
        self.verify(pair.upper, "all_meets")
        self.assertEqual(self.rejects(pair.upper, "binary_joins", "preservation"),
                         ((1, 2), 1, 0))

    def test_galois_connection_is_not_isomorphism(self):
        _, _, pair = powerset_example()
        self.verify(pair, "galois")
        self.assertEqual(pair.upper.images[pair.lower.images[1]], 3)
        self.assertEqual(self.rejects(pair, "order_iso", "left_inverse"), (1,))

    def test_preorder_equivalence_cannot_replace_inverse_equalities(self):
        order = replace(chain(2), le=((True, True), (True, True)))
        constant = r.Map("constant", "1", order, order, (0, 0))
        pair = r.Pair(constant, constant)
        self.verify(pair, "galois")
        self.rejects(pair, "order_iso", "left_inverse")

    def test_order_isomorphism_of_distinct_named_orders(self):
        a, b = chain(), dual(chain())
        l = r.Map("reverse", "1", a, b, (2, 1, 0))
        u = r.Map("unreverse", "1", b, a, (2, 1, 0))
        self.verify(r.Pair(l, u), "order_iso")
        self.verify(r.Pair(l, u), "galois")
        self.assertNotEqual(a, b)

    def test_forged_adjoint_has_independent_unit_and_counit_failures(self):
        c = chain(2)
        pair = r.Pair(r.Map("l", "1", c, c, (1, 1)), r.Map("u", "1", c, c, (0, 0)))
        checks = {check.name: check for check in r.inspect_connection(pair)}
        self.assertEqual(checks["unit"].counterexample, (1,))
        self.assertEqual(checks["counit"].counterexample, (0,))
        self.assertIsNotNone(checks["adjunction"].counterexample)
        self.assertIsNone(checks["lower_monotonicity"].counterexample)
        self.assertIsNone(checks["upper_monotonicity"].counterexample)
        self.rejects(pair, "galois", "adjunction")

    def test_unit_counit_without_monotonicity_are_insufficient(self):
        c = chain()
        pair = r.Pair(r.Map("l", "1", c, c, (0, 2, 1)), r.Map("u", "1", c, c, (0, 2, 2)))
        checks = {check.name: check for check in r.inspect_connection(pair)}
        self.assertIsNone(checks["unit"].counterexample)
        self.assertIsNone(checks["counit"].counterexample)
        self.assertIsNotNone(checks["adjunction"].counterexample)
        self.rejects(pair, "galois", "lower_monotonicity")

    def test_reversed_adjoints_and_relation_orientation(self):
        _, _, pair = powerset_example()
        self.rejects(r.Pair(pair.upper, pair.lower), "galois", "adjunction")
        b = dual(pair.lower.target)
        swapped = r.Pair(replace(pair.lower, target=b), replace(pair.upper, source=b))
        self.verify(b, "linear_order")  # Reversal remains a lawful order.
        self.rejects(swapped, "galois", "lower_monotonicity")
        # Correct order duality also exchanges the adjoints.
        a = dual(pair.lower.source)
        correct = r.Pair(replace(pair.upper, source=b, target=a),
                         replace(pair.lower, source=a, target=b))
        self.verify(correct, "galois")
        self.verify(correct.lower, "all_joins")
        self.verify(correct.upper, "all_meets")

    def test_monotone_and_antitone_are_distinct(self):
        c = chain()
        reverse = r.Map("reversal", "1", c, c, (2, 1, 0))
        self.verify(reverse, "antitone")
        self.rejects(reverse, "monotone", "monotonicity")
        identity = replace(reverse, images=(0, 1, 2))
        self.verify(identity, "monotone")
        self.rejects(identity, "antitone", "monotonicity")

    def test_binary_preservation_does_not_imply_empty_family_preservation(self):
        c = chain(2)
        for value, kind in ((1, "joins"), (0, "meets")):
            constant = r.Map("constant", "1", c, c, (value, value))
            self.verify(constant, "binary_" + kind)
            self.assertEqual(self.rejects(constant, "all_" + kind, "preservation")[0], ())

    def test_empty_domain_cannot_claim_all_joins_without_bottom(self):
        mapping = r.Map("empty", "1", chain(0), chain(1), ())
        self.assertEqual(self.verify(mapping, "binary_joins"), {"preservation": 0})
        self.rejects(mapping, "all_joins", "MISSING_JOIN")

    def test_every_powerset_map_pair_against_actual_set_inclusion(self):
        _, _, prototype = powerset_example()
        a = (frozenset(), frozenset({0}), frozenset({1}), frozenset({0, 1}))
        b = (frozenset(), frozenset({"x"}))
        accepted = 0
        for f in product(range(2), repeat=4):
            for g in product(range(4), repeat=2):
                expected = all((b[f[x]] <= b[y]) == (a[x] <= a[g[y]])
                               for x, y in product(range(4), range(2)))
                pair = r.Pair(replace(prototype.lower, images=f), replace(prototype.upper, images=g))
                try:
                    self.verify(pair, "galois")
                    actual = True
                except r.Invalid:
                    actual = False
                self.assertEqual(actual, expected, (f, g))
                if actual:
                    accepted += 1
                    self.verify(pair.lower, "all_joins")
                    self.verify(pair.upper, "all_meets")
        self.assertEqual(accepted, 4)

    def test_full_order_subject_binding_including_names_and_table(self):
        original = chain()
        mutations = (replace(original, context="other-context"),
                     replace(original, carrier="other-carrier"),
                     replace(original, name="other-named-order"),
                     replace(original, revision="2"),
                     replace(original, elements=("2", "1", "0")),
                     replace(original, le=tuple(zip(*original.le))))
        for expected in mutations:
            with self.subTest(expected=expected):
                self.verify(expected, "linear_order")  # Each target is itself lawful.
                self.rejects(expected, "linear_order", "SUBJECT_MISMATCH",
                             r.Claim(original, "linear_order"))

    def test_candidate_name_is_not_authority_and_rebinding_rechecks_laws(self):
        expected = absolute_order()
        fabricated = replace(chain(), carrier=expected.carrier, name=expected.name,
                             elements=expected.elements)
        self.verify(fabricated, "partial_order")
        self.rejects(expected, "partial_order", "SUBJECT_MISMATCH", r.Claim(fabricated, "partial_order"))
        self.rejects(expected, "partial_order", "antisymmetry")

    def test_required_profile_cannot_be_downgraded_by_candidate(self):
        expected = absolute_order()
        self.rejects(expected, "partial_order", "CLAIM_MISMATCH", r.Claim(expected, "preorder"))
        self.rejects(expected, "unknown", "UNSUPPORTED_LAW")
        self.rejects(expected, "galois", "INVALID_EXPECTED_SUBJECT")

    def test_full_map_binding_and_pair_endpoint_matching(self):
        _, _, pair = powerset_example()
        m = pair.lower
        for expected in (replace(m, name="another-map"), replace(m, revision="2"),
                         replace(m, images=(0, 0, 1, 1)),
                         replace(m, source=replace(m.source, name="other-subset"))):
            self.rejects(expected, "monotone", "SUBJECT_MISMATCH", r.Claim(m, "monotone"))
        with self.assertRaisesRegex(r.Invalid, "ENDPOINT_MISMATCH"):
            r.Pair(m, replace(pair.upper, target=replace(m.source, name="other-subset")))
        changed = r.Pair(replace(m, revision="2"), pair.upper)
        self.rejects(changed, "galois", "SUBJECT_MISMATCH", r.Claim(pair, "galois"))

    def test_lattice_evidence_binds_operations_not_just_order_name(self):
        la, _, _ = powerset_example()
        changed = replace(la, joins=la.meets)
        self.rejects(changed, "bounded_lattice", "SUBJECT_MISMATCH", r.Claim(la, "bounded_lattice"))
        self.rejects(changed, "bounded_lattice", "join_universal")

    def test_malformed_carriers_tables_and_map_images(self):
        c = chain(2)
        for fields in ({"elements": ("0", "0")}, {"elements": ["0", "1"]},
                       {"le": ((1, 1), (0, 1))}, {"le": ((True,),)},
                       {"le": [[True, True], [False, True]]}, {"name": ""}):
            with self.subTest(fields=fields), self.assertRaises(r.Invalid):
                replace(c, **fields)
        with self.assertRaisesRegex(r.Invalid, "INVALID_CARRIER"):
            chain(r.MAX_ELEMENTS + 1)
        for images in ((0,), (0, 2), (False, 1), (0.0, 1), (0, -1), [0, 1]):
            with self.subTest(images=images), self.assertRaises(r.Invalid):
                r.Map("bad", "1", c, c, images)
        with self.assertRaisesRegex(r.Invalid, "CONTEXT_MISMATCH"):
            r.Map("bad", "1", c, replace(c, context="another"), (0, 1))
        _, lb, _ = powerset_example()
        with self.assertRaises(r.Invalid):
            replace(lb, bottom=True)
        with self.assertRaises(r.Invalid):
            replace(lb, joins=((0, 2), (1, 1)))

    def test_demo_without_site_packages_and_exact_regression_counts(self):
        path = Path(__file__).with_name("demo_order_reference.py")
        result = subprocess.run([sys.executable, "-S", str(path)], capture_output=True, text=True, check=True)
        report = json.loads(result.stdout)
        self.assertTrue(all(case["matched"] for case in report["cases"]))
        cases = {case["name"]: case for case in report["cases"]}
        self.assertEqual(cases["direct-inverse-adjunction"]["counts"]["adjunction"], 8)
        self.assertEqual(cases["left-binary-joins"]["counts"]["preservation"], 16)
        self.assertEqual(cases["right-binary-meets"]["counts"]["preservation"], 4)
        self.assertEqual(report["counterexamples"], {
            "direct_image_of_intersection": "{}", "intersection_of_direct_images": "{x}",
            "upper_lower_of_singleton": "{0,1}", "original_singleton": "{0}"})


if __name__ == "__main__":
    unittest.main()
