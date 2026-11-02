"""Exact semantic and rejection regressions; no speed or GPU assertions."""

from dataclasses import FrozenInstanceError, replace
from fractions import Fraction
from itertools import product
import random
import unittest

from sparse_reference import (
    Binding, CSR, IntegerProfile, Pattern, PlanInvalidated, SparseError,
    bind_pivot_guard, cancellation_example, execute_guarded, execute_spgemm,
    from_coo, from_csr, inspect_spgemm, pivot_row, require_structural_bound,
)


def dense_product(a, b):
    """Independent dense triple-loop oracle, including zero inner dimensions."""
    av, bv = a.dense(), b.dense()
    return [[sum((av[i][k] * bv[k][j] for k in range(a.pattern.columns)), Fraction(0))
             for j in range(b.pattern.columns)] for i in range(a.pattern.rows)]


class SparseTests(unittest.TestCase):
    def setUp(self):
        self.a, self.b, self.updated = cancellation_example()
        self.binding = Binding("fixture/AB")
        self.plan = inspect_spgemm(self.a, self.b, self.binding)

    def error(self, code, fn, *args, **kwargs):
        with self.assertRaises(SparseError) as caught:
            fn(*args, **kwargs)
        self.assertEqual(caught.exception.code, code)
        return caught.exception

    def test_cancellation_and_value_update_reuse_exact_plan(self):
        first = execute_spgemm(self.plan, self.a, self.b, self.binding)
        second = execute_spgemm(self.plan, self.a, self.updated, self.binding)
        self.assertEqual(first.dense(), [[0, 1], [-1, 0]])
        self.assertEqual(second.dense(), [[-1, 1], [-2, -2]])
        self.assertEqual((first.numerical_nonzeros, second.numerical_nonzeros), (2, 4))
        self.assertEqual((first.pattern.slots, second.pattern.slots), (4, 4))
        self.assertEqual(self.plan.multiplication_contributions, 6)
        self.assertIs(self.b.pattern, self.updated.pattern)
        self.assertIs(first.pattern, second.pattern)
        self.assertIs(second.pattern, self.plan.output)
        self.assertEqual(first.values, (0, 1, -1, 0))

    def test_zero_inputs_still_schedule_all_products(self):
        a = self.a.with_values([0] * 4)
        c = execute_spgemm(self.plan, a, self.b, self.binding)
        self.assertEqual((a.pattern.slots, a.numerical_nonzeros), (4, 0))
        self.assertEqual((c.pattern.slots, c.numerical_nonzeros), (4, 0))
        self.assertEqual(self.plan.multiplication_contributions, 6)
        self.assertEqual(execute_spgemm(self.plan, self.a, self.updated, self.binding).dense(),
                         dense_product(self.a, self.updated))

    def test_coo_duplicates_cancel_without_dropping_slots(self):
        entries = [(1, 2, 7), (0, 1, Fraction(1, 3)), (0, 0, 0),
                   (0, 1, Fraction(-1, 3)), (1, 2, -2)]
        a = from_coo(3, 3, entries, label="duplicates")
        self.assertEqual(a.pattern.offsets, (0, 2, 3, 3))
        self.assertEqual(a.pattern.indices, (0, 1, 2))
        self.assertEqual(a.values, (0, 0, 5))
        self.assertEqual((len(entries), a.pattern.slots, a.numerical_nonzeros), (5, 3, 1))
        reverse = from_coo(3, 3, reversed(entries), label="reordered")
        self.assertEqual(a.values, reverse.values)  # Exact Q only.
        self.assertEqual(a.pattern.positions(), reverse.pattern.positions())

    def test_duplicate_aggregation_precedes_contribution_count(self):
        a = from_coo(1, 1, [(0, 0, 1), (0, 0, -1)], label="A")
        b = from_coo(1, 1, [(0, 0, 2), (0, 0, 3)], label="B")
        plan = inspect_spgemm(a, b, self.binding)
        c = execute_spgemm(plan, a, b, self.binding)
        self.assertEqual((plan.multiplication_contributions, c.pattern.slots, c.numerical_nonzeros),
                         (1, 1, 0))
        self.assertEqual(execute_spgemm(plan, a.with_values([2]), b, self.binding).dense(), [[10]])

    def test_empty_rows_and_empty_inner_dimension(self):
        a = from_csr(3, 2, [0, 0, 1, 1], [1], [2], label="A")
        b = from_csr(2, 3, [0, 0, 1], [2], [3], label="B")
        plan = inspect_spgemm(a, b, self.binding)
        self.assertEqual(plan.output.offsets, (0, 0, 1, 1))
        self.assertEqual(execute_spgemm(plan, a, b, self.binding).dense(),
                         [[0, 0, 0], [0, 0, 6], [0, 0, 0]])
        for m, k, n in [(0, 0, 0), (0, 3, 2), (3, 0, 2), (2, 3, 0), (3, 2, 4)]:
            with self.subTest(shape=(m, k, n)):
                a = from_coo(m, k, [], label="emptyA")
                b = from_coo(k, n, [], label="emptyB")
                plan = inspect_spgemm(a, b, self.binding)
                self.assertEqual(plan.multiplication_contributions, 0)
                self.assertEqual(plan.output.offsets, (0,) * (m + 1))
                self.assertEqual(execute_spgemm(plan, a, b, self.binding).dense(), dense_product(a, b))

    def test_offset_rejections(self):
        for offsets, code in [([0, 2], "S_OFFSET_LENGTH"),
                              ([1, 1, 2], "S_OFFSET_ENDPOINT"),
                              ([0, 1, 1], "S_OFFSET_ENDPOINT"),
                              ([0, 3, 2], "S_OFFSET_BOUNDS"),
                              ([0, -1, 2], "S_INTEGER_RANGE"),
                              ([0, True, 2], "S_INTEGER_RANGE"),
                              ([0, 1.0, 2], "S_INTEGER_RANGE")]:
            with self.subTest(offsets=offsets):
                self.error(code, from_csr, 2, 2, offsets, [0, 1], [1, 1], label="bad")
        self.error("S_OFFSET_ORDER", from_csr, 3, 2, [0, 2, 1, 2], [0, 1], [1, 1], label="bad")
        self.error("S_OFFSET_LENGTH", from_csr, 0, 0, [], [], [], label="bad")
        self.error("S_OFFSET_BOUNDS", from_csr, 0, 0, [1], [], [], label="bad")

    def test_index_order_and_duplicate_rejections(self):
        for indices, code in [([1, 0], "S_CANONICAL_ROW"), ([0, 0], "S_CANONICAL_ROW"),
                              ([0, 2], "S_INDEX_BOUNDS"), ([0, -1], "S_INTEGER_RANGE"),
                              ([0, True], "S_INTEGER_RANGE"), ([0, 0.5], "S_INTEGER_RANGE")]:
            with self.subTest(indices=indices):
                self.error(code, from_csr, 1, 2, [0, 2], indices, [1, 1], label="bad")
        self.error("S_INDEX_BOUNDS", from_csr, 1, 0, [0, 1], [0], [0], label="bad")

    def test_shape_and_value_rejections(self):
        for rows, cols in [(-1, 2), (1, -2), (True, 2), (1, 2.0)]:
            self.error("S_INTEGER_RANGE", from_coo, rows, cols, [], label="bad")
        for values in [[], [1, 2]]:
            self.error("S_VALUE_LENGTH", from_csr, 1, 1, [0, 1], [0], values, label="bad")
        for value in [1.0, float("nan"), float("inf"), True, "1/2"]:
            self.error("S_EXACT_SCALAR", from_csr, 1, 1, [0, 1], [0], [value], label="bad")
        self.error("S_VALUE_LENGTH", self.a.with_values, [1])
        self.error("S_SHAPE", inspect_spgemm, self.a, self.a, self.binding)

    def test_coo_rejections(self):
        for entries, code in [([(1, 0, 1)], "S_INDEX_BOUNDS"),
                              ([(0, 1, 1)], "S_INDEX_BOUNDS"),
                              ([(-1, 0, 1)], "S_INTEGER_RANGE"),
                              ([(0, False, 1)], "S_INTEGER_RANGE"),
                              ([(0, 0)], "S_COO_ENTRY"),
                              ([(0, 0, 1.0)], "S_EXACT_SCALAR")]:
            self.error(code, from_coo, 1, 1, entries, label="bad")

    def test_unsigned_index_boundaries_without_large_allocation(self):
        for bits in (2, 32, 64):
            widths = IntegerProfile(bits, 64, 64)
            maximum = (1 << bits) - 1
            a = from_csr(1, maximum, [0, 1], [maximum - 1], [1], label="max", widths=widths)
            self.assertEqual(a.pattern.indices, (maximum - 1,))
            self.error("S_INTEGER_RANGE", from_coo, 0, maximum + 1, [], label="over", widths=widths)
            self.error("S_INDEX_BOUNDS", from_csr, 1, maximum, [0, 1], [maximum], [1],
                       label="over", widths=widths)
            self.error("S_INTEGER_RANGE", from_csr, 1, maximum, [0, 1], [maximum + 1], [1],
                       label="over", widths=widths)

    def test_offset_width_limits_and_raw_coo_limit(self):
        widths = IntegerProfile(4, 2, 8)  # Max offset/count = 3.
        a = from_csr(1, 4, [0, 3], [0, 1, 3], [0, 1, 0], label="max", widths=widths)
        self.assertEqual(a.pattern.slots, 3)
        self.error("S_INTEGER_RANGE", from_csr, 1, 4, [0, 4], [0, 1, 2, 3], [1] * 4,
                   label="over", widths=widths)
        self.error("S_INTEGER_RANGE", from_csr, 1, 4, [0, 4], [0], [1], label="over", widths=widths)
        self.error("S_INTEGER_RANGE", from_coo, 3, 0, [], label="row-count-over", widths=widths)
        self.assertEqual(from_coo(1, 1, [(0, 0, 1)] * 3, label="max", widths=widths).values, (3,))
        self.error("S_INTEGER_RANGE", from_coo, 1, 1, [(0, 0, 1)] * 4, label="raw-over", widths=widths)

    def test_output_slot_and_contribution_overflow(self):
        widths = IntegerProfile(3, 3, 8)  # Inputs each fit; nine output slots do not.
        a = from_coo(3, 1, [(i, 0, 1) for i in range(3)], label="A", widths=widths)
        b = from_coo(1, 3, [(0, j, 1) for j in range(3)], label="B", widths=widths)
        self.error("S_INTEGER_RANGE", inspect_spgemm, a, b, self.binding)
        widths = IntegerProfile(3, 4, 2)  # Count max = 3; one output slot.
        for k in (3, 4):
            a = from_coo(1, k, [(0, i, 0) for i in range(k)], label="A", widths=widths)
            b = from_coo(k, 1, [(i, 0, 0) for i in range(k)], label="B", widths=widths)
            if k == 3:
                self.assertEqual(inspect_spgemm(a, b, self.binding).multiplication_contributions, 3)
            else:
                self.error("S_INTEGER_RANGE", inspect_spgemm, a, b, self.binding)

    def test_bad_width_profiles_and_mismatched_profiles(self):
        for width in (0, -1, 65, True, 2.0):
            for field in ("index_bits", "offset_bits", "count_bits"):
                self.error("S_INTEGER_PROFILE", IntegerProfile, **{field: width})
        b = CSR(replace(self.b.pattern, widths=IntegerProfile(16, 32, 32)), self.b.values)
        self.error("S_WIDTH_MISMATCH", inspect_spgemm, self.a, b, self.binding)

    def test_immutable_snapshots_and_values(self):
        offsets, indices, values = [0, 1], [0], [2]
        a = from_csr(1, 1, offsets, indices, values, label="A")
        offsets[-1], indices[0], values[0] = 0, 9, 0
        self.assertEqual((a.pattern.offsets, a.pattern.indices, a.values), ((0, 1), (0,), (2,)))
        with self.assertRaises(FrozenInstanceError):
            a.pattern.revision = 5

    def test_nominal_identity_revision_and_pattern_changes_invalidate(self):
        variants = [replace(self.b.pattern), replace(self.b.pattern, revision=1),
                    replace(self.b.pattern, label="other"),
                    replace(self.b.pattern, indices=(1, 0, 1, 1))]
        for pattern in variants:
            with self.subTest(pattern=pattern):
                error = self.error("S_PATTERN_CHANGED", execute_spgemm, self.plan, self.a,
                                   CSR(pattern, self.b.values), self.binding)
                self.assertIsInstance(error, PlanInvalidated)
        rebuilt = inspect_spgemm(self.a, CSR(variants[-1], self.b.values), self.binding)
        self.assertEqual(execute_spgemm(rebuilt, self.a, CSR(variants[-1], self.b.values),
                                       self.binding).dense(), dense_product(self.a, CSR(variants[-1], self.b.values)))

    def test_eliminating_explicit_zero_is_a_pattern_change(self):
        b = self.b.with_values([1, 0, 1, -1])
        execute_spgemm(self.plan, self.a, b, self.binding)
        compacted = from_csr(3, 2, [0, 1, 2, 3], [0, 1, 1], [1, 1, -1], label="B", revision=1)
        self.assertEqual(b.dense(), compacted.dense())
        self.error("S_PATTERN_CHANGED", execute_spgemm, self.plan, self.a, compacted, self.binding)

    def test_occurrence_and_method_changes_invalidate(self):
        for binding in [Binding("different/AB"), replace(self.binding, method_revision=2)]:
            self.error("S_BINDING_CHANGED", execute_spgemm, self.plan, self.a, self.b, binding)

    def test_rejects_numerically_compacted_bound_and_plan(self):
        candidate = Pattern("observed", 0, 2, 2, (0, 1, 2), (1, 0))
        self.error("S_BOUND_MISSING", require_structural_bound, self.a, self.b, candidate)
        bad = replace(self.plan, output=candidate, products=(self.plan.products[1], self.plan.products[2]))
        self.error("S_PLAN_TAMPERED", execute_spgemm, bad, self.a, self.b, self.binding)
        self.error("S_PLAN_TAMPERED", execute_spgemm, replace(self.plan, products=self.plan.products[::-1]),
                   self.a, self.b, self.binding)
        missing = (self.plan.products[0][:-1],) + self.plan.products[1:]
        self.error("S_PLAN_TAMPERED", execute_spgemm, replace(self.plan, products=missing),
                   self.a, self.b, self.binding)

    def test_subset_is_not_sound_output_bound_even_for_singleton(self):
        one = from_coo(1, 1, [(0, 0, 1)], label="one")
        empty = from_coo(1, 1, [], label="empty")
        self.error("S_BOUND_MISSING", require_structural_bound, one, one, empty.pattern)
        zero = one.with_values([0])
        self.error("S_BOUND_MISSING", require_structural_bound, zero, one, empty.pattern)
        require_structural_bound(one, one, one.pattern)

    def test_conservative_superset_bound_is_allowed(self):
        diagonal = from_coo(2, 2, [(0, 0, 1), (1, 1, 1)], label="diagonal")
        require_structural_bound(diagonal, diagonal, self.plan.output)
        wrong_shape = from_coo(1, 1, [], label="wrong")
        self.error("S_SHAPE", require_structural_bound, diagonal, diagonal, wrong_shape.pattern)

    def test_numeric_pivot_guard_reuse_invalidation_and_reinspection(self):
        a = from_coo(2, 2, [(0, 0, 2), (0, 1, 1), (1, 0, 1), (1, 1, 1)], label="pivotA")
        b = from_coo(2, 1, [(0, 0, 1), (1, 0, 1)], label="pivotB")
        structural = inspect_spgemm(a, b, self.binding)
        guarded = bind_pivot_guard(structural, a, b, self.binding)
        stable = a.with_values([3, -2, 1, 9])
        self.assertEqual(execute_guarded(guarded, stable, b, self.binding).dense(), dense_product(stable, b))
        for changed in [a.with_values([1, 1, 4, 1]), a.with_values([0, 1, 0, 1])]:
            self.assertEqual(execute_spgemm(structural, changed, b, self.binding).dense(), dense_product(changed, b))
            self.error("S_NUMERIC_DEPENDENCY_CHANGED", execute_guarded, guarded, changed, b, self.binding)
        changed = a.with_values([1, 1, 4, 1])
        renewed = bind_pivot_guard(structural, changed, b, self.binding)
        self.assertEqual(renewed.selected_row, 1)
        self.assertEqual(execute_guarded(renewed, changed, b, self.binding).dense(), dense_product(changed, b))
        self.assertEqual(pivot_row(a.with_values([-2, 1, 2, 1]), 0), 0)
        self.error("S_PIVOT_ZERO", bind_pivot_guard, structural, a.with_values([0, 1, 0, 1]), b, self.binding)

    def test_numeric_guard_still_requires_exact_pattern_and_binding(self):
        guarded = bind_pivot_guard(self.plan, self.a, self.b, self.binding)
        self.error("S_PATTERN_CHANGED", execute_guarded, guarded, CSR(replace(self.a.pattern), self.a.values),
                   self.b, self.binding)
        self.error("S_BINDING_CHANGED", execute_guarded, guarded, self.a, self.b, Binding("other"))

    def test_all_two_by_two_pattern_pairs_against_dense_and_boolean_oracles(self):
        coordinates = tuple(product(range(2), repeat=2))
        for mask_a, mask_b in product(range(16), repeat=2):
            pa = {p for bit, p in enumerate(coordinates) if mask_a & (1 << bit)}
            pb = {p for bit, p in enumerate(coordinates) if mask_b & (1 << bit)}
            a = from_coo(2, 2, [(i, j, (-1, 0, 1)[(i + j) % 3]) for i, j in sorted(pa)], label="A")
            b = from_coo(2, 2, [(i, j, (-1, 0, 1)[(2*i + j) % 3]) for i, j in sorted(pb)], label="B")
            expected = {(i, j) for i, j in coordinates if any((i, k) in pa and (k, j) in pb for k in range(2))}
            contributions = sum(sum(col == k for _, col in pa) * sum(row == k for row, _ in pb)
                                for k in range(2))
            plan = inspect_spgemm(a, b, self.binding)
            c = execute_spgemm(plan, a, b, self.binding)
            self.assertEqual(plan.output.positions(), expected)
            self.assertEqual(plan.multiplication_contributions, contributions)
            self.assertEqual(c.dense(), dense_product(a, b))
            self.assertLessEqual(c.numerical_nonzeros, c.pattern.slots)

    def test_all_small_signed_values_under_one_fixed_plan(self):
        a = from_coo(1, 2, [(0, 0, 0), (0, 1, 0)], label="A")
        b = from_coo(2, 1, [(0, 0, 0), (1, 0, 0)], label="B")
        plan = inspect_spgemm(a, b, self.binding)
        for values in product((-1, 0, 1), repeat=4):
            av, bv = a.with_values(values[:2]), b.with_values(values[2:])
            self.assertEqual(execute_spgemm(plan, av, bv, self.binding).dense(), dense_product(av, bv))
            self.assertEqual((plan.output.slots, plan.multiplication_contributions), (1, 2))

    def test_rectangular_rational_products_and_updates(self):
        rng = random.Random(243)
        for _ in range(100):
            m, k, n = (rng.randrange(5) for _ in range(3))
            def matrix(rows, columns, label):
                return from_coo(rows, columns,
                                [(i, j, Fraction(rng.randrange(-3, 4), rng.randrange(1, 5)))
                                 for i in range(rows) for j in range(columns) if rng.randrange(2)], label=label)
            a, b = matrix(m, k, "A"), matrix(k, n, "B")
            plan = inspect_spgemm(a, b, self.binding)
            for _ in range(3):
                c = execute_spgemm(plan, a, b, self.binding)
                self.assertEqual(c.dense(), dense_product(a, b))
                self.assertLessEqual(c.numerical_nonzeros, c.pattern.slots)
                a = a.with_values([Fraction(rng.randrange(-2, 3), 3) for _ in a.values])
                b = b.with_values([Fraction(rng.randrange(-2, 3), 5) for _ in b.values])


if __name__ == "__main__":
    unittest.main()
