"""Finite enumeration is an independent test oracle, never a preflight path."""

from dataclasses import replace
import itertools
from pathlib import Path
import subprocess
import sys
import unittest

import storage_layout_reference as r


KEY = r.AllocationKey("buffer", 1)
SAFE, INVALID, UNKNOWN = r.Verdict.SAFE, r.Verdict.INVALID, r.Verdict.NEEDS_EVIDENCE


def world(capacity=128, *, base=4096, key=KEY, element=r.Element(), loans=()):
    return r.World(0, (r.Allocation(key, capacity, base, element),), loans)


def byte_intervals(access):
    """Independent literal address semantics, only used on small test inputs."""
    l = access.layout
    return [(l.offset + i * l.strides[0] + j * l.strides[1], l.element.width)
            for i in range(l.shape[0]) for j in range(l.shape[1])]


def byte_set(access):
    return {byte for start, width in byte_intervals(access) for byte in range(start, start + width)}


def broadcast(rows=5, columns=3, mode=r.Mode.READ):
    return r.Access(KEY, r.Layout(r.Kind.BROADCAST, (rows, columns), (0, 8),
                                 source=r.DenseSource(1, columns, 1)), mode)


class LayoutTests(unittest.TestCase):
    def test_positive_strides_bounds_are_not_write_injectivity(self):
        access = r.Access(KEY, r.Layout(r.Kind.STRIDED, (2, 2), (8, 8)), r.Mode.WRITE)
        report = r.check_layout(world(24), access)
        self.assertEqual([x for x, _ in byte_intervals(access)], [0, 8, 8, 16])
        self.assertIs(report["bounds"].verdict, SAFE)
        self.assertIs(report["alignment"].verdict, SAFE)
        self.assertIs(report["write_injectivity"].verdict, INVALID)
        self.assertIs(report.verdict, INVALID)
        good = r.dense(KEY, 2, 2, 2, mode=r.Mode.WRITE)
        self.assertEqual(len(byte_set(good)), 4 * 8)
        self.assertIs(r.check_layout(world(32), good).verdict, SAFE)

    def test_partial_bytes_matter_not_just_distinct_starts(self):
        e = r.Element(16, 8)
        access = r.Access(KEY, r.Layout(r.Kind.STRIDED, (2, 1), (8, 32), element=e), r.Mode.WRITE)
        report = r.check_layout(world(24, element=e), access)
        self.assertEqual(len(set(start for start, _ in byte_intervals(access))), 2)
        self.assertIs(report["bounds"].verdict, SAFE)
        self.assertIs(report["alignment"].verdict, SAFE)
        self.assertIs(report["write_injectivity"].verdict, INVALID)

    def test_dense_transpose_same_bytes_not_same_layout(self):
        a = r.dense(KEY, 2, 3, 4, offset=8, mode=r.Mode.READ_WRITE)
        b = r.transpose(a)
        self.assertNotEqual(a.layout, b.layout)
        self.assertEqual(byte_set(a), byte_set(b))
        self.assertEqual(b.layout.shape, (3, 2))
        self.assertEqual(b.layout.strides, (32, 8))
        self.assertIs(r.check_layout(world(88), b).verdict, SAFE)
        forged = replace(b, layout=replace(b.layout, strides=(8, 32)))
        self.assertEqual(r.check_layout(world(), forged)["profile"].reason,
                         "layout_does_not_match_declared_source")

    def test_empty_shapes_offset_and_alignment(self):
        for shape in ((0, 0), (0, 4), (4, 0)):
            a = r.dense(KEY, *shape, max(1, shape[0]), offset=1, mode=r.Mode.WRITE)
            for a in (a, r.transpose(a)):
                report = r.check_layout(world(1), a)
                self.assertIs(report.verdict, SAFE)
                self.assertIsNone(report.envelope)
                self.assertEqual(byte_intervals(a), [])
                self.assertIs(r.check_layout(world(0), a).verdict, INVALID)
        self.assertIs(r.check_layout(world(0), r.dense(KEY, 0, 5, 1)).verdict, SAFE)
        # Empty means no access, not permission to carry malformed metadata.
        bad = r.dense(KEY, 0, 3, 0)
        self.assertEqual(r.check_layout(world(), bad)["profile"].reason, "invalid_leading_dimension")

    def test_read_only_broadcast_is_explicit(self):
        a = broadcast()
        self.assertIs(r.check_layout(world(24), a).verdict, SAFE)
        self.assertEqual(len(byte_set(a)), 24)
        for mode in (r.Mode.WRITE, r.Mode.READ_WRITE):
            self.assertIs(r.check_layout(world(24), broadcast(mode=mode)).verdict, INVALID)
            self.assertIs(r.check_layout(world(0), broadcast(rows=0, mode=mode)).verdict, INVALID)
        implicit = replace(a, layout=replace(a.layout, kind=r.Kind.STRIDED, source=None))
        self.assertIs(r.check_layout(world(24), implicit).verdict, UNKNOWN)
        forged = replace(a, layout=replace(a.layout, source=r.DenseSource(2, 3, 2)))
        self.assertIs(r.check_layout(world(24), forged).verdict, INVALID)
        scalar = replace(a, layout=r.Layout(r.Kind.BROADCAST, (7, 9), (0, 0),
                                           source=r.DenseSource(1, 1, 1)))
        self.assertEqual(byte_set(scalar), set(range(8)))
        self.assertIs(r.check_layout(world(8), scalar).verdict, SAFE)

    def test_capacity_counts_element_width_and_padding(self):
        a = r.dense(KEY, 2, 3, 4)
        self.assertEqual(max(byte_set(a)) + 1, 80)
        self.assertIs(r.check_layout(world(80), a).verdict, SAFE)
        self.assertEqual(r.check_layout(world(79), a)["bounds"].reason, "capacity_exceeded")
        self.assertNotIn(16, byte_set(a))  # padding is not initialized/read data

    def test_alignment_is_absolute_and_ignores_inactive_axis_strides(self):
        a = r.dense(KEY, 1, 1, 1)
        self.assertIs(r.check_layout(world(base=4097), a)["alignment"].verdict, INVALID)
        a = replace(a, layout=replace(a.layout, offset=7))
        self.assertIs(r.check_layout(world(base=4097), a)["alignment"].verdict, SAFE)
        raw = replace(a, layout=r.Layout(r.Kind.STRIDED, (1, 2), (1, 8)))
        self.assertIs(r.check_layout(world(), raw)["alignment"].verdict, SAFE)
        raw = replace(raw, layout=replace(raw.layout, shape=(2, 2)))
        self.assertIs(r.check_layout(world(), raw)["alignment"].verdict, INVALID)

    def test_native_overflow_is_separate_from_mathematical_bounds(self):
        a = r.dense(KEY, 1, 2, 1 << 31)
        report = r.check_layout(world((1 << 34) + 8), a)
        self.assertIs(report["bounds"].verdict, SAFE)
        self.assertEqual(report["native"].reason, "native_dimension_overflow")
        a = r.dense(KEY, 1, 1, 1, offset=1 << 63)
        report = r.check_layout(world((1 << 63) + 8), a)
        self.assertIs(report["bounds"].verdict, SAFE)
        self.assertEqual(report["native"].reason, "native_byte_arithmetic_overflow")
        a = r.dense(KEY, 1, 1, 1)
        report = r.check_layout(world(8, base=(1 << 64) - 8), a)
        self.assertEqual(report["native"].reason, "native_address_overflow")

    def test_native_products_and_sums_at_small_limits(self):
        limits = r.NativeLimits(16, 8, 8)
        for offset in range(0, 128, 8):
            for m, n, ld in itertools.product(range(1, 4), range(1, 4), range(3, 6)):
                a = r.dense(KEY, m, n, ld, offset=offset)
                end = max(byte_set(a)) + 1
                report = r.check_layout(world(end), a, limits)
                self.assertIs(report["bounds"].verdict, SAFE)
                self.assertIs(report["native"].verdict, SAFE if end <= 127 else INVALID)

    def test_malformed_and_unsupported_are_distinct(self):
        a = r.dense(KEY, 2, 2, 2)
        for layout in (replace(a.layout, shape=(-1, 2)), replace(a.layout, shape=(True, 2)),
                       replace(a.layout, shape=(2.0, 2)), replace(a.layout, strides=(8,)),
                       replace(a.layout, element=r.Element(0, 8)),
                       replace(a.layout, element=r.Element(8, 3))):
            self.assertIs(r.check_layout(world(), replace(a, layout=layout)).verdict, INVALID)
        for strides in ((-8, 16), (16, 40)):
            raw = replace(a, layout=r.Layout(r.Kind.STRIDED, (2, 2), strides))
            self.assertIs(r.check_layout(world(), raw).verdict, UNKNOWN)

    def test_finite_dense_bounds_and_injectivity_oracle(self):
        cases = 0
        for m, n, ld, offset, capacity in itertools.product(
                range(5), range(5), range(1, 7), (0, 8, 16), range(0, 161, 8)):
            a = r.dense(KEY, m, n, ld, offset=offset, mode=r.Mode.WRITE)
            for access in (a, r.transpose(a)):
                report = r.check_layout(world(capacity), access)
                intervals = byte_intervals(access)
                expected_bounds = (offset <= capacity if not intervals else
                                   all(0 <= start and start + width <= capacity
                                       for start, width in intervals))
                self.assertEqual(report["bounds"].verdict is SAFE, expected_bounds)
                if report.verdict is SAFE:
                    self.assertGreaterEqual(ld, max(1, m))
                    self.assertEqual(len(byte_set(access)), len(intervals) * 8)
                    self.assertTrue(all((4096 + start) % 8 == 0 for start, _ in intervals))
                cases += 1
        self.assertEqual(cases, 18900)


class LoanTests(unittest.TestCase):
    def test_read_read_write_read_write_write(self):
        a = r.dense(KEY, 2, 2, 2)
        for x, y in itertools.product(r.Mode, repeat=2):
            verdict = r.check_loans(world(), replace(a, mode=x), replace(a, mode=y)).verdict
            self.assertIs(verdict, SAFE if x is y is r.Mode.READ else INVALID)

    def test_interleaved_unknown_is_not_actual_overlap(self):
        even = r.dense(KEY, 1, 3, 2, mode=r.Mode.WRITE)
        odd = r.dense(KEY, 1, 3, 2, offset=8)
        self.assertFalse(byte_set(even) & byte_set(odd))
        self.assertEqual(r.check_loans(world(48), even, odd).reason,
                         "overlapping_envelopes_need_partition_evidence")
        self.assertIs(r.check_loans(world(48), even, odd).verdict, UNKNOWN)
        overlap = r.dense(KEY, 1, 2, 2, offset=16)
        self.assertTrue(byte_set(even) & byte_set(overlap))
        self.assertEqual(r.check_loans(world(48), even, overlap).reason, "actual_byte_overlap")

    def test_unknown_does_not_mean_disjoint(self):
        a = r.dense(KEY, 1, 4, 3, mode=r.Mode.WRITE)
        b = r.dense(KEY, 1, 3, 2, offset=8)
        self.assertTrue(byte_set(a) & byte_set(b))  # a later column overlaps
        self.assertIs(r.check_loans(world(), a, b).verdict, UNKNOWN)

    def test_disjoint_intervals_and_empty_regions(self):
        a = r.dense(KEY, 2, 2, 2, mode=r.Mode.WRITE)
        b = r.dense(KEY, 2, 2, 2, offset=32, mode=r.Mode.WRITE)
        self.assertIs(r.check_loans(world(), a, b).verdict, SAFE)
        self.assertIs(r.check_loans(world(), a, r.dense(KEY, 0, 4, 1)).verdict, SAFE)

    def test_distinct_allocations_and_stale_generations(self):
        other = r.AllocationKey("other", 1)
        a = r.dense(KEY, 2, 2, 2, mode=r.Mode.WRITE)
        w = r.World(0, (r.Allocation(KEY, 32, 4096), r.Allocation(other, 32, 8192)))
        self.assertIs(r.check_loans(w, a, replace(a, allocation=other)).verdict, SAFE)
        newer = replace(KEY, generation=2)
        self.assertIs(r.check_layout(world(key=newer), a).verdict, INVALID)
        duplicate = replace(w, allocations=(w.allocations[0], r.Allocation(newer, 32, 8192)))
        self.assertIs(r.check_world(duplicate).verdict, INVALID)
        aliased = replace(w, allocations=(w.allocations[0], r.Allocation(other, 32, 4096)))
        self.assertIs(r.check_world(aliased).verdict, INVALID)

    def test_loan_answers_against_finite_byte_oracle(self):
        accesses = [r.dense(KEY, m, n, ld, offset=offset, mode=r.Mode.WRITE)
                    for m, n, ld, offset in itertools.product((1, 2), (1, 2, 3), (2, 3), (0, 8, 24))]
        accesses += [r.transpose(a) for a in accesses]
        for a, b in itertools.product(accesses, repeat=2):
            result = r.check_loans(world(128), a, b)
            overlap = bool(byte_set(a) & byte_set(b))
            if result.verdict is SAFE:
                self.assertFalse(overlap)
            elif result.verdict is INVALID:
                self.assertTrue(overlap)


class EvidenceTests(unittest.TestCase):
    def setUp(self):
        self.access = r.dense(KEY, 2, 2, 2, mode=r.Mode.WRITE)
        self.ir = r.LayoutIR("fill", 1, (self.access,))
        self.world = world()
        self.session = r.PreflightSession()

    def test_no_evidence_before_success_and_after_failure(self):
        prepared = r.Prepared(self.ir)
        for alleged in (None, True, prepared, r.Success(self.ir, self.world, r.NativeLimits(), object()),
                        r.Success(self.ir, self.world, r.NativeLimits(), [])):
            self.assertIs(self.session.audit_for_bounds_elision(alleged, self.ir, self.world).verdict,
                          INVALID)
        report, success = self.session.preflight(prepared, world(1))
        self.assertIs(report.verdict, INVALID)
        self.assertIsNone(success)
        unknown_ir = replace(self.ir, accesses=(r.dense(KEY, 1, 3, 2, mode=r.Mode.WRITE),
                                                r.dense(KEY, 1, 3, 2, offset=8)))
        report, success = self.session.preflight(r.Prepared(unknown_ir), self.world)
        self.assertIs(report.verdict, UNKNOWN)
        self.assertIsNone(success)

    def test_same_actual_returned_ir_and_world_and_target_only(self):
        _, success = self.session.preflight(r.Prepared(self.ir), self.world)
        self.assertIs(success.ir, self.ir)
        self.assertIs(self.session.audit_for_bounds_elision(success, success.ir, self.world).verdict, SAFE)
        variants = (replace(self.ir, operation="different"), replace(self.ir, revision=2),
                    replace(self.ir, accesses=(r.transpose(self.access),)),
                    replace(self.ir, accesses=(replace(self.access, mode=r.Mode.READ),)),
                    replace(self.ir, accesses=()))
        for actual in variants:
            self.assertEqual(self.session.audit_for_bounds_elision(success, actual, self.world).reason,
                             "evidence_binding_mismatch")
        a = self.world.allocations[0]
        variants = (replace(self.world, epoch=1), world(key=replace(KEY, generation=2)),
                    world(64), world(base=8192), replace(self.world, active_loans=(self.access,)),
                    replace(self.world, allocations=(replace(a, element=r.Element(16, 8)),)))
        for current in variants:
            self.assertIs(self.session.audit_for_bounds_elision(success, self.ir, current).verdict, INVALID)
        self.assertIs(self.session.audit_for_bounds_elision(success, self.ir, self.world,
                                                            r.NativeLimits(32, 32, 32)).verdict, INVALID)

    def test_forged_receipt_cross_session_and_expired_scope(self):
        _, success = self.session.preflight(r.Prepared(self.ir), self.world)
        forged = replace(success, ir=replace(self.ir, revision=2))
        self.assertIs(self.session.audit_for_bounds_elision(forged, forged.ir, self.world).verdict, INVALID)
        self.assertIs(r.PreflightSession().audit_for_bounds_elision(success, self.ir, self.world).verdict,
                      INVALID)
        self.session.end_scope(success)
        self.assertIs(self.session.audit_for_bounds_elision(success, self.ir, self.world).verdict, INVALID)

    def test_active_loans_and_invalid_existing_environment(self):
        for loans in ((replace(self.access, mode=r.Mode.READ),), (self.access, self.access)):
            report, success = self.session.preflight(r.Prepared(self.ir), world(loans=loans))
            self.assertIs(report.verdict, INVALID)
            self.assertIsNone(success)
        report, success = self.session.preflight(r.Prepared(replace(self.ir, accesses=())),
                                                 world(loans=(self.access, self.access)))
        self.assertIs(report.verdict, INVALID)
        self.assertIsNone(success)

    def test_empty_ir_still_checks_target_contract(self):
        ir = replace(self.ir, accesses=())
        self.assertIs(r.inspect_preflight(world(), ir, r.NativeLimits(0, 0, 0)).verdict, INVALID)
        # The address expression widens indices before multiplication. Even a
        # zero-stride broadcast must not justify narrowing those indices.
        self.assertIs(r.inspect_preflight(world(), ir, r.NativeLimits(16, 8, 16)).verdict, INVALID)

    def test_huge_layout_preflight_does_not_enumerate_elements(self):
        # 10^18 logical cells. A subprocess deadline also catches accidental
        # future enumeration without hanging the entire regression suite.
        code = """
import storage_layout_reference as r
k = r.AllocationKey('huge', 1)
w = r.World(0, (r.Allocation(k, 8 * 10**18, 4096),))
a = r.dense(k, 10**9, 10**9, 10**9, mode=r.Mode.WRITE)
ir = r.LayoutIR('fill', 1, (r.transpose(a),))
s = r.PreflightSession()
report, receipt = s.preflight(r.Prepared(ir), w)
assert report.verdict is r.Verdict.SAFE
assert s.audit_for_bounds_elision(receipt, ir, w).verdict is r.Verdict.SAFE
"""
        subprocess.run([sys.executable, "-c", code], cwd=Path(__file__).resolve().parent,
                       check=True, timeout=5, capture_output=True, text=True)


if __name__ == "__main__":
    unittest.main()
