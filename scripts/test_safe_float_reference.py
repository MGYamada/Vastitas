"""Independent law, equality, effect, and internal-trace regressions for #318."""

from dataclasses import FrozenInstanceError
from fractions import Fraction as Q
from itertools import product
import unittest
from unittest.mock import patch

import float_reference as r
import safe_float_reference as m


F = r.Flags
ONE = r.F64(0x3FF0000000000000)
TWO = r.F64(0x4000000000000000)
SAMPLES = (r.zero(), r.zero(True), ONE, r.F64(1), r.F64(0x7FEFFFFFFFFFFFFF),
           r.infinity(), r.infinity(True), r.F64(0x7FF8000000000042),
           r.F64(0xFFF8000000000043), r.F64(0x7FF0000000000042))
SMALL_FLAGS = (F.NONE, F.UNDERFLOW, F.INEXACT, F.UNDERFLOW | F.INEXACT)


def raw(value, flags=F.NONE):
    """Synthetic finite law fixture, not a public emit/clear/inspect-flags API."""
    return m.Float(lambda cfg: m._Run(value, flags))


def safe(result, flags=F.NONE):
    return m.SafeFloat(lambda cfg: m._Run(result, flags))


def underflow(site="tiny"):
    return m.lift(m.convert(Q(1, 2**1075), site=site))


def bad_continuation(_):
    raise AssertionError("continuation after failure executed")


def bad_branch():
    raise AssertionError("unselected branch constructed")


class FlagMonoidTests(unittest.TestCase):
    def test_all_32_masks_have_units_associativity_and_sticky_union(self):
        masks = tuple(F(n) for n in range(32))
        for a in masks:
            self.assertEqual(F.NONE | a, a)
            self.assertEqual(a | F.NONE, a)
            self.assertEqual(a | a, a)
        for a, b, c in product(masks, repeat=3):
            self.assertEqual((a | b) | c, a | (b | c))


class FloatLawTests(unittest.TestCase):
    def setUp(self):
        self.outcomes = [(a, w) for a, w in product((0, 1), SMALL_FLAGS)]
        self.functions = [lambda a, table=table: raw(*table[a])
                          for table in product(self.outcomes, repeat=2)]

    def test_left_unit(self):
        for a, f in product((0, 1), self.functions):
            self.assertTrue(m.same_observation(m.Float.pure(a).bind(f).run(), f(a).run()))

    def test_right_unit(self):
        for a, w in self.outcomes:
            program = raw(a, w)
            self.assertTrue(m.same_observation(program.bind(m.Float.pure).run(), program.run()))

    def test_associativity(self):
        for (a, w), f, g in product(self.outcomes, self.functions, self.functions):
            program = raw(a, w)
            left = program.bind(f).bind(g).run()
            right = program.bind(lambda x: f(x).bind(g)).run()
            self.assertTrue(m.same_observation(left, right))


class SafeFloatLawTests(unittest.TestCase):
    def setUp(self):
        results = (m.Ok(0), m.Ok(1), m.Err(m.Error.DIVISION_BY_ZERO))
        self.outcomes = list(product(results, SMALL_FLAGS))
        self.functions = [lambda a, table=table: safe(*table[a])
                          for table in product(self.outcomes, repeat=2)]

    def test_left_unit(self):
        for a, f in product((0, 1), self.functions):
            self.assertTrue(m.same_observation(m.SafeFloat.pure(a).bind(f).run(), f(a).run()))

    def test_right_unit(self):
        for result, flags in self.outcomes:
            program = safe(result, flags)
            self.assertTrue(m.same_observation(program.bind(m.SafeFloat.pure).run(), program.run()))

    def test_associativity_including_failure_at_each_step(self):
        for (result, flags), f, g in product(self.outcomes, self.functions, self.functions):
            program = safe(result, flags)
            left = program.bind(f).bind(g).run()
            right = program.bind(lambda x: f(x).bind(g)).run()
            self.assertTrue(m.same_observation(left, right))


class LiftAndEqualityTests(unittest.TestCase):
    def test_lift_preserves_pure_bits_and_empty_flags(self):
        for value in SAMPLES:
            self.assertEqual(m.lift(m.Float.pure(value)).run(), (m.Ok(value), F.NONE))
            self.assertTrue(m.same_observation(m.lift(m.Float.pure(value)).run(),
                                               m.SafeFloat.pure(value).run()))

    def test_lift_preserves_bind_for_all_flag_pairs_and_special_bits(self):
        for a, w1, w2 in product(SAMPLES, range(32), range(32)):
            program = raw(a, F(w1))
            f = lambda x: raw((x, r.zero(True)), F(w2))
            self.assertTrue(m.same_observation(m.lift(program.bind(f)).run(),
                                               m.lift(program).bind(lambda x: m.lift(f(x))).run()))

    def test_laws_with_real_reference_operations_and_special_bits(self):
        for value in SAMPLES:
            for cls, f, g in (
                (m.Float, lambda x: m.binary("add", x, r.zero(True)),
                 lambda x: m.binary("div", ONE, x)),
                (m.SafeFloat, lambda x: m.checked_div(ONE, x),
                 lambda x: m.checked_div(x, x)),
            ):
                program = cls.pure(value)
                self.assertTrue(m.same_observation(program.bind(f).run(), f(value).run()))
                effect = f(value)
                self.assertTrue(m.same_observation(effect.bind(cls.pure).run(), effect.run()))
                self.assertTrue(m.same_observation(effect.bind(f).bind(g).run(),
                                                   effect.bind(lambda a: f(a).bind(g)).run()))

    def test_representation_equality_is_independent_of_numeric_equality(self):
        positive, negative = r.zero(), r.zero(True)
        self.assertEqual(positive.as_fraction(), negative.as_fraction())
        self.assertFalse(m.same_observation(m.Float.pure(positive).run(),
                                           m.Float.pure(negative).run()))
        for nan in SAMPLES[-3:]:
            self.assertTrue(m.same_observation(m.Float.pure(nan).run(), m.Float.pure(nan).run()))
            self.assertEqual(m.Float.pure(nan).audit().trace, ())
        self.assertFalse(m.same_observation((m.Ok(SAMPLES[-3]), F.NONE),
                                           (m.Ok(SAMPLES[-2]), F.NONE)))
        self.assertFalse(m.same_observation((m.Ok(ONE), F.NONE), (m.Ok(ONE), F.INEXACT)))
        self.assertFalse(m.same_observation((m.Ok(ONE), F.NONE),
                                           (m.Err(m.Error.DIVISION_BY_ZERO), F.NONE)))
        for native in (0.0, float("nan")):
            with self.assertRaises(TypeError):
                m.same_observation((native, F.NONE), (native, F.NONE))

    def test_same_numeric_zero_has_distinguishable_continuations(self):
        first = m.Float.pure(r.zero()).bind(lambda x: m.binary("div", ONE, x)).run()
        second = m.Float.pure(r.zero(True)).bind(lambda x: m.binary("div", ONE, x)).run()
        self.assertEqual(first, (r.infinity(), F.DIVIDE_BY_ZERO))
        self.assertEqual(second, (r.infinity(True), F.DIVIDE_BY_ZERO))
        self.assertFalse(m.same_observation(first, second))

    def test_raw_result_carrier_is_not_short_circuiting_safe_bind(self):
        error = m.Err(m.Error.DIVISION_BY_ZERO)
        self.assertEqual(m.Float.pure(error).bind(lambda _: raw(1, F.INVALID)).run(),
                         (1, F.INVALID))
        self.assertEqual(m.SafeFloat.fail().bind(bad_continuation).run(), (error, F.NONE))
        self.assertEqual(m.lift(m.Float.pure(error)).run(), (m.Ok(error), F.NONE))

    def test_unit_config_is_immutable_and_unknown_profiles_are_rejected(self):
        with self.assertRaises(FrozenInstanceError):
            m.CONFIG.rounding = "down"
        with self.assertRaises(TypeError):
            m.Float.pure(ONE).run("fast-math")
        with self.assertRaises(ValueError):
            m.binary("fma", ONE, ONE)


class FailureAndNumericalBoundaryTests(unittest.TestCase):
    def test_every_zero_guard_rejects_without_running_ieee_division(self):
        for numerator, denominator in product(SAMPLES, (r.zero(), r.zero(True))):
            with patch.object(r, "div", side_effect=AssertionError("raw division after failed guard")):
                out = m.checked_div(numerator, denominator, site="zero").audit()
            self.assertEqual(out.value, m.Err(m.Error.DIVISION_BY_ZERO))
            self.assertEqual(out.flags, F.NONE)  # Even sNaN numerator is not quieted.
            self.assertEqual(out.trace, (m.Event("zero", "guard-fail"),))

    def test_failure_preserves_every_preexisting_mask(self):
        for mask in range(32):
            program = m.lift(raw(ONE, F(mask))).bind(lambda x: m.checked_div(x, r.zero()))
            self.assertEqual(program.run(), (m.Err(m.Error.DIVISION_BY_ZERO), F(mask)))

    def test_prior_underflow_survives_failure_and_skipped_work_adds_no_flags(self):
        program = underflow().bind(lambda _: m.checked_div(ONE, r.zero()))
        self.assertEqual(program.bind(bad_continuation).run(),
                         (m.Err(m.Error.DIVISION_BY_ZERO), F.UNDERFLOW | F.INEXACT))
        skipped_overflow = program.bind(lambda _: m.lift(m.binary(
            "mul", r.F64(0x7FEFFFFFFFFFFFFF), TWO)))
        self.assertEqual(skipped_overflow.run(), program.run())

    def test_repeated_sticky_flags_are_occurrences_not_new_mask_bits(self):
        program = underflow("first").bind(lambda _: underflow("second"))
        out = program.audit()
        self.assertEqual(out.flags, F.UNDERFLOW | F.INEXACT)
        self.assertEqual([e.local_flags for e in out.trace],
                         [F.UNDERFLOW | F.INEXACT] * 2)

    def test_two_raw_zero_divisions_both_run_and_set_one_sticky_flag(self):
        program = m.binary("div", ONE, r.zero(), site="first").bind(
            lambda _: m.binary("div", ONE, r.zero(True), site="second"))
        self.assertEqual(program.run(), (r.infinity(True), F.DIVIDE_BY_ZERO))
        self.assertEqual(program.audit().trace,
                         (m.Event("first", "div", F.DIVIDE_BY_ZERO),
                          m.Event("second", "div", F.DIVIDE_BY_ZERO)))

    def test_checked_branch_is_lazy_and_failed_condition_skips_both(self):
        failing = lambda: m.checked_div(ONE, r.zero(), site="selected-failure")
        self.assertEqual(m.choose(m.SafeFloat.pure(True), lambda: underflow(), bad_branch).run(),
                         (m.Ok(r.zero()), F.UNDERFLOW | F.INEXACT))
        self.assertEqual(m.choose(m.SafeFloat.pure(False), failing, lambda: m.SafeFloat.pure(ONE)).run(),
                         (m.Ok(ONE), F.NONE))
        self.assertEqual(m.choose(m.SafeFloat.pure(False), lambda: underflow(),
                                  lambda: m.SafeFloat.pure(ONE)).audit().trace, ())
        self.assertEqual(m.choose(m.SafeFloat.pure(True), failing, bad_branch).run(),
                         (m.Err(m.Error.DIVISION_BY_ZERO), F.NONE))
        self.assertEqual(m.choose(m.SafeFloat.fail(), bad_branch, bad_branch).run(),
                         (m.Err(m.Error.DIVISION_BY_ZERO), F.NONE))

    def test_checked_failure_cannot_be_erased_by_multiply_zero_or_self_division(self):
        failure = m.checked_div(ONE, r.zero())
        self.assertIsInstance(failure.bind(lambda x: m.lift(m.binary("mul", r.zero(), x))).run()[0], m.Err)
        self.assertIsInstance(m.checked_div(r.zero(), r.zero()).run()[0], m.Err)
        self.assertIsInstance(m.divide(m.SafeFloat.pure(ONE), failure).run()[0], m.Err)

    def test_mathematical_nonzero_can_round_to_zero(self):
        exact = Q(1, 2**1075)
        self.assertNotEqual(exact, 0)
        program = m.lift(m.convert(exact)).bind(lambda b: m.checked_div(ONE, b))
        self.assertEqual(program.run(),
                         (m.Err(m.Error.DIVISION_BY_ZERO), F.UNDERFLOW | F.INEXACT))

    def test_exact_cancellation_can_have_nonzero_rounded_denominator(self):
        self.assertEqual(Q(1, 10) + Q(1, 5) - Q(3, 10), 0)
        denominator = m.convert(Q(1, 10)).bind(lambda x:
            m.convert(Q(1, 5)).bind(lambda y:
                m.binary("add", x, y).bind(lambda xy:
                    m.convert(Q(3, 10)).bind(lambda z: m.binary("sub", xy, z)))))
        self.assertEqual(denominator.run(), (r.F64(0x3C90000000000000), F.INEXACT))
        self.assertEqual(m.lift(denominator).bind(lambda d: m.checked_div(ONE, d)).run(),
                         (m.Ok(r.F64(0x4350000000000000)), F.INEXACT))

    def test_primal_guard_does_not_protect_a_rounded_denominator_square(self):
        b = r.from_fraction(Q(1, 10**200)).value
        self.assertFalse(b.is_zero)
        self.assertIsInstance(m.checked_div(ONE, b).run()[0], m.Ok)
        squared = m.lift(m.binary("mul", b, b)).bind(lambda bb: m.checked_div(ONE, bb))
        self.assertEqual(squared.run(),
                         (m.Err(m.Error.DIVISION_BY_ZERO), F.UNDERFLOW | F.INEXACT))

    def test_floating_guard_is_not_the_exact_meadow_unit_test(self):
        b = r.from_fraction(Q(49)).value
        reciprocal = r.div(ONE, b).value
        self.assertNotEqual(r.mul(b, reciprocal).value, ONE)
        self.assertIsInstance(m.checked_div(ONE, b).run()[0], m.Ok)

    def test_nan_infinity_and_subnormal_success_are_not_finiteness_promises(self):
        nan = r.F64(0xFFF0000000000007)
        self.assertEqual(m.checked_div(ONE, nan).run(),
                         (m.Ok(r.F64(nan.bits | r.QUIET)), F.INVALID))
        self.assertEqual(m.checked_div(r.infinity(), r.infinity()).run(),
                         (m.Ok(r.DEFAULT_NAN), F.INVALID))
        self.assertEqual(m.checked_div(r.F64(1), ONE).run(), (m.Ok(r.F64(1)), F.NONE))
        self.assertEqual(m.checked_div(ONE, r.F64(1)).run(),
                         (m.Ok(r.infinity()), F.OVERFLOW | F.INEXACT))


class OperationalTraceTests(unittest.TestCase):
    def test_consecutive_zero_divisions_have_same_denotation_but_different_first_sites(self):
        a = m.checked_div(ONE, r.zero(), site="A")
        b = m.checked_div(ONE, r.zero(True), site="B")
        ab, ba = a.bind(lambda _: b), b.bind(lambda _: a)
        self.assertTrue(m.same_observation(ab.run(), ba.run()))
        self.assertEqual(ab.audit().trace, (m.Event("A", "guard-fail"),))
        self.assertEqual(ba.audit().trace, (m.Event("B", "guard-fail"),))
        self.assertNotEqual(ab.audit().trace, ba.audit().trace)

    def test_associative_bracketings_preserve_internal_first_failure_trace(self):
        start = underflow("earlier")
        f = lambda _: m.checked_div(ONE, r.zero(), site="first-failure")
        g = lambda _: m.checked_div(ONE, r.zero(), site="second-failure")
        left, right = start.bind(f).bind(g), start.bind(lambda a: f(a).bind(g))
        self.assertEqual(left.audit(), right.audit())
        self.assertEqual(left.audit().trace,
                         (m.Event("earlier", "convert", F.UNDERFLOW | F.INEXACT),
                          m.Event("first-failure", "guard-fail")))

    def test_failure_and_flag_production_cannot_be_reordered(self):
        fail = m.checked_div(ONE, r.zero(), site="fail")
        before = underflow().bind(lambda _: fail)
        after = fail.bind(lambda _: underflow())
        self.assertFalse(m.same_observation(before.run(), after.run()))
        self.assertEqual(after.audit().trace, (m.Event("fail", "guard-fail"),))

    def test_operands_run_left_then_right_then_guard_and_failed_left_skips_right(self):
        left = underflow("left").bind(lambda _: m.SafeFloat.pure(ONE))
        right = m.lift(m.binary("div", r.zero(), r.zero(), site="right"))
        right = right.bind(lambda _: m.SafeFloat.pure(r.zero()))
        out = m.divide(left, right, site="outer").audit()
        self.assertEqual(out.flags, F.UNDERFLOW | F.INEXACT | F.INVALID)
        self.assertEqual(out.trace,
                         (m.Event("left", "convert", F.UNDERFLOW | F.INEXACT),
                          m.Event("right", "div", F.INVALID),
                          m.Event("outer", "guard-fail")))
        poisoned_right = m.SafeFloat(lambda cfg: bad_branch())
        failed_left = m.checked_div(ONE, r.zero(), site="left-failure")
        self.assertEqual(m.divide(failed_left, poisoned_right).audit(), failed_left.audit())

    def test_lift_preserves_primitive_trace_without_reexecution(self):
        program = m.convert(Q(1, 10), site="input").bind(
            lambda x: m.binary("add", x, ONE, site="sum"))
        lifted = m.lift(program)
        expected = program.audit().trace
        with patch.object(r, "add", wraps=r.add) as addition:
            observed = lifted.audit()
            self.assertEqual(addition.call_count, 1)
        self.assertEqual(observed.trace, expected)
        self.assertEqual([e.site for e in observed.trace], ["input", "sum"])


if __name__ == "__main__":
    unittest.main()
