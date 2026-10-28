"""Executable protocol regressions; these tests do not run Vastitas or Lean."""

import copy
from dataclasses import FrozenInstanceError, replace
from itertools import product
import unittest

from model import (ConsumedStateError, CountFrom, Event, Filter, Handle, Machine,
                   Map, MapOp, Predicate, StopReason, Take)


class IteratorPrefixTests(unittest.TestCase):
    def assert_consumed(self, machine, handle):
        before = machine.audit(handle.run)
        with self.assertRaises(ConsumedStateError):
            machine.step(handle)
        with self.assertRaises(ConsumedStateError):
            machine.dispose(handle)
        with self.assertRaises(ConsumedStateError):
            machine.observe(handle, 0)
        self.assertEqual(machine.audit(handle.run), before)

    def test_take_zero_stops_before_false_filter(self):
        machine = Machine()
        state = machine.start(Take(Filter(CountFrom(), Predicate.FALSE), 0))
        result = machine.step(state)
        self.assertEqual(result.event, Event.DONE)
        self.assertIsNone(result.state)
        audit = machine.audit(state.run)
        self.assertEqual(audit.source_pulls, 0)
        self.assertEqual(audit.drops, (1, 1, 1))
        machine.assert_invariants()
        self.assert_consumed(machine, state)

    def test_take_one_false_filter_32_skips_and_fresh_ownership(self):
        machine = Machine()
        state = machine.start(Take(Filter(CountFrom(), Predicate.FALSE), 1))
        old_states = []
        for generation in range(1, 33):
            old_states.append(state)
            result = machine.step(state)
            self.assertEqual(result.event, Event.SKIP)
            self.assertIsNone(result.value)
            self.assertIsNot(result.state, state)
            self.assertEqual(result.state.generation, generation)
            self.assert_consumed(machine, state)
            state = result.state
            audit = machine.audit(state.run)
            self.assertEqual(audit.take_remaining, (1,))
            self.assertEqual(audit.drops, (0, 0, 0))
            self.assertEqual(audit.yields, 0)
            machine.assert_invariants()
        self.assertEqual(machine.audit(state.run).source_pulls, 32)
        machine.dispose(state)
        self.assertEqual(machine.audit(state.run).drops, (1, 1, 1))
        for old in old_states + [state]:
            self.assert_consumed(machine, old)

    def test_budget_exhaustion_is_not_done_and_is_resumable(self):
        machine = Machine()
        initial = machine.start(Take(Filter(CountFrom(), Predicate.FALSE), 1))
        first = machine.observe(initial, 32)
        self.assertEqual(first.reason, StopReason.BUDGET_EXHAUSTED)
        self.assertEqual(first.trace, (Event.SKIP,) * 32)
        self.assertEqual(first.values, ())
        self.assertTrue(machine.audit(initial.run).live)
        self.assertEqual(machine.audit(initial.run).take_remaining, (1,))
        second = machine.observe(first.state, 7)
        self.assertEqual(second.reason, StopReason.BUDGET_EXHAUSTED)
        self.assertEqual(machine.audit(initial.run).skips, 39)
        self.assert_consumed(machine, first.state)
        machine.dispose(second.state)
        machine.assert_invariants()

    def test_zero_budget_does_not_step_or_dispose_even_take_zero(self):
        machine = Machine()
        state = machine.start(Take(CountFrom(), 0))
        before = machine.audit(state.run)
        observed = machine.observe(state, 0)
        self.assertEqual(observed.reason, StopReason.BUDGET_EXHAUSTED)
        self.assertIs(observed.state, state)
        self.assertEqual(machine.audit(state.run), before)
        self.assertEqual(machine.step(state).event, Event.DONE)

    def test_square_prefix_and_terminal_cleanup(self):
        machine = Machine()
        state = machine.start(Take(Map(CountFrom(), MapOp.SQUARE), 3))
        observed = machine.observe(state, 4)
        self.assertEqual(observed.values, (0, 1, 4))
        self.assertEqual(observed.trace, (Event.YIELD,) * 3 + (Event.DONE,))
        self.assertEqual(observed.reason, StopReason.DONE)
        self.assertIsNone(observed.state)
        self.assertEqual(machine.audit(state.run).source_pulls, 3)
        self.assertEqual(machine.audit(state.run).drops, (1, 1, 1))

    def test_last_yield_needs_next_done_pulse_or_explicit_disposal(self):
        machine = Machine()
        state = machine.start(Take(CountFrom(), 1))
        result = machine.observe(state, 1)
        self.assertEqual(result.reason, StopReason.BUDGET_EXHAUSTED)
        self.assertEqual(result.values, (0,))
        self.assertEqual(machine.audit(state.run).take_remaining, (0,))
        self.assertEqual(machine.audit(state.run).drops, (0, 0))
        machine.dispose(result.state)
        self.assertEqual(machine.audit(state.run).dones, 0)
        self.assertEqual(machine.audit(state.run).cancellations, 1)
        self.assertEqual(machine.audit(state.run).drops, (1, 1))

    def test_take_counts_yields_not_skips(self):
        machine = Machine()
        state = machine.start(Take(Filter(CountFrom(1), Predicate.EVEN), 2))
        trace, remaining, values = [], [], []
        for expected_remaining in (2, 1, 1, 0):
            result = machine.step(state)
            self.assert_consumed(machine, state)
            state = result.state
            trace.append(result.event)
            if result.value is not None:
                values.append(result.value)
            remaining.append(machine.audit(state.run).take_remaining[0])
            self.assertEqual(remaining[-1], expected_remaining)
        self.assertEqual(trace, [Event.SKIP, Event.YIELD, Event.SKIP, Event.YIELD])
        self.assertEqual(values, [2, 4])
        self.assertEqual(machine.step(state).event, Event.DONE)

    def test_skip_propagates_through_map_and_nested_take(self):
        machine = Machine()
        plan = Take(Map(Take(Filter(CountFrom(), Predicate.FALSE), 2), MapOp.ADD, 9), 1)
        state = machine.start(plan)
        observed = machine.observe(state, 10)
        self.assertEqual(observed.trace, (Event.SKIP,) * 10)
        self.assertEqual(machine.audit(state.run).take_remaining, (1, 2))
        machine.dispose(observed.state)
        self.assertEqual(machine.audit(state.run).drops, (1,) * 5)

    def test_finite_upstream_done_propagates_through_false_filter(self):
        machine = Machine()
        state = machine.start(Take(Filter(Take(CountFrom(), 3), Predicate.FALSE), 1))
        observed = machine.observe(state, 10)
        self.assertEqual(observed.reason, StopReason.DONE)
        self.assertEqual(observed.values, ())
        self.assertEqual(observed.trace, (Event.SKIP,) * 3 + (Event.DONE,))
        self.assertEqual(machine.audit(state.run).drops, (1,) * 4)

    def test_take_zero_under_wrappers_never_pulls_source(self):
        machine = Machine()
        state = machine.start(Map(Filter(Take(CountFrom(), 0), Predicate.TRUE), MapOp.SQUARE))
        self.assertEqual(machine.step(state).event, Event.DONE)
        self.assertEqual(machine.audit(state.run).source_pulls, 0)

    def test_abort_every_boundary_of_yielding_and_skipping_prefixes(self):
        plans = (CountFrom(), Map(CountFrom(), MapOp.SQUARE),
                 Take(Filter(CountFrom(), Predicate.FALSE), 1),
                 Take(Filter(CountFrom(), Predicate.EVEN), 3))
        for plan, budget in product(plans, range(9)):
            with self.subTest(plan=plan, budget=budget):
                machine = Machine()
                initial = machine.start(plan)
                observation = machine.observe(initial, budget)
                if observation.state is not None:
                    machine.dispose(observation.state)
                    self.assert_consumed(machine, observation.state)
                audit = machine.audit(initial.run)
                self.assertEqual(audit.drops, (1,) * len(audit.resources))
                self.assertEqual(audit.dones + audit.cancellations, 1)
                machine.assert_invariants()

    def test_replay_and_interleaving_have_independent_one_shot_states(self):
        plan = Take(Map(CountFrom(2), MapOp.ADD, 5), 2)
        machine = Machine()
        a, b = machine.start(plan), machine.start(plan)
        self.assertTrue(set(machine.audit(a.run).resources).isdisjoint(
            machine.audit(b.run).resources))
        first = machine.step(a)
        self.assertEqual(first.value, 7)
        self.assertEqual(machine.observe(b, 3).values, (7, 8))
        self.assertEqual(machine.observe(first.state, 2).values, (8,))
        self.assertEqual(machine.observe(machine.start(plan), 3).values, (7, 8))
        with self.assertRaises(FrozenInstanceError):
            plan.limit = 7
        machine.assert_invariants()

    def test_explicit_scalar_environment_and_remaining_operation_tags(self):
        environment = 3
        plan = Take(Map(Filter(CountFrom(), Predicate.AT_LEAST, environment),
                        MapOp.IDENTITY), 2)
        environment = 99  # Not a captured cell in the immutable plan.
        machine = Machine()
        state = machine.start(plan)
        result = machine.observe(state, 6)
        self.assertEqual(result.reason, StopReason.DONE)
        self.assertEqual(result.values, (3, 4))
        self.assertEqual(result.trace, (Event.SKIP,) * 3
                         + (Event.YIELD,) * 2 + (Event.DONE,))
        machine.assert_invariants()

    def test_copied_forged_and_foreign_handles_have_no_authority(self):
        machine, foreign = Machine(), Machine()
        state = machine.start(CountFrom())
        alien = foreign.start(CountFrom())
        for fake in (copy.copy(state), copy.deepcopy(state), replace(state),
                     Handle(state.run, state.generation), alien, None):
            with self.subTest(fake=fake):
                with self.assertRaises(ConsumedStateError):
                    machine.step(fake)
                with self.assertRaises(ConsumedStateError):
                    machine.dispose(fake)
        next_state, next_alien = machine.step(state), foreign.step(alien)
        self.assertEqual(next_state.value, 0)
        self.assertEqual(next_alien.value, 0)
        machine.dispose(next_state.state)
        foreign.dispose(next_alien.state)

    def test_stale_handles_stay_rejected_after_further_steps(self):
        machine = Machine()
        state = machine.start(CountFrom())
        stale = []
        for _ in range(8):
            stale.append(state)
            state = machine.step(state).state
            for handle in stale:
                self.assert_consumed(machine, handle)
        machine.dispose(state)
        for handle in stale:
            self.assert_consumed(machine, handle)

    def test_reject_impure_unsupported_and_non_nat_descriptions(self):
        machine = Machine()
        state = machine.start(CountFrom())
        bad_plans = (CountFrom(-1), CountFrom(True), CountFrom(0, -1),
                     Take(CountFrom(), -1), Map(CountFrom(), lambda x: x),
                     Map(CountFrom(), MapOp.ADD, []),
                     Filter(CountFrom(), lambda x: True),
                     Filter(CountFrom(), Predicate.AT_LEAST, -2),
                     state)
        for plan in bad_plans:
            with self.subTest(plan=plan), self.assertRaises(ValueError):
                machine.start(plan)
        machine.dispose(state)

    def test_invalid_observation_budget_does_not_consume_state(self):
        machine = Machine()
        state = machine.start(CountFrom())
        for budget in (-1, True, 1.5):
            with self.assertRaises(ValueError):
                machine.observe(state, budget)
        next_state = machine.step(state)
        self.assertEqual(next_state.value, 0)
        machine.dispose(next_state.state)

    def test_1200_bounded_compositions_against_eager_list_oracle(self):
        # Independent finite-list oracle; no call to _pulse or cursor helpers.
        # 3 sources * (1 + 7 + 49 + 343) operator sequences = 1200 cases.
        for start, stride in ((0, 1), (2, 3), (4, 0)):
            for depth in range(4):
                for operations in product(range(7), repeat=depth):
                    plan = Take(CountFrom(start, stride), 8)
                    expected = [start + stride * i for i in range(8)]
                    for op in operations:
                        if op == 0:
                            plan, expected = Map(plan, MapOp.SQUARE), [x*x for x in expected]
                        elif op == 1:
                            plan, expected = Map(plan, MapOp.ADD, 3), [x+3 for x in expected]
                        elif op == 2:
                            plan, expected = Filter(plan, Predicate.FALSE), []
                        elif op == 3:
                            plan, expected = Filter(plan, Predicate.EVEN), [x for x in expected if x % 2 == 0]
                        else:
                            limit = (0, 1, 3)[op - 4]
                            plan, expected = Take(plan, limit), expected[:limit]
                    with self.subTest(start=start, stride=stride, operations=operations):
                        machine = Machine()
                        state = machine.start(plan)
                        result = machine.observe(state, 9)
                        self.assertEqual(result.reason, StopReason.DONE)
                        self.assertEqual(result.values, tuple(expected))
                        self.assertLessEqual(machine.audit(state.run).source_pulls, 8)
                        self.assert_consumed(machine, state)
                        machine.assert_invariants()


if __name__ == "__main__":
    unittest.main()
