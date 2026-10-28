"""Reproduce the three motivating observations without an unbounded next()."""

import json

from model import CountFrom, Filter, Machine, Map, MapOp, Predicate, Take


def run_case(name, plan, budget):
    machine = Machine()
    initial = machine.start(plan)
    observation = machine.observe(initial, budget)
    before_cleanup = machine.audit(initial.run)
    if observation.state is not None:
        machine.dispose(observation.state)
    machine.assert_invariants()
    return {
        "case": name,
        "budget": budget,
        "reason": observation.reason.value,
        "trace": [event.value for event in observation.trace],
        "values": observation.values,
        "source_pulls": before_cleanup.source_pulls,
        "remaining_before_cleanup": before_cleanup.take_remaining,
        "live_before_cleanup": before_cleanup.live,
        "drops_before_cleanup": before_cleanup.drops,
        "drops_after_cleanup": machine.audit(initial.run).drops,
        "explicit_cleanup": observation.state is not None,
    }


if __name__ == "__main__":
    print(json.dumps([
        run_case("take(0, filter(false, countfrom(0)))",
                 Take(Filter(CountFrom(), Predicate.FALSE), 0), 32),
        run_case("take(1, filter(false, countfrom(0)))",
                 Take(Filter(CountFrom(), Predicate.FALSE), 1), 32),
        run_case("take(3, map(square, countfrom(0)))",
                 Take(Map(CountFrom(), MapOp.SQUARE), 3), 4),
    ], indent=2))
