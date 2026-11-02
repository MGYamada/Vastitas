"""Finite-pulse reference experiment for #190/#191, NOT Vastitas execution.

Nat scalars, closed pure operation tags, and one affine owner per traversal.
Resource IDs and releases are instrumentation, not host-memory semantics.
"""
if not __debug__:
    raise RuntimeError("verification requires Python assertions; remove -O / PYTHONOPTIMIZE")

from dataclasses import dataclass, replace
from enum import Enum


class MapOp(Enum):
    IDENTITY = "identity"
    SQUARE = "square"
    ADD = "add"


class Predicate(Enum):
    FALSE = "false"
    TRUE = "true"
    EVEN = "even"
    AT_LEAST = "at_least"


@dataclass(frozen=True)
class CountFrom:
    start: int = 0
    stride: int = 1


@dataclass(frozen=True)
class Map:
    source: "Plan"
    op: MapOp
    environment: int = 0


@dataclass(frozen=True)
class Filter:
    source: "Plan"
    predicate: Predicate
    environment: int = 0


@dataclass(frozen=True)
class Take:
    source: "Plan"
    limit: int


Plan = CountFrom | Map | Filter | Take


def _nat(value: int) -> None:
    if type(value) is not int or value < 0:
        raise ValueError("this experiment accepts Nat scalars only")


def validate(plan: Plan) -> None:
    """No host callbacks, mutable captures, or iterator handles in a plan."""
    if type(plan) is CountFrom:
        _nat(plan.start)
        _nat(plan.stride)
        return
    if type(plan) is Map:
        if type(plan.op) is not MapOp:
            raise ValueError("unknown map operation")
        _nat(plan.environment)
    elif type(plan) is Filter:
        if type(plan.predicate) is not Predicate:
            raise ValueError("unknown predicate")
        _nat(plan.environment)
    elif type(plan) is Take:
        _nat(plan.limit)
    else:
        raise ValueError("not a pure supported plan")
    validate(plan.source)


@dataclass(frozen=True)
class _Cursor:
    plan: Plan
    position: int  # next CountFrom value / remaining Take demand / zero
    source: "_Cursor | None" = None


def _initial(plan: Plan) -> _Cursor:
    if type(plan) is CountFrom:
        return _Cursor(plan, plan.start)
    return _Cursor(plan, plan.limit if type(plan) is Take else 0,
                   _initial(plan.source))


def _nodes(cursor: _Cursor):
    while cursor is not None:
        yield cursor
        cursor = cursor.source


class Event(Enum):
    YIELD = "Yield"
    SKIP = "Skip"
    DONE = "Done"


@dataclass(frozen=True)
class _Pulse:
    event: Event
    value: int | None
    cursor: _Cursor | None
    source_pulls: int


def _pulse(cursor: _Cursor) -> _Pulse:
    """At most ONE upstream pulse per wrapper; never search for a next yield."""
    plan = cursor.plan
    if type(plan) is CountFrom:
        return _Pulse(Event.YIELD, cursor.position,
                      replace(cursor, position=cursor.position + plan.stride), 1)
    # Demand is checked BEFORE touching the upstream cursor.
    if type(plan) is Take and cursor.position == 0:
        return _Pulse(Event.DONE, None, None, 0)
    upstream = _pulse(cursor.source)
    if upstream.event is Event.DONE:
        return upstream
    following = replace(cursor, source=upstream.cursor)
    if upstream.event is Event.SKIP:
        return replace(upstream, cursor=following)
    value = upstream.value
    if type(plan) is Map:
        if plan.op is MapOp.SQUARE:
            value = value * value
        elif plan.op is MapOp.ADD:
            value += plan.environment
    elif type(plan) is Filter:
        keep = (plan.predicate is Predicate.TRUE
                or (plan.predicate is Predicate.EVEN and value % 2 == 0)
                or (plan.predicate is Predicate.AT_LEAST
                    and value >= plan.environment))
        if not keep:
            return _Pulse(Event.SKIP, None, following, upstream.source_pulls)
    else:  # Take consumes demand only on Yield.
        following = replace(following, position=cursor.position - 1)
    return _Pulse(Event.YIELD, value, following, upstream.source_pulls)


@dataclass(frozen=True, eq=False)
class Handle:
    """An opaque issued object; copying its fields does not copy authority."""
    run: int
    generation: int


class ConsumedStateError(RuntimeError):
    pass


@dataclass(frozen=True)
class Transition:
    event: Event
    value: int | None
    state: Handle | None


class StopReason(Enum):
    DONE = "Done"
    BUDGET_EXHAUSTED = "BudgetExhausted"


@dataclass(frozen=True)
class Observation:
    reason: StopReason
    values: tuple[int, ...]
    trace: tuple[Event, ...]
    state: Handle | None


@dataclass
class _Run:
    cursor: _Cursor | None
    handle: Handle | None
    resources: tuple[tuple[int, int], ...]
    drops: tuple[int, ...]
    generation: int = 0
    yields: int = 0
    skips: int = 0
    dones: int = 0
    cancellations: int = 0
    source_pulls: int = 0


@dataclass(frozen=True)
class Audit:
    live: bool
    generation: int
    yields: int
    skips: int
    dones: int
    cancellations: int
    source_pulls: int
    resources: tuple[tuple[int, int], ...]
    drops: tuple[int, ...]
    take_remaining: tuple[int, ...]


class Machine:
    """Sequential trusted host harness. Not a sandbox against Python reflection.

    One lease owns the whole cursor tree. All frame resources are retained until
    Done or explicit dispose, when each is released once. No element resources,
    loans, real allocators, concurrency, or exception unwinding are modeled.
    """

    def __init__(self):
        self._runs: dict[int, _Run] = {}

    def start(self, plan: Plan) -> Handle:
        validate(plan)
        cursor = _initial(plan)
        run_id = len(self._runs)
        handle = Handle(run_id, 0)
        resources = tuple((run_id, i) for i, _ in enumerate(_nodes(cursor)))
        self._runs[run_id] = _Run(cursor, handle, resources,
                                  (0,) * len(resources))
        return handle

    def _owned(self, handle: Handle) -> _Run:
        run = self._runs.get(handle.run) if type(handle) is Handle else None
        if run is None or run.handle is not handle:
            raise ConsumedStateError("state is consumed, foreign, or not issued")
        return run

    @staticmethod
    def _release(run: _Run) -> None:
        # Increment, do not overwrite with 1: a double release must be observable.
        run.drops = tuple(count + 1 for count in run.drops)
        run.handle = None
        run.cursor = None

    def step(self, handle: Handle) -> Transition:
        run = self._owned(handle)
        result = _pulse(run.cursor)
        # Commit one atomic abstract transition, even if it produced no value.
        run.generation += 1
        run.source_pulls += result.source_pulls
        if result.event is Event.DONE:
            run.dones += 1
            self._release(run)
        else:
            run.yields += int(result.event is Event.YIELD)
            run.skips += int(result.event is Event.SKIP)
            run.cursor = result.cursor
            run.handle = Handle(handle.run, run.generation)
        return Transition(result.event, result.value, run.handle)

    def dispose(self, handle: Handle) -> None:
        """Explicit early termination consumes the current lease, exactly once."""
        run = self._owned(handle)
        run.generation += 1
        run.cancellations += 1
        self._release(run)

    def observe(self, handle: Handle, budget: int) -> Observation:
        """Fuel limits ALL pulses, including Skip and the final Done pulse.

        Budget exhaustion neither advances again nor disposes the live state.
        Its caller must resume or dispose the returned handle.
        """
        _nat(budget)
        self._owned(handle)
        values, trace = [], []
        for _ in range(budget):
            transition = self.step(handle)
            trace.append(transition.event)
            self.assert_invariants()
            if transition.event is Event.YIELD:
                values.append(transition.value)
            if transition.event is Event.DONE:
                return Observation(StopReason.DONE, tuple(values), tuple(trace), None)
            handle = transition.state
        return Observation(StopReason.BUDGET_EXHAUSTED, tuple(values), tuple(trace), handle)

    def audit(self, run_id: int) -> Audit:
        run = self._runs[run_id]
        remaining = tuple(node.position for node in _nodes(run.cursor)
                          if type(node.plan) is Take)
        return Audit(run.handle is not None, run.generation, run.yields, run.skips,
                     run.dones, run.cancellations, run.source_pulls,
                     run.resources, run.drops, remaining)

    def assert_invariants(self) -> None:
        """Boundary-state monitor, NOT a checker acceptance or memory proof."""
        for run_id, run in self._runs.items():
            assert len(set(run.resources)) == len(run.resources)
            assert all(owner == run_id for owner, _ in run.resources)
            assert len(run.drops) == len(run.resources)
            assert run.generation == (run.yields + run.skips + run.dones
                                      + run.cancellations)
            assert run.dones + run.cancellations <= 1
            if run.handle is not None:
                assert run.handle.run == run_id
                assert run.handle.generation == run.generation
                assert run.cursor is not None
                assert len(tuple(_nodes(run.cursor))) == len(run.resources)
                assert all(node.position >= 0 for node in _nodes(run.cursor))
                assert run.dones + run.cancellations == 0
                assert run.drops == (0,) * len(run.resources)
            else:
                assert run.cursor is None
                assert run.dones + run.cancellations == 1
                assert run.drops == (1,) * len(run.resources)
