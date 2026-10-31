"""Dedicated Float/SafeFloat reference for #318; no general transformer API.

run returns ONLY (value/result, symbolic flags). audit returns an additional
internal ordered trace from the SAME evaluator. The trace is diagnostic evidence,
not part of the minimal denotation or a claim about accepted Core/native code.
Only deterministic effect-closed callbacks are admitted by the reference laws;
Python does not certify arbitrary callbacks, captures, or ownership.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from typing import Callable, Generic, TypeVar

import float_reference as ref
from float_reference import F64, Flags


A = TypeVar("A")
B = TypeVar("B")


@dataclass(frozen=True)
class Config:
    """Unit configuration: the named reference/execution profile is fully fixed."""


CONFIG = Config()
EXECUTION_PROFILE = ref.PROFILE + "/left-to-right-short-circuit-v1"


class Error(Enum):
    DIVISION_BY_ZERO = "DivisionByZero"


@dataclass(frozen=True)
class Ok(Generic[A]):
    value: A


@dataclass(frozen=True)
class Err:
    error: Error


@dataclass(frozen=True)
class Event:
    site: str
    operation: str
    local_flags: Flags = Flags.NONE


@dataclass(frozen=True)
class _Run(Generic[A]):
    value: A
    flags: Flags = Flags.NONE
    trace: tuple[Event, ...] = ()


@dataclass(frozen=True)
class Float(Generic[A]):
    _evaluate: Callable[[Config], _Run[A]]

    def audit(self, cfg=CONFIG):
        if type(cfg) is not Config:
            raise TypeError("only the fixed Unit configuration is supported")
        return self._evaluate(cfg)

    def run(self, cfg=CONFIG):
        out = self.audit(cfg)
        return out.value, out.flags

    @staticmethod
    def pure(value):
        return Float(lambda cfg: _Run(value))

    def bind(self, continuation: Callable[[A], Float[B]]) -> Float[B]:
        def evaluate(cfg):
            first = self.audit(cfg)
            second = continuation(first.value).audit(cfg)
            return _Run(second.value, first.flags | second.flags,
                        first.trace + second.trace)
        return Float(evaluate)


@dataclass(frozen=True)
class SafeFloat(Generic[A]):
    _evaluate: Callable[[Config], _Run[Ok[A] | Err]]

    def audit(self, cfg=CONFIG):
        if type(cfg) is not Config:
            raise TypeError("only the fixed Unit configuration is supported")
        return self._evaluate(cfg)

    def run(self, cfg=CONFIG):
        out = self.audit(cfg)
        return out.value, out.flags

    @staticmethod
    def pure(value):
        return SafeFloat(lambda cfg: _Run(Ok(value)))

    @staticmethod
    def fail(error=Error.DIVISION_BY_ZERO):
        return SafeFloat(lambda cfg: _Run(Err(error)))

    def bind(self, continuation: Callable[[A], SafeFloat[B]]) -> SafeFloat[B]:
        def evaluate(cfg):
            first = self.audit(cfg)
            if isinstance(first.value, Err):
                return first
            second = continuation(first.value.value).audit(cfg)
            return _Run(second.value, first.flags | second.flags,
                        first.trace + second.trace)
        return SafeFloat(evaluate)


def lift(program: Float[A]) -> SafeFloat[A]:
    def evaluate(cfg):
        out = program.audit(cfg)
        return _Run(Ok(out.value), out.flags, out.trace)
    return SafeFloat(evaluate)


def _primitive(site, name, operation):
    def evaluate(cfg):
        out = operation()
        return _Run(out.value, out.flags, (Event(site, name, out.flags),))
    return Float(evaluate)


def convert(value, *, site="convert"):
    return _primitive(site, "convert", lambda: ref.from_fraction(value))


def binary(operation, a: F64, b: F64, *, site="binary"):
    operations = {"add": ref.add, "sub": ref.sub, "mul": ref.mul, "div": ref.div}
    if operation not in operations:
        raise ValueError("unsupported reference primitive")
    return _primitive(site, operation, lambda: operations[operation](a, b))


def checked_div(a: F64, b: F64, *, site="checked_div") -> SafeFloat[F64]:
    """Guard evaluated bits BEFORE raw division; failure fabricates no IEEE flag.

    With this profile's gradual underflow and disabled DAZ, effective zero is
    exactly either signed zero. Success is not ideal-Field nonzero evidence.
    """
    def evaluate(cfg):
        if b.is_zero:
            return _Run(Err(Error.DIVISION_BY_ZERO), trace=(Event(site, "guard-fail"),))
        out = ref.div(a, b)
        return _Run(Ok(out.value), out.flags,
                    (Event(site, "guard-pass"), Event(site, "div", out.flags)))
    return SafeFloat(evaluate)


def divide(left: SafeFloat[F64], right: SafeFloat[F64], *, site="checked_div"):
    """Explicit left-then-right operand evaluation, then operation-effective guard."""
    return left.bind(lambda a: right.bind(lambda b: checked_div(a, b, site=site)))


def choose(condition: SafeFloat[bool], when_true, when_false):
    """Branches are thunks; construct and evaluate only the selected branch."""
    def branch(value):
        if type(value) is not bool:
            raise TypeError("branch condition must be a represented bool")
        return when_true() if value else when_false()
    return condition.bind(branch)


def representation_key(value):
    """Explicit equality for this test carrier; NEVER fall back to IEEE ==.

    Supported A: F64, bool, int, None, tuples and nested Result. Native floats
    (including Python NaNs) and arbitrary objects are outside this equality.
    """
    if type(value) is F64:
        return ("F64", value.bits)
    if type(value) is Ok:
        return ("Ok", representation_key(value.value))
    if type(value) is Err:
        return ("Err", value.error)
    if type(value) is tuple:
        return ("tuple", tuple(representation_key(x) for x in value))
    if value is None or type(value) in (bool, int):
        return (type(value), value)
    raise TypeError("value outside the reference equality carrier")


def same_observation(left, right):
    """Compare run outputs. No failing-site identity is smuggled into equality."""
    return (representation_key(left[0]) == representation_key(right[0])
            and left[1] == right[1])
