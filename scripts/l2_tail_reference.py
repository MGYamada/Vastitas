"""Exact, deliberately incomplete tail-certificate reference for #208/#209.

Only two closed generator definitions and two algebraic proof rules are admitted.
Acceptance NEVER evaluates sequence terms, finite sums, or numerical limits.
Fractions compute certificate data; the intended denotation is in exact real l2.
This Python model is not a Lean proof or the compiler's Indexed.Core acceptance.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from fractions import Fraction


RULESET = "l2-tail-reference-v1"
GEOMETRIC_RULE = "geometric-square-telescope-v1"
RECIPROCAL_RULE = "reciprocal-square-comparison-v1"


@dataclass(frozen=True)
class Geometric:
    """Closed syntax denoting a * r**n, starting at n = 0 (also 0**0 = 1)."""

    amplitude: Fraction
    ratio: Fraction


@dataclass(frozen=True)
class Reciprocal:
    """Closed syntax denoting a / (n + 1), starting at n = 0."""

    amplitude: Fraction


@dataclass(frozen=True)
class PrefixThenConstant:
    """Evaluable adversarial fixture, with NO supported certificate rule."""

    prefix: tuple[Fraction, ...]
    constant: Fraction


@dataclass(frozen=True)
class Opaque:
    """An unresolved definition, not executable code or proof authority."""

    description: str


Body = Geometric | Reciprocal | PrefixThenConstant | Opaque


@dataclass(frozen=True)
class ReferenceCore:
    """Complete immutable reference term; NOT Vastitas's compiler Core."""

    definition_id: str
    definition_revision: str
    body: Body


@dataclass(frozen=True)
class Environment:
    """Fixture snapshot only; production authority/authenticity is not modeled."""

    scalar_profile: str = "exact-real"
    dependencies: tuple[tuple[str, str], ...] = ()


@dataclass(frozen=True)
class Binding:
    core: ReferenceCore
    environment: Environment
    ruleset: str = RULESET


@dataclass(frozen=True)
class GeometricBound:
    """B(N) = coefficient * ratio_squared**N."""

    coefficient: Fraction
    ratio_squared: Fraction


@dataclass(frozen=True)
class ReciprocalBound:
    """B(0) = 2 * coefficient; B(N) = coefficient / N for N >= 1."""

    coefficient: Fraction


Bound = GeometricBound | ReciprocalBound


@dataclass(frozen=True)
class Certificate:
    binding: Binding
    rule: str
    bound: Bound


class Outcome(Enum):
    ACCEPTED_REFERENCE = "accepted_reference"
    INVALID_BOUND = "invalid_bound"
    EVIDENCE_MISMATCH = "evidence_mismatch"
    UNSUPPORTED = "unsupported"
    MALFORMED = "malformed"


@dataclass(frozen=True)
class ReferenceAcceptance:
    binding: Binding
    certificate: Certificate


@dataclass(frozen=True)
class Result:
    outcome: Outcome
    reason: str
    accepted: ReferenceAcceptance | None = None


def _text(value: object) -> bool:
    return type(value) is str and bool(value)


def _valid_core(core: object) -> bool:
    if type(core) is not ReferenceCore:
        return False
    if not _text(core.definition_id) or not _text(core.definition_revision):
        return False
    body = core.body
    if type(body) is Geometric:
        values = (body.amplitude, body.ratio)
    elif type(body) is Reciprocal:
        values = (body.amplitude,)
    elif type(body) is PrefixThenConstant:
        if type(body.prefix) is not tuple:
            return False
        values = (*body.prefix, body.constant)
    elif type(body) is Opaque:
        return _text(body.description)
    else:
        return False
    # Do not silently treat floats, bools, or equality-overriding subclasses
    # as exact rational input. Callers explicitly construct Fraction values.
    return all(type(value) is Fraction for value in values)


def _valid_environment(env: object) -> bool:
    if type(env) is not Environment or not _text(env.scalar_profile):
        return False
    if type(env.dependencies) is not tuple:
        return False
    if not all(type(dep) is tuple and len(dep) == 2 and all(map(_text, dep))
               for dep in env.dependencies):
        return False
    names = [name for name, _ in env.dependencies]
    return len(names) == len(set(names))


def _valid_binding(binding: object) -> bool:
    return (type(binding) is Binding and _valid_core(binding.core)
            and _valid_environment(binding.environment) and _text(binding.ruleset))


def _valid_bound(bound: object) -> bool:
    if type(bound) is GeometricBound:
        return (type(bound.coefficient) is Fraction
                and type(bound.ratio_squared) is Fraction)
    return type(bound) is ReciprocalBound and type(bound.coefficient) is Fraction


def check_certificate(core: ReferenceCore, env: Environment,
                      certificate: Certificate | None) -> Result:
    """Replay a closed proof schema, with no sequence sampling or callbacks.

    INVALID_BOUND rejects this certificate, not the sequence's l2 membership.
    UNSUPPORTED is an unresolved proof obligation, never a divergence verdict.
    """
    if not _valid_core(core) or not _valid_environment(env):
        return Result(Outcome.MALFORMED, "invalid Core/environment or non-rational data")
    if env.scalar_profile != "exact-real":
        return Result(Outcome.UNSUPPORTED, "only the exact real semantic profile is supported")
    if certificate is None:
        return Result(Outcome.UNSUPPORTED, "missing summability evidence")
    if (type(certificate) is not Certificate or not _valid_binding(certificate.binding)
            or not _text(certificate.rule) or not _valid_bound(certificate.bound)):
        return Result(Outcome.MALFORMED, "invalid certificate syntax or non-rational data")
    binding = Binding(core, env)
    if certificate.binding != binding:
        return Result(Outcome.EVIDENCE_MISMATCH,
                      "different definition, parameters, Core, environment, or ruleset")
    if certificate.rule not in (GEOMETRIC_RULE, RECIPROCAL_RULE):
        return Result(Outcome.UNSUPPORTED, "unknown proof rule; no evaluation fallback")

    body, bound = core.body, certificate.bound
    if certificate.rule == GEOMETRIC_RULE:
        if type(body) is not Geometric or type(bound) is not GeometricBound:
            return Result(Outcome.EVIDENCE_MISMATCH, "rule does not match the actual definition/bound")
        q = body.ratio * body.ratio
        if bound.ratio_squared != q:
            return Result(Outcome.EVIDENCE_MISMATCH, "tail ratio is not the actual generator ratio squared")
        if not q < 1:
            return Result(Outcome.UNSUPPORTED, "geometric decay premise |r| < 1 is not available")
        if bound.coefficient < 0 or bound.coefficient * (1 - q) < body.amplitude**2:
            return Result(Outcome.INVALID_BOUND, "requires c >= 0 and c*(1-r^2) >= a^2")
    else:
        if type(body) is not Reciprocal or type(bound) is not ReciprocalBound:
            return Result(Outcome.EVIDENCE_MISMATCH, "rule does not match the actual definition/bound")
        if bound.coefficient < body.amplitude**2:
            return Result(Outcome.INVALID_BOUND, "requires c >= a^2 (and hence c >= 0)")

    # Return the exact argument Core/environment, not a certificate's substitute.
    return Result(Outcome.ACCEPTED_REFERENCE, "closed algebraic rule conditions checked",
                  ReferenceAcceptance(binding, certificate))


def propose_certificate(core: ReferenceCore, env: Environment) -> Certificate | None:
    """Untrusted convenience producer. Only check_certificate decides acceptance."""
    if not _valid_core(core) or not _valid_environment(env):
        raise ValueError("invalid reference input")
    body = core.body
    if type(body) is Geometric and body.ratio**2 < 1:
        q = body.ratio**2
        return Certificate(Binding(core, env), GEOMETRIC_RULE,
                           GeometricBound(body.amplitude**2 / (1 - q), q))
    if type(body) is Reciprocal:
        return Certificate(Binding(core, env), RECIPROCAL_RULE,
                           ReciprocalBound(body.amplitude**2))
    return None


def audit_acceptance(core: ReferenceCore, env: Environment,
                     accepted: ReferenceAcceptance) -> Result:
    """Consumers replay the checker; a public Python dataclass is not authority."""
    if type(accepted) is not ReferenceAcceptance or not _valid_binding(accepted.binding):
        return Result(Outcome.MALFORMED, "not a reference acceptance record")
    replay = check_certificate(core, env, accepted.certificate)
    if replay.outcome is not Outcome.ACCEPTED_REFERENCE:
        return replay
    if replay.accepted != accepted:
        return Result(Outcome.EVIDENCE_MISMATCH, "acceptance record changed its returned Core/environment")
    return replay


def _natural(n: int) -> None:
    if type(n) is not int or n < 0:
        raise ValueError("index must be a nonnegative integer")


def term(core: ReferenceCore, n: int) -> Fraction:
    """Finite observation only. Never called by check_certificate."""
    _natural(n)
    if not _valid_core(core):
        raise ValueError("invalid reference Core")
    body = core.body
    if type(body) is Geometric:
        return body.amplitude * body.ratio**n
    if type(body) is Reciprocal:
        return body.amplitude / (n + 1)
    if type(body) is PrefixThenConstant:
        return body.prefix[n] if n < len(body.prefix) else body.constant
    raise ValueError("opaque definition has no reference evaluator")


def tail_value(bound: Bound, n: int) -> Fraction:
    """Evaluate a candidate bound; this does not certify it."""
    _natural(n)
    if not _valid_bound(bound):
        raise ValueError("invalid bound syntax")
    if type(bound) is GeometricBound:
        return bound.coefficient * bound.ratio_squared**n
    return 2 * bound.coefficient if n == 0 else bound.coefficient / n


def finite_tail_square_sum(core: ReferenceCore, start: int, stop: int) -> Fraction:
    """Observation on [start, stop); never evidence for a universal statement."""
    _natural(start)
    _natural(stop)
    if stop < start or not _valid_core(core):
        raise ValueError("invalid interval/Core")
    return sum((term(core, n)**2 for n in range(start, stop)), Fraction(0))
