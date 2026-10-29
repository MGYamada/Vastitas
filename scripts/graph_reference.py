"""Exact, deliberately incomplete crossing reference for Vastitas issue #201.

Python standard library only. This is NOT the Vastitas Graph Checker, a Lean
certificate verifier, or a braid/morphism equality decision procedure.

Two separate paths:
  evaluate: observe a graded rational-line representation;
  check_rewrite/check_trace: replay a whitelist of local structural rules.
The second path never calls the first and never compares scalar observations.
"""

from __future__ import annotations

from dataclasses import dataclass, replace
from enum import Enum, IntEnum
from fractions import Fraction
from types import MappingProxyType
from typing import TypeAlias


class Rejected(ValueError):
    """Malformed input, mismatched evidence, or unsupported rewrite."""


class Capability(IntEnum):
    MONOIDAL = 1
    BRAIDED = 2
    SYMMETRIC = 3


class Direction(Enum):
    POSITIVE = 1
    NEGATIVE = -1


class Rule(Enum):
    INVERSE = "inverse cancellation"
    BRAID = "same-sign adjacent braid relation"
    FAR = "distant crossings commute"
    SYMMETRIC = "same-sign double crossing cancellation"


# These are fixture identifiers, NOT actual resolver IDs from Vastitas.
REFERENCE_TENSOR_ID = "fixture-only:std::monoidal::tensor"


@dataclass(frozen=True)
class ProfileKey:
    canonical_tensor_id: str
    selected_method_id: str
    implementation_revision: str
    profile_id: str
    category_id: str
    coefficient_id: str
    tensor_model_id: str
    unit_id: str
    associator_id: str
    braiding_id: str


@dataclass(frozen=True)
class ReferenceProfile:
    key: ProfileKey
    capability: Capability
    q: Fraction | None


def _profile(name: str, capability: Capability, q: Fraction | None) -> ReferenceProfile:
    return ReferenceProfile(
        ProfileKey(
            REFERENCE_TENSOR_ID, f"fixture-method:{name}", "fixture-impl:1",
            f"fixture-profile:{name}", "Z-graded-rational-lines", "QQ",
            "graded-tensor", "degree-zero-line", "chosen-line-associator",
            "none" if q is None else f"chosen-braiding:{name}",
        ),
        capability, q,
    )


# Closed fixture authority. Matching an entry is NOT a mathematical proof.
# In particular, q=-1 with only BRAIDED evidence never acquires SYMMETRIC
# authority from its evaluated scalars.
FIXTURES = MappingProxyType({
    "monoidal": _profile("monoidal", Capability.MONOIDAL, None),
    "braided_two": _profile("braided-two", Capability.BRAIDED, Fraction(2)),
    "braided_two_other": _profile("braided-two-other", Capability.BRAIDED, Fraction(2)),
    "braided_sign": _profile("braided-sign", Capability.BRAIDED, Fraction(-1)),
    "symmetric_sign": _profile("symmetric-sign", Capability.SYMMETRIC, Fraction(-1)),
    "symmetric_one": _profile("symmetric-one", Capability.SYMMETRIC, Fraction(1)),
})
_BY_KEY = MappingProxyType({profile.key: profile for profile in FIXTURES.values()})


@dataclass(frozen=True)
class FixtureEvidence:
    """Fixture provenance only; never serialize this as a Lean proof."""

    profile: ReferenceProfile
    rule: Rule
    token: str


def _required(rule: Rule) -> Capability:
    if type(rule) is not Rule:
        raise Rejected("unknown rule; there is no permutation/evaluation fallback")
    return Capability.SYMMETRIC if rule is Rule.SYMMETRIC else Capability.BRAIDED


_EVIDENCE = MappingProxyType({
    (profile.key, rule): FixtureEvidence(
        profile, rule, f"fixture-only:{profile.key.profile_id}:{rule.name}:v1"
    )
    for profile in FIXTURES.values()
    for rule in Rule
    if profile.capability >= _required(rule)
})


def fixture_profile(key: ProfileKey) -> ReferenceProfile:
    if type(key) is not ProfileKey:
        raise Rejected("missing full profile identity")
    if any(type(value) is not str or not value for value in vars(key).values()):
        raise Rejected("invalid profile identity fields")
    if key.canonical_tensor_id != REFERENCE_TENSOR_ID:
        raise Rejected("tensor spelling does not grant canonical identity")
    profile = _BY_KEY.get(key)
    if profile is None:
        raise Rejected("unknown or stale method/profile; reference fixtures only")
    return profile


def evidence_for(key: ProfileKey, rule: Rule) -> FixtureEvidence:
    profile = fixture_profile(key)
    if profile.capability < _required(rule):
        raise Rejected("profile lacks the rule's required capability")
    return _EVIDENCE[key, rule]


def _check_evidence(key: ProfileKey, rule: Rule, evidence: FixtureEvidence) -> None:
    expected = evidence_for(key, rule)
    if (
        type(evidence) is not FixtureEvidence
        or type(evidence.profile) is not ReferenceProfile
        or type(evidence.profile.capability) is not Capability
        or (evidence.profile.q is not None and type(evidence.profile.q) is not Fraction)
        or evidence != expected
    ):
        raise Rejected("evidence is forged, stale, or belongs to another method/profile/rule")


@dataclass(frozen=True)
class Strand:
    occurrence_id: str
    object_id: str
    degree: int


# Leaves name slots in the current ordered boundary, not degrees or object IDs.
# None represents the empty word. No associator/unitor rewrite is implemented.
Shape: TypeAlias = int | tuple["Shape", "Shape"] | None


def right_bracketing(arity: int) -> Shape:
    if type(arity) is not int or arity < 0:
        raise Rejected("invalid arity")
    if arity == 0:
        return None
    result: Shape = arity - 1
    for slot in reversed(range(arity - 1)):
        result = (slot, result)
    return result


@dataclass(frozen=True)
class Boundary:
    """Nominal presentation brand + exact bracket syntax + ordered occurrences.

    This is a free-diagram presentation, NOT a compiler object identity or an
    assertion that all equal-coordinate tensor objects are nominally equal.
    """

    presentation_id: str
    bracketing: Shape
    strands: tuple[Strand, ...]


def _shape_slots(shape: Shape) -> tuple[int, ...]:
    if shape is None:
        return ()
    if type(shape) is int:
        return (shape,)
    if type(shape) is tuple and len(shape) == 2:
        if shape[0] is None or shape[1] is None:
            raise Rejected("unitors/empty tensor factors are outside this fragment")
        return _shape_slots(shape[0]) + _shape_slots(shape[1])
    raise Rejected("malformed bracketing")


def _check_boundary(boundary: Boundary) -> None:
    if type(boundary) is not Boundary:
        raise Rejected("missing boundary")
    if type(boundary.presentation_id) is not str or not boundary.presentation_id:
        raise Rejected("missing nominal presentation brand")
    if type(boundary.strands) is not tuple:
        raise Rejected("ordered immutable strands required")
    if _shape_slots(boundary.bracketing) != tuple(range(len(boundary.strands))):
        raise Rejected("bracketing must contain each ordered slot exactly once")
    seen: set[str] = set()
    for strand in boundary.strands:
        _check_strand(strand)
        if strand.occurrence_id in seen:
            raise Rejected("duplicate occurrence ID (object IDs and degrees may repeat)")
        seen.add(strand.occurrence_id)


def _check_strand(strand: Strand) -> None:
    if type(strand) is not Strand or type(strand.degree) is not int:
        raise Rejected("strand requires an exact integer degree")
    for identifier in (strand.occurrence_id, strand.object_id):
        if type(identifier) is not str or not identifier:
            raise Rejected("strand identity is missing")


@dataclass(frozen=True)
class Crossing:
    profile: ProfileKey
    position: int  # zero based, among the CURRENT ordered strands
    direction: Direction
    left: Strand
    right: Strand


@dataclass(frozen=True)
class Word:
    profile: ProfileKey
    source: Boundary
    crossings: tuple[Crossing, ...]
    target: Boundary


def _check_position(position: int, arity: int) -> None:
    if type(position) is not int or not 0 <= position < arity - 1:
        raise Rejected("crossing position must select two adjacent current strands")


def _check_direction(direction: Direction) -> None:
    if type(direction) is not Direction:
        raise Rejected("crossing orientation must be explicit, not erased")


def audit_word(word: Word) -> None:
    """Replay identity/typing metadata without observing any rational scalar."""
    if type(word) is not Word:
        raise Rejected("not a crossing word; arbitrary user morphisms are unsupported")
    profile = fixture_profile(word.profile)
    _check_boundary(word.source)
    _check_boundary(word.target)
    if type(word.crossings) is not tuple:
        raise Rejected("immutable ordered crossings required")
    if word.crossings and profile.capability < Capability.BRAIDED:
        raise Rejected("plain Monoidal has no crossing")
    current = list(word.source.strands)
    for crossing in word.crossings:
        if (
            type(crossing) is not Crossing
            or type(crossing.profile) is not ProfileKey
            or crossing.profile != word.profile
        ):
            raise Rejected("crossing uses a different certified-profile identity")
        _check_position(crossing.position, len(current))
        _check_direction(crossing.direction)
        _check_strand(crossing.left)
        _check_strand(crossing.right)
        i = crossing.position
        if (crossing.left, crossing.right) != (current[i], current[i + 1]):
            raise Rejected("crossing occurrence IDs, object IDs, or degrees do not match ports")
        current[i], current[i + 1] = current[i + 1], current[i]
    expected_target = replace(word.source, strands=tuple(current))
    if word.target != expected_target:
        raise Rejected("target does not match exact ordered ports/brand/bracketing")


def make_word(
    key: ProfileKey,
    source: Boundary,
    instructions: tuple[tuple[int, Direction], ...],
) -> Word:
    """Elaborate position/sign syntax into an occurrence- and profile-bound word."""
    profile = fixture_profile(key)
    _check_boundary(source)
    if type(instructions) is not tuple:
        raise Rejected("immutable instruction sequence required")
    if instructions and profile.capability < Capability.BRAIDED:
        raise Rejected("plain Monoidal has no crossing")
    current = list(source.strands)
    crossings = []
    for instruction in instructions:
        if type(instruction) is not tuple or len(instruction) != 2:
            raise Rejected("crossing requires a position and a direction")
        position, direction = instruction
        _check_position(position, len(current))
        _check_direction(direction)
        left, right = current[position:position + 2]
        crossings.append(Crossing(key, position, direction, left, right))
        current[position], current[position + 1] = right, left
    word = Word(key, source, tuple(crossings), replace(source, strands=tuple(current)))
    audit_word(word)
    return word


def bicharacter(q: Fraction, a: int, b: int) -> Fraction:
    if type(q) is not Fraction or q == 0 or type(a) is not int or type(b) is not int:
        raise Rejected("nonzero exact Fraction and integer degrees required")
    return q ** (a * b)


@dataclass(frozen=True)
class Observation:
    profile: ProfileKey
    source: Boundary
    target: Boundary
    scalar: Fraction
    crossing_factors: tuple[Fraction, ...]


def evaluate(word: Word) -> Observation:
    """Exact representation observation; NEVER an equality certificate."""
    audit_word(word)
    q = fixture_profile(word.profile).q
    scalar = Fraction(1)
    factors = []
    for crossing in word.crossings:
        if q is None:  # Also protected independently by audit_word.
            raise Rejected("plain Monoidal has no selected braiding")
        a, b = crossing.left.degree, crossing.right.degree
        if crossing.direction is Direction.POSITIVE:
            factor = bicharacter(q, a, b)
        else:
            # At CURRENT ports A,B, negative means beta_(B,A)^(-1),
            # NOT beta_(A,B)^(-1), whose domain would be B tensor A.
            factor = Fraction(1) / bicharacter(q, b, a)
        scalar *= factor
        factors.append(factor)
    return Observation(word.profile, word.source, word.target, scalar, tuple(factors))


def _instructions(word: Word) -> tuple[tuple[int, Direction], ...]:
    return tuple((crossing.position, crossing.direction) for crossing in word.crossings)


def _replacement(
    word: Word, offset: int, rule: Rule, evidence: FixtureEvidence
) -> Word:
    audit_word(word)
    _check_evidence(word.profile, rule, evidence)
    if type(offset) is not int or offset < 0:
        raise Rejected("invalid rewrite offset")
    ops = _instructions(word)
    width = 3 if rule is Rule.BRAID else 2
    window = ops[offset:offset + width]
    if len(window) != width:
        raise Rejected("rewrite window out of bounds")
    new: tuple[tuple[int, Direction], ...]
    if rule in (Rule.INVERSE, Rule.SYMMETRIC):
        (i, a), (j, b) = window
        if i != j:
            raise Rejected("cancellation requires the same adjacent position")
        if rule is Rule.INVERSE and a is b:
            raise Rejected("same-direction double braiding is not inverse cancellation")
        if rule is Rule.SYMMETRIC and a is not b:
            raise Rejected("use inverse cancellation for opposite directions")
        new = ()
    elif rule is Rule.BRAID:
        (i, a), (j, b), (k, c) = window
        if i != k or abs(i - j) != 1 or not (a is b is c):
            raise Rejected("only same-sign i,j,i with adjacent i,j is supported")
        new = ((j, a), (i, a), (j, a))
    else:  # Rule.FAR; arbitrary/unknown rules were rejected before this point.
        (i, a), (j, b) = window
        if abs(i - j) <= 1:
            raise Rejected("far commutation requires disjoint positions")
        new = ((j, b), (i, a))
    after = make_word(word.profile, word.source, ops[:offset] + new + ops[offset + width:])
    if after.target != word.target:
        raise Rejected("local rule failed to preserve the exact boundary")
    return after


@dataclass(frozen=True)
class RewriteClaim:
    offset: int
    rule: Rule
    evidence: FixtureEvidence
    after: Word


def propose_rewrite(
    word: Word, offset: int, rule: Rule, evidence: FixtureEvidence
) -> RewriteClaim:
    """Construct a proposal. Consumers must still call check_rewrite/check_trace."""
    return RewriteClaim(offset, rule, evidence, _replacement(word, offset, rule, evidence))


def check_rewrite(before: Word, claim: RewriteClaim) -> Word:
    if type(claim) is not RewriteClaim:
        raise Rejected("missing local-rule claim")
    expected = _replacement(before, claim.offset, claim.rule, claim.evidence)
    audit_word(claim.after)
    if claim.after != expected:
        raise Rejected("returned word is not the exact justified rewrite (including context)")
    return claim.after


@dataclass(frozen=True)
class CheckedTrace:
    """Reference replay record, not proof-carrying Vastitas Core."""

    initial: Word
    returned: Word
    claims: tuple[RewriteClaim, ...]


def check_trace(
    initial: Word, claims: tuple[RewriteClaim, ...], returned: Word
) -> CheckedTrace:
    audit_word(initial)
    if type(claims) is not tuple:
        raise Rejected("immutable claim sequence required")
    current = initial
    for claim in claims:
        current = check_rewrite(current, claim)
    audit_word(returned)
    if returned != current:
        raise Rejected("actual returned word differs from the end of the checked trace")
    return CheckedTrace(initial, returned, claims)
