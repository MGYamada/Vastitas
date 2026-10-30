"""Finite reference for #249; no PRNG, compiler acceptance, or Lean proof.

State execution, explicit partitioning, finite rational laws, and logical address
ownership are separate models. Immutable supply snapshots are test data, not
Python-enforced linear resources. See docs/rand-reference.md for proof boundaries.
"""

from __future__ import annotations

from collections import defaultdict
from dataclasses import dataclass, replace
from enum import Enum
from fractions import Fraction as Q
from itertools import product
from typing import Callable, Hashable


def _natural(value, name):
    if type(value) is not int or value < 0:
        raise ValueError(f"{name} must be a nonnegative integer")


@dataclass(frozen=True)
class Supply:
    bits: tuple[int, ...]
    addresses: tuple[int, ...]
    position: int = 0

    def __post_init__(self):
        if type(self.bits) is not tuple or any(
            type(b) is not int or b not in (0, 1) for b in self.bits
        ):
            raise ValueError("expected a tuple of integer bits")
        if type(self.addresses) is not tuple or len(self.addresses) != len(self.bits):
            raise ValueError("one address is required per bit")
        for address in self.addresses:
            _natural(address, "address")
        if len(set(self.addresses)) != len(self.addresses):
            raise ValueError("duplicate supply address")
        _natural(self.position, "position")
        if self.position > len(self.bits):
            raise ValueError("position outside supply")

    @classmethod
    def from_bits(cls, bits):
        return cls(bits, tuple(range(len(bits))))

    @property
    def remaining(self):
        return len(self.bits) - self.position


@dataclass(frozen=True)
class Read:
    address: int
    bit: int
    consumed: bool


@dataclass(frozen=True)
class Split:
    left: tuple[int, ...]
    right: tuple[int, ...]


@dataclass(frozen=True)
class Success:
    value: object
    rest: Supply
    trace: tuple[Read | Split, ...] = ()


@dataclass(frozen=True)
class Exhausted:
    rest: Supply
    needed: int = 1
    trace: tuple[Read | Split, ...] = ()


Program = Callable[[Supply], Success | Exhausted]


def pure(value) -> Program:
    return lambda supply: Success(value, supply)


def bind(program: Program, continuation: Callable[[object], Program]) -> Program:
    """Sequential state passing, with absorbing shortage and ordered audit trace."""
    def run(supply):
        first = program(supply)
        if isinstance(first, Exhausted):
            return first
        second = continuation(first.value)(first.rest)
        return replace(second, trace=first.trace + second.trace)
    return run


def _read(supply, consume):
    if not supply.remaining:
        return Exhausted(supply)
    p = supply.position
    rest = replace(supply, position=p + int(consume))
    return Success(supply.bits[p], rest, (Read(supply.addresses[p], supply.bits[p], consume),))


def read_bit(supply: Supply):
    return _read(supply, True)


def unsafe_peek_bit(supply: Supply):
    """Negative State fixture: exposes the next bit without consuming it."""
    return _read(supply, False)


def split_at(left_size: int) -> Program:
    """Explicitly partition the remaining supply, preserving original addresses.

    The returned parent has no remaining bits. Children own disjoint snapshots
    in the intended model; retaining the old Python snapshot is not prevented.
    Insufficient capacity fails without a partial partition or a split event.
    """
    _natural(left_size, "left_size")

    def run(supply):
        if left_size > supply.remaining:
            return Exhausted(supply, needed=left_size)
        start, middle = supply.position, supply.position + left_size
        left = Supply(supply.bits[start:middle], supply.addresses[start:middle])
        right = Supply(supply.bits[middle:], supply.addresses[middle:])
        return Success((left, right), replace(supply, position=len(supply.bits)),
                       (Split(left.addresses, right.addresses),))
    return run


@dataclass(frozen=True)
class FiniteDist:
    """Normalized finite measure; every weight must be an exact Fraction."""
    masses: frozenset[tuple[Hashable, Q]]

    def __post_init__(self):
        if type(self.masses) is not frozenset:
            raise ValueError("masses must be a frozenset")
        weights = [weight for _, weight in self.masses]
        if any(type(weight) is not Q or weight <= 0 for weight in weights):
            raise ValueError("stored weights must be positive exact Fractions")
        if len(dict(self.masses)) != len(self.masses) or sum(weights, Q(0)) != 1:
            raise ValueError("support must be unique and total mass exactly one")

    @classmethod
    def from_weights(cls, entries):
        masses = defaultdict(Q)
        for value, weight in entries:
            if type(weight) is not Q or weight < 0:
                raise ValueError("weights must be nonnegative exact Fractions")
            masses[value] += weight
        return cls(frozenset((value, weight) for value, weight in masses.items() if weight))

    def mass(self, value):
        return dict(self.masses).get(value, Q(0))


def dirac(value):
    return FiniteDist.from_weights(((value, Q(1)),))


def compose_dist(dist: FiniteDist, kernel: Callable[[object], FiniteDist]):
    """Finite mathematical sum/product, not an operational std bind API."""
    return FiniteDist.from_weights(
        (b, p * q) for a, p in dist.masses for b, q in kernel(a).masses
    )


def pushforward(dist: FiniteDist, function):
    return compose_dist(dist, lambda value: dirac(function(value)))


def uniform_bits(width: int):
    _natural(width, "width")
    if width > 12:
        raise ValueError("this tiny exhaustive reference supports at most 12 bits")
    return FiniteDist.from_weights((bits, Q(1, 2**width))
                                   for bits in product((0, 1), repeat=width))


@dataclass(frozen=True)
class Returned:
    value: Hashable


class Failure(Enum):
    SUPPLY_EXHAUSTED = "supply_exhausted"


def execution_law(program: Program, source: FiniteDist):
    """Exact output/failure pushforward of an explicitly supplied finite source."""
    def outcome(bits):
        result = program(Supply.from_bits(bits))
        if isinstance(result, Success):
            return Returned(result.value)
        if isinstance(result, Exhausted):
            return Failure.SUPPLY_EXHAUSTED
        raise TypeError("program must return Success or Exhausted")
    return pushforward(source, outcome)


def output_law(program: Program, source: FiniteDist):
    """Output-only law for total finite runs; never condition away shortages."""
    law = execution_law(program, source)
    if law.mass(Failure.SUPPLY_EXHAUSTED):
        raise ValueError("nonzero shortage mass: use execution_law")
    return pushforward(law, lambda result: result.value)


def bad_split_bind(program, continuation):
    """Deliberately incorrect address-only bind, for the syntax-tree counterexample."""
    return lambda path: continuation(program(path + "L"))(path + "R")


def implicit_split_addresses():
    leaf = lambda path: (path,)
    append = lambda previous: lambda path: previous + (path,)
    left = bad_split_bind(bad_split_bind(leaf, append), append)
    right = bad_split_bind(leaf, lambda a: bad_split_bind(append(a), append))
    return left(""), right("")


ADDRESS_PROFILE = "finite-logical-address-v1"  # No PRNG algorithm is specified.
ADDRESS_LIMIT = 2**32  # Toy address bounds, not a PRNG's word-size contract.


@dataclass(frozen=True)
class LogicalAddress:
    seed: int
    namespace: str
    logical_index: int
    draw_index: int
    profile: str = ADDRESS_PROFILE

    def __post_init__(self):
        _natural(self.seed, "seed")
        if type(self.namespace) is not str or not self.namespace:
            raise ValueError("namespace must be nonempty text")
        if self.profile != ADDRESS_PROFILE:
            raise ValueError("unsupported logical-address profile")
        for name in ("logical_index", "draw_index"):
            value = getattr(self, name)
            _natural(value, name)
            if value >= ADDRESS_LIMIT:
                raise ValueError(f"{name} overflow")


class KeyReuse(ValueError):
    pass


class DuplicateAddress(ValueError):
    pass


class LinearKey:
    """One-use handle in this model; public construction exposes re-derivation."""
    def __init__(self, address: LogicalAddress):
        if type(address) is not LogicalAddress:
            raise ValueError("expected a LogicalAddress")
        self._address = address
        self._used = False

    def consume(self):
        if self._used:
            raise KeyReuse("key already consumed")
        self._used = True
        return self._address


class AddressBook:
    """One run's finite domain owner. Claim history survives key consumption.

    Simulated schedules use one book; separate books are separate runs/replays.
    This is not a concurrent allocator or a Python ownership/security boundary.
    """
    def __init__(self, domain):
        addresses = tuple(domain)
        if any(type(address) is not LogicalAddress for address in addresses):
            raise ValueError("expected logical addresses")
        self._domain = frozenset(addresses)
        if len(self._domain) != len(addresses):
            raise DuplicateAddress("overlapping logical domain")
        self._claimed = set()

    def claim(self, address: LogicalAddress):
        if address not in self._domain:
            raise ValueError("address outside owned domain")
        if address in self._claimed:
            raise DuplicateAddress("logical address already allocated in this run")
        self._claimed.add(address)
        return LinearKey(address)
