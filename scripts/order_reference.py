"""Bounded finite order reference for #294; no Core or Lean authority.

Rows of ``le`` are left operands, columns are right operands. Carrier equality
is equality of distinct element indices, never mutual reachability. Only the
Python standard library is used; see docs/order-reference.md for the boundary.
"""

from dataclasses import dataclass
from itertools import combinations, product


MAX_ELEMENTS = 8


class Invalid(ValueError):
    def __init__(self, code, witness=()):
        self.code, self.witness = code, witness
        super().__init__(f"{code}: {witness}")


def _name(value):
    if type(value) is not str or not value.strip():
        raise Invalid("INVALID_NAME")


def _index(value, size):
    if type(value) is not int or not 0 <= value < size:
        raise Invalid("INVALID_INDEX", (value, size))


def _table(table, size, entry_check):
    if type(table) is not tuple or len(table) != size:
        raise Invalid("INVALID_TABLE")
    for row in table:
        if type(row) is not tuple or len(row) != size:
            raise Invalid("INVALID_TABLE")
        for entry in row:
            entry_check(entry)


def _boolean(value):
    if type(value) is not bool:
        raise Invalid("INVALID_BOOLEAN")


@dataclass(frozen=True)
class Order:
    context: str
    carrier: str
    name: str
    revision: str
    elements: tuple[str, ...]
    le: tuple[tuple[bool, ...], ...]

    def __post_init__(self):
        for value in (self.context, self.carrier, self.name, self.revision):
            _name(value)
        if type(self.elements) is not tuple or len(self.elements) > MAX_ELEMENTS:
            raise Invalid("INVALID_CARRIER")
        for value in self.elements:
            _name(value)
        if len(set(self.elements)) != len(self.elements):
            raise Invalid("DUPLICATE_ELEMENT")
        _table(self.le, len(self.elements), _boolean)

    def indices(self):
        return range(len(self.elements))


@dataclass(frozen=True)
class Map:
    name: str
    revision: str
    source: Order
    target: Order
    images: tuple[int, ...]

    def __post_init__(self):
        _name(self.name)
        _name(self.revision)
        if type(self.source) is not Order or type(self.target) is not Order:
            raise Invalid("INVALID_ENDPOINT")
        if self.source.context != self.target.context:
            raise Invalid("CONTEXT_MISMATCH")
        if type(self.images) is not tuple or len(self.images) != len(self.source.elements):
            raise Invalid("NON_TOTAL_MAP")
        for value in self.images:
            _index(value, len(self.target.elements))


@dataclass(frozen=True)
class Pair:
    lower: Map
    upper: Map

    def __post_init__(self):
        if type(self.lower) is not Map or type(self.upper) is not Map:
            raise Invalid("INVALID_MAP")
        if (self.lower.source != self.upper.target
                or self.lower.target != self.upper.source):
            raise Invalid("ENDPOINT_MISMATCH")


@dataclass(frozen=True)
class Lattice:
    order: Order
    joins: tuple[tuple[int, ...], ...]
    meets: tuple[tuple[int, ...], ...]
    bottom: int
    top: int

    def __post_init__(self):
        if type(self.order) is not Order:
            raise Invalid("INVALID_ORDER")
        n = len(self.order.elements)
        for table in (self.joins, self.meets):
            _table(table, n, lambda value: _index(value, n))
        _index(self.bottom, n)
        _index(self.top, n)


@dataclass(frozen=True)
class Claim:
    """Untrusted request payload, not a proof object or acceptance receipt."""
    subject: object
    law: str


@dataclass(frozen=True)
class Check:
    name: str
    checked: int
    counterexample: tuple | None


def _scan(name, cases, predicate):
    count, first = 0, None
    for case in cases:
        count += 1
        if not predicate(*case) and first is None:
            first = case
    return Check(name, count, first)


def inspect_order(order):
    """Compute all four laws independently; this is not bound acceptance."""
    if type(order) is not Order:
        raise Invalid("INVALID_ORDER")
    xs, le = order.indices(), order.le
    return (
        _scan("reflexivity", ((a,) for a in xs), lambda a: le[a][a]),
        _scan("transitivity", product(xs, repeat=3),
              lambda a, b, c: not (le[a][b] and le[b][c]) or le[a][c]),
        _scan("antisymmetry", product(xs, repeat=2),
              lambda a, b: not (le[a][b] and le[b][a]) or a == b),
        _scan("totality", product(xs, repeat=2), lambda a, b: le[a][b] or le[b][a]),
    )


def _require(checks):
    for check in checks:
        if check.counterexample is not None:
            raise Invalid(check.name, check.counterexample)
    return {check.name: check.checked for check in checks}


def _order(order, partial=False):
    _require(inspect_order(order)[:3 if partial else 2])


def _monotone(mapping, name="monotonicity", reverse=False):
    a, b, f = mapping.source.le, mapping.target.le, mapping.images
    return _scan(name, product(mapping.source.indices(), repeat=2),
                 lambda x, y: not a[x][y] or (b[f[y]][f[x]] if reverse else b[f[x]][f[y]]))


def _pair_checks(pair, law):
    l, u = pair.lower, pair.upper
    a, b, f, g = l.source, l.target, l.images, u.images
    _order(a)
    _order(b)
    checks = (
        _monotone(l, "lower_monotonicity"),
        _monotone(u, "upper_monotonicity"),
    )
    if law == "galois":
        return checks + (
            _scan("adjunction", product(a.indices(), b.indices()),
                  lambda x, y: b.le[f[x]][y] == a.le[x][g[y]]),
            _scan("unit", ((x,) for x in a.indices()), lambda x: a.le[x][g[f[x]]]),
            _scan("counit", ((y,) for y in b.indices()), lambda y: b.le[f[g[y]]][y]),
        )
    return checks + (
        _scan("left_inverse", ((x,) for x in a.indices()), lambda x: g[f[x]] == x),
        _scan("right_inverse", ((y,) for y in b.indices()), lambda y: f[g[y]] == y),
        _scan("order_equivalence", product(a.indices(), repeat=2),
              lambda x, y: a.le[x][y] == b.le[f[x]][f[y]]),
    )


def inspect_connection(pair):
    """Audit each connection law independently, without granting bound acceptance."""
    if type(pair) is not Pair:
        raise Invalid("INVALID_PAIR")
    return _pair_checks(pair, "galois")


def _lattice_checks(lattice):
    o, sup, inf = lattice.order, lattice.joins, lattice.meets
    _order(o, partial=True)
    le, xs = o.le, o.indices()
    return (
        _scan("join_universal", product(xs, repeat=3),
              lambda a, b, z: le[sup[a][b]][z] == (le[a][z] and le[b][z])),
        _scan("meet_universal", product(xs, repeat=3),
              lambda a, b, z: le[z][inf[a][b]] == (le[z][a] and le[z][b])),
        _scan("bottom", ((x,) for x in xs), lambda x: le[lattice.bottom][x]),
        _scan("top", ((x,) for x in xs), lambda x: le[x][lattice.top]),
    )


def families(order):
    """All subsets of the bounded index domain, including the empty family."""
    return (xs for size in range(len(order.elements) + 1)
            for xs in combinations(order.indices(), size))


def _bound(order, family, join):
    """Search the relation itself, without consulting claimed lattice tables."""
    le = order.le
    bounds = [z for z in order.indices()
              if all(le[x][z] if join else le[z][x] for x in family)]
    universal = [z for z in bounds
                 if all(le[z][w] if join else le[w][z] for w in bounds)]
    if len(universal) != 1:
        raise Invalid("MISSING_JOIN" if join else "MISSING_MEET", family)
    return universal[0]


def _preservation(mapping, law):
    _order(mapping.source, partial=True)
    _order(mapping.target, partial=True)
    _require((_monotone(mapping),))
    join = law.endswith("joins")
    domain = (families(mapping.source) if law.startswith("all_")
              else product(mapping.source.indices(), repeat=2))
    # Require every requested bound to exist. A missing operation is never a pass.
    checks = []
    for family in domain:
        source = _bound(mapping.source, family, join)
        target = _bound(mapping.target, tuple(mapping.images[x] for x in family), join)
        checks.append((family, mapping.images[source], target))
    return (_scan("preservation", checks, lambda xs, actual, required: actual == required),)


_PROFILES = {
    "preorder": Order, "partial_order": Order, "linear_order": Order,
    "bounded_lattice": Lattice,
    "monotone": Map, "antitone": Map,
    "binary_joins": Map, "binary_meets": Map, "all_joins": Map, "all_meets": Map,
    "galois": Pair, "order_iso": Pair,
}


def verify(expected, candidate, *, law):
    """Bind to the caller's full expected subject AND law, then recompute.

    Candidates cannot select their own target, downgrade a required law, or
    carry trusted success flags. The return value contains enumeration counts;
    failures raise Invalid with a deterministic first counterexample.
    """
    if type(law) is not str or law not in _PROFILES:
        raise Invalid("UNSUPPORTED_LAW")
    if type(expected) is not _PROFILES[law]:
        raise Invalid("INVALID_EXPECTED_SUBJECT")
    if type(candidate) is not Claim or candidate.law != law:
        raise Invalid("CLAIM_MISMATCH")
    if type(candidate.subject) is not type(expected) or candidate.subject != expected:
        raise Invalid("SUBJECT_MISMATCH")
    if type(expected) is Order:
        count = {"preorder": 2, "partial_order": 3, "linear_order": 4}[law]
        checks = inspect_order(expected)[:count]
    elif type(expected) is Lattice:
        checks = _lattice_checks(expected)
    elif type(expected) is Pair:
        checks = inspect_connection(expected) if law == "galois" else _pair_checks(expected, law)
    elif law in ("monotone", "antitone"):
        _order(expected.source)
        _order(expected.target)
        checks = (_monotone(expected, reverse=law == "antitone"),)
    else:
        checks = _preservation(expected, law)
    return _require(checks)
