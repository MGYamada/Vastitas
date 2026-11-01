"""Finite-open Cech reference for #265, not compiler acceptance or a Lean proof.

Only the locally constant integer sheaf on an explicitly finite topology.
The #258 handoff is plain complex data, not a second homological algebra API.
"""

from dataclasses import dataclass, fields
from itertools import combinations


SITE = "finite-open-topology/v1"
COEFFICIENTS = "locally-constant-Z/v1"


class Invalid(ValueError):
    """Malformed or unsupported reference data; never mathematical acceptance."""


def require(condition, message):
    if not condition:
        raise Invalid(message)


def items(value, kind):
    require(type(value) is tuple and all(type(x) is kind for x in value),
            f"expected immutable tuple of {kind.__name__}")


def identifiers(value):
    items(value, str)
    require(all(value) and len(set(value)) == len(value), "empty/duplicate identifier")


def open_set(value):
    require(type(value) is frozenset and all(type(x) is str and x for x in value),
            "expected immutable point set")


@dataclass(frozen=True)
class Matrix:
    rows: int
    cols: int
    entries: tuple

    def __post_init__(self):
        require(all(type(n) is int and 0 <= n <= 128 for n in (self.rows, self.cols)),
                "matrix dimensions outside the small reference profile")
        items(self.entries, tuple)
        require(len(self.entries) == self.rows, "wrong matrix row count")
        for row in self.entries:
            items(row, int)  # bool and float are not integral evidence
            require(len(row) == self.cols, "wrong matrix column count")


def matrix(rows, cols=None):
    rows = tuple(tuple(row) for row in rows)
    return Matrix(len(rows), len(rows[0]) if rows else (0 if cols is None else cols), rows)


def zero(rows, cols):
    return Matrix(rows, cols, tuple((0,) * cols for _ in range(rows)))


def identity(n):
    return matrix(tuple(int(i == j) for j in range(n)) for i in range(n))


def multiply(a, b):
    require(a.cols == b.rows, "noncomposable matrices")
    return Matrix(a.rows, b.cols, tuple(tuple(
        sum(a.entries[i][k] * b.entries[k][j] for k in range(a.cols))
        for j in range(b.cols)) for i in range(a.rows)))


@dataclass(frozen=True)
class Context:
    environment: str
    space_id: str
    site_id: str
    coefficient_id: str
    sheaf_id: str
    cover_id: str
    model_revision: str
    site_profile: str = SITE
    coefficient_profile: str = COEFFICIENTS

    def __post_init__(self):
        for field in fields(self):
            value = getattr(self, field.name)
            require(type(value) is str and bool(value), "expected nonempty identity/profile")


@dataclass(frozen=True)
class Subject:
    context: Context
    points: tuple
    opens: tuple
    cover_labels: tuple
    cover: tuple

    def __post_init__(self):
        require(type(self.context) is Context, "expected Context")
        identifiers(self.points)
        identifiers(self.cover_labels)
        items(self.opens, frozenset)
        items(self.cover, frozenset)
        for u in self.opens + self.cover:
            open_set(u)
        require(1 <= len(self.points) <= 8 and len(self.opens) <= 256,
                "reference supports 1..8 points, at most 256 opens")
        require(1 <= len(self.cover) <= 4 and len(self.cover) == len(self.cover_labels),
                "reference supports 1..4 ordered, distinctly labelled cover members")


@dataclass(frozen=True)
class Overlap:
    indices: tuple
    points: frozenset

    def __post_init__(self):
        items(self.indices, int)
        open_set(self.points)


@dataclass(frozen=True)
class Slot:
    indices: tuple
    component: frozenset

    def __post_init__(self):
        items(self.indices, int)
        open_set(self.component)


@dataclass(frozen=True)
class Restriction:
    source: frozenset
    target: frozenset
    matrix: Matrix

    def __post_init__(self):
        open_set(self.source)
        open_set(self.target)
        require(type(self.matrix) is Matrix, "expected restriction matrix")


@dataclass(frozen=True)
class ComplexData:
    """Proposed #258 input: C^p = Z^ranks[p], column-vector differentials.

    Integer basis slots are local to this presentation. Cover meanings of those
    slots live exclusively in CoverData. This is not an implemented std API.
    """

    coefficient_id: str
    ranks: tuple
    differentials: tuple

    def __post_init__(self):
        require(type(self.coefficient_id) is str and bool(self.coefficient_id),
                "expected coefficient identity")
        items(self.ranks, int)
        require(1 <= len(self.ranks) <= 4 and all(0 <= n <= 128 for n in self.ranks),
                "invalid finite ranks")
        items(self.differentials, Matrix)


@dataclass(frozen=True)
class CoverData:
    overlaps: tuple
    bases: tuple
    restrictions: tuple

    def __post_init__(self):
        items(self.overlaps, Overlap)
        items(self.bases, tuple)
        for basis in self.bases:
            items(basis, Slot)
        items(self.restrictions, Restriction)


@dataclass(frozen=True)
class Candidate:
    subject: Subject
    cover_data: CoverData
    complex: ComplexData

    def __post_init__(self):
        require(type(self.subject) is Subject and type(self.cover_data) is CoverData
                and type(self.complex) is ComplexData, "invalid candidate records")


def is_topology(subject):
    opens, whole = set(subject.opens), frozenset(subject.points)
    return (len(opens) == len(subject.opens) and frozenset() in opens and whole in opens
            and all(u <= whole for u in opens)
            and all(u | v in opens and u & v in opens for u in opens for v in opens))


def is_cover(subject):
    return (all(u in subject.opens for u in subject.cover)
            and frozenset().union(*subject.cover) == frozenset(subject.points))


def intersections(subject):
    """No declared overlap table is an input to reconstruction, including empties."""
    return tuple(Overlap(indices, frozenset.intersection(*(subject.cover[i] for i in indices)))
                 for size in range(1, len(subject.cover) + 1)
                 for indices in combinations(range(len(subject.cover)), size))


def components(subject, u):
    """Connected components via the undirected specialization graph of u."""
    minimum = {x: frozenset.intersection(*(v for v in subject.opens if x in v))
               for x in u}
    remaining, result = set(u), []
    for x in subject.points:
        if x not in remaining:
            continue
        found, pending = {x}, [x]
        while pending:
            y = pending.pop()
            for z in u - found:
                if z in minimum[y] or y in minimum[z]:
                    found.add(z)
                    pending.append(z)
        remaining -= found
        result.append(frozenset(found))
    return tuple(result)


def cover_data(subject):
    overlaps = intersections(subject)
    bases = tuple(tuple(Slot(o.indices, c) for o in overlaps if len(o.indices) == p + 1
                        for c in components(subject, o.points))
                  for p in range(len(subject.cover)))
    # All inclusions among actual intersection opens, including identities and empty.
    opens = tuple(dict.fromkeys(o.points for o in overlaps))
    restrictions = tuple(Restriction(u, v, Matrix(
        len(components(subject, v)), len(components(subject, u)),
        tuple(tuple(int(b <= a) for a in components(subject, u))
              for b in components(subject, v))))
        for u in opens for v in opens if v <= u)
    return CoverData(overlaps, bases, restrictions)


def differential_data(subject, data):
    opens = {o.indices: o.points for o in data.overlaps}
    restrictions = {(r.source, r.target): r.matrix for r in data.restrictions}
    differentials = []
    for p in range(len(data.bases) - 1):
        rows, cols = data.bases[p + 1], data.bases[p]
        entries = [[0] * len(cols) for _ in rows]
        for i, target in enumerate(rows):
            target_open = opens[target.indices]
            ti = components(subject, target_open).index(target.component)
            for k in range(len(target.indices)):
                face = target.indices[:k] + target.indices[k + 1:]
                source_open = opens[face]
                restriction = restrictions[source_open, target_open]
                for j, source in enumerate(cols):
                    if source.indices == face:
                        sj = components(subject, source_open).index(source.component)
                        entries[i][j] += (-1) ** k * restriction.entries[ti][sj]
        differentials.append(Matrix(len(rows), len(cols), tuple(map(tuple, entries))))
    return ComplexData(subject.context.coefficient_id, tuple(map(len, data.bases)),
                       tuple(differentials))


def propose(subject):
    """Convenience producer only. verify never trusts or calls this function."""
    require(subject.context.site_profile == SITE
            and subject.context.coefficient_profile == COEFFICIENTS, "unsupported profile")
    require(is_topology(subject) and is_cover(subject), "invalid topology/open cover")
    data = cover_data(subject)
    return Candidate(subject, data, differential_data(subject, data))


def endpoints(data):
    return (len(data.differentials) == len(data.ranks) - 1 and all(
        (d.rows, d.cols) == (data.ranks[p + 1], data.ranks[p])
        for p, d in enumerate(data.differentials)))


def d_squared(data):
    """Algebra only: success says nothing about where the complex came from."""
    return endpoints(data) and all(multiply(b, a) == zero(b.rows, a.cols)
                                  for a, b in zip(data.differentials, data.differentials[1:]))


def restriction_laws(declared, expected):
    maps = {(r.source, r.target): r.matrix for r in declared}
    shapes = {(r.source, r.target): (r.matrix.rows, r.matrix.cols) for r in expected}
    if (len(maps) != len(declared) or maps.keys() != shapes.keys()
            or any((r.rows, r.cols) != shapes[key] for key, r in maps.items())):
        return None  # ill-typed or incomplete: cannot check a functor
    identities = all(r == identity(r.rows) for (u, v), r in maps.items() if u == v)
    composition = all(multiply(b, a) == maps[u, w]
                      for (u, v), a in maps.items() for (v2, w), b in maps.items() if v == v2)
    return identities and composition


@dataclass(frozen=True)
class Check:
    name: str
    status: str
    code: str


@dataclass(frozen=True)
class Report:
    checks: tuple
    returned: Candidate | None

    @property
    def accepted(self):
        return self.returned is not None and all(c.status == "pass" for c in self.checks)


CHECKS = ("binding", "profile", "topology", "cover", "overlaps", "sections",
          "restrictions", "restriction_laws", "orientation", "endpoints", "d_squared")


def verify(expected, candidate):
    """Reconstruct from the independently supplied subject, not candidate tables.

    Returned records are Python reference data, not proof capabilities. Consumers
    must replay this check on their current subject; nominal strings authenticate
    neither a compiler environment nor an actual accepted Core.
    """
    require(type(expected) is Subject and type(candidate) is Candidate, "invalid check inputs")
    checks = []

    def add(name, valid, code):
        checks.append(Check(name, "pass" if valid else "fail", "OK" if valid else code))
        return valid

    def blocked():
        return Report(tuple(checks) + tuple(Check(n, "not_checked", "PREREQUISITE_REQUIRED")
                      for n in CHECKS[len(checks):]), None)

    if not add("binding", expected == candidate.subject, "SUBJECT_MISMATCH"):
        return blocked()
    if (expected.context.site_profile != SITE
            or expected.context.coefficient_profile != COEFFICIENTS):
        checks.append(Check("profile", "unsupported", "UNSUPPORTED_PROFILE"))
        return blocked()
    add("profile", True, "")
    if not add("topology", is_topology(expected), "INVALID_FINITE_TOPOLOGY"):
        return blocked()
    if not add("cover", is_cover(expected), "NOT_AN_OPEN_COVER"):
        return blocked()
    actual = cover_data(expected)
    complex_data = differential_data(expected, actual)
    supplied = candidate.cover_data
    add("overlaps", supplied.overlaps == actual.overlaps, "INTERSECTION_MISMATCH")
    add("sections", supplied.bases == actual.bases, "SECTION_BASIS_MISMATCH")
    add("restrictions", supplied.restrictions == actual.restrictions, "RESTRICTION_MISMATCH")
    laws = restriction_laws(supplied.restrictions, actual.restrictions)
    if laws is None:
        checks.append(Check("restriction_laws", "not_checked", "RESTRICTION_ENDPOINTS_REQUIRED"))
    else:
        add("restriction_laws", laws, "RESTRICTION_LAWS_FAILED")
    add("orientation", candidate.complex == complex_data, "ALTERNATING_DIFFERENTIAL_MISMATCH")
    add("endpoints", endpoints(candidate.complex), "COMPLEX_ENDPOINT_MISMATCH")
    if checks[-1].status == "pass":
        add("d_squared", d_squared(candidate.complex), "D_SQUARED_NONZERO")
    else:
        checks.append(Check("d_squared", "not_checked", "COMPLEX_ENDPOINTS_REQUIRED"))
    return Report(tuple(checks), candidate if all(c.status == "pass" for c in checks) else None)


def six_point_subject():
    points = ("v0", "v1", "v2", "e01", "e02", "e12")
    above = {"v0": {"e01", "e02"}, "v1": {"e01", "e12"}, "v2": {"e02", "e12"}}
    subsets = (frozenset(x for i, x in enumerate(points) if mask & (1 << i))
               for mask in range(1 << len(points)))
    opens = tuple(u for u in subsets if all(above.get(x, set()) <= u for x in u))
    context = Context("reference:environment:1", "triangle-face-space", "opens:A",
                      "integers:A", "constant-integer-sheaf:A", "vertex-stars:A", "1")
    cover = tuple(frozenset({v} | above[v]) for v in points[:3])
    return Subject(context, points, opens, ("U0", "U1", "U2"), cover)


D0 = matrix(((-1, 1, 0), (-1, 0, 1), (0, -1, 1)))
Q = matrix(((1, -1, 1),))


def triangle_integral_witness(data):
    """Fixed-example integer identities, not a general SNF/homology algorithm.

    Also handles the algebraic fake-triangle complex, without certifying a cover.
    Both bases have explicit integral inverses: no rational-rank substitution.
    """
    require(endpoints(data) and data.ranks in ((3, 3, 0), (3, 3, 1))
            and data.differentials[0] == D0, "not the fixed triangle presentation")
    filled = data.ranks[-1] == 1
    require(data.differentials[1] == (Q if filled else zero(0, 3)),
            "not the fixed triangle presentation")
    u = matrix(((1, 0, 0), (0, 1, 0), (1, -1, 1)))
    ui = matrix(((1, 0, 0), (0, 1, 0), (-1, 1, 1)))
    v = matrix(((0, 0, 1), (1, 0, 1), (0, 1, 1)))
    vi = matrix(((-1, 1, 0), (-1, 0, 1), (1, 0, 0)))
    smith = matrix(((1, 0, 0), (0, 1, 0), (0, 0, 0)))
    require(multiply(u, ui) == multiply(ui, u) == identity(3)
            and multiply(v, vi) == multiply(vi, v) == identity(3)
            and multiply(multiply(u, D0), v) == smith, "invalid integral bases")
    # y = D0 * S * y + g * Q * y, Q*D0=0, Q*g=1.
    s = matrix(((0, 0, 0), (1, 0, 0), (0, 1, 0)))
    g = matrix(((0,), (0,), (1,)))
    a, b = multiply(D0, s), multiply(g, Q)
    require(matrix(tuple(x + y for x, y in zip(r, t))
                   for r, t in zip(a.entries, b.entries)) == identity(3)
            and multiply(Q, D0) == zero(1, 3) and multiply(Q, g) == identity(1),
            "invalid integral kernel/image/quotient splitting")
    return {"scope": "fixed complex over Z only; no geometric comparison",
            "U": u.entries, "U_inverse": ui.entries, "V": v.entries, "V_inverse": vi.entries,
            "smith_diagonal": (1, 1, 0), "kernel_d0_generator": (1, 1, 1),
            "image_d0_basis": ((1, 0, -1), (0, 1, 1)),
            "kernel_d1": "ker(a-b+c) = im(d0)" if filled else "Z^3",
            "cokernel_d0_map": Q.entries[0], "cokernel_d0_section": (0, 0, 1),
            "H1_quotient": "ker(q)/im(D) = 0" if filled else "Z^3/im(D) -> Z via q",
            "splitting_S": s.entries, "H0": "Z", "H1": "0" if filled else "Z"}
