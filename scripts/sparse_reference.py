"""Finite exact CSR/SpGEMM reference for #243; no compiler or storage authority.

Patterns are immutable, nominal *fixture* snapshots. Values can change without
changing that snapshot. All slots, including explicit/cancellation zeros, survive.
Python validation and plan auditing are not Lean certificates or native preflight.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction


class SparseError(ValueError):
    def __init__(self, code: str, detail: str):
        self.code = code
        super().__init__(f"{code}: {detail}")


class PlanInvalidated(SparseError):
    pass


def require(condition, code, detail):
    if not condition:
        raise SparseError(code, detail)


def bounded(value, bits, label):
    require(type(value) is int and 0 <= value < 1 << bits,
            "S_INTEGER_RANGE", f"{label} must fit unsigned {bits} bits")
    return value


@dataclass(frozen=True)
class IntegerProfile:
    """Logical unsigned metadata/count widths, not a native ABI or byte budget."""

    index_bits: int = 32
    offset_bits: int = 64
    count_bits: int = 64

    def __post_init__(self):
        require(all(type(b) is int and 1 <= b <= 64 for b in
                    (self.index_bits, self.offset_bits, self.count_bits)),
                "S_INTEGER_PROFILE", "widths must be integers in [1, 64]")


def check_shape(rows, columns, widths):
    require(type(widths) is IntegerProfile, "S_INTEGER_PROFILE", "invalid profile")
    bounded(rows, widths.index_bits, "rows")
    bounded(columns, widths.index_bits, "columns")
    bounded(rows + 1, widths.offset_bits, "row-offset array length")


@dataclass(frozen=True, eq=False)
class Pattern:
    """Object identity is nominal in this process; label/revision are descriptive.

    An equal-looking reconstruction (even with the same label/revision) is a new
    snapshot. No hash, caller-written ID or Python object is production evidence.
    """

    label: str
    revision: int
    rows: int
    columns: int
    offsets: tuple[int, ...]
    indices: tuple[int, ...]
    widths: IntegerProfile = IntegerProfile()

    def __post_init__(self):
        object.__setattr__(self, "offsets", tuple(self.offsets))
        object.__setattr__(self, "indices", tuple(self.indices))
        require(type(self.label) is str and bool(self.label), "S_PATTERN_ID", "empty label")
        require(type(self.revision) is int and self.revision >= 0,
                "S_PATTERN_ID", "revision must be a nonnegative integer")
        check_shape(self.rows, self.columns, self.widths)
        slots = bounded(len(self.indices), self.widths.offset_bits, "slot count")
        require(len(self.offsets) == self.rows + 1, "S_OFFSET_LENGTH", "expected rows + 1")
        for offset in self.offsets:
            bounded(offset, self.widths.offset_bits, "row offset")
            require(offset <= slots, "S_OFFSET_BOUNDS", "offset exceeds slot count")
        require(self.offsets[0] == 0 and self.offsets[-1] == slots,
                "S_OFFSET_ENDPOINT", "expected first = 0 and last = slot count")
        require(all(a <= b for a, b in zip(self.offsets, self.offsets[1:])),
                "S_OFFSET_ORDER", "offsets must be monotone")
        for column in self.indices:
            bounded(column, self.widths.index_bits, "column index")
            require(column < self.columns, "S_INDEX_BOUNDS", "column outside shape")
        for row in range(self.rows):
            cols = self.indices[self.offsets[row]:self.offsets[row + 1]]
            require(all(a < b for a, b in zip(cols, cols[1:])),
                    "S_CANONICAL_ROW", "CSR columns must be strictly increasing; use COO to aggregate")

    @property
    def slots(self):
        return len(self.indices)

    def positions(self):
        return frozenset((r, self.indices[s]) for r in range(self.rows)
                         for s in range(self.offsets[r], self.offsets[r + 1]))


def exact(value):
    require(type(value) in (int, Fraction), "S_EXACT_SCALAR", "only int/Fraction; no Float or bool")
    return Fraction(value)


@dataclass(frozen=True)
class CSR:
    pattern: Pattern
    values: tuple[Fraction, ...]

    def __post_init__(self):
        require(type(self.pattern) is Pattern, "S_PATTERN", "expected a validated pattern")
        object.__setattr__(self, "values", tuple(exact(v) for v in self.values))
        require(len(self.values) == self.pattern.slots,
                "S_VALUE_LENGTH", "one value per stored slot is required")

    def with_values(self, values):
        return CSR(self.pattern, values)

    @property
    def numerical_nonzeros(self):
        return sum(v != 0 for v in self.values)

    def dense(self):
        p = self.pattern
        result = [[Fraction(0) for _ in range(p.columns)] for _ in range(p.rows)]
        for row in range(p.rows):
            for slot in range(p.offsets[row], p.offsets[row + 1]):
                result[row][p.indices[slot]] = self.values[slot]
        return result


def from_csr(rows, columns, offsets, indices, values, *, label, revision=0,
             widths=IntegerProfile()):
    return CSR(Pattern(label, revision, rows, columns, offsets, indices, widths), values)


def from_coo(rows, columns, entries, *, label, revision=0, widths=IntegerProfile()):
    """Aggregate in input order over Q, then sort; keep every encountered position.

    Even a duplicate sum of zero retains its slot. The raw COO count must fit the
    offset width before aggregation. This policy does not license Float reordering.
    """
    check_shape(rows, columns, widths)
    totals = {}
    for count, entry in enumerate(entries, 1):
        bounded(count, widths.offset_bits, "raw COO entry count")
        require(type(entry) in (tuple, list) and len(entry) == 3,
                "S_COO_ENTRY", "expected (row, column, value)")
        row, column, value = entry
        bounded(row, widths.index_bits, "COO row")
        bounded(column, widths.index_bits, "COO column")
        require(row < rows and column < columns, "S_INDEX_BOUNDS", "COO index outside shape")
        key = (row, column)
        totals[key] = totals.get(key, Fraction(0)) + exact(value)
    offsets, indices, values = [0], [], []
    ordered = iter(sorted(totals))
    current = next(ordered, None)
    for row in range(rows):
        while current is not None and current[0] == row:
            indices.append(current[1])
            values.append(totals[current])
            current = next(ordered, None)
        offsets.append(len(indices))
    return from_csr(rows, columns, offsets, indices, values,
                    label=label, revision=revision, widths=widths)


@dataclass(frozen=True)
class Binding:
    """Fixture operation occurrence and method revision, not checked Core IDs."""

    occurrence: str
    method_revision: int = 1

    def __post_init__(self):
        require(type(self.occurrence) is str and bool(self.occurrence),
                "S_BINDING", "empty occurrence")
        require(type(self.method_revision) is int and self.method_revision >= 0,
                "S_BINDING", "invalid method revision")


@dataclass(frozen=True)
class SpGEMMPlan:
    left: Pattern
    right: Pattern
    output: Pattern
    binding: Binding
    # Per output slot, ordered (left input slot, right input slot) products.
    products: tuple[tuple[tuple[int, int], ...], ...]

    @property
    def multiplication_contributions(self):
        return sum(len(group) for group in self.products)


def symbolic(left, right):
    """Relational composition of validated stored patterns; never inspect values."""
    require(left.columns == right.rows, "S_SHAPE", "inner dimensions disagree")
    require(left.widths == right.widths, "S_WIDTH_MISMATCH", "explicit conversion required")
    check_shape(left.rows, right.columns, left.widths)
    offsets, indices, products, count = [0], [], [], 0
    for row in range(left.rows):
        columns = {}
        for a_slot in range(left.offsets[row], left.offsets[row + 1]):
            k = left.indices[a_slot]
            for b_slot in range(right.offsets[k], right.offsets[k + 1]):
                count = bounded(count + 1, left.widths.count_bits, "multiplication contributions")
                column = right.indices[b_slot]
                columns.setdefault(column, []).append((a_slot, b_slot))
        bounded(len(indices) + len(columns), left.widths.offset_bits, "output slot count")
        for column in sorted(columns):
            indices.append(column)
            products.append(tuple(columns[column]))
        offsets.append(len(indices))
    return tuple(offsets), tuple(indices), tuple(products)


def inspect_spgemm(left: CSR, right: CSR, binding: Binding):
    require(type(binding) is Binding, "S_BINDING", "expected fixture binding")
    a, b = left.pattern, right.pattern
    offsets, indices, products = symbolic(a, b)
    output = Pattern(f"{binding.occurrence}/output", 0, a.rows, b.columns,
                     offsets, indices, a.widths)
    return SpGEMMPlan(a, b, output, binding, products)


def require_structural_bound(left: CSR, right: CSR, candidate: Pattern):
    """Accept only supersets of relational composition; no cancellation evidence API."""
    plan = inspect_spgemm(left, right, Binding("bound-check"))
    require((candidate.rows, candidate.columns) == (left.pattern.rows, right.pattern.columns),
            "S_SHAPE", "candidate bound has wrong shape")
    require(plan.output.positions() <= candidate.positions(), "S_BOUND_MISSING",
            "a numerical zero cannot justify an omitted structural candidate")


def audit_plan(plan: SpGEMMPlan, left: CSR, right: CSR, binding: Binding):
    if plan.left is not left.pattern or plan.right is not right.pattern:
        raise PlanInvalidated("S_PATTERN_CHANGED", "exact nominal pattern snapshots are required")
    if plan.binding != binding:
        raise PlanInvalidated("S_BINDING_CHANGED", "operation occurrence or method revision changed")
    # Deliberately recompute the full symbolic audit in this reference. This is
    # not a measured inspector/executor optimization or a Python trust boundary.
    offsets, indices, products = symbolic(left.pattern, right.pattern)
    p = plan.output
    require((p.rows, p.columns, p.widths, p.offsets, p.indices, plan.products) ==
            (left.pattern.rows, right.pattern.columns, left.pattern.widths,
             offsets, indices, products), "S_PLAN_TAMPERED", "output or contribution schedule differs")


def execute_spgemm(plan: SpGEMMPlan, left: CSR, right: CSR, binding: Binding):
    audit_plan(plan, left, right, binding)
    return CSR(plan.output, tuple(sum((left.values[a] * right.values[b] for a, b in group),
                                     Fraction(0)) for group in plan.products))


def pivot_row(matrix: CSR, column: int):
    """First partial-pivot choice only: max abs, ties choose the lowest row."""
    p = matrix.pattern
    bounded(column, p.widths.index_bits, "pivot column")
    require(column < p.columns, "S_INDEX_BOUNDS", "pivot column outside shape")
    best_row, best_size = None, Fraction(0)
    for row in range(p.rows):
        for slot in range(p.offsets[row], p.offsets[row + 1]):
            if p.indices[slot] == column and abs(matrix.values[slot]) > best_size:
                best_row, best_size = row, abs(matrix.values[slot])
    return best_row


@dataclass(frozen=True)
class PivotGuardPlan:
    """A numeric dependency demonstrator, not LU or a cached factorization."""

    structural: SpGEMMPlan
    column: int
    selected_row: int


def bind_pivot_guard(plan, left, right, binding, *, column=0):
    audit_plan(plan, left, right, binding)
    selected = pivot_row(left, column)
    require(selected is not None, "S_PIVOT_ZERO", "no nonzero pivot exists")
    return PivotGuardPlan(plan, column, selected)


def execute_guarded(plan: PivotGuardPlan, left, right, binding):
    audit_plan(plan.structural, left, right, binding)
    if pivot_row(left, plan.column) != plan.selected_row:
        raise PlanInvalidated("S_NUMERIC_DEPENDENCY_CHANGED", "pivot vanished or selected row changed")
    return execute_spgemm(plan.structural, left, right, binding)


def cancellation_example():
    left = from_csr(2, 3, (0, 2, 4), (0, 1, 1, 2), (1, 1, 1, 1), label="A")
    right = from_csr(3, 2, (0, 1, 3, 4), (0, 0, 1, 1), (1, -1, 1, -1), label="B")
    return left, right, right.with_values((1, -2, 1, -3))
