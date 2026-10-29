"""Executable, deliberately incomplete layout/preflight reference for #183.

Python integers are mathematical integers. No element enumeration, dereference,
native code, compiler acceptance, or production check elimination occurs here.
The receipt API models successful-branch/snapshot binding, not Python security.
Run this file for a small demonstration; see test_storage_layout_reference.py.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum


class Verdict(Enum):
    SAFE = "safe"
    INVALID = "invalid"
    NEEDS_EVIDENCE = "needs_evidence"


@dataclass(frozen=True)
class Decision:
    verdict: Verdict
    reason: str


def safe(reason):
    return Decision(Verdict.SAFE, reason)


def invalid(reason):
    return Decision(Verdict.INVALID, reason)


def unknown(reason):
    return Decision(Verdict.NEEDS_EVIDENCE, reason)


def combine(decisions):
    decisions = tuple(decisions)
    for verdict in (Verdict.INVALID, Verdict.NEEDS_EVIDENCE):
        if any(d.verdict is verdict for d in decisions):
            return verdict
    return Verdict.SAFE


class Mode(Enum):
    READ = "read"
    WRITE = "write"
    READ_WRITE = "read_write"


class Kind(Enum):
    DENSE = "column_major"
    TRANSPOSE = "explicit_transpose"
    BROADCAST = "read_only_broadcast"
    STRIDED = "unsupported_strided"


@dataclass(frozen=True)
class Element:
    width: int = 8
    alignment: int = 8


@dataclass(frozen=True)
class AllocationKey:
    identity: str
    generation: int


@dataclass(frozen=True)
class Allocation:
    key: AllocationKey
    capacity: int
    base: int
    element: Element = Element()


@dataclass(frozen=True)
class DenseSource:
    rows: int
    columns: int
    ld: int


@dataclass(frozen=True)
class Layout:
    kind: Kind
    shape: tuple[int, int]
    strides: tuple[int, int]
    offset: int = 0
    element: Element = Element()
    source: DenseSource | None = None


@dataclass(frozen=True)
class Access:
    allocation: AllocationKey
    layout: Layout
    mode: Mode


def dense(key, rows, columns, ld, *, offset=0, element=Element(), mode=Mode.READ):
    return Access(key, Layout(Kind.DENSE, (rows, columns),
                             (element.width, ld * element.width), offset,
                             element, DenseSource(rows, columns, ld)), mode)


def transpose(access):
    """Explicitly permute a dense source; never conjugate or allocate."""
    from dataclasses import replace

    if access.layout.kind is not Kind.DENSE:
        raise ValueError("only an explicit transpose of a dense source is supported")
    layout = access.layout
    return replace(access, layout=replace(layout, kind=Kind.TRANSPOSE,
                                         shape=layout.shape[::-1],
                                         strides=layout.strides[::-1]))


@dataclass(frozen=True)
class NativeLimits:
    """Conservative synchronous CPU LP64 address-expression contract."""

    pointer_bits: int = 64
    offset_bits: int = 64
    index_bits: int = 32


@dataclass(frozen=True)
class World:
    """Authoritative *fixture* snapshot, stable during a synchronous operation.

    The production allocator/Ownership Checker must establish this snapshot.
    A caller-authored snapshot is not production lifetime/ownership evidence.
    Every resource transition must advance epoch, including return/drop/reuse.
    """

    epoch: int
    allocations: tuple[Allocation, ...]
    active_loans: tuple[Access, ...] = ()


@dataclass(frozen=True)
class LayoutIR:
    """Reference IR: all listed whole-view accesses have overlapping lifetimes.

    Its only access expression is offset + i*stride[0] + j*stride[1].
    This is not Vastitas Indexed.Core or public protocol 8.
    """

    operation: str
    revision: int
    accesses: tuple[Access, ...]


@dataclass(frozen=True)
class LayoutReport:
    checks: tuple[tuple[str, Decision], ...]
    envelope: tuple[int, int] | None = None

    @property
    def verdict(self):
        return combine(d for _, d in self.checks)

    def __getitem__(self, stage):
        return dict(self.checks)[stage]


def _nat(value):
    return type(value) is int and value >= 0


def _element_valid(element):
    return (type(element) is Element and _nat(element.width) and element.width > 0
            and _nat(element.alignment) and element.alignment > 0
            and element.alignment & (element.alignment - 1) == 0
            and element.width % element.alignment == 0)


def _key_valid(key):
    return (type(key) is AllocationKey and type(key.identity) is str
            and bool(key.identity) and _nat(key.generation))


def check_world(world):
    if (type(world) is not World or not _nat(world.epoch)
            or type(world.allocations) is not tuple or type(world.active_loans) is not tuple):
        return invalid("malformed_world")
    seen = set()
    for a in world.allocations:
        if (type(a) is not Allocation or not _key_valid(a.key)
                or not _nat(a.capacity) or not _nat(a.base) or not _element_valid(a.element)):
            return invalid("malformed_allocation")
        if a.key.identity in seen:
            return invalid("multiple_live_generations_or_duplicate_allocation")
        seen.add(a.key.identity)
    # Independently sanity-check the fixture allocator's disjointness claim.
    for i, a in enumerate(world.allocations):
        for b in world.allocations[i + 1:]:
            if a.capacity and b.capacity and max(a.base, b.base) < min(
                    a.base + a.capacity, b.base + b.capacity):
                return invalid("distinct_live_allocations_overlap")
    return safe("live_allocation_snapshot")


def _metadata(access):
    if type(access) is not Access or not _key_valid(access.allocation) or type(access.mode) is not Mode:
        return invalid("malformed_access")
    l = access.layout
    if (type(l) is not Layout or type(l.kind) is not Kind
            or type(l.shape) is not tuple or len(l.shape) != 2
            or type(l.strides) is not tuple or len(l.strides) != 2
            or not all(_nat(x) for x in l.shape) or not _nat(l.offset)
            or not all(type(x) is int for x in l.strides) or not _element_valid(l.element)):
        return invalid("malformed_rank_two_layout")
    if l.source is not None and (type(l.source) is not DenseSource
            or not all(_nat(x) for x in (l.source.rows, l.source.columns, l.source.ld))):
        return invalid("malformed_dense_source")
    if any(x < 0 for x in l.strides):
        return unknown("negative_stride_extension_required")
    return safe("mathematical_integer_metadata")


def _profile(l):
    if l.kind is Kind.STRIDED:
        return unknown("general_strided_layout_requires_evidence")
    s, w = l.source, l.element.width
    if s is None:
        return invalid("missing_dense_source")
    # Also imposed for empty metadata; never compute rows-1 here.
    if s.ld < max(1, s.rows):
        return invalid("invalid_leading_dimension")
    shape, strides = (s.rows, s.columns), (w, s.ld * w)
    if l.kind is Kind.TRANSPOSE:
        shape, strides = shape[::-1], strides[::-1]
    elif l.kind is Kind.BROADCAST:
        if any(old != new and old != 1 for old, new in zip(shape, l.shape)):
            return invalid("broadcast_requires_singleton_source_axis")
        strides = tuple(0 if old != new else stride
                        for old, new, stride in zip(shape, l.shape, strides))
        shape = l.shape
    if (l.shape, l.strides) != (shape, strides):
        return invalid("layout_does_not_match_declared_source")
    return safe("reconstructed_dense_layout")


def _write_injectivity(access, profile):
    l = access.layout
    if l.kind is Kind.BROADCAST and access.mode is not Mode.READ:
        return invalid("broadcast_is_read_only")
    if 0 in l.shape:
        return safe("empty_access_domain")
    if access.mode is Mode.READ:
        return safe("read_only_aliases_permitted")
    # Concrete two-element byte-overlap witnesses, NOT a general strided solver.
    for extent, stride in zip(l.shape, l.strides):
        if extent > 1 and stride < l.element.width:
            return invalid("adjacent_elements_overlap")
    if min(l.shape) > 1 and abs(l.strides[0] - l.strides[1]) < l.element.width:
        return invalid("cross_axis_elements_overlap")  # indices (1,0), (0,1)
    if profile.verdict is Verdict.SAFE:
        return safe("dense_or_transpose_byte_injective")
    return unknown("write_injectivity_requires_evidence")


def _native_contract(limits):
    if (type(limits) is not NativeLimits
            or not all(type(n) is int and 2 <= n <= 64
                       for n in (limits.pointer_bits, limits.offset_bits, limits.index_bits))
            or limits.offset_bits > limits.pointer_bits
            or limits.index_bits > limits.offset_bits):
        return invalid("unsupported_native_integer_contract")
    return safe("native_integer_contract")


def _check_native(a, l, end, limits):
    """Conversion stage after nonnegative mathematical metadata validation.

    Indices are widened to the offset type before multiplication. This helper
    is not a standalone layout validator and cannot issue a success receipt.
    """
    contract = _native_contract(limits)
    if contract.verdict is not Verdict.SAFE:
        return contract
    pointer_max = (1 << limits.pointer_bits) - 1
    offset_max = (1 << (limits.offset_bits - 1)) - 1
    index_max = (1 << (limits.index_bits - 1)) - 1
    dimensions = l.shape + (() if l.source is None else
                            (l.source.rows, l.source.columns, l.source.ld))
    if any(x > index_max for x in dimensions):
        return invalid("native_dimension_overflow")
    if any(x > offset_max for x in (a.capacity, l.offset, l.element.width,
                                    l.element.alignment, *l.strides, end)):
        return invalid("native_byte_arithmetic_overflow")
    if a.base > pointer_max or a.base + a.capacity > pointer_max:
        return invalid("native_address_overflow")
    # All nonnegative partial products/sums of the specified access expression
    # are bounded by end. Empty views evaluate none of those products at runtime.
    return safe("native_fields_and_all_access_intermediates_fit")


def _check_layout(world, access, limits):
    metadata = _metadata(access)
    if metadata.verdict is not Verdict.SAFE:
        return LayoutReport((("metadata", metadata),))
    a = next((a for a in world.allocations if a.key == access.allocation), None)
    if a is None:
        return LayoutReport((("provenance", invalid("missing_or_stale_allocation_generation")),))
    l = access.layout
    if l.element != a.element:
        return LayoutReport((("provenance", invalid("element_representation_mismatch")),))
    profile = _profile(l)
    empty = 0 in l.shape
    # Never use extent-1 for an empty view, even in the mathematical reference.
    end = l.offset if empty else (l.offset + (l.shape[0] - 1) * l.strides[0]
                                  + (l.shape[1] - 1) * l.strides[1] + l.element.width)
    bounds = safe("empty_metadata_in_capacity" if empty else "all_element_bytes_in_capacity")
    if end > a.capacity:
        bounds = invalid("capacity_exceeded")
    align = l.element.alignment
    alignment = safe("empty_no_element_pointer" if empty else "all_accesses_aligned")
    if not empty and ((a.base + l.offset) % align
                     or any(n > 1 and stride % align for n, stride in zip(l.shape, l.strides))):
        alignment = invalid("misaligned_access")
    checks = (("metadata", metadata), ("provenance", safe("same_live_generation")),
              ("profile", profile), ("bounds", bounds), ("alignment", alignment),
              ("write_injectivity", _write_injectivity(access, profile)),
              ("native", _check_native(a, l, end, limits)))
    return LayoutReport(checks, None if empty else (l.offset, end))


def check_layout(world, access, limits=NativeLimits()):
    validity = check_world(world)
    if validity.verdict is not Verdict.SAFE:
        return LayoutReport((("world", validity),))
    return _check_layout(world, access, limits)


def _contains_byte(l, byte):
    """O(1) membership in a validated dense source; transpose has same bytes."""
    if 0 in l.shape or byte < l.offset:
        return False
    s, w = l.source, l.element.width
    column, within_column = divmod(byte - l.offset, s.ld * w)
    return column < s.columns and within_column < s.rows * w


def _loan_relation(left, lr, right, rr):
    if left.mode is Mode.READ and right.mode is Mode.READ:
        return safe("shared_reads")
    if lr.envelope is None or rr.envelope is None:
        return safe("empty_region")
    if left.allocation != right.allocation:
        return safe("distinct_live_allocations")
    lo, hi = lr.envelope
    other_lo, other_hi = rr.envelope
    if hi <= other_lo or other_hi <= lo:
        return safe("disjoint_enclosing_intervals")
    # A real byte witness, not overlap of bounding boxes alone.
    if _contains_byte(left.layout, other_lo) or _contains_byte(right.layout, lo):
        return invalid("actual_byte_overlap")
    return unknown("overlapping_envelopes_need_partition_evidence")


def check_loans(world, left, right, limits=NativeLimits()):
    lr, rr = check_layout(world, left, limits), check_layout(world, right, limits)
    verdict = combine((Decision(lr.verdict, "left"), Decision(rr.verdict, "right")))
    if verdict is not Verdict.SAFE:
        return Decision(verdict, "layout_prerequisite_failed")
    return _loan_relation(left, lr, right, rr)


@dataclass(frozen=True)
class PreflightReport:
    checks: tuple[Decision, ...]
    layouts: tuple[LayoutReport, ...] = ()
    loans: tuple[tuple[int, int, Decision], ...] = ()

    @property
    def verdict(self):
        return combine((*self.checks, *(Decision(r.verdict, "layout") for r in self.layouts),
                        *(d for _, _, d in self.loans)))


def inspect_preflight(world, ir, limits=NativeLimits()):
    validity = check_world(world)
    if validity.verdict is not Verdict.SAFE:
        return PreflightReport((validity,))
    contract = _native_contract(limits)
    if contract.verdict is not Verdict.SAFE:
        return PreflightReport((contract,))
    if (type(ir) is not LayoutIR or type(ir.operation) is not str or not ir.operation
            or not _nat(ir.revision) or type(ir.accesses) is not tuple):
        return PreflightReport((invalid("malformed_reference_ir"),))
    accesses = world.active_loans + ir.accesses
    reports = tuple(_check_layout(world, a, limits) for a in accesses)
    # Include old/old pairs: an inconsistent environment cannot mint evidence.
    pairs = tuple((i, j, _loan_relation(a, reports[i], accesses[j], reports[j]))
                  for i, a in enumerate(accesses) for j in range(i + 1, len(accesses))
                  if reports[i].verdict is Verdict.SAFE and reports[j].verdict is Verdict.SAFE)
    return PreflightReport((validity, contract), reports, pairs)


@dataclass(frozen=True)
class Prepared:
    """A plan contains no successful-branch evidence."""

    ir: LayoutIR


@dataclass(frozen=True)
class Success:
    ir: LayoutIR
    world: World
    limits: NativeLimits
    ticket: object


class PreflightSession:
    """Receipt issuance, independent re-audit and scope expiry in the reference.

    No buffer parameter exists, so failure cannot modify output. Production
    dominance, lifetime and initialization must be checked by the real Core.
    """

    def __init__(self):
        self._issued = {}

    def preflight(self, prepared, world, limits=NativeLimits()):
        if type(prepared) is not Prepared:
            return PreflightReport((invalid("missing_prepared_ir"),)), None
        report = inspect_preflight(world, prepared.ir, limits)
        if report.verdict is not Verdict.SAFE:
            return report, None
        success = Success(prepared.ir, world, limits, object())
        self._issued[success.ticket] = success
        return report, success

    def audit_for_bounds_elision(self, success, actual_returned_ir, current_world,
                                limits=NativeLimits()):
        if (type(success) is not Success or type(success.ticket) is not object
                or self._issued.get(success.ticket) is not success):
            return invalid("no_successful_preflight_in_this_scope")
        if (success.ir != actual_returned_ir or success.world != current_world
                or success.limits != limits):
            return invalid("evidence_binding_mismatch")
        report = inspect_preflight(current_world, actual_returned_ir, limits)
        return Decision(report.verdict, "rechecked_actual_returned_reference_ir")

    def end_scope(self, success):
        if (type(success) is Success and type(success.ticket) is object
                and self._issued.get(success.ticket) is success):
            self._issued.pop(success.ticket, None)


def main():
    """Demonstrate classifications without accessing a real buffer."""
    from dataclasses import replace

    key = AllocationKey("demo", 1)
    world = World(0, (Allocation(key, 48, 4096),))
    good = dense(key, 2, 2, 2, mode=Mode.WRITE)
    overlap = replace(good, layout=Layout(Kind.STRIDED, (2, 2), (8, 8)))
    for name, access in (("dense", good), ("transpose", transpose(good)),
                         ("positive-stride overlapping write", overlap),
                         ("empty", dense(key, 0, 2, 1))):
        r = check_layout(world, access)
        print(name + ": " + r.verdict.value)
        for stage, decision in r.checks:
            print(f"  {stage}: {decision.verdict.value} ({decision.reason})")
    even = dense(key, 1, 3, 2, mode=Mode.WRITE)
    odd = dense(key, 1, 3, 2, offset=8)
    print("interleaved loans:", check_loans(world, even, odd).verdict.value)


if __name__ == "__main__":
    main()
