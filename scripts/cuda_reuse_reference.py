"""Finite #266 planning experiment. No CUDA, cleanup machine, or Core authority.

The independent workload and #210 contract snapshot are synthetic fixtures.
See docs/cuda-reuse-reference.md for the trusted-input and integration boundary.
Python 3.10+, standard library only. JSON is output only, never a certificate.
"""

from __future__ import annotations

from dataclasses import asdict, dataclass
import json


class Rejected(ValueError):
    """A stable reference-only diagnostic, not a compiler diagnostic."""


def require(condition, code):
    if not condition:
        raise Rejected(code)


@dataclass(frozen=True, order=True)
class AllocationKey:
    identity: str
    generation: int

    def __post_init__(self):
        # Python otherwise identifies True/1/1.0 in dict keys and dataclass equality.
        require(type(self.identity) is str and self.identity
                and type(self.generation) is int and self.generation >= 0,
                "INVALID_GENERATION")


@dataclass(frozen=True)
class Binding:
    core_fixture: str
    environment: str
    adapter_profile: str
    runtime: str
    context_epoch: str


@dataclass(frozen=True)
class Access:
    allocation: AllocationKey
    role: str  # operand, output, or workspace; all retain the whole allocation


@dataclass(frozen=True)
class Node:
    identity: str
    stream_epoch: str
    kind: str  # alloc, use, release; these are DEVICE operations, not host calls
    allocation: AllocationKey | None = None
    accesses: tuple[Access, ...] = ()
    duration: int | None = 0  # hypothetical cost, None = unknown; never a measurement
    memory_contract_complete: bool = True


@dataclass(frozen=True)
class Allocation:
    key: AllocationKey
    owner: str
    allocate: str
    release: str
    size_bytes: int
    alignment: int = 8
    layout: str = "whole-contiguous-bytes"
    pool_class: str = "fixture-pool"
    lifetime_closed: bool = True  # false for escaped/returned/out-of-scope owners


@dataclass(frozen=True)
class Workload:
    binding: Binding
    allocations: tuple[Allocation, ...]
    nodes: tuple[Node, ...]
    required_edges: tuple[tuple[str, str], ...]
    coverage_complete: bool = True


@dataclass(frozen=True)
class UseSet:
    allocation: AllocationKey
    consumers: tuple[str, ...]
    sealed: bool = True


@dataclass(frozen=True)
class Submission:
    node: Node  # full operation, including generation and workspace accesses
    binding: Binding
    outcome: str = "enqueued"


@dataclass(frozen=True)
class OrderReceipt:
    before: str
    after: str
    kind: str  # stream_order or event_wait; already audited by the #210 provider
    receipt_id: str
    binding: Binding
    source: Node
    target: Node
    outcome: str = "enqueued"


@dataclass(frozen=True)
class CleanupContract:
    """Read-only #210 boundary view, NOT an implementation of that protocol.

    This fixture asserts that the provider retained all tickets and checked the
    event/stream/record generations, release identity and actual enqueue chain.
    No caller-authored object of this class is production evidence.
    """

    subject: Workload
    uses: tuple[UseSet, ...]
    submissions: tuple[Submission, ...]
    orders: tuple[OrderReceipt, ...]


@dataclass(frozen=True)
class Candidate:
    subject: Workload
    name: str
    added_edges: tuple[tuple[str, str], ...]
    slots: tuple[tuple[AllocationKey, str], ...]


class Dag:
    def __init__(self, nodes, edges):
        self.nodes = tuple(sorted(nodes))
        require(len(set(self.nodes)) == len(self.nodes), "DUPLICATE_NODE")
        self.edges = tuple(sorted(edges))
        require(len(set(self.edges)) == len(self.edges), "DUPLICATE_EDGE")
        self.parents = {n: set() for n in self.nodes}
        for before, after in self.edges:
            require(before in self.parents and after in self.parents, "UNKNOWN_NODE")
            self.parents[after].add(before)
        self.ancestors = {}
        while len(self.ancestors) != len(self.nodes):
            ready = [n for n in self.nodes if n not in self.ancestors
                     and self.parents[n] <= self.ancestors.keys()]
            require(ready, "CYCLIC_ORDER")
            for n in ready:
                self.ancestors[n] = set(self.parents[n])
                for p in self.parents[n]:
                    self.ancestors[n].update(self.ancestors[p])
        self.topological = tuple(self.ancestors)

    def precedes(self, before, after):
        return before in self.ancestors[after]

    def frontier(self, consumers):
        consumers = tuple(consumers)
        require(set(consumers) <= self.parents.keys(), "UNKNOWN_USE")
        return tuple(sorted(u for u in consumers
                            if not any(self.precedes(u, v) for v in consumers)))


def _unique(items, key, code):
    result = {key(item): item for item in items}
    require(len(result) == len(items), code)
    return result


def _natural(value):
    return type(value) is int and value >= 0


def inventory(workload):
    """Reconstruct uses from the independent complete operation inventory."""
    require(workload.coverage_complete is True, "INCOMPLETE_GRAPH_COVERAGE")
    allocations = _unique(workload.allocations, lambda a: a.key, "DUPLICATE_ALLOCATION")
    nodes = _unique(workload.nodes, lambda n: n.identity, "DUPLICATE_NODE")
    require(all(isinstance(v, str) and v for v in asdict(workload.binding).values()),
            "INVALID_BINDING")
    uses = {k: set() for k in allocations}
    for key, a in allocations.items():
        require(isinstance(key.identity, str) and key.identity
                and _natural(key.generation), "INVALID_GENERATION")
        require(_natural(a.size_bytes) and _natural(a.alignment)
                and a.alignment > 0 and a.alignment & (a.alignment - 1) == 0,
                "UNSUPPORTED_SIZE_OR_ALIGNMENT")
        require(a.lifetime_closed is True, "OPEN_OWNER_LIFETIME")
        require(a.owner and a.layout and a.pool_class, "MISSING_STORAGE_PROFILE")
        for name, kind in ((a.allocate, "alloc"), (a.release, "release")):
            require(name in nodes and nodes[name].kind == kind
                    and nodes[name].allocation == key, "ALLOCATION_NODE_MISMATCH")
    for node in nodes.values():
        require(node.identity and node.stream_epoch
                and (node.duration is None or _natural(node.duration)),
                "INVALID_NODE")
        require(node.memory_contract_complete is True, "INCOMPLETE_MEMORY_CONTRACT")
        require(node.kind in {"alloc", "use", "release"}, "UNSUPPORTED_OPERATION")
        if node.kind == "use":
            require(node.allocation is None, "INVALID_USE_NODE")
            require(len(set(node.accesses)) == len(node.accesses), "DUPLICATE_ACCESS")
            for access in node.accesses:
                require(access.allocation in allocations, "STALE_OR_UNKNOWN_ALLOCATION")
                require(access.role in {"operand", "output", "workspace"}, "UNKNOWN_ROLE")
                uses[access.allocation].add(node.identity)
        else:
            require(node.allocation in allocations and not node.accesses,
                    "INVALID_RESOURCE_NODE")
            a = allocations[node.allocation]
            expected = a.allocate if node.kind == "alloc" else a.release
            require(node.identity == expected, "DUPLICATE_RESOURCE_OPERATION")
    Dag(nodes, workload.required_edges)
    return allocations, nodes, uses


def _check_order(allocations, uses, dag, slots):
    """Check EVERY use, independent of planner-supplied frontier suggestions."""
    for key, allocation in allocations.items():
        require(dag.precedes(allocation.allocate, allocation.release), "ALLOCATION_RELEASE_ORDER")
        for use in uses[key]:
            require(dag.precedes(allocation.allocate, use), "ALLOCATION_USE_ORDER")
            require(dag.precedes(use, allocation.release), "USE_RELEASE_ORDER")
    ordered = sorted(allocations)
    for i, key in enumerate(ordered):
        first = allocations[key]
        for other in ordered[i + 1:]:
            if slots[key] != slots[other]:
                continue
            second = allocations[other]
            # Exact layout/alignment/pool matching is deliberately conservative.
            require((first.layout, first.alignment, first.pool_class)
                    == (second.layout, second.alignment, second.pool_class),
                    "INCOMPATIBLE_STORAGE")
            require(dag.precedes(first.release, second.allocate)
                    or dag.precedes(second.release, first.allocate), "REUSE_OVERLAP")


def _plan(workload, candidate):
    require(candidate.subject == workload, "PLAN_SUBJECT_MISMATCH")
    allocations, nodes, uses = inventory(workload)
    assignments = _unique(candidate.slots, lambda p: p[0], "DUPLICATE_SLOT_ASSIGNMENT")
    require(assignments.keys() == allocations.keys(), "INCOMPLETE_SLOT_ASSIGNMENT")
    slots = {key: value[1] for key, value in assignments.items()}
    require(all(isinstance(s, str) and s for s in slots.values()), "INVALID_SLOT")
    dag = Dag(nodes, workload.required_edges + candidate.added_edges)
    _check_order(allocations, uses, dag, slots)
    return allocations, nodes, uses, slots, dag


def propose_separate(workload):
    """Optional liveness analysis; no dependency between independent owners."""
    allocations, nodes, uses = inventory(workload)
    dag = Dag(nodes, workload.required_edges)
    added = set()
    for key, a in allocations.items():
        for use in dag.frontier(uses[key]) or (a.allocate,):
            if not dag.precedes(use, a.release):
                added.add((use, a.release))
    slots = tuple((key, f"slot-{i}") for i, key in enumerate(sorted(allocations)))
    candidate = Candidate(workload, "preserve_parallelism", tuple(sorted(added)), slots)
    _plan(workload, candidate)
    return candidate


def propose_reuse(workload, order):
    """One explicit whole-slot chain, not an optimizer or an optimality claim."""
    baseline = propose_separate(workload)
    allocations, _, _ = inventory(workload)
    require(len(order) == len(set(order)) and set(order) == allocations.keys(),
            "INCOMPLETE_REUSE_CHAIN")
    edges = set(baseline.added_edges)
    for first, second in zip(order, order[1:]):
        pair = (allocations[first].release, allocations[second].allocate)
        if pair not in workload.required_edges:
            edges.add(pair)
    candidate = Candidate(workload, "reduce_memory", tuple(sorted(edges)),
                          tuple((key, "shared-slot") for key in sorted(allocations)))
    _plan(workload, candidate)
    return candidate


def audit(workload, candidate, contract):
    """Fresh independent finite audit. A returned fact is reference-only."""
    require(candidate.subject == workload, "PLAN_SUBJECT_MISMATCH")
    require(contract.subject == workload, "CONTRACT_SUBJECT_MISMATCH")
    allocations, nodes, uses = inventory(workload)
    ledgers = _unique(contract.uses, lambda x: x.allocation, "DUPLICATE_USE_SET")
    require(ledgers.keys() == allocations.keys(), "INCOMPLETE_USE_LEDGER")
    for key, ledger in ledgers.items():
        require(ledger.sealed is True, "UNSEALED_USES")
        require(len(ledger.consumers) == len(set(ledger.consumers))
                and set(ledger.consumers) == uses[key], "USE_LEDGER_MISMATCH")
    submissions = _unique(contract.submissions, lambda s: s.node.identity,
                          "DUPLICATE_SUBMISSION")
    require(submissions.keys() == nodes.keys(), "INCOMPLETE_SUBMISSIONS")
    for name, submission in submissions.items():
        require(submission.binding == workload.binding, "SUBMISSION_BINDING_MISMATCH")
        require(submission.node == nodes[name], "STALE_SUBMISSION")
        require(submission.outcome == "enqueued", "UNRESOLVED_ENQUEUE")
    _unique(contract.orders, lambda r: r.receipt_id, "DUPLICATE_ORDER_RECEIPT")
    for receipt in contract.orders:
        require(receipt.receipt_id and receipt.before in nodes and receipt.after in nodes,
                "INVALID_ORDER_RECEIPT")
        require(receipt.binding == workload.binding, "ORDER_BINDING_MISMATCH")
        require(receipt.source == nodes[receipt.before] and receipt.target == nodes[receipt.after],
                "STALE_ORDER_RECEIPT")
        require(receipt.outcome == "enqueued", "UNRESOLVED_ORDER_ENQUEUE")
        require(receipt.kind in {"stream_order", "event_wait"}, "UNSUPPORTED_ORDER_EVIDENCE")
        if receipt.kind == "stream_order":
            require(nodes[receipt.before].stream_epoch == nodes[receipt.after].stream_epoch,
                    "CROSS_STREAM_SEQUENCE")
    # Reconstruct actual relation from the independent #210 view, NOT the plan.
    actual = Dag(nodes, tuple((r.before, r.after) for r in contract.orders))
    expected_edges = workload.required_edges + candidate.added_edges
    require(set(actual.edges) == set(expected_edges), "ORDER_RECEIPTS_MISMATCH")
    _, _, _, slots, _ = _plan(workload, candidate)
    _check_order(allocations, uses, actual, slots)
    return {
        "status": "verified_in_reference_model",
        "allocations": [
            {"key": asdict(key), "complete_uses": sorted(uses[key]),
             "last_use_frontier": list(actual.frontier(uses[key])),
             "allocate": a.allocate, "release": a.release, "slot": slots[key],
             "retire_node": None, "retirement_contract": "external_issue_210_obligation"}
            for key, a in sorted(allocations.items())],
        "ordered_edges": [list(e) for e in actual.edges],
        "receipt_ids": sorted(r.receipt_id for r in contract.orders),
        "order_kinds": [{"before": r.before, "after": r.after, "kind": r.kind}
                        for r in sorted(contract.orders, key=lambda r: (r.before, r.after))],
    }


def estimate(workload, candidate):
    """Conditional costs. Exact finite peak over ideals; hypothetical durations.

    Each slot is provisioned at its largest occupant's size. Peak counts live
    slots only, not retained pool pages. No CUDA scheduling/allocator is modeled.
    """
    allocations, nodes, _, slots, dag = _plan(workload, candidate)
    require(len(nodes) <= 14, "COST_ENUMERATION_LIMIT")
    capacity = {slot: max(a.size_bytes for k, a in allocations.items() if slots[k] == slot)
                for slot in sorted(set(slots.values()))}
    initial = frozenset()
    pending, visited, live_sums = [initial], {initial}, set()
    while pending:
        done = pending.pop()
        live = {slots[k] for k, a in allocations.items()
                if a.allocate in done and a.release not in done}
        live_sums.add(sum(capacity[s] for s in live))
        for node in dag.nodes:
            if node not in done and dag.parents[node] <= done:
                following = done | {node}
                if following not in visited:
                    visited.add(following)
                    pending.append(following)
    finish = {}
    known_durations = all(n.duration is not None for n in nodes.values())
    if known_durations:
        for name in dag.topological:
            finish[name] = nodes[name].duration + max((finish[p] for p in dag.parents[name]), default=0)
    base = Dag(nodes, workload.required_edges)
    work = sorted(n.identity for n in nodes.values() if n.kind == "use")
    lost_parallelism = [(a, b) for i, a in enumerate(work) for b in work[i + 1:]
                        if not base.precedes(a, b) and not base.precedes(b, a)
                        and (dag.precedes(a, b) or dag.precedes(b, a))]
    return {
        "evidence_status": "conditional_on_candidate_order_and_cost_assumptions",
        "peak_live_slot_bytes": {"value": max(live_sums), "status": "exact_in_finite_model",
                                 "expression": {"op": "max", "args": [
                                     {"op": "const", "value": n} for n in sorted(live_sums)]}},
        "makespan": {"value": max(finish.values(), default=0) if known_durations else None,
                     "status": "estimated" if known_durations else "unknown",
                     "unit": "hypothetical_time_unit"},
        "newly_ordered_work_pairs": [list(pair) for pair in lost_parallelism],
        "added_edges": [list(e) for e in sorted(candidate.added_edges)],
        "pool_reserved_bytes": {"value": None, "status": "unknown"},
        "sync_allocator_remapping_cost": {"value": None, "status": "unknown"},
        "assumptions": ["unlimited processors", "node durations hypothetical when supplied",
                        "unmodeled overhead excluded", "whole-slot storage",
                        "peak is worst over all dependency-respecting prefixes"],
    }


def conservative_fallback(reason):
    """No cleanup decisions: the original #210 keeper retains every obligation."""
    return {"decision": "ownership_cleanup_fallback", "reason": reason,
            "early_release_permission": False, "reuse_permission": False,
            "storage_policy": "separate_allocations",
            "cleanup": "retain_all_tickets_and_quarantine_under_issue_210",
            "progress_guaranteed": False}


def select(workload, candidate=None, contract=None, *, optimize=False):
    if not optimize:
        return conservative_fallback("OPTIONAL_ANALYSIS_DISABLED")
    if candidate is None or contract is None:
        return conservative_fallback("MISSING_PLAN_OR_CONTRACT")
    try:
        facts = audit(workload, candidate, contract)
    except Rejected as error:
        return conservative_fallback(str(error))
    return {"decision": "reference_plan_admissible", "facts": facts,
            "production_reuse_permission": False}


def emit(workload, candidate, contract=None):
    """Advisory extension payload for #242. Never imports serialized facts."""
    result = {
        "schema": "vastitas.cuda-reuse-reference.v1",
        "scope": "synthetic_finite_order_model",
        "expected_binding": asdict(workload.binding),
        "expected_workload": workload_record(workload),
        "candidate": {"subject": workload_record(candidate.subject), "name": candidate.name,
                      "added_edges": sorted(candidate.added_edges),
                      "slots": [(asdict(key), slot) for key, slot in sorted(candidate.slots)]},
        "candidate_analysis": None, "verified_facts": None, "diagnostics": [],
        "integration": {"accepted_core": "not_connected", "cuda_adapter": "not_connected",
                        "common_graph_emit_242": "proposed_extension_only",
                        "lean_proof": "not_provided"},
        "production_reuse_permission": False,
        "package_registration_gate": False, "mandatory_optimization": False,
    }
    try:
        result["candidate_analysis"] = estimate(workload, candidate)
    except Rejected as error:
        result["diagnostics"].append({"stage": "candidate_analysis", "code": str(error)})
    if contract is not None:
        try:
            result["verified_facts"] = audit(workload, candidate, contract)
        except Rejected as error:
            result["diagnostics"].append({"stage": "contract_audit", "code": str(error)})
    else:
        result["diagnostics"].append({"stage": "contract_audit", "code": "MISSING_CONTRACT"})
    return result


def workload_record(workload):
    """Canonical ordering for unordered inventory fields, not an input decoder."""
    result = asdict(workload)
    result["allocations"] = [asdict(a) for a in sorted(workload.allocations, key=lambda a: a.key)]
    result["nodes"] = []
    for node in sorted(workload.nodes, key=lambda n: n.identity):
        record = asdict(node)
        record["accesses"] = [asdict(a) for a in sorted(node.accesses, key=lambda a: (a.allocation, a.role))]
        result["nodes"].append(record)
    result["required_edges"] = sorted(workload.required_edges)
    return result


def canonical_json(record):
    return json.dumps(record, sort_keys=True, indent=2, ensure_ascii=True) + "\n"
