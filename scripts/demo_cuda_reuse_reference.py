"""Synthetic #210 snapshots for the #266 experiment; no GPU is contacted."""

from dataclasses import replace

from cuda_reuse_reference import (
    Access, Allocation, AllocationKey, Binding, CleanupContract,
    Node, OrderReceipt, Submission, UseSet, Workload, canonical_json, emit,
    propose_reuse, propose_separate, select,
)


A, B = AllocationKey("A", 1), AllocationKey("B", 1)


def contract_fixture(workload, edges, uses):
    """Assume a #210 provider supplied EXACTLY this hypothetical ledger/DAG.

    Tests pass explicit independent edge/use lists, not a candidate's claims.
    This helper does not simulate enqueue, retire, free or acknowledgement.
    """
    nodes = {node.identity: node for node in workload.nodes}
    return CleanupContract(workload, uses, tuple(Submission(n, workload.binding) for n in workload.nodes),
                           tuple(OrderReceipt(a, b, "stream_order" if
                                              nodes[a].stream_epoch == nodes[b].stream_epoch
                                              else "event_wait", f"receipt-{i}",
                                              workload.binding, nodes[a], nodes[b])
                                 for i, (a, b) in enumerate(edges)))


def independent_workspaces():
    workload = Workload(
        Binding("synthetic:independent:v1", "env-1", "whole-slot-fixture-v1", "run-1", "ctx-1"),
        (Allocation(A, "owner-A", "alloc_A", "free_A", 64),
         Allocation(B, "owner-B", "alloc_B", "free_B", 64)),
        (Node("alloc_A", "stream-1@1", "alloc", A),
         Node("use_A", "stream-1@1", "use", accesses=(Access(A, "workspace"),), duration=3),
         Node("free_A", "stream-1@1", "release", A),
         Node("alloc_B", "stream-2@1", "alloc", B),
         Node("use_B", "stream-2@1", "use", accesses=(Access(B, "workspace"),), duration=5),
         Node("free_B", "stream-2@1", "release", B)),
        (("alloc_A", "use_A"), ("alloc_B", "use_B")))
    uses = (UseSet(A, ("use_A",)), UseSet(B, ("use_B",)))
    parallel_edges = (("alloc_A", "use_A"), ("use_A", "free_A"),
                      ("alloc_B", "use_B"), ("use_B", "free_B"))
    parallel = contract_fixture(workload, parallel_edges, uses)
    serial = contract_fixture(workload, parallel_edges + (("free_A", "alloc_B"),), uses)
    return workload, parallel, serial


def diamond():
    workload = Workload(
        Binding("synthetic:diamond:v1", "env-1", "whole-slot-fixture-v1", "run-1", "ctx-1"),
        (Allocation(A, "owner-A", "alloc_A", "free_A", 64),
         Allocation(B, "owner-B", "alloc_B", "free_B", 64)),
        (Node("alloc_A", "acquisition@1", "alloc", A),
         Node("use_1", "stream-1@1", "use", accesses=(Access(A, "operand"),)),
         Node("use_2", "stream-2@1", "use", accesses=(Access(A, "workspace"),)),
         Node("free_A", "cleanup@1", "release", A),
         Node("alloc_B", "cleanup@1", "alloc", B),
         Node("free_B", "cleanup@1", "release", B)),
        (("alloc_A", "use_1"), ("alloc_A", "use_2"), ("alloc_B", "free_B")))
    edges = (("alloc_A", "use_1"), ("alloc_A", "use_2"), ("use_1", "free_A"),
             ("use_2", "free_A"), ("free_A", "alloc_B"), ("alloc_B", "free_B"))
    contract = contract_fixture(workload, edges, (UseSet(A, ("use_1", "use_2")), UseSet(B, ())))
    return workload, contract


def demonstration():
    workload, parallel, serial = independent_workspaces()
    fork, joined = diamond()
    reuse = propose_reuse(fork, (A, B))
    missing_wait = replace(joined, orders=tuple(r for r in joined.orders
                                              if (r.before, r.after) != ("use_2", "free_A")))
    return {
        "kind": "abstract_order_experiment_not_cuda_execution",
        "parallel": emit(workload, propose_separate(workload), parallel),
        "reuse": emit(workload, propose_reuse(workload, (A, B)), serial),
        "diamond": emit(fork, reuse, joined),
        "one_sided_wait": emit(fork, reuse, missing_wait),
        "fallback": select(fork, reuse, missing_wait, optimize=True),
        "analysis_disabled": select(fork),
    }


if __name__ == "__main__":
    print(canonical_json(demonstration()), end="")
