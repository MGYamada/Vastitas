"""Order/coverage regressions, with an independent permutation oracle."""

from dataclasses import replace
import itertools
import json
from pathlib import Path
import subprocess
import sys
import unittest

from cuda_reuse_reference import (
    Access, AllocationKey, Dag, Node, Rejected, UseSet,
    audit, canonical_json, emit, estimate, propose_reuse,
    propose_separate, select,
)
from demo_cuda_reuse_reference import (
    A, B, contract_fixture, diamond, independent_workspaces,
)


def orders(nodes, edges):
    """Brute-force oracle; deliberately does not use Dag or the auditor."""
    for order in itertools.permutations(nodes):
        position = {n: i for i, n in enumerate(order)}
        if all(position[a] < position[b] for a, b in edges):
            yield position


class ReuseTests(unittest.TestCase):
    def setUp(self):
        self.workload, self.contract = diamond()
        self.plan = propose_reuse(self.workload, (A, B))

    def rejected(self, code, *, workload=None, candidate=None, contract=None):
        with self.assertRaisesRegex(Rejected, "^" + code + "$"):
            audit(workload or self.workload, candidate or self.plan, contract or self.contract)

    def test_original_five_node_experiment(self):
        nodes = ("alloc_A", "use_1", "use_2", "free_A", "alloc_B")
        bad = (("alloc_A", "use_1"), ("alloc_A", "use_2"),
               ("use_1", "free_A"), ("free_A", "alloc_B"))
        schedules = list(orders(nodes, bad))
        self.assertEqual(len(schedules), 4)
        self.assertEqual(sum(p["free_A"] < p["use_2"] for p in schedules), 2)
        schedules = list(orders(nodes, bad + (("use_2", "free_A"),)))
        self.assertEqual(len(schedules), 2)
        self.assertTrue(all(p["use_2"] < p["free_A"] for p in schedules))

    def test_frontier_is_all_incomparable_maximal_uses(self):
        facts = audit(self.workload, self.plan, self.contract)
        self.assertEqual(facts["allocations"][0]["last_use_frontier"], ["use_1", "use_2"])
        self.assertEqual(facts["allocations"][1]["last_use_frontier"], [])
        dag = Dag(("u0", "u1", "u2", "u3"), (("u0", "u1"), ("u1", "u2")))
        self.assertEqual(dag.frontier(("u0", "u1", "u2", "u3")), ("u2", "u3"))

    def test_transitive_frontier_join_is_sufficient(self):
        w = replace(self.workload, required_edges=self.workload.required_edges + (("use_1", "use_2"),))
        p = propose_reuse(w, (A, B))
        self.assertNotIn(("use_1", "free_A"), p.added_edges)
        c = contract_fixture(w, (("alloc_A", "use_1"), ("alloc_A", "use_2"),
                                ("use_1", "use_2"), ("use_2", "free_A"),
                                ("free_A", "alloc_B"), ("alloc_B", "free_B")), self.contract.uses)
        self.assertEqual(audit(w, p, c)["allocations"][0]["last_use_frontier"], ["use_2"])

    def test_one_sided_wait_does_not_realize_candidate(self):
        c = replace(self.contract, orders=tuple(r for r in self.contract.orders
                                               if r.before != "use_2"))
        self.rejected("ORDER_RECEIPTS_MISMATCH", contract=c)

    def test_agreeing_but_unsafe_candidate_and_receipts_rejected(self):
        p = replace(self.plan, added_edges=tuple(e for e in self.plan.added_edges if e[0] != "use_2"))
        c = replace(self.contract, orders=tuple(r for r in self.contract.orders if r.before != "use_2"))
        self.rejected("USE_RELEASE_ORDER", candidate=p, contract=c)

    def test_hidden_workspace_omitted_from_use_ledger(self):
        c = replace(self.contract, uses=(UseSet(A, ("use_1",)), UseSet(B, ())))
        self.rejected("USE_LEDGER_MISMATCH", contract=c)

    def test_unsealed_missing_duplicate_and_extra_use_records(self):
        mutations = (
            ((replace(self.contract.uses[0], sealed=False), self.contract.uses[1]), "UNSEALED_USES"),
            ((self.contract.uses[0],), "INCOMPLETE_USE_LEDGER"),
            (self.contract.uses + (self.contract.uses[0],), "DUPLICATE_USE_SET"),
            ((UseSet(A, ("use_1", "use_2", "use_2")), UseSet(B, ())), "USE_LEDGER_MISMATCH"),
            ((UseSet(A, ("use_1", "use_2", "unrecorded")), UseSet(B, ())), "USE_LEDGER_MISMATCH"),
        )
        for uses, code in mutations:
            with self.subTest(code=code):
                self.rejected(code, contract=replace(self.contract, uses=uses))

    def test_incomplete_ffi_and_graph_coverage(self):
        cases = (
            (replace(self.workload, coverage_complete=False), "INCOMPLETE_GRAPH_COVERAGE"),
            (replace(self.workload, nodes=tuple(replace(n, memory_contract_complete=False)
                                               if n.identity == "use_2" else n
                                               for n in self.workload.nodes)), "INCOMPLETE_MEMORY_CONTRACT"),
        )
        for w, code in cases:
            with self.subTest(code=code):
                self.rejected(code, workload=w, candidate=replace(self.plan, subject=w),
                              contract=replace(self.contract, subject=w))

    def test_generation_is_part_of_every_allocation_use(self):
        stale = AllocationKey("A", 0)
        c = replace(self.contract, uses=(UseSet(stale, ("use_1", "use_2")), UseSet(B, ())))
        self.rejected("INCOMPLETE_USE_LEDGER", contract=c)
        nodes = tuple(replace(n, accesses=(Access(stale, "workspace"),))
                      if n.identity == "use_2" else n for n in self.workload.nodes)
        w = replace(self.workload, nodes=nodes)
        with self.assertRaisesRegex(Rejected, "STALE_OR_UNKNOWN_ALLOCATION"):
            propose_separate(w)
        p = replace(self.plan, slots=((stale, "shared-slot"), (B, "shared-slot")))
        self.rejected("INCOMPLETE_SLOT_ASSIGNMENT", candidate=p)

    def test_generation_tokens_do_not_alias_python_boolean_or_float_keys(self):
        for generation in (True, 1.0, -1, "1"):
            with self.subTest(generation=generation), self.assertRaisesRegex(Rejected, "INVALID_GENERATION"):
                AllocationKey("A", generation)

    def test_stale_node_receipt_cannot_be_relabelled_with_current_subject(self):
        receipts = tuple(replace(s, node=replace(s.node, accesses=(Access(A, "operand"),)))
                         if s.node.identity == "use_2" else s for s in self.contract.submissions)
        self.rejected("STALE_SUBMISSION", contract=replace(self.contract, submissions=receipts))

    def test_old_wait_cannot_be_attached_to_a_new_allocation_generation(self):
        newer = AllocationKey("A", 2)
        w = replace(self.workload,
                    allocations=tuple(replace(a, key=newer) if a.key == A else a for a in self.workload.allocations),
                    nodes=tuple(replace(n, allocation=newer if n.allocation == A else n.allocation,
                                        accesses=tuple(replace(a, allocation=newer) if a.allocation == A else a
                                                       for a in n.accesses)) for n in self.workload.nodes))
        p = propose_reuse(w, (newer, B))
        c = contract_fixture(w, tuple((r.before, r.after) for r in self.contract.orders),
                             (UseSet(newer, ("use_1", "use_2")), UseSet(B, ())))
        audit(w, p, c)
        # Reusing node names does not make an old event/wait chain current.
        c = replace(c, orders=(self.contract.orders[0],) + c.orders[1:])
        self.rejected("STALE_ORDER_RECEIPT", workload=w, candidate=p, contract=c)

    def test_mixed_run_or_context_receipts_are_rejected(self):
        for field in ("runtime", "context_epoch", "adapter_profile"):
            binding = replace(self.workload.binding, **{field: "foreign"})
            c = replace(self.contract, submissions=(replace(self.contract.submissions[0], binding=binding),)
                        + self.contract.submissions[1:])
            self.rejected("SUBMISSION_BINDING_MISMATCH", contract=c)
            c = replace(self.contract, orders=(replace(self.contract.orders[0], binding=binding),)
                        + self.contract.orders[1:])
            self.rejected("ORDER_BINDING_MISMATCH", contract=c)

    def test_exact_core_environment_adapter_and_epoch_binding(self):
        for field in ("core_fixture", "environment", "adapter_profile", "runtime", "context_epoch"):
            with self.subTest(field=field):
                w = replace(self.workload, binding=replace(self.workload.binding, **{field: "stale"}))
                self.rejected("PLAN_SUBJECT_MISMATCH", candidate=replace(self.plan, subject=w))
                self.rejected("CONTRACT_SUBJECT_MISMATCH", contract=replace(self.contract, subject=w))

    def test_unresolved_enqueue_for_use_release_or_allocation(self):
        for name, outcome in itertools.product(("alloc_A", "use_2", "free_A", "alloc_B"),
                                               ("unknown", "partial", "not_enqueued", "cancelled")):
            with self.subTest(node=name, outcome=outcome):
                submissions = tuple(replace(s, outcome=outcome) if s.node.identity == name else s
                                    for s in self.contract.submissions)
                self.rejected("UNRESOLVED_ENQUEUE", contract=replace(self.contract, submissions=submissions))

    def test_unknown_wait_and_host_observations_not_receipts(self):
        for outcome in ("unknown", "not_enqueued", "partial"):
            c = replace(self.contract, orders=(replace(self.contract.orders[0], outcome=outcome),)
                        + self.contract.orders[1:])
            self.rejected("UNRESOLVED_ORDER_ENQUEUE", contract=c)
        for kind in ("host_enqueue", "cancelled", "stream_destroy", "sequence_number", "event_query"):
            c = replace(self.contract, orders=(replace(self.contract.orders[0], kind=kind),)
                        + self.contract.orders[1:])
            self.rejected("UNSUPPORTED_ORDER_EVIDENCE", contract=c)

    def test_unrelated_stream_sequences_do_not_order_uses(self):
        c = replace(self.contract, orders=(replace(self.contract.orders[0], kind="stream_order"),)
                    + self.contract.orders[1:])
        self.rejected("CROSS_STREAM_SEQUENCE", contract=c)

    def test_missing_and_duplicate_submissions_and_receipts(self):
        self.rejected("INCOMPLETE_SUBMISSIONS", contract=replace(self.contract, submissions=self.contract.submissions[:-1]))
        self.rejected("DUPLICATE_SUBMISSION", contract=replace(self.contract, submissions=self.contract.submissions * 2))
        self.rejected("DUPLICATE_ORDER_RECEIPT", contract=replace(self.contract, orders=self.contract.orders * 2))
        r = replace(self.contract.orders[0], receipt_id="different-receipt")
        self.rejected("DUPLICATE_EDGE", contract=replace(self.contract, orders=self.contract.orders + (r,)))

    def test_reuse_requires_order_even_with_valid_individual_lifetimes(self):
        w, c, _ = independent_workspaces()
        p = replace(propose_separate(w), slots=((A, "shared"), (B, "shared")))
        self.rejected("REUSE_OVERLAP", workload=w, candidate=p, contract=c)

    def test_unused_allocation_still_needs_allocate_before_release(self):
        w = replace(self.workload, required_edges=self.workload.required_edges[:-1])
        p = replace(self.plan, subject=w)
        c = replace(self.contract, subject=w, orders=self.contract.orders[:-1])
        self.rejected("ALLOCATION_RELEASE_ORDER", workload=w, candidate=p, contract=c)

    def test_allocation_must_precede_every_use(self):
        w = replace(self.workload, required_edges=self.workload.required_edges[1:])
        p = replace(self.plan, subject=w)
        c = replace(self.contract, subject=w, orders=self.contract.orders[1:])
        self.rejected("ALLOCATION_USE_ORDER", workload=w, candidate=p, contract=c)

    def test_cycles_unknown_nodes_and_duplicate_edges(self):
        for extra, code in ((("free_B", "alloc_A"), "CYCLIC_ORDER"),
                            (("unknown", "free_A"), "UNKNOWN_NODE"),
                            (("alloc_A", "use_1"), "DUPLICATE_EDGE")):
            p = replace(self.plan, added_edges=self.plan.added_edges + (extra,))
            with self.assertRaisesRegex(Rejected, code):
                estimate(self.workload, p)

    def test_storage_compatibility_and_lifetime_escape(self):
        for field, value in (("layout", "transposed"), ("alignment", 16), ("pool_class", "other")):
            w = replace(self.workload, allocations=(self.workload.allocations[0],
                                                    replace(self.workload.allocations[1], **{field: value})))
            with self.assertRaisesRegex(Rejected, "INCOMPATIBLE_STORAGE"):
                propose_reuse(w, (A, B))
        w = replace(self.workload, allocations=(replace(self.workload.allocations[0], lifetime_closed=False),
                                                self.workload.allocations[1]))
        with self.assertRaisesRegex(Rejected, "OPEN_OWNER_LIFETIME"):
            propose_separate(w)

    def test_invalid_or_symbolic_dimensions_do_not_grant_reuse(self):
        for size in (-1, True, 64.0, "N"):
            w = replace(self.workload, allocations=(replace(self.workload.allocations[0], size_bytes=size),
                                                    self.workload.allocations[1]))
            with self.assertRaisesRegex(Rejected, "UNSUPPORTED_SIZE_OR_ALIGNMENT"):
                propose_reuse(w, (A, B))

    def test_original_memory_parallelism_tradeoff(self):
        w, parallel, serial = independent_workspaces()
        p, s = propose_separate(w), propose_reuse(w, (A, B))
        audit(w, p, parallel)
        audit(w, s, serial)
        pc, sc = estimate(w, p), estimate(w, s)
        self.assertEqual((pc["peak_live_slot_bytes"]["value"], pc["makespan"]["value"]), (128, 5))
        self.assertEqual((sc["peak_live_slot_bytes"]["value"], sc["makespan"]["value"]), (64, 8))
        self.assertEqual(pc["newly_ordered_work_pairs"], [])
        self.assertEqual(sc["newly_ordered_work_pairs"], [["use_A", "use_B"]])
        self.assertEqual(sc["pool_reserved_bytes"]["status"], "unknown")
        self.assertEqual(sc["sync_allocator_remapping_cost"]["status"], "unknown")

    def test_shared_slot_capacity_covers_largest_generation(self):
        w, _, _ = independent_workspaces()
        w = replace(w, allocations=(w.allocations[0], replace(w.allocations[1], size_bytes=96)))
        self.assertEqual(estimate(w, propose_reuse(w, (A, B)))["peak_live_slot_bytes"]["value"], 96)
        self.assertEqual(estimate(w, propose_separate(w))["peak_live_slot_bytes"]["value"], 160)

    def test_cost_uncertainty_or_enumeration_limit_does_not_block_order_audit(self):
        w = replace(self.workload, nodes=tuple(replace(n, duration=None) if n.kind == "use" else n
                                               for n in self.workload.nodes))
        p = propose_reuse(w, (A, B))
        edges = tuple((r.before, r.after) for r in self.contract.orders)
        c = contract_fixture(w, edges, self.contract.uses)
        self.assertEqual(audit(w, p, c)["status"], "verified_in_reference_model")
        self.assertEqual(estimate(w, p)["makespan"]["status"], "unknown")
        w = replace(w, nodes=w.nodes + tuple(Node(f"extra-{i}", f"extra-stream-{i}", "use")
                                             for i in range(9)))
        p = propose_reuse(w, (A, B))
        c = contract_fixture(w, edges, self.contract.uses)
        result = emit(w, p, c)
        self.assertIsNone(result["candidate_analysis"])
        self.assertEqual(result["diagnostics"][0]["code"], "COST_ENUMERATION_LIMIT")
        self.assertIsNotNone(result["verified_facts"])

    def test_exhaustive_three_edge_mutations_against_all_schedules(self):
        # Every subset of the two joins and the reuse edge, all 6! permutations.
        optional = (("use_1", "free_A"), ("use_2", "free_A"), ("free_A", "alloc_B"))
        accepted = 0
        for bits in itertools.product((False, True), repeat=3):
            added = tuple(e for e, included in zip(optional, bits) if included)
            edges = self.workload.required_edges + added
            p = replace(self.plan, added_edges=added)
            c = contract_fixture(self.workload, edges, self.contract.uses)
            permutations = list(orders([n.identity for n in self.workload.nodes], edges))
            self.assertTrue(permutations)
            all_safe = all(pos["alloc_A"] < pos["use_1"] < pos["free_A"] < pos["alloc_B"] < pos["free_B"]
                           and pos["alloc_A"] < pos["use_2"] < pos["free_A"] for pos in permutations)
            try:
                audit(self.workload, p, c)
            except Rejected:
                self.assertFalse(all_safe, bits)
            else:
                accepted += 1
                self.assertTrue(all_safe, bits)
        self.assertEqual(accepted, 1)

    def test_candidates_and_old_reports_cannot_supply_verified_facts(self):
        report = emit(self.workload, self.plan)
        self.assertIsNotNone(report["candidate_analysis"])
        self.assertIsNone(report["verified_facts"])
        report["verified_facts"] = {"status": "forged"}
        report["production_reuse_permission"] = True
        fresh = emit(self.workload, self.plan)
        self.assertIsNone(fresh["verified_facts"])
        self.assertFalse(fresh["production_reuse_permission"])
        c = replace(self.contract, orders=self.contract.orders[:-1])
        failed = emit(self.workload, self.plan, c)
        self.assertIsNone(failed["verified_facts"])
        self.assertEqual(failed["diagnostics"][0]["code"], "ORDER_RECEIPTS_MISMATCH")

    def test_emit_is_deterministic_and_has_explicit_unconnected_boundaries(self):
        report = emit(self.workload, self.plan, self.contract)
        self.assertEqual(canonical_json(report), canonical_json(emit(self.workload, self.plan, self.contract)))
        record = json.loads(canonical_json(report))
        self.assertEqual(record["integration"]["accepted_core"], "not_connected")
        self.assertEqual(record["integration"]["cuda_adapter"], "not_connected")
        self.assertFalse(record["package_registration_gate"])
        self.assertFalse(record["mandatory_optimization"])
        self.assertFalse(record["production_reuse_permission"])
        self.assertEqual(record["verified_facts"]["status"], "verified_in_reference_model")

    def test_emit_canonicalizes_inventory_and_receipt_order(self):
        w = replace(self.workload, allocations=self.workload.allocations[::-1], nodes=self.workload.nodes[::-1],
                    required_edges=self.workload.required_edges[::-1])
        p = replace(self.plan, subject=w, added_edges=self.plan.added_edges[::-1], slots=self.plan.slots[::-1])
        c = replace(self.contract, subject=w, uses=self.contract.uses[::-1],
                    submissions=self.contract.submissions[::-1], orders=self.contract.orders[::-1])
        self.assertEqual(canonical_json(emit(w, p, c)),
                         canonical_json(emit(self.workload, self.plan, self.contract)))

    def test_fallback_keeps_cleanup_responsibility_and_no_permission(self):
        disabled = select(self.workload)
        broken = select(self.workload, self.plan, replace(self.contract, orders=()), optimize=True)
        for result in (disabled, broken, select(self.workload, optimize=True)):
            self.assertEqual(result["decision"], "ownership_cleanup_fallback")
            self.assertFalse(result["early_release_permission"])
            self.assertFalse(result["reuse_permission"])
            self.assertFalse(result["progress_guaranteed"])
        result = select(self.workload, self.plan, self.contract, optimize=True)
        self.assertEqual(result["decision"], "reference_plan_admissible")
        self.assertFalse(result["production_reuse_permission"])

    def test_demo_runs_without_cuda_and_emits_json(self):
        script = Path(__file__).with_name("demo_cuda_reuse_reference.py")
        result = subprocess.run([sys.executable, str(script)], capture_output=True, text=True, check=True)
        data = json.loads(result.stdout)
        self.assertEqual(data["kind"], "abstract_order_experiment_not_cuda_execution")
        self.assertIsNone(data["one_sided_wait"]["verified_facts"])
        self.assertEqual(data["fallback"]["reason"], "ORDER_RECEIPTS_MISMATCH")


if __name__ == "__main__":
    unittest.main()
