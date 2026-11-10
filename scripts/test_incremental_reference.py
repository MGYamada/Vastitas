"""Clean/incremental differential and cache-adversary regressions for #339."""

from copy import deepcopy
from dataclasses import replace
from itertools import product
import json
import unittest

import incremental_reference as r


CORE = r.ModuleId("core-source-A", "ops")
ADDON = r.ModuleId("addon-source", "ops")
BRIDGE = r.ModuleId("app-source", "bridge")
USER = r.ModuleId("app-source", "main")
QUIET = r.ModuleId("app-source", "quiet")
F = r.DeclId(CORE, "f")
LM = r.Key("Linear", ("HasMetric",))


def example(core=CORE):
    family = r.DeclId(core, "f")
    return r.Program(("app-source",), (
        r.Package(core.package, "core"),
        r.Package(ADDON.package, "addon", dependencies=(core.package,)),
        r.Package(USER.package, "app", dependencies=(core.package, ADDON.package)),
    ), (
        r.Module(core, families=(r.Family("f"),), methods=(r.Method("base", family),)),
        r.Module(ADDON, imports=(core,)),
        r.Module(BRIDGE, imports=(core,), uses=(r.Use(core),)),
        r.Module(USER, imports=(BRIDGE,), uses=(r.Use(BRIDGE),), calls=(r.Call(family, LM),)),
        r.Module(QUIET),
    ))


def module(program, identity):
    return next(m for m in program.modules if m.identity == identity)


def edit(program, target, **changes):
    return replace(program, modules=tuple(replace(m, **changes) if m.identity == target else m
                                          for m in program.modules))


def add_method(program, identity, method, *, apply=False, region=r.KEYS):
    changed = edit(program, identity, methods=module(program, identity).methods + (method,))
    if apply:
        assembly = replace(program.assembly,
                           applied=program.assembly.applied + (r.DeclId(identity, method.name),),
                           grants=program.assembly.grants + (r.Grant(method.family, method.family.module,
                                                                    identity, region),))
        changed = replace(changed, assembly=assembly)
    return changed


def outcome(run, identity):
    return next(u for u in run.observation["units"] if u["module"] == identity.token())


def winner(run):
    return outcome(run, USER)["calls"][0]["selection"]["winner"]


def rehash(entry):
    # An attacker can recompute every digest. This is deliberately NOT a signature.
    entry["evidence"] = {"kind": "finite-recheck-required",
                         "context_sha256": r.digest(entry["context"]),
                         "candidate_sha256": r.digest(entry["candidate"])}


class IncrementalTests(unittest.TestCase):
    def parity(self, program, cache=None):
        before = deepcopy(cache)
        actual = r.incremental_build(program, cache)
        self.assertEqual(r.canonical(actual.observation),
                         r.canonical(r.clean_build(program).observation))
        self.assertEqual(cache, before, "build mutated an earlier cache")
        return actual

    def test_cold_warm_and_json_roundtrip(self):
        p = example()
        cold = self.parity(p)
        self.assertTrue(cold.observation["accepted"])
        self.assertEqual(winner(cold), r.DeclId(CORE, "base").token())
        self.assertEqual(set(cold.trace["recomputed"]), {m.identity.token() for m in p.modules})
        warm = self.parity(p, json.loads(json.dumps(cold.cache)))
        self.assertEqual(warm.trace["invalidated"], [])
        self.assertEqual(warm.trace["recomputed"], [])
        self.assertEqual(set(warm.trace["reused"]), set(cold.trace["recomputed"]))
        self.assertEqual(warm.trace["checked"], cold.trace["checked"])

    def test_body_edit_transitive_consumers_and_unrelated_reuse(self):
        p = example()
        cache = self.parity(p).cache
        changed = edit(p, CORE, body=7)
        run = self.parity(changed, cache)
        self.assertEqual(set(run.trace["invalidated"]),
                         {i.token() for i in (CORE, ADDON, BRIDGE, USER)})
        self.assertEqual(run.trace["reused"], [QUIET.token()])
        self.assertEqual(outcome(run, CORE)["body"], {"type": "Int", "literal": 7})
        broken = self.parity(edit(p, CORE, body=True), cache)
        self.assertFalse(broken.observation["accepted"])
        self.assertIn("E_BODY", outcome(broken, CORE)["diagnostics"])
        self.assertIn("E_DEPENDENCY", outcome(broken, USER)["diagnostics"])
        repaired = self.parity(p, broken.cache)
        self.assertTrue(repaired.observation["accepted"])

    def test_public_interface_and_import_changes(self):
        p = example()
        old = self.parity(p)
        signature = self.parity(edit(p, CORE, interface="Bool", body=True), old.cache)
        self.assertIn("E_INTERFACE:" + CORE.token(), outcome(signature, BRIDGE)["diagnostics"])
        self.assertFalse(signature.observation["accepted"])
        detached = edit(p, BRIDGE, imports=(), uses=())
        removed = self.parity(detached, old.cache)
        self.assertIn("E_CALL_SCOPE:" + F.token(), outcome(removed, USER)["diagnostics"])
        self.assertEqual(set(removed.trace["invalidated"]), {BRIDGE.token(), USER.token()})
        restored = self.parity(p, removed.cache)
        self.assertTrue(restored.observation["accepted"])

    def test_old_and_new_edges_survive_simultaneous_rewire_and_edit(self):
        p = example()
        old = self.parity(p)
        changed = edit(edit(p, CORE, body=8), BRIDGE, imports=(QUIET,), uses=(r.Use(QUIET),))
        run = self.parity(changed, old.cache)
        self.assertEqual(set(run.trace["invalidated"]),
                         {i.token() for i in (CORE, ADDON, BRIDGE, USER)})
        self.assertEqual(run.trace["reused"], [QUIET.token()])

    def test_product_order_ambiguity_repair_removal_and_unchanged_consumer(self):
        p = add_method(example(), CORE, r.Method("linear", F, "Linear", body=11))
        initial = self.parity(p)
        self.assertEqual(winner(initial), r.DeclId(CORE, "linear").token())
        ambiguous = add_method(p, CORE, r.Method("metric", F, requires=("HasMetric",), body=22))
        conflict = self.parity(ambiguous, initial.cache)
        self.assertEqual(module(p, USER), module(ambiguous, USER))
        self.assertFalse(conflict.observation["accepted"])
        self.assertIsNone(winner(conflict))
        self.assertTrue(any("E_AMBIGUOUS:" in e for e in conflict.observation["diagnostics"]))
        repaired = add_method(ambiguous, CORE,
                              r.Method("repair", F, "Linear", ("HasMetric",), body=33))
        fixed = self.parity(repaired, conflict.cache)
        self.assertTrue(fixed.observation["accepted"])
        self.assertEqual(winner(fixed), r.DeclId(CORE, "repair").token())
        self.assertEqual(outcome(fixed, USER)["calls"][0]["selection"]["body"], 33)
        self.assertEqual(len(fixed.trace["invalidated"]), len(p.modules))
        self.assertEqual(fixed.trace["reused"], [])
        self.assertFalse(self.parity(ambiguous, fixed.cache).observation["accepted"])

    def test_winner_change_without_ambiguity_and_selected_body_edit(self):
        p = example()
        before = self.parity(p)
        added = add_method(p, CORE, r.Method("linear", F, "Linear", body=17))
        after = self.parity(added, before.cache)
        self.assertTrue(after.observation["accepted"])
        self.assertNotEqual(winner(before), winner(after))
        self.assertEqual(module(p, USER), module(added, USER))
        methods = module(added, CORE).methods
        changed = edit(added, CORE, methods=methods[:-1] + (replace(methods[-1], body=19),))
        run = self.parity(changed, after.cache)
        self.assertEqual(winner(run), winner(after))
        self.assertEqual(outcome(run, USER)["calls"][0]["selection"]["body"], 19)
        self.assertEqual(len(run.trace["invalidated"]), len(p.modules))

    def test_extension_outside_consumer_imports_and_grant_revocation(self):
        p = example()
        old = self.parity(p)
        contributed = add_method(p, ADDON, r.Method("refine", F, "Linear", body=9), apply=True)
        self.assertNotIn(ADDON, module(contributed, USER).imports)
        run = self.parity(contributed, old.cache)
        self.assertTrue(run.observation["accepted"])
        self.assertEqual(winner(run), r.DeclId(ADDON, "refine").token())
        self.assertEqual(len(run.trace["invalidated"]), len(p.modules))
        revoked = replace(contributed, assembly=replace(contributed.assembly, grants=()))
        rejected = self.parity(revoked, run.cache)
        self.assertFalse(rejected.observation["accepted"])
        self.assertTrue(any("E_NO_GRANT:" in e for e in rejected.observation["diagnostics"]))

    def test_final_footprint_exact_issuer_and_exact_grantee(self):
        p = add_method(example(), ADDON, r.Method("refine", F, "Linear", body=9), apply=True)
        old = self.parity(p)
        grant = p.assembly.grants[0]
        for bad in (replace(grant, region=(LM,)), replace(grant, issuer=USER),
                    replace(grant, grantee=BRIDGE)):
            with self.subTest(grant=bad):
                changed = replace(p, assembly=replace(p.assembly, grants=(bad,)))
                result = self.parity(changed, old.cache)
                self.assertFalse(result.observation["accepted"])
                self.assertEqual(len(result.trace["invalidated"]), len(p.modules))

    def test_assembly_revision_and_unapplication(self):
        p = add_method(example(), ADDON, r.Method("refine", F, "Linear", body=9), apply=True)
        old = self.parity(p)
        revision = replace(p, assembly=replace(p.assembly, revision="2"))
        run = self.parity(revision, old.cache)
        self.assertEqual(run.observation, old.observation)
        self.assertEqual(len(run.trace["invalidated"]), len(p.modules))
        unapplied = replace(revision, assembly=replace(revision.assembly, applied=()))
        run = self.parity(unapplied, run.cache)
        self.assertEqual(winner(run), r.DeclId(CORE, "base").token())

    def test_invalid_losing_unused_and_unapplied_bodies(self):
        p = add_method(example(), CORE, r.Method("winner", F, "Linear", body=9))
        old = self.parity(p)
        variants = [
            edit(p, CORE, methods=(replace(module(p, CORE).methods[0], body=True),
                                   module(p, CORE).methods[1])),
            edit(p, QUIET, body="ill-typed"),
            add_method(p, ADDON, r.Method("unused", F, body=True)),
        ]
        for changed in variants:
            with self.subTest(changed=changed):
                run = self.parity(changed, old.cache)
                self.assertFalse(run.observation["accepted"])
                self.assertEqual(winner(run), r.DeclId(CORE, "winner").token())
                warm_rejection = self.parity(changed, run.cache)
                self.assertEqual(len(warm_rejection.trace["reused"]), len(p.modules))

    def test_all_key_ambiguity_cannot_be_hidden_by_unused_declared_domain(self):
        p = example()
        p = edit(p, USER, calls=())
        p = edit(p, CORE, families=(r.Family("f", (r.Key("Scalar"),)),))
        p = add_method(p, CORE, r.Method("linear", F, "Linear"))
        p = add_method(p, CORE, r.Method("metric", F, requires=("HasMetric",)))
        run = self.parity(p)
        self.assertFalse(run.observation["accepted"])
        self.assertTrue(any("E_AMBIGUOUS:" in e for e in run.observation["diagnostics"]))

    def test_missing_coverage_duplicate_signatures_and_unknown_contributions(self):
        p = example()
        old = self.parity(p)
        cases = [edit(p, CORE, methods=()),
                 add_method(p, CORE, r.Method("duplicate", F)),
                 replace(p, assembly=r.Assembly(applied=(r.DeclId(ADDON, "absent"),)))]
        for changed, code in zip(cases, ("E_COVERAGE:", "E_DUPLICATE_SIGNATURE:",
                                          "E_MISSING_CONTRIBUTION:")):
            run = self.parity(changed, old.cache)
            self.assertFalse(run.observation["accepted"])
            self.assertTrue(any(code in e for e in run.observation["diagnostics"]))

    def test_nominal_package_identity_not_display_name_version_or_body_hash(self):
        p = example()
        old = self.parity(p)
        other = example(r.ModuleId("core-source-B", "ops"))
        self.assertEqual(p.packages[0].name, other.packages[0].name)
        self.assertEqual(p.packages[0].version, other.packages[0].version)
        run = self.parity(other, old.cache)
        self.assertTrue(run.observation["accepted"])
        self.assertNotEqual(winner(old), winner(run))
        self.assertEqual(len(run.trace["invalidated"]), len(other.modules))
        self.assertNotIn(CORE.token(), run.cache["entries"])

    def test_compiler_manifest_and_package_dependency_changes(self):
        p = example()
        old = self.parity(p)
        versions = [replace(p, compiler="reference-compiler/2"),
                    replace(p, packages=(replace(p.packages[0], manifest_revision="2"),)
                            + p.packages[1:])]
        for changed in versions:
            run = self.parity(changed, old.cache)
            self.assertEqual(run.observation, old.observation)
            self.assertEqual(len(run.trace["invalidated"]), len(p.modules))
        detached = replace(p, packages=p.packages[:-1] +
                           (replace(p.packages[-1], dependencies=(CORE.package,)),))
        run = self.parity(detached, old.cache)
        self.assertNotIn(ADDON.token(), run.cache["entries"])
        self.assertEqual(len(run.trace["invalidated"]), 4)

    def test_module_addition_deletion_and_deterministic_input_order(self):
        p = example()
        old = self.parity(p)
        renamed = edit(p, QUIET, identity=r.ModuleId(QUIET.package, "new"))
        run = self.parity(renamed, old.cache)
        self.assertEqual(len(run.trace["invalidated"]), len(p.modules))
        self.assertNotIn(QUIET.token(), run.cache["entries"])
        reordered = replace(p, modules=p.modules[::-1], packages=p.packages[::-1])
        run = self.parity(reordered, old.cache)
        self.assertEqual(run.observation, old.observation)
        self.assertEqual(len(run.trace["reused"]), len(p.modules))

    def test_disconnected_packages_are_outside_selected_dependency_closure(self):
        p = example()
        extra = r.ModuleId("not-selected", "mod")
        extended = replace(p, packages=p.packages + (r.Package(extra.package, "unused"),),
                           modules=p.modules + (r.Module(extra, body="bad"),))
        old = self.parity(p)
        run = self.parity(extended, old.cache)
        self.assertEqual(run.observation, old.observation)
        self.assertEqual(len(run.trace["reused"]), len(p.modules))

    def test_invalid_input_graphs_do_not_publish_reusable_candidates(self):
        p = example()
        old = self.parity(p)
        cases = [
            edit(p, CORE, imports=(BRIDGE,)),
            edit(p, USER, imports=(r.ModuleId(USER.package, "missing"),)),
            replace(p, modules=p.modules + (module(p, CORE),)),
            replace(p, packages=p.packages + (p.packages[0],)),
            replace(p, packages=(replace(p.packages[0], dependencies=(USER.package,)),)
                    + p.packages[1:]),
            replace(p, roots=("missing-package",)),
            edit(p, BRIDGE, imports=(USER,)),
        ]
        for changed in cases:
            run = self.parity(changed, old.cache)
            self.assertFalse(run.observation["accepted"])
            self.assertEqual(run.cache["entries"], {})

    def test_all_prior_variant_caches_and_edit_revert_histories(self):
        p = example()
        variants = [p, edit(p, CORE, body=4), edit(p, CORE, body=True),
                    edit(p, CORE, interface="Bool", body=True), edit(p, USER, imports=()),
                    add_method(p, CORE, r.Method("linear", F, "Linear", body=6)),
                    replace(p, assembly=r.Assembly(revision="2")),
                    example(r.ModuleId("core-source-B", "ops")),
                    replace(p, compiler="reference-compiler/2")]
        caches = [None] + [r.clean_build(v).cache for v in variants]
        for i, current in enumerate(variants):
            for j, cache in enumerate(caches):
                with self.subTest(current=i, cache=j):
                    self.parity(current, cache)
        cache = None
        for current in variants + variants[::-1] + variants:
            cache = self.parity(current, cache).cache


# Separate test case class; the helper does not depend on fixture state.
class CacheTests(unittest.TestCase):
    parity = IncrementalTests.parity

    def test_corrupt_partial_and_wrong_schema_cache_states(self):
        p = example()
        old = self.parity(p)
        states = [None, 17, "truncated JSON", [], {}, {"verified": True},
                  {**old.cache, "schema": "old-schema"}, {**old.cache, "entries": None},
                  {**old.cache, "snapshot": {"modules": None}},
                  {**old.cache, "entries": {USER.token(): {"verified": True}}}]
        for state in states:
            self.parity(p, state)
        self.parity(p, {"cycle": float("nan")})
        cycle = {}
        cycle["cycle"] = cycle
        # deepcopy equality cannot compare cycles; use the actual API directly.
        self.assertEqual(r.incremental_build(p, cycle).observation, old.observation)

    def test_forged_receipts_outputs_diagnostics_and_true_vs_one(self):
        p = example()
        old = self.parity(p)
        for mutation in ("winner", "body", "acceptance", "diagnostic", "evidence", "context", "shape"):
            with self.subTest(mutation=mutation):
                cache = deepcopy(old.cache)
                entry = cache["entries"][USER.token()]
                if mutation == "winner":
                    entry["candidate"]["calls"][0]["selection"]["winner"] = "forged"
                elif mutation == "body":
                    entry["candidate"]["body"]["literal"] = False  # Python False == 0.
                elif mutation == "acceptance":
                    entry["candidate"]["accepted"] = 1  # Python 1 == True.
                elif mutation == "diagnostic":
                    entry["candidate"]["diagnostics"] = ["FORGED_REJECTION"]
                elif mutation == "context":
                    entry["context"]["source"]["identity"]["package"] = "foreign-package"
                elif mutation == "shape":
                    entry["verified"] = True
                rehash(entry)
                if mutation == "evidence":
                    entry["evidence"] = {"verified": True}
                run = self.parity(p, cache)
                self.assertEqual(run.trace["fallback"], [USER.token()])
                self.assertNotIn(USER.token(), run.trace["reused"])

    def test_poisoned_success_cannot_hide_current_rejection_even_with_forged_snapshot(self):
        p = example()
        old = self.parity(p)
        bad = edit(p, USER, body=True)
        current = r.clean_build(bad)
        cache = deepcopy(old.cache)
        cache["snapshot"] = current.cache["snapshot"]  # Lie to the invalidation planner.
        entry = cache["entries"][USER.token()]
        entry["context"] = current.cache["entries"][USER.token()]["context"]
        rehash(entry)  # All hashes and context now match; the claimed result does not.
        run = self.parity(bad, cache)
        self.assertEqual(run.trace["invalidated"], [])
        self.assertIn(USER.token(), run.trace["fallback"])
        self.assertFalse(run.observation["accepted"])

    def test_stale_winner_cannot_hide_environment_change_with_all_metadata_rehashed(self):
        p = example()
        old = self.parity(p)
        changed = add_method(p, CORE, r.Method("linear", F, "Linear", body=42))
        current = r.clean_build(changed)
        cache = deepcopy(current.cache)
        entry = cache["entries"][USER.token()]
        entry["candidate"] = old.cache["entries"][USER.token()]["candidate"]
        rehash(entry)
        run = self.parity(changed, cache)
        self.assertEqual(run.trace["fallback"], [USER.token()])
        self.assertEqual(winner(run), r.DeclId(CORE, "linear").token())

    def test_arbitrary_omissions_and_foreign_entries_never_supply_authority(self):
        p = example()
        old = self.parity(p)
        foreign = r.clean_build(example(r.ModuleId("core-source-B", "ops")))
        for identity in (CORE, ADDON, BRIDGE, USER, QUIET):
            cache = deepcopy(old.cache)
            del cache["entries"][identity.token()]
            run = self.parity(p, cache)
            self.assertIn(identity.token(), run.trace["recomputed"])
        cache = deepcopy(old.cache)
        cache["entries"][USER.token()] = foreign.cache["entries"][USER.token()]
        run = self.parity(p, cache)
        self.assertIn(USER.token(), run.trace["fallback"])
        stale = deepcopy(old.cache)
        stale["entries"][USER.token()]["context"]["compiler"] = "old-compiler"
        rehash(stale["entries"][USER.token()])
        self.assertIn(USER.token(), self.parity(p, stale).trace["fallback"])


class GraphEnumerationTests(unittest.TestCase):
    def test_all_64_four_module_dags_and_each_single_body_edit(self):
        ids = tuple(r.ModuleId("p", str(i)) for i in range(4))
        possible = [(i, j) for i in range(4) for j in range(i)]
        count = 0
        for bits in product((False, True), repeat=len(possible)):
            edges = {edge for edge, present in zip(possible, bits) if present}
            modules = tuple(r.Module(ids[i], imports=tuple(ids[j] for j in range(i) if (i, j) in edges))
                            for i in range(4))
            p = r.Program(("p",), (r.Package("p", "display"),), modules)
            cache = r.clean_build(p).cache
            for target in range(4):
                for body in (7, True):  # Acceptance and rejection propagate through diamonds.
                    changed = edit(p, ids[target], body=body)
                    run = r.incremental_build(changed, cache)
                    self.assertEqual(run.observation, r.clean_build(changed).observation)
                    # Independent reachability via bounded adjacency-matrix powers.
                    reach = [[int(i == j or (i, j) in edges) for j in range(4)] for i in range(4)]
                    for k in range(4):
                        for i in range(4):
                            for j in range(4):
                                reach[i][j] |= reach[i][k] & reach[k][j]
                    affected = {ids[i].token() for i in range(4) if reach[i][target]}
                    self.assertEqual(set(run.trace["invalidated"]), affected)
                    self.assertEqual(set(run.trace["reused"]), {x.token() for x in ids} - affected)
                    self.assertEqual(run.observation["accepted"], type(body) is int)
                    count += 1
        self.assertEqual(count, 512)


if __name__ == "__main__":
    unittest.main()
