"""Identity, uncertainty and actual-checker join/repair regression coverage."""

import copy
import itertools
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

import diagnostic_reference as dr
from demo_diagnostic_reference import dispatch_table, fixture, package_sources


ROOT = Path(__file__).resolve().parents[1]
CLI = ROOT / "target/debug/vastitas"
KERNEL = ROOT / "lean-kernel/.lake/build/bin/vastitas-kernel"


def failure():
    return {"version": 5, "ok": False, "diagnostics": [{
        "code": "E_DISPATCH_AMBIGUOUS", "message": "ambiguous dispatch for choose",
        "span": {"start": 1, "end": 10, "line": 2, "column": 3},
        "notes": [{"message": "first crossing method",
                   "span": {"start": 11, "end": 20, "line": 4, "column": 5}}]}]}


def reorder_objects(value):
    if isinstance(value, dict):
        return {k: reorder_objects(v) for k, v in reversed(list(value.items()))}
    if isinstance(value, list):
        return [reorder_objects(v) for v in value]
    return value


def revise(value, package):
    """Change every occurrence of one pin, including ordered trace references."""
    if isinstance(value, dict):
        for child in value.values():
            revise(child, package)
        if value.get("package") == package:
            value["revision"] = "r2"
    elif isinstance(value, list):
        for child in value:
            revise(child, package)


class DiagnosticReferenceTests(unittest.TestCase):
    def test_v1_fingerprint_vector(self):
        ids = dr.identities(fixture())
        self.assertEqual(ids["reference_occurrence_id"], "vastitas-reference-occurrence-v1:"
                         "a5508f1820cdaee8f4d921e71500dff893bd670c85c450cf0ec825161c405771")
        self.assertEqual(ids["semantic_issue_key"], "vastitas-reference-issue-v1:"
                         "76dbc53ef5595642f8c6d1fe4331052d4f6f724cfecfb8154fa0ec506c244e8d")

    def test_independent_contributions_join_and_owner_repair(self):
        for names in (("default",), ("default", "A"), ("default", "B"),
                      ("default", "A", "B", "repair")):
            table = dispatch_table(names)
            self.assertEqual(len(table), 16)
            self.assertTrue(all(len(winners) == 1 for winners in table.values()))
        joined = dispatch_table(("default", "A", "B"))
        self.assertEqual({key for key, winners in joined.items() if len(winners) == 2},
                         set(itertools.product(("Nat", "Int"), repeat=2)))
        self.assertEqual({winners for winners in joined.values() if len(winners) == 2}, {("A", "B")})
        record = fixture()
        self.assertEqual({r["declaration"] for r in record["semantic"]["conflict_set"]},
                         {"A.method-0", "B.method-0"})

    def test_24_order_and_location_variants_have_identical_bytes_and_ids(self):
        original = fixture()
        encoded, ids = dr.canonical_occurrence(original), dr.identities(original)
        count = 0
        for participants, reverse_conflicts, reverse_dependencies in itertools.product(
                itertools.permutations(original["semantic"]["participants"]), (False, True), (False, True)):
            record = copy.deepcopy(original)
            s = record["semantic"]
            s["participants"] = list(participants)
            if reverse_conflicts:
                s["conflict_set"].reverse()
                s["witness_keys"].reverse()
            if reverse_dependencies:
                s["environment"]["dependencies"].reverse()
                s["environment"]["dependency_edges"].reverse()
            record["presentation"]["source_path"] = f"/different/machine/{count}/source.vast"
            record["presentation"]["diagnostic"]["span"] = {
                "start": count, "end": count + 10, "line": count + 1, "column": 5}
            record["presentation"]["diagnostic"]["message"] = "Different explanation / 表示"
            record = dr.load_json(json.dumps(reorder_objects(record)))
            self.assertEqual(dr.canonical_occurrence(record), encoded)
            self.assertEqual(dr.identities(record), ids)
            count += 1
        self.assertEqual(count, 24)

    def test_only_declared_sets_are_deduplicated(self):
        record = fixture()
        original = dr.canonical_occurrence(record)
        s = record["semantic"]
        for name in ("participants", "conflict_set", "witness_keys"):
            s[name].append(copy.deepcopy(s[name][0]))
        for name in ("dependencies", "dependency_edges"):
            s["environment"][name].append(copy.deepcopy(s["environment"][name][0]))
        self.assertEqual(dr.canonical_occurrence(record), original)
        s["history"].append(copy.deepcopy(s["history"][-1]))
        self.assertNotEqual(dr.canonical_occurrence(record), original)

    def test_ordered_history_and_argument_positions_remain_significant(self):
        record = fixture()
        ids = dr.identities(record)
        record["semantic"]["history"].reverse()
        changed = dr.identities(record)
        self.assertNotEqual(changed["reference_occurrence_id"], ids["reference_occurrence_id"])
        self.assertEqual(changed["semantic_issue_key"], ids["semantic_issue_key"])
        # Identity serialization preserves order; it does not assert this reversed
        # trace is a valid loan history or revalidate it as a second checker.
        first, second = fixture(), fixture()
        first["semantic"]["witness_keys"] = [["Nat", "Int"]]
        second["semantic"]["witness_keys"] = [["Int", "Nat"]]
        self.assertNotEqual(dr.canonical_occurrence(first), dr.canonical_occurrence(second))

    def test_revision_environment_and_toolchain_changes_do_not_reuse_exact_id(self):
        original = fixture()
        ids = dr.identities(original)
        variants = []
        changed = copy.deepcopy(original)
        revise(changed, "fixture:addon")
        variants.append(changed)
        for field in ("input_revision", "environment_revision", "compiler_revision", "toolchain_revision"):
            changed = copy.deepcopy(original)
            changed["semantic"]["environment"][field] = "other:r2"
            variants.append(changed)
        for record in variants:
            self.assertNotEqual(dr.identities(record)["reference_occurrence_id"], ids["reference_occurrence_id"])
            self.assertEqual(dr.identities(record)["semantic_issue_key"], ids["semantic_issue_key"])
        changed = copy.deepcopy(original)
        changed["semantic"]["environment"]["dependency_edges"].pop()
        self.assertNotEqual(dr.canonical_occurrence(changed), dr.canonical_occurrence(original))

    def test_different_obligation_holder_or_participant_cannot_alias(self):
        original = fixture()
        variants = []
        for path in (("obligation", "id"), ("holder", "subject", "declaration"),
                     ("assembly", "declaration"), ("function", "declaration")):
            changed = copy.deepcopy(original)
            target = changed["semantic"]
            for key in path[:-1]:
                target = target[key]
            target[path[-1]] = "different"
            variants.append(changed)
        changed = copy.deepcopy(original)
        changed["semantic"]["participants"].append({"role": "method_contributor", "status": "unresolved",
            "basis": "reference_fixture", "subject": {"package": "fixture:addon", "revision": "r1",
                                                        "declaration": "C.method-0"}})
        changed["semantic"]["conflict_set"].append(changed["semantic"]["participants"][-1]["subject"])
        variants.append(changed)
        for record in variants:
            self.assertNotEqual(dr.canonical_occurrence(original), dr.canonical_occurrence(record))

    def test_candidate_hints_never_change_identity_or_become_verified(self):
        record = fixture()
        ids = dr.identities(record)
        record["external_candidates"] = [{"role": "current_obligation_holder", "status": "candidate",
            "basis": "external_heuristic", "hint": "git history suggests a person; not semantic evidence"}]
        self.assertEqual(dr.identities(record), ids)
        self.assertNotIn("git history suggests a person", dr.render(record))
        self.assertEqual(dr.machine_report(record)["record"]["external_candidates"][0]["status"], "candidate")
        record["external_candidates"][0]["status"] = "verified"
        with self.assertRaises(dr.Invalid):
            dr.identities(record)

    def test_one_record_drives_human_and_machine_projections_without_mutation(self):
        record = fixture()
        original = copy.deepcopy(record)
        rendered, machine = dr.render(record), dr.machine_report(record)
        self.assertEqual(record, original)
        self.assertEqual(machine["record"], original)
        for text in ("E_DISPATCH_AMBIGUOUS", "dispatch_unique", "A.method-0", "B.method-0",
                     "root-assembly", "unresolved", machine["identity"]["reference_occurrence_id"]):
            self.assertIn(text, rendered)
        self.assertIsNone(machine["identity"]["diagnostic_occurrence_id"])
        machine["record"]["semantic"]["code"] = "MUTATED"
        self.assertEqual(record, original)

    def test_rejects_forged_roles_unknown_profiles_and_unpinned_ids(self):
        mutations = [
            lambda r: r["semantic"]["holder"].update(status="verified"),
            lambda r: r["semantic"]["participants"][0].update(basis="checked_authority"),
            lambda r: r["semantic"].update(cause="fixture:addon"),
            lambda r: r.update(origin="checker_ledger"),
            lambda r: r.update(schema="unknown/2"),
            lambda r: r["semantic"]["environment"].update(profile="unsupported/2"),
            lambda r: r["semantic"]["environment"].update(input_revision="/home/somebody/file"),
            lambda r: r["semantic"]["environment"].update(dependencies=[]),
            lambda r: r["semantic"]["participants"].pop(),
            lambda r: r["semantic"].update(outcome="accepted"),
        ]
        for mutation in mutations:
            record = fixture()
            mutation(record)
            with self.assertRaises(dr.Invalid):
                dr.render(record)

    def test_kernel_adapter_preserves_all_rejections_notes_and_unknown_roles(self):
        response = failure()
        second = copy.deepcopy(response["diagnostics"][0])
        second["code"] = "E_OWNER"
        response["diagnostics"].append(second)
        original = copy.deepcopy(response)
        records = dr.from_kernel_response(response, 5)
        self.assertEqual(len(records), 2)
        for diagnostic, record in zip(response["diagnostics"], records):
            self.assertEqual(record["presentation"]["diagnostic"], diagnostic)
            self.assertEqual(record["semantic"]["holder"]["status"], "unresolved")
            self.assertIsNone(record["semantic"]["holder"]["subject"])
            self.assertEqual(record["semantic"]["outcome"], "rejected")
            self.assertIsNone(dr.canonical_occurrence(record))
            self.assertIsNone(dr.identities(record)["reference_occurrence_id"])
            self.assertIsNone(dr.identities(record)["semantic_issue_key"])
            self.assertIn(diagnostic["message"], dr.render(record))
            self.assertIn(diagnostic["notes"][0]["message"], dr.render(record))
        self.assertEqual(response, original)

    def test_kernel_adapter_never_certifies_claimed_ledger_or_wrong_version(self):
        for key, value in (("ok", True), ("ok", 0), ("version", True), ("version", 6),
                           ("diagnostics", []), ("ledger", {"owner": "asserted"})):
            response = failure()
            response[key] = value
            with self.assertRaises(dr.Invalid):
                dr.from_kernel_response(response, 5)
        response = failure()
        response["diagnostics"][0]["holder"] = {"status": "verified"}
        with self.assertRaises(dr.Invalid):
            dr.from_kernel_response(response, 5)
        partial = dr.from_kernel_response(failure(), 5)[0]
        partial["semantic"]["holder"]["subject"] = fixture()["semantic"]["assembly"]
        with self.assertRaises(dr.Invalid):
            dr.machine_report(partial)

    def test_duplicate_json_keys_and_nonfinite_values_are_not_silently_normalized(self):
        for source in ('{"status":"candidate","status":"verified"}', '{"nested":{"a":1,"a":2}}',
                       '{"value":NaN}', '{"value":Infinity}'):
            with self.assertRaises(dr.Invalid):
                dr.load_json(source)

    def test_demo_json_and_captured_failure_exit_status(self):
        demo = subprocess.run([sys.executable, str(ROOT / "scripts/demo_diagnostic_reference.py"), "--json"],
                              capture_output=True, text=True, check=True)
        self.assertEqual(json.loads(demo.stdout), dr.machine_report(fixture()))
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "response.json"
            path.write_text(json.dumps(failure()))
            result = subprocess.run([sys.executable, str(ROOT / "scripts/demo_diagnostic_reference.py"),
                                     "--kernel-response", str(path), "--expected-version", "5", "--json"],
                                    capture_output=True, text=True)
            self.assertEqual(result.returncode, 1)
            self.assertEqual(json.loads(result.stdout)["record"]["semantic"]["outcome"], "rejected")


@unittest.skipUnless(CLI.is_file() and KERNEL.is_file(), "build Rust CLI and Lean kernel for live integration")
class LiveCheckerTests(unittest.TestCase):
    def test_separate_contributions_join_rejection_and_repair_use_actual_checker(self):
        with tempfile.TemporaryDirectory(prefix="vastitas diagnostic ") as directory:
            root = Path(directory)
            # Transparent test tap: forward exact request/response bytes, mode and
            # exit code. It never fabricates a successful or failed kernel result.
            proxy = root / "capture-kernel"
            proxy.write_text(f'''#!{sys.executable}
import pathlib, subprocess, sys
root = pathlib.Path({str(root)!r})
data = sys.stdin.buffer.read()
(root / "request.json").write_bytes(data)
result = subprocess.run([{str(KERNEL)!r}, *sys.argv[1:]], input=data, capture_output=True)
(root / "response.json").write_bytes(result.stdout)
sys.stdout.buffer.write(result.stdout)
sys.stderr.buffer.write(result.stderr)
sys.exit(result.returncode)
''')
            proxy.chmod(0o700)
            env = dict(os.environ, VASTITAS_KERNEL=str(proxy))
            for names, repair, accepted in ((("A",), False, True), (("B",), False, True),
                                             (("A", "B"), False, False), (("A", "B"), True, True)):
                for name, source in package_sources(names, repair).items():
                    path = root / name
                    path.parent.mkdir(parents=True, exist_ok=True)
                    path.write_text(source)
                result = subprocess.run([str(CLI), "check", "--manifest-path", str(root / "app/Vastitas.toml")],
                                        env=env, capture_output=True, text=True, timeout=60)
                self.assertEqual(result.returncode == 0, accepted, result.stderr)
                response = dr.load_json((root / "response.json").read_text())
                request = dr.load_json((root / "request.json").read_text())
                self.assertEqual(response["ok"], accepted)
                if not accepted:
                    self.assertEqual(response["diagnostics"][0]["code"], "E_DISPATCH_AMBIGUOUS")
                    record = dr.from_kernel_response(response, request["version"])[0]
                    self.assertIn("E_DISPATCH_AMBIGUOUS", result.stderr)
                    self.assertEqual(record["presentation"]["diagnostic"], response["diagnostics"][0])
                    self.assertEqual(record["semantic"]["holder"]["status"], "unresolved")
                    self.assertIsNone(dr.identities(record)["diagnostic_occurrence_id"])


if __name__ == "__main__":
    unittest.main()
