"""Acceptance-boundary tests for the isolated reduction measurement runner."""
import importlib.util
import json
import os
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

spec = importlib.util.spec_from_file_location("reduction_run", Path(__file__).with_name("run.py"))
run = importlib.util.module_from_spec(spec)
spec.loader.exec_module(run)


class ExportBoundary(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.path = Path(self.directory.name) / "export.ndjson"
        self.target = "ReductionFixture.accepted0"
        # Structural scanner fixture only, never submitted as a real proof.
        self.records = [
            {"meta": {"exporter": {"name": "lean4export", "version": "3.1.0"},
                      "format": {"version": "3.1.0"},
                      "lean": {"githash": run.LEAN_COMMIT, "version": "4.35.0"}}},
            {"in": 1, "str": {"pre": 0, "str": "ReductionFixture"}},
            {"in": 2, "str": {"pre": 1, "str": "accepted0"}},
            {"thm": {"name": 2, "type": 0, "value": 0}},
        ]

    def inspect(self):
        self.path.write_text("".join(json.dumps(record) + "\n" for record in self.records))
        return run.inspect_export(self.path, [self.target])

    def test_structural_check_has_no_environment_authentication_claim(self):
        report = self.inspect()
        self.assertEqual(report["declarations"], 1)
        self.assertFalse(report["axiom_environment_authenticated"])

    def test_missing_requested_theorem_rejects_truncated_valid_prefix(self):
        self.records.pop()
        with self.assertRaisesRegex(ValueError, "missing requested theorem"):
            self.inspect()

    def test_renamed_or_non_theorem_target_rejects(self):
        self.records[-1] = {"def": {"name": 2, "type": 0, "value": 0, "safety": "safe"}}
        with self.assertRaisesRegex(ValueError, "missing requested theorem"):
            self.inspect()

    def test_unterminated_record_rejects(self):
        self.inspect()
        self.path.write_text(self.path.read_text().rstrip("\n"))
        with self.assertRaisesRegex(ValueError, "unterminated"):
            run.inspect_export(self.path, [self.target])

    def test_wrong_toolchain_metadata_rejects(self):
        self.records[0]["meta"]["lean"]["githash"] = "wrong"
        with self.assertRaisesRegex(ValueError, "metadata"):
            self.inspect()

    def test_duplicate_metadata_or_declaration_rejects(self):
        for record in (self.records[0], self.records[-1]):
            with self.subTest(record=record):
                self.records.append(record)
                with self.assertRaises(ValueError):
                    self.inspect()
                self.records.pop()

    def test_unapproved_even_unused_axiom_rejects(self):
        self.records += [
            {"in": 3, "str": {"pre": 0, "str": "forged"}},
            {"axiom": {"name": 3, "type": 0, "isUnsafe": False}},
        ]
        with self.assertRaisesRegex(ValueError, "unapproved axiom"):
            self.inspect()

    def test_rendered_name_spoof_rejects(self):
        self.records += [{"in": 3, "str": {"pre": 0, "str": "Classical.choice"}}]
        with self.assertRaisesRegex(ValueError, "dotted"):
            self.inspect()

    def test_unsafe_inductive_declaration_rejects(self):
        self.records += [
            {"in": 3, "str": {"pre": 0, "str": "Bad"}},
            {"inductive": {"types": [{"name": 3, "isUnsafe": True}], "ctors": [], "recs": []}},
        ]
        with self.assertRaisesRegex(ValueError, "unsafe"):
            self.inspect()

    def test_all_inductive_declarations_count_towards_checker_report(self):
        self.records += [
            {"in": 3, "str": {"pre": 0, "str": "Finite"}},
            {"in": 4, "str": {"pre": 3, "str": "mk"}},
            {"in": 5, "str": {"pre": 3, "str": "rec"}},
            {"inductive": {"types": [{"name": 3}], "ctors": [{"name": 4}], "recs": [{"name": 5}]}},
        ]
        self.assertEqual(self.inspect()["declarations"], 4)

    def test_unsupported_record_rejects(self):
        self.records.append({"future_declaration": {"name": 2}})
        with self.assertRaisesRegex(ValueError, "unknown"):
            self.inspect()


class ReportsAndWorkload(unittest.TestCase):
    def test_retained_records_bind_current_fixture_and_model(self):
        for path in sorted(Path(__file__).with_name("results").glob("*.json")):
            with self.subTest(record=path.name):
                report = json.loads(path.read_text())
                workload = report["workload"]
                text, targets = run.fixture(workload["operations"], workload["chunk_size"],
                                            workload["proof_method"])
                self.assertEqual(workload["model_sha256"], run.digest(run.HERE / "Model.lean"))
                self.assertEqual(workload["fixture_sha256"], run.hashlib.sha256(text.encode()).hexdigest())
                self.assertEqual(report["export"]["target_theorems"], targets)
                self.assertFalse(report["compiler_acceptance"])
                self.assertFalse(report["production_midir"])
                self.assertFalse(report["export"]["axiom_environment_authenticated"])
                self.assertEqual(report["phases"][-1]["checked_declarations"],
                                 report["export"]["declarations"])

    def test_preflight_failure_replaces_a_stale_success_record(self):
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory) / "report.json"
            output.write_text('{"status":"passed"}\n')
            with patch.object(sys, "argv", ["run.py", "--output", str(output)]):
                with patch.object(run, "toolchain", side_effect=ValueError("unavailable")):
                    self.assertEqual(run.main(), 2)
            report = json.loads(output.read_text())
            self.assertEqual(report["status"], "failed")
            self.assertEqual(report["phases"], [])

    def test_nanoda_report_requires_exact_count_and_no_diagnostics(self):
        self.assertEqual(run.checked_count("Checked 12 declarations with no errors\n", "", 12), 12)
        for output, errors, expected in (
            ("Checked 12 declarations with no errors", "", 12),
            ("Checked 12 declarations with no errors\n", "", 13),
            ("Checked 12 declarations with no errors\n", "warning", 12),
            ("Checked 0 declarations with no errors\n", "", 0),
            ("Checked 12 declarations with no errors\nextra", "", 12),
        ):
            with self.subTest(output=output, errors=errors):
                self.assertIsNone(run.checked_count(output, errors, expected))

    def test_workload_keeps_all_operations_and_exports_negative_theorems(self):
        text, targets = run.fixture(1000, 64, "decide")
        self.assertEqual(sum(line.startswith("def source") for line in text.splitlines()), 16)
        self.assertEqual(len(targets), 16 * 4 + 2)
        self.assertIn("theorem changedCall15", text)
        self.assertIn("theorem changedWitness15", text)
        self.assertIn("theorem forwardReference", text)
        self.assertIn("theorem wrongOperandType", text)
        # No target is defined by executing lower on the source artifact.
        self.assertNotIn(".map lower", text)
        self.assertNotIn("native_decide", text)

    def test_small_tail_is_merged_without_losing_operations(self):
        _, targets = run.fixture(65, 64, "rfl")
        self.assertEqual(len(targets), 6)

    def test_process_failure_and_timeout_cannot_be_reported_as_success(self):
        with tempfile.TemporaryDirectory() as directory:
            work = Path(directory)
            failed = run.measure([sys.executable, "-c", "raise SystemExit(7)"], work,
                                 dict(os.environ), "failure", 2)
            self.assertEqual(failed["exit_code"], 7)
            self.assertEqual(failed["status"], "failed")
            timed_out = run.measure([sys.executable, "-c", "import time; time.sleep(10)"],
                                    work, dict(os.environ), "timeout", 0.05)
            self.assertTrue(timed_out["timed_out"])
            self.assertNotEqual(timed_out["exit_code"], 0)


if __name__ == "__main__":
    unittest.main()
