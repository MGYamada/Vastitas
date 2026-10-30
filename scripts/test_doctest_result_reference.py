"""Result-contract regressions, not execution/proof of the fixture .vast inputs."""

import copy
import itertools
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

import doctest_result_reference as ref
from demo_doctest_result_reference import FIXTURE, cases, example


ROOT = Path(__file__).resolve().parents[1]


class ResultTests(unittest.TestCase):
    def setUp(self):
        self.expected, self.result = example()

    def assert_judgment(self, status, reason):
        report = ref.judge(self.expected, self.result)
        self.assertEqual((report["status"], report["reason"]), (status, reason), report)
        self.assertEqual(report["scope"], "reference_only")
        self.assertIs(report["registry_eligible"], False)
        return report

    def diagnostics(self, codes):
        values = [{"code": code, "message": "fixture"} for code in codes]
        self.result["diagnostics"] = values
        self.result["backend"]["response"]["diagnostics"] = copy.deepcopy(values)

    def test_ten_case_reference_table(self):
        expected = [("passed", "expected_rejection"), ("passed", "expected_rejection"),
                    ("failed", "protocol_mismatch"), ("failed", "integrity_unknown"),
                    ("failed", "infrastructure_failure"), ("failed", "interrupted"),
                    ("failed", "diagnostic_mismatch"), ("failed", "diagnostic_mismatch"),
                    ("failed", "accepted"), ("skipped", "not_run")]
        observed = []
        for name, self.expected, self.result in cases():
            with self.subTest(case=name):
                report = ref.judge(self.expected, self.result)
                observed.append((report["status"], report["reason"]))
                self.assertIs(report["registry_eligible"], False)
        self.assertEqual(observed, expected)

    def test_original_rust_regression_payload_is_preserved(self):
        # Keep an exact link to the existing mock response without running Rust.
        payload = FIXTURE.read_text(encoding="utf-8").strip()
        rust = (ROOT / "tests/driver_issues.rs").read_text(encoding="utf-8")
        rust = rust.split("fn mismatched_failure_version_preserves_diagnostics_but_success_is_rejected()", 1)[1]
        self.assertIn(payload.replace('"', '\\"'), rust)
        self.result["backend"]["response"] = ref.load_json(payload)
        self.result["diagnostics"] = copy.deepcopy(self.result["backend"]["response"]["diagnostics"])
        self.expected["codes"] = ["E_SENTINEL"]
        # A code-only check would pass; the result contract must not.
        self.assertEqual(self.expected["codes"], [d["code"] for d in self.result["diagnostics"]])
        report = self.assert_judgment("failed", "protocol_mismatch")
        self.assertEqual(report["result"]["backend"]["response"], json.loads(payload))
        self.assertEqual(report["result"]["diagnostics"][0]["message"], "original diagnostic")

    def test_frontend_rejection_requires_no_kernel_version_or_process(self):
        _, self.expected, self.result = next(cases())
        self.assert_judgment("passed", "expected_rejection")
        self.result["backend"]["request_version"] = 2
        self.assert_judgment("failed", "frontend_backend_inconsistent")

    def test_matching_supported_kernel_protocols(self):
        for version in range(2, 9):
            with self.subTest(version=version):
                self.result["backend"]["request_version"] = version
                self.result["backend"]["response"]["version"] = version
                self.assert_judgment("passed", "expected_rejection")
        self.result["backend"]["request_version"] = 99
        self.result["backend"]["response"]["version"] = 99
        self.assert_judgment("failed", "unsupported_protocol")

    def test_kernel_ok_false_does_not_override_abnormal_termination(self):
        for code in (None, 0, 2, -9, -11, 130, 143):
            with self.subTest(code=code):
                self.result["backend"]["exit_code"] = code
                self.assert_judgment("failed", "backend_termination_mismatch")
        self.result["backend"]["exit_code"] = 1
        for state in ("failed", "unknown", "not_reached"):
            self.result["backend"]["state"] = state
            self.assert_judgment("failed", "backend_termination_mismatch")

    def test_driver_termination_and_incomplete_capture_block_matching_codes(self):
        for code in (None, 0, 2, -9, 130, 143):
            self.result["driver_exit_code"] = code
            self.assert_judgment("failed", "driver_termination_mismatch")
        self.result["driver_exit_code"] = 1
        self.result["integrity"] = "unknown"
        self.assert_judgment("failed", "integrity_unknown")

    def test_unsupported_skipped_and_unknown_never_pass(self):
        for outcome, status in (("unsupported", "unsupported"), ("not_run", "skipped"),
                                ("unknown", "failed")):
            self.result["outcome"] = outcome
            self.assert_judgment(status, outcome)

    def test_codes_cannot_reclassify_infrastructure_or_unsupported_failures(self):
        codes = ("E_PROTOCOL", "E_BACKEND", "E_BUILD", "E_INPUT", "E_OUTPUT", "E_USAGE",
                 "E_ARGUMENT", "E_INTERRUPTED", "E_CODEGEN", "E_LIMIT", "E_DISPATCH_LIMIT",
                 "E_UNSUPPORTED", "E_INTERNAL_TYPE", "E_INTERNAL_AUTHORITY")
        for code in codes:
            with self.subTest(code=code):
                self.expected["codes"] = [code]
                self.diagnostics([code])
                self.assert_judgment("failed", "non_language_diagnostic")

    def test_every_binding_component_is_compared_to_independent_expectation(self):
        for key, value in self.expected["binding"].items():
            if key == "policy":
                continue
            with self.subTest(key=key):
                self.result["binding"][key] = "0" * 64 if key.endswith("_sha256") else value + ":stale"
                self.assert_judgment("failed", "binding_mismatch")
                self.result["binding"][key] = value
        self.result["binding"]["policy"] = "expected-rejection/2"
        self.assert_judgment("failed", "invalid_contract")

    def test_multiset_order_ignored_multiplicity_required(self):
        self.expected["codes"] = ["E_NAME", "E_TYPE", "E_NAME"]
        for codes in itertools.permutations(self.expected["codes"]):
            self.diagnostics(codes)
            self.assert_judgment("passed", "expected_rejection")
        self.diagnostics(["E_NAME", "E_TYPE"])
        report = self.assert_judgment("failed", "diagnostic_mismatch")
        self.assertEqual(report["missing_codes"], ["E_NAME"])
        self.diagnostics(["E_NAME", "E_NAME", "E_NAME", "E_TYPE", "E_PARSE"])
        report = self.assert_judgment("failed", "diagnostic_mismatch")
        self.assertEqual(report["unexpected_codes"], ["E_NAME", "E_PARSE"])

    def test_text_spans_and_notes_do_not_satisfy_expectations(self):
        self.expected["codes"] = ["E_TYPE"]
        diagnostic = self.result["diagnostics"][0]
        diagnostic["message"] = "E_TYPE: matches only in message text"
        diagnostic["notes"] = [{"message": "E_TYPE: matches only in a note"}]
        self.result["backend"]["response"]["diagnostics"] = copy.deepcopy(self.result["diagnostics"])
        self.assert_judgment("failed", "diagnostic_mismatch")
        self.expected["codes"] = ["E_NAME"]
        before = copy.deepcopy(self.result)
        report = self.assert_judgment("passed", "expected_rejection")
        self.assertEqual(report["result"], before)
        self.assertEqual(self.result, before)
        report["result"]["diagnostics"][0]["message"] = "changed output"
        self.assertEqual(self.result, before)

    def test_raw_response_or_other_path_cannot_stand_in_for_driver(self):
        report = ref.judge(self.expected, self.result["backend"]["response"])
        self.assertEqual((report["status"], report["reason"]), ("failed", "invalid_contract"))
        for path in ("raw_kernel", "stderr", "independent_evaluator", "unknown"):
            self.result["path"] = path
            self.assert_judgment("failed", "not_ordinary_driver_path")

    def test_response_and_report_cannot_disagree_or_filter_diagnostics(self):
        self.result["backend"]["response"]["diagnostics"].append({"code": "E_TYPE", "message": "extra"})
        self.assert_judgment("failed", "diagnostic_payload_mismatch")
        self.result["backend"]["response"]["diagnostics"] = []
        self.assert_judgment("failed", "diagnostic_payload_mismatch")
        self.result["diagnostics"] = []
        self.assert_judgment("failed", "missing_diagnostics")
        self.result["backend"]["response"]["ok"] = True
        self.assert_judgment("failed", "backend_not_rejected")

    def test_missing_unknown_and_wrongly_typed_fields_fail_closed(self):
        original = copy.deepcopy(self.result)
        for key in original:
            self.result = copy.deepcopy(original)
            del self.result[key]
            self.assert_judgment("failed", "invalid_contract")
        self.result = copy.deepcopy(original)
        self.result["verified"] = True
        self.assert_judgment("failed", "invalid_contract")
        for section, key, value in (("backend", "exit_code", True),
                                    ("backend", "request_version", True),
                                    ("backend", "response", []),
                                    ("binding", "input_sha256", "unknown")):
            self.result = copy.deepcopy(original)
            self.result[section][key] = value
            self.assert_judgment("failed", "invalid_contract")
        for version in (None, True, "2", 2.0):
            self.result = copy.deepcopy(original)
            self.result["backend"]["response"]["version"] = version
            self.assert_judgment("failed", "invalid_contract")
        self.result = copy.deepcopy(original)
        self.result["backend"]["response"]["diagnostics"][0]["span"]["start"] = 19.0
        self.assert_judgment("failed", "invalid_contract")

    def test_invalid_expectations_and_diagnostic_extensions(self):
        for codes in ([], ["*"], ["E_NAME: text"], [None], "E_NAME"):
            self.expected["codes"] = codes
            self.assert_judgment("failed", "invalid_contract")
        self.expected["codes"] = ["E_NAME"]
        self.expected["match"] = "subset"
        self.assert_judgment("failed", "invalid_contract")
        self.expected["match"] = "exact_code_multiset"
        self.result["diagnostics"][0]["severity"] = "warning"
        self.assert_judgment("failed", "invalid_contract")


class JsonAndCliTests(unittest.TestCase):
    def test_ambiguous_json_and_noninteger_numbers_fail_closed(self):
        for text in ('{"outcome":"accepted","outcome":"kernel_rejected"}',
                     '{"backend":{"exit_code":0,"exit_code":1}}', 'NaN', 'Infinity', '1e999', '2.0'):
            with self.subTest(text=text), self.assertRaises(ref.Invalid):
                ref.load_json(text)

    def test_cli_round_trip_statuses_exit_codes_and_invalid_json(self):
        with tempfile.TemporaryDirectory() as directory:
            expected_path = Path(directory) / "expectation.json"
            result_path = Path(directory) / "result.json"
            expectation, result = example()
            expected_path.write_text(json.dumps(expectation), encoding="utf-8")
            for outcome, status in (("kernel_rejected", "passed"), ("accepted", "failed"),
                                    ("not_run", "skipped"), ("unsupported", "unsupported")):
                result["outcome"] = outcome
                result_path.write_text(json.dumps(result), encoding="utf-8")
                run = subprocess.run([sys.executable, str(ROOT / "scripts/doctest_result_reference.py"),
                                      str(expected_path), str(result_path)], capture_output=True, text=True,
                                     timeout=10, check=False)
                self.assertEqual(run.returncode, 0 if status == "passed" else 1, run.stderr)
                report = json.loads(run.stdout)
                self.assertEqual(report["status"], status)
                self.assertIs(report["registry_eligible"], False)
            for malformed in ('{"schema":1,"schema":2}', '{"unexpected":1e999}', '{'):
                result_path.write_text(malformed, encoding="utf-8")
                run = subprocess.run([sys.executable, str(ROOT / "scripts/doctest_result_reference.py"),
                                      str(expected_path), str(result_path)], capture_output=True, text=True,
                                     timeout=10, check=False)
                self.assertEqual(run.returncode, 1, run.stderr)
                self.assertEqual(json.loads(run.stdout)["reason"], "invalid_input")


if __name__ == "__main__":
    unittest.main()
