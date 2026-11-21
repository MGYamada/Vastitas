"""Verify the retained Official and nanoda workload measurements on Linux and macOS."""
import json
from pathlib import Path
import unittest

import run


class QualificationRecords(unittest.TestCase):
    def test_both_hosts_replayed_the_same_thousand_operation_exports(self):
        results = run.HERE / "results"
        for chunk, suffix in [(1000, ""), (64, "-chunk64")]:
            exports = []
            for prefix, system, machine in [
                ("macos-arm64", "Darwin", "arm64"),
                ("ci-macos-arm64", "Darwin", "arm64"),
                ("ci-linux-x86_64", "Linux", "x86_64"),
            ]:
                with self.subTest(host=prefix, chunk=chunk):
                    record = json.loads((results / f"{prefix}-1000{suffix}.json").read_bytes())
                    self.assertEqual((record["host"]["os"], record["host"]["machine"]), (system, machine))
                    self.assertEqual(record["toolchain"],
                                     {"lean": run.PIN, "commit": run.LEAN_COMMIT, "nanoda": "0.4.19"})
                    self.assertEqual((record["workload"]["operations"], record["workload"]["chunk_size"]),
                                     (1000, chunk))
                    self.assertEqual(record["status"], "passed")
                    self.assertEqual([p["phase"] for p in record["phases"]],
                                     ["elaboration", "official_replay", "export", "nanoda"])
                    for phase in record["phases"]:
                        self.assertEqual((phase["status"], phase["exit_code"], phase["timed_out"]),
                                         ("passed", 0, False))
                        self.assertGreater(phase["wall_seconds"], 0)
                        self.assertGreater(phase["peak_rss_bytes"], 0)
                    exports.append(record["export"]["sha256"])
            self.assertEqual(len(set(exports)), 1)

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
