"""Verify the retained static LLVM and runtime ABI measurements on Linux and macOS."""
import json
import unittest

import run


class QualificationRecords(unittest.TestCase):
    def test_static_abi_records_bind_both_hosts_to_the_complete_fixture(self):
        template = (run.HERE / "program.ll.in").read_text()
        for directory, system, arch, triple_prefix in [
            ("macos-arm64", "Darwin", "arm64", "arm64-apple-darwin"),
            ("linux-x86_64", "Linux", "x86_64", "x86_64-unknown-linux-"),
        ]:
            with self.subTest(host=directory):
                path = run.HERE / "results" / directory
                report = json.loads((path / "qualification.json").read_bytes())
                self.assertEqual((report["host"]["system"], report["host"]["machine"]), (system, arch))
                self.assertEqual((report["status"], report["llvm_link_mode"]), ("passed", "static"))
                self.assertEqual((report["llvm"]["version"], report["llvm_sys"]), (run.LLVM_VERSION, "231.0.1"))
                self.assertEqual((report["lean"]["version"], report["lean"]["commit"]),
                                 (run.LEAN_VERSION, run.LEAN_COMMIT))
                self.assertEqual(report["openblas"]["version"], run.BLAS_VERSION)
                config = report["openblas"]["runtime_configuration"].split()
                self.assertIn("SINGLE_THREADED", config)
                self.assertNotIn("USE64BITINT", config)
                required = {"big_nat_square", "indexed_runtime", "sgemm", "dgemm", "cgemm", "zgemm"}
                self.assertLessEqual(required, set(report["checks"]))
                triple, layout = report["target"]["triple"], report["target"]["data_layout"]
                self.assertTrue(triple.startswith(triple_prefix), triple)
                module = path / "program.ll"
                self.assertEqual(module.read_bytes(), run.generated_ir(template, triple, layout))
                self.assertEqual((module.stat().st_size, run.digest(module)),
                                 (report["llvm"]["input_bytes"], report["llvm"]["input_sha256"]))
                for phase in ("backend_build", "llvm_object", "link", "execute"):
                    measured = report["phases"][phase]
                    self.assertEqual(measured["exit_code"], 0)
                    self.assertGreater(measured["max_child_rss_bytes"], 0)
                    self.assertGreater(measured["wall_seconds"], 0)
                for phase in ("reject_changed_bytes", "reject_parser", "reject_layout"):
                    self.assertNotEqual(report["phases"][phase]["exit_code"], 0)
                self.assertGreater(report["build_tree_bytes"], 0)
                self.assertGreater(report["backend_binary_bytes"], 0)
                self.assertGreater(report["artifacts"]["program"]["bytes"], 0)
                comparison = report["emitter_comparison"]
                self.assertEqual(comparison["sha256"],
                                 "635bb0e78a3703614b9f175b13f2a8e2adaa890fe7ed144bc33e6e67fab99414")
                self.assertTrue(comparison["fixtures"]["FamilyComparison"]["reference_results_checked"])
