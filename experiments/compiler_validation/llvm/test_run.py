"""Dependency-independent negative tests for the qualification harness."""
import argparse
from copy import deepcopy
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

import run
import run_exit


class QualificationTests(unittest.TestCase):
    def test_assembled_fixture_requires_the_contribution_and_all_three_current_symbols(self):
        case = run_exit.CASES["assembled-bool"]
        text = (run.ROOT / "llvm/fixtures" / case.source).read_bytes()
        with tempfile.TemporaryDirectory() as tmp:
            work = Path(tmp)
            args, manifest = run_exit.prepare_case(work, case, text)
            self.assertEqual(args, ["--manifest-path", manifest])
            self.assertEqual((work / "main.vast").read_bytes(), text)
            root = str(manifest.resolve())
            package = {"source": root, "name": case.package, "version": "0.1.0"}
            def owner(name):
                return {"module": [], "name": name, "package": package}
            def symbol(core, name, definition):
                return {"core": core, "id": owner(name), "specialization": {"definition": definition, "targets": []}}
            symbols = [symbol(0, "choose", 2), symbol(1, "main", 0), symbol(2, "choose", 1)]
            receipt = {
                "input": {"file": root, "version": 10, "root": root,
                          "root_source": {"offset": len(manifest.read_bytes()) + 1, "text": text.decode()},
                          "packages": [{**package, "edition": "2026", "dependencies": []}]},
                "families": [{"id": owner("main"), "definition": 0},
                             {"id": owner("choose"), "dispatch": [{"key": [2], "selected": {"definition": 2, "ordinal": 1,
                              "origin": {"contribution": owner("winner"), "index": 0}}}]}],
                "pure": {"operator_sites": [], "symbols": symbols,
                         "dispatch_calls": [{"id": owner("choose"), "key": [2], "method": 1,
                                             "caller": 0, "caller_targets": [], "core": 0, "definition": 2}],
                         "calls": [{"caller": 0, "caller_targets": [], "core": 0, "definition": 2, "targets": []}]},
            }
            self.assertEqual(run_exit.checked_sites(receipt, case, text.decode(), manifest), [])
            summary = run_exit.checked_dispatch(receipt, case, manifest)
            self.assertEqual(summary["selected_core"], 0)
            self.assertNotIn(root, json.dumps(summary))
            for path, value in [
                (("families", 1, "dispatch", 0, "selected", "origin", "contribution", "name"), "loser"),
                (("pure", "dispatch_calls", 0, "method"), 0),
                (("pure", "calls", 0, "core"), 2),
                (("pure", "symbols", 2, "specialization", "definition"), 2),
                (("pure", "symbols"), symbols[:2]),
                (("input", "packages", 0, "source"), "wrong-root"),
            ]:
                tampered = deepcopy(receipt)
                field = tampered
                for part in path[:-1]:
                    field = field[part]
                field[path[-1]] = value
                with self.subTest(path=path), self.assertRaises(ValueError):
                    run_exit.checked_dispatch(tampered, case, manifest)
            receipt["input"]["root_source"]["offset"] -= 1
            with self.assertRaisesRegex(ValueError, "physical fixture"):
                run_exit.checked_sites(receipt, case, text.decode(), manifest)

    def test_status_fixture_requires_original_source_and_canonical_operator_keys(self):
        case = run_exit.CASES["folded-arithmetic"]
        text = (run.ROOT / "llvm/fixtures" / case.source).read_text()
        package = {"source": "vastitas:compat:operators", "name": "std", "version": "2026.0.0"}
        sites = [
            {"core": 0, "id": {"name": name, "module": ["operator"], "package": package},
             "key": list(key)}
            for name, key in case.operators
        ]
        receipt = {"input": {"file": case.source, "version": 10, "root": "vastitas:compat:flat",
                             "root_source": {"offset": 0, "text": text}},
                   "pure": {"operator_sites": sites}}
        self.assertEqual(run_exit.checked_sites(receipt, case, text), sites)
        with self.assertRaisesRegex(ValueError, "physical fixture"):
            run_exit.checked_sites(receipt, case, text + "\n")
        sites[-1]["key"].reverse()
        with self.assertRaisesRegex(ValueError, "argument keys"):
            run_exit.checked_sites(receipt, case, text)
        package["source"] = "unrelated"
        with self.assertRaisesRegex(ValueError, "owner"):
            run_exit.checked_sites(receipt, case, text)

    def test_target_fields_cannot_inject_ir(self):
        template = 'target triple = "@TRIPLE@"\ntarget datalayout = "@LAYOUT@"\n'
        with self.assertRaises(ValueError):
            run.generated_ir(template, 'aarch64"\ndefine i32 @attack()', 'e-p:64:64')
        with self.assertRaises(ValueError):
            run.generated_ir(template, 'aarch64-apple-darwin', 'e-p:64:64"\n')

    def test_patch_version_is_not_silently_accepted(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            (root / "llvm/bin").mkdir(parents=True)
            config = root / "llvm/bin/llvm-config"
            config.write_text('#!/bin/sh\nprintf "23.1.5\\n"\n')
            config.chmod(0o700)
            args = argparse.Namespace(llvm_prefix=root / "llvm", lean_prefix=root / "lean",
                openblas_prefix=root / "blas", output=root / "result", target_dir=None,
                link_mode="static", allow_cargo_downloads=False)
            self.assertEqual(run.run(args), 1)
            report = json.loads((root / "result/report.json").read_text())
            self.assertEqual(report["status"], "blocked")
            self.assertIn("23.1.5", report["failure"])
            self.assertFalse((root / "result/target").exists())
            self.assertFalse((root / "result/program.o").exists())

    def test_existing_output_is_preserved(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            original = root / "report.json"
            original.write_text("keep this evidence")
            args = argparse.Namespace(llvm_prefix=root, lean_prefix=root,
                openblas_prefix=root, output=root)
            with self.assertRaisesRegex(ValueError, "empty"):
                run.run(args)
            self.assertEqual(original.read_text(), "keep this evidence")

    def test_measurement_preserves_child_failure(self):
        with tempfile.TemporaryDirectory() as temporary:
            report = Path(temporary) / "measure.json"
            result = subprocess.run([sys.executable, str(run.HERE / "measure.py"), str(report), "--",
                                     sys.executable, "-c", "raise SystemExit(7)"], capture_output=True)
            self.assertEqual(result.returncode, 7)
            measured = json.loads(report.read_text())
            self.assertEqual(measured["exit_code"], 7)
            self.assertGreater(measured["max_child_rss_bytes"], 0)
            self.assertGreaterEqual(measured["wall_seconds"], 0)


if __name__ == "__main__":
    unittest.main()
