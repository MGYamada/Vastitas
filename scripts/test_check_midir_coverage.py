"""Constructor additions/removals/signature changes must invalidate #750 coverage."""
import copy
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

import check_midir_coverage as guard

CORE = """\
import Init
namespace Example
inductive Ty where
  | nat | bool
  deriving Repr
structure Payload where
  value : Nat
  revision : Nat := 1
inductive Term where
  | literal (value : Nat)
  | call (arguments : List Term)
      (result : Ty)
  deriving Repr
end Example
"""
MANIFEST = """\
pub const KERNEL: Package = Package {
    name: "kernel runtime",
    directory: "",
    files: &["lakefile.toml"],
    forbidden: &["lakefile.lean"],
    modules: &["Kernel.First", "Kernel.Second"],
};
pub const OPTIONAL: Package = Package {
    name: "optional runtime",
    directory: "optional",
    files: &["runtime.c"],
    forbidden: &["lakefile.toml"],
    modules: &["Optional"],
};
const TOOLCHAIN_LIBRARIES: &[&str] = &["Init", "Std", "Lean", "Lake"];
"""


class ScannerTests(unittest.TestCase):
    def scan(self, source=CORE):
        return guard.scan_declarations(source, "Core.lean")

    def test_grouped_multiline_constructors_and_record_defaults(self):
        schema = self.scan()
        self.assertEqual([item["id"] for item in schema],
                         ["Example.Ty", "Example.Payload", "Example.Term"])
        self.assertEqual(len(schema[0]["constructors"]), 2)
        self.assertEqual(schema[1]["fields"], "value : Nat revision : Nat : = 1")
        self.assertEqual(schema[2]["constructors"][1]["signature"],
                         "call ( arguments : List Term ) ( result : Ty )")

    def test_comments_do_not_manufacture_constructors_or_declarations(self):
        source = CORE.replace("  | nat", "  /- nested /- | falseCtor -/ comment -/\n  | nat")
        source += '\n-- inductive Bogus where | notReal\n'
        self.assertEqual(self.scan(source), self.scan())

    def test_string_literals_cannot_manufacture_declarations(self):
        source = CORE + '\ndef ignored := "\ninductive Fake where\n  | fake\n"\n'
        self.assertEqual(self.scan(source), self.scan())

    def test_interpolated_nested_string_cannot_manufacture_declarations(self):
        source = CORE + '\ndef ignored := s!"{if true then "\ninductive Fake where\n | no\n" else ""}"\n'
        self.assertEqual(self.scan(source), self.scan())

    def test_literal_whitespace_is_not_normalized(self):
        self.assertNotEqual(guard.normalize('field : String := "a b"'),
                            guard.normalize('field : String := "a  b"'))
        self.assertNotEqual(guard.normalize('field : String := "a\nb"'),
                            guard.normalize('field : String := "a b"'))

    def test_namespace_and_mutual_inductives(self):
        source = """namespace Outer
namespace Inner
mutual
  inductive A where
    | mk (next : B)
  inductive B where
    | mk (next : A)
end
end Inner
end Outer
"""
        self.assertEqual([item["id"] for item in self.scan(source)], ["Outer.Inner.A", "Outer.Inner.B"])

    def test_private_record_and_sum_preserve_visibility_and_payload(self):
        source = "private structure Cursor where\n  index : Nat\nprivate inductive Kind where\n  | emit\n"
        cursor, kind = self.scan(source)
        self.assertEqual((cursor["header"], cursor["fields"]), ("private structure Cursor", "index : Nat"))
        self.assertEqual(kind["header"], "private inductive Kind")
        self.assertEqual([c["id"] for c in kind["constructors"]], ["Kind.emit"])

    def test_unsupported_syntax_and_incomplete_sources_fail_closed(self):
        cases = ["inductive A | mk", "unsafe inductive A where\n  | mk\n",
                 "inductive A where\n  | mk (value : Nat\n",
                 "inductive A where\n  | mk | mk\n", "/- unclosed",
                 "namespace A\ninductive B where\n  | mk\n",
                 "namespace A\nend B\n", "end A\n",
                 "inductive A where\n  | a\n| b\n", "@[special] inductive A where\n  | mk\n",
                 "  inductive A where\n    | mk\n"]
        for source in cases:
            with self.subTest(source=source), self.assertRaises(guard.CoverageError):
                self.scan(source)


class CoverageTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.write("lean-kernel/Core.lean", CORE)
        self.write("src/runtime_inputs.rs", MANIFEST)
        self.write("lean-kernel/lakefile.toml", 'name = "runtime"\n')
        self.write("lean-kernel/Kernel/First.lean", "import Kernel.Shared\nimport Init\n")
        self.write("lean-kernel/Kernel/Second.lean", "import Kernel.First\n")
        self.write("lean-kernel/Kernel/Shared.lean", "import Std\n")
        self.write("lean-kernel/optional/Optional.lean", "import Kernel.Shared\n")
        self.write("lean-kernel/optional/runtime.c", "void runtime(void) {}\n")
        self.patcher = patch.object(guard, "SOURCES", ("lean-kernel/Core.lean",))
        self.patcher.start()
        self.addCleanup(self.patcher.stop)
        self.ledger = guard.pending_ledger(self.root, "a" * 40)

    def write(self, path, value):
        target = self.root / path
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(value)

    def check(self, ledger=None, complete=False):
        return guard.validate(self.ledger if ledger is None else ledger,
                              guard.inventory(self.root), complete)

    def test_current_snapshot_is_covered_but_not_admitted(self):
        self.assertEqual(self.check(), {"pending": 4, "lowered": 0, "structural": 0, "admitted": 0, "rejected": 0})
        with self.assertRaisesRegex(guard.CoverageError, "not release acceptance"):
            self.check(complete=True)

    def test_add_remove_change_constructor_and_payload_all_fail(self):
        changes = [CORE.replace("| nat | bool", "| nat | bool | unit"),
                   CORE.replace("| nat | bool", "| nat"),
                   CORE.replace("(value : Nat)", "(value : Int)"),
                   CORE.replace("value : Nat\n", "value : Int\n"),
                   CORE.replace("revision : Nat := 1", "revision : Nat := 2"),
                   CORE.replace("namespace Example", "namespace Other").replace("end Example", "end Other"),
                   CORE.replace("inductive Ty where", "inductive Ty (n : Nat) where"),
                   CORE.replace("end Example", "inductive New where\n  | mk\nend Example")]
        for changed in changes:
            with self.subTest(source=changed):
                self.write("lean-kernel/Core.lean", changed)
                with self.assertRaisesRegex(guard.CoverageError, "source schema drift"):
                    self.check()

    def test_runtime_manifest_follows_all_roots_and_transitive_cross_package_imports(self):
        runtime = self.ledger["schema"]["runtime"]
        self.assertEqual([item["module"] for item in runtime["modules"]],
                         ["Kernel.First", "Kernel.Second", "Kernel.Shared", "Optional"])
        self.assertEqual(runtime["packages"][0]["modules"], ["Kernel.First", "Kernel.Second"])

    def test_new_runtime_root_and_import_change_fail(self):
        self.write("lean-kernel/Kernel/New.lean", "import Init\n")
        self.write("src/runtime_inputs.rs", MANIFEST.replace('"Kernel.Second"', '"Kernel.Second", "Kernel.New"'))
        with self.assertRaisesRegex(guard.CoverageError, "source schema drift"):
            self.check()
        self.write("src/runtime_inputs.rs", MANIFEST)
        self.write("lean-kernel/Kernel/First.lean", "import Kernel.New\nimport Init\n")
        with self.assertRaisesRegex(guard.CoverageError, "source schema drift"):
            self.check()

    def test_runtime_implementation_and_native_file_change_fail(self):
        for path, changed in [("lean-kernel/Kernel/Shared.lean", "import Std\ndef changed := 1\n"),
                              ("lean-kernel/optional/runtime.c", "void runtime(void) { abort(); }\n")]:
            with self.subTest(path=path):
                self.write(path, changed)
                with self.assertRaisesRegex(guard.CoverageError, "source schema drift"):
                    self.check()

    def test_manifest_implementation_change_requires_review_even_with_same_roots(self):
        self.write("src/runtime_inputs.rs", MANIFEST + "\nfn changed_selection() {}\n")
        with self.assertRaisesRegex(guard.CoverageError, "source schema drift"):
            self.check()

    def test_unregistered_import_and_missing_module_fail(self):
        for module, error in [("Foreign.Runtime", "unregistered external"), ("Kernel.Missing", "missing runtime module")]:
            self.write("lean-kernel/Kernel/Shared.lean", f"import {module}\n")
            with self.subTest(module=module), self.assertRaisesRegex(guard.CoverageError, error):
                self.check()

    def test_forbidden_or_missing_runtime_inputs_fail(self):
        self.write("lean-kernel/lakefile.lean", "import Lake\n")
        with self.assertRaisesRegex(guard.CoverageError, "forbidden runtime file"):
            self.check()
        (self.root / "lean-kernel/lakefile.lean").unlink()
        (self.root / "lean-kernel/optional/runtime.c").unlink()
        with self.assertRaisesRegex(guard.CoverageError, "missing runtime input"):
            self.check()

    def test_constructor_coverage_has_no_missing_unknown_or_duplicate_rows(self):
        changes = [lambda rows: rows.pop(), lambda rows: rows.append(copy.deepcopy(rows[0])),
                   lambda rows: rows[0].update(origin="Example.Ty.unknown")]
        for change in changes:
            ledger = copy.deepcopy(self.ledger)
            change(ledger["coverage"])
            with self.subTest(change=change), self.assertRaises(guard.CoverageError):
                self.check(ledger)

    def test_local_mappings_require_the_compiled_origin_and_opcode(self):
        ledger = copy.deepcopy(self.ledger)
        row = ledger["coverage"][0]
        row.update(disposition="lowered", planned_opcode="midir.unit.const.v1", evidence=[guard.LITERAL_THEOREM])
        self.assertEqual(self.check(ledger)["lowered"], 1)
        compiled = {"origin": row["origin"], "opcode": "unit.const.v1", "theorem": guard.LITERAL_THEOREM}
        guard.check_lowerings(ledger, [compiled])
        for forged in [[], [compiled, compiled], [{**compiled, "opcode": "bool.const.v1"}],
                       [{**compiled, "origin": "Example.Term.other"}], [{**compiled, "theorem": guard.FINITE_TAG_THEOREM}]]:
            with self.subTest(forged=forged), self.assertRaises(guard.CoverageError):
                guard.check_lowerings(ledger, forged)
        row["evidence"] = []
        with self.assertRaises(guard.CoverageError):
            self.check(ledger)

    def test_no_json_only_admission_or_wildcard_opcode(self):
        for fields in [{"disposition": "admitted"}, {"disposition": "unknown"},
                       {"planned_opcode": "midir.*"}, {"owner": ""}, {"reason": ""},
                       {"evidence": ["unchecked.lean"]}]:
            ledger = copy.deepcopy(self.ledger)
            ledger["coverage"][0].update(fields)
            with self.subTest(fields=fields), self.assertRaises(guard.CoverageError):
                self.check(ledger)

    def test_rejection_is_explicit_but_does_not_make_release_complete(self):
        ledger = copy.deepcopy(self.ledger)
        for row in ledger["coverage"]:
            row.update(disposition="rejected", reason="Outside this finite profile; no lowering exists.")
        self.assertEqual(self.check(ledger)["rejected"], 4)
        with self.assertRaises(guard.CoverageError):
            self.check(ledger, complete=True)

    def test_snapshot_commit_is_provenance_not_a_substitute_for_schema_digest(self):
        ledger = copy.deepcopy(self.ledger)
        ledger["snapshot"]["base_commit"] = "b" * 40
        self.assertEqual(self.check(ledger)["pending"], 4)
        ledger["snapshot"]["schema_sha256"] = "a" * 64
        with self.assertRaisesRegex(guard.CoverageError, "digest mismatch"):
            self.check(ledger)

    def test_recomputed_digest_does_not_hide_stale_source(self):
        ledger = copy.deepcopy(self.ledger)
        ledger["schema"]["declarations"][0]["fields"] += " fake : Nat"
        ledger["snapshot"]["schema_sha256"] = guard.digest(ledger["schema"])
        with self.assertRaisesRegex(guard.CoverageError, "source schema drift"):
            self.check(ledger)


class ManifestTests(unittest.TestCase):
    def test_manifest_comments_are_ignored_but_strings_are_not_commands(self):
        manifest = MANIFEST + '\n/* nested /* pub const FAKE: Package = Package {}; */ */\n'
        manifest += 'const TEXT: &str = "pub const FAKE: Package = Package {};";\n'
        self.assertEqual(guard.parse_runtime_manifest(manifest), guard.parse_runtime_manifest(MANIFEST))

    def test_nonliteral_partial_duplicate_or_unsafe_paths_fail_closed(self):
        for changed in [MANIFEST.replace('&["Optional"]', 'module_roots()'),
                        MANIFEST.replace('    name: "optional runtime",', ''),
                        MANIFEST.replace('pub const OPTIONAL:', 'pub const KERNEL:'),
                        MANIFEST.replace('name: "optional runtime",', 'name: "optional runtime", name: "again",'),
                        MANIFEST.replace('modules: &["Optional"]', 'modules: &["Optional", "Optional"]')]:
            with self.subTest(manifest=changed), self.assertRaises(guard.CoverageError):
                guard.parse_runtime_manifest(changed)
        for path in ["/private/source", "../escape", "native/../escape", "native\\escape"]:
            with self.subTest(path=path), self.assertRaises(guard.CoverageError):
                guard.relative_path(path)

    def test_duplicate_json_keys_fail(self):
        with self.assertRaisesRegex(guard.CoverageError, "duplicate JSON key"):
            json.loads('{"schema_version": 1, "schema_version": 2}', object_pairs_hook=guard.unique_json)


class RepositoryTests(unittest.TestCase):
    def test_repository_ledger_matches_all_current_origins(self):
        ledger = json.loads((guard.ROOT / guard.LEDGER).read_text())
        actual = guard.inventory(guard.ROOT)
        counts = guard.validate(ledger, actual)
        self.assertEqual(counts["admitted"], 0)
        self.assertGreater(counts["pending"], 100)
        identifiers = {item["id"] for item in actual["declarations"]}
        self.assertTrue({"VastitasKernel.Indexed.Declaration", "VastitasKernel.Indexed.Core.Term", "VastitasKernel.Indexed.Core.PureType",
                         "VastitasKernel.Indexed.Core.DataType", "VastitasKernel.Indexed.FiniteLookup",
                         "VastitasKernel.Indexed.FiniteLookup.Plan", "VastitasKernel.Indexed.FiniteLookup.Layout",
                         "VastitasKernel.Indexed.FiniteSort",
                         "VastitasKernel.MidIR.CallTarget", "VastitasKernel.MidIR.Opcode",
                         "VastitasKernel.ResourceSource.RealizationSite",
                         "VastitasKernel.Storage.Realization.Descriptor", "VastitasKernel.Storage.Realization.Plan",
                         "VastitasKernel.Storage.Functions.RealizationRunReceipt",
                         "VastitasKernel.Storage.Action",
                         "VastitasKernel.Storage.Native.Instruction", "VastitasKernel.Storage.Shapes.Extent",
                         "VastitasKernel.Storage.Shapes.Action", "VastitasKernel.Storage.Shapes.Event",
                         "VastitasKernel.Storage.Shapes.Numerical.Operation"} <= identifiers)
        origins = {entry["origin"] for entry in ledger["coverage"]}
        self.assertTrue({"VastitasKernel.MidIR.Opcode.call", "VastitasKernel.ResourceSource.Statement.realization",
                         "VastitasKernel.Storage.Realization.Operation.run",
                         "VastitasKernel.Storage.NumericalCoverage.Family.realizationRun"} <= origins)
        runtime = {item["module"] for item in actual["runtime"]["modules"]}
        self.assertTrue({"VastitasKernel.SpectralRuntime", "VastitasKernel.FrameRuntime"} <= runtime)

    def test_structural_rows_require_the_matching_proof_and_no_instruction(self):
        ledger = json.loads((guard.ROOT / guard.LEDGER).read_text())
        selected = [r for r in ledger["coverage"] if r["disposition"] == "structural"]
        self.assertEqual({r["origin"] for r in selected}, set(guard.STRUCTURAL_THEOREMS))
        compiled = [{"origin": r["origin"], "opcode": None, "theorem": r["evidence"][0]} for r in selected]
        guard.check_lowerings({"coverage": selected}, compiled)
        first, second = selected[:2]
        for fields in [{"planned_opcode": "midir.unit.const.v1"}, {"evidence": second["evidence"]}]:
            with self.subTest(fields=fields), self.assertRaisesRegex(guard.CoverageError, "structural lowering"):
                guard.validate({**ledger, "coverage": [{**r, **fields} if r is first else r
                                                       for r in ledger["coverage"]]}, ledger["schema"])
        for rows in [compiled[1:], [{**compiled[0], "opcode": "unit.const.v1"}, *compiled[1:]],
                     [{**compiled[0], "theorem": second["evidence"][0]}, *compiled[1:]]]:
            with self.subTest(rows=rows), self.assertRaisesRegex(guard.CoverageError, "compiled lowering differs"):
                guard.check_lowerings({"coverage": selected}, rows)

    def test_static_call_mapping_requires_the_exact_constructor_opcode_and_theorem(self):
        ledger = json.loads((guard.ROOT / guard.LEDGER).read_text())
        call = next(r for r in ledger["coverage"] if r["origin"] == guard.STATIC_CALL_ORIGIN)
        self.assertEqual(call["disposition"], "lowered")
        for changed in [{"planned_opcode": "midir.int.const.v1"}, {"evidence": [guard.LITERAL_THEOREM]}]:
            rows = [{**r, **changed} if r is call else r for r in ledger["coverage"]]
            with self.subTest(changed=changed), self.assertRaisesRegex(guard.CoverageError, "static call"):
                guard.validate({**ledger, "coverage": rows}, ledger["schema"])
        fake = {**call, "origin": "VastitasKernel.Term.call"}
        rows = [fake if r["origin"] == fake["origin"] else r for r in ledger["coverage"]]
        with self.assertRaisesRegex(guard.CoverageError, "missing checked local lowering"):
            guard.validate({**ledger, "coverage": rows}, ledger["schema"])

    def test_complete_cli_rejects_the_current_pending_inventory(self):
        run = subprocess.run([sys.executable, str(guard.ROOT / "scripts/check_midir_coverage.py"),
                              "--require-complete"], text=True, capture_output=True, check=False)
        self.assertEqual(run.returncode, 1)
        self.assertIn("not release acceptance", run.stderr)


if __name__ == "__main__":
    unittest.main()
