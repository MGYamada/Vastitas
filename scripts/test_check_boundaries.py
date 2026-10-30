"""Regression checks for the dependency-boundary CI gate."""
import json
from pathlib import Path
import tempfile
import unittest

from check_boundaries import MATHLIB_REVISION, check_boundaries, lean_imports, module_allowed


class ImportScannerTests(unittest.TestCase):
    def test_checks_all_imports_and_real_modifiers(self):
        source = """module
prelude
public import Std.Data.HashMap
meta import Lean.Parser
public meta import Lean.Elab
import all Lean.Meta
import Std Mathlib
import Init import VastitasKernel.Core
"""
        self.assertEqual(lean_imports(source), [
            "Std.Data.HashMap", "Lean.Parser", "Lean.Elab", "Lean.Meta",
            "Std", "Mathlib", "Init", "VastitasKernel.Core",
        ])

    def test_comments_cannot_hide_imports_or_create_false_imports(self):
        source = """/- import Mathlib /- nested import Bad -/ -/
module
-- import Forbidden
public /- note /- nested -/ -/ meta import /- multi
line comment -/ Mathlib.Data.Real.Basic -- import Hidden
import Std /- between commands -/ import Lean
def sample : String := "import Secret /-"
"""
        self.assertEqual(lean_imports(source), ["Mathlib.Data.Real.Basic", "Std", "Lean"])

    def test_stops_before_declaration_strings_and_quotations(self):
        source = '''import Std
def example := "
import Mathlib
/- not a comment inside a string
"
'''
        self.assertEqual(lean_imports(source), ["Std"])
        self.assertEqual(lean_imports("import Std theorem p : True := by trivial"), ["Std"])

    def test_exact_roots_and_quoted_module_names(self):
        roots = {"Std", "Lean", "VastitasKernel"}
        for name in ["Std", "Std.Data", "Lean.Parser", "VastitasKernel.Core", "«Std».Data", "Std.«a.b»"]:
            self.assertTrue(module_allowed(name, roots), name)
        for name in ["StdEvil", "LeanOracle", "VastitasKernelExtra", "Mathlib", "«Std.Mathlib»", "«StdEvil»"]:
            self.assertFalse(module_allowed(name, roots), name)
        self.assertEqual(lean_imports("import «Std».«a.b»\nimport «Mathlib»"), ["«Std».«a.b»", "«Mathlib»"])

    def test_malformed_headers_fail_closed(self):
        for source in ["import", "import all", "import /- never closed", "import Std\n/- never closed"]:
            with self.assertRaises(ValueError, msg=source):
                lean_imports(source)


class RepositoryBoundaryTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name)
        self.write("lean-kernel/lean-toolchain", "leanprover/lean4:v4.35.0\n")
        self.write("lean-kernel/lake-manifest.json", json.dumps({"packages": []}))
        self.write("lean-kernel/VastitasKernel/Runtime.lean", "import Init\n")

    def write(self, name, text):
        path = self.root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)

    def test_kernel_can_be_checked_without_an_oracle(self):
        self.write("lean-kernel/VastitasKernel/Core.lean", "import Std\n")
        self.write("lean-kernel/.lake/packages/Other/Imported.lean", "import Forbidden\n")
        self.assertEqual(check_boundaries(self.root), [])

    def test_second_import_and_prefix_lookalike_are_rejected(self):
        self.write("lean-kernel/VastitasKernel/Core.lean", "import Std Mathlib\nimport StdEvil\n")
        errors = check_boundaries(self.root)
        self.assertTrue(any("forbidden import Mathlib" in error for error in errors))
        self.assertTrue(any("forbidden import StdEvil" in error for error in errors))

    def test_promotion_fixture_library_cannot_enter_the_compiler(self):
        self.write("lean-kernel/VastitasPromotion/Regression.lean",
                   "import VastitasPromotion.Fixture\nimport VastitasKernel.Core\n")
        self.assertEqual(check_boundaries(self.root), [])
        self.write("lean-kernel/VastitasKernel/Core.lean", "import VastitasPromotion.Fixture\n")
        self.assertTrue(any("forbidden import VastitasPromotion.Fixture" in error
                            for error in check_boundaries(self.root)))
        self.write("lean-kernel/VastitasPromotion/Fixture.lean", "import Mathlib\n")
        self.assertTrue(any("forbidden import Mathlib" in error
                            for error in check_boundaries(self.root)))

    def test_runtime_cannot_import_compiler_or_external_packages(self):
        self.write("lean-kernel/VastitasKernel/Runtime.lean", "import Lean\nimport VastitasKernel.Core\n")
        self.write("lean-kernel/VastitasKernel/IndexedRuntime.lean", "import VastitasKernel.IndexedCore\n")
        self.write("lean-kernel/lake-manifest.json", json.dumps({"packages": [{"name": "mathlib"}]}))
        errors = check_boundaries(self.root)
        self.assertTrue(any("no external Lake" in error for error in errors))
        self.assertEqual(sum("runtime must not import" in error for error in errors), 3)

    def test_storage_fixtures_stay_within_the_test_library(self):
        self.write("lean-kernel/VastitasStorageTest/Regression.lean",
                   "import VastitasStorageTest.NumericalFixture\nimport VastitasKernel.Storage\n")
        self.assertEqual(check_boundaries(self.root), [])
        self.write("lean-kernel/VastitasKernel/Storage.lean", "import VastitasStorageTest.NumericalFixture\n")
        self.write("lean-kernel/VastitasStorageTestExtra/Bad.lean", "import VastitasStorageTest.NumericalFixture\n")
        self.write("lean-kernel/VastitasStorageTest/NumericalFixture.lean", "import Mathlib\n")
        errors = check_boundaries(self.root)
        self.assertEqual(sum("forbidden import VastitasStorageTest.NumericalFixture" in e for e in errors), 2)
        self.assertTrue(any("forbidden import Mathlib" in e for e in errors))

    def test_missing_runtime_cannot_silently_pass(self):
        (self.root / "lean-kernel/VastitasKernel/Runtime.lean").unlink()
        self.assertIn("kernel runtime source is missing", check_boundaries(self.root))

    def native_package(self):
        self.write("lean-kernel/native/lean-toolchain", "leanprover/lean4:v4.35.0\n")
        self.write("lean-kernel/native/lake-manifest.json", json.dumps({"packages": []}))
        self.write("lean-kernel/native/lakefile.lean", "import Lake\n")
        self.write("lean-kernel/native/VastitasStorageNative.lean", "import VastitasStorageNative.Runtime\n")
        self.write("lean-kernel/native/VastitasStorageNative/Runtime.lean", "import Init\n")

    def test_optional_native_runtime_cannot_enter_compiler_or_import_it(self):
        self.native_package()
        self.assertEqual(check_boundaries(self.root), [])
        self.write("lean-kernel/VastitasKernel/Core.lean", "import VastitasStorageNative.Runtime\n")
        self.write("lean-kernel/native/VastitasStorageNative/Runtime.lean", "import VastitasKernel.Core\n")
        self.write("lean-kernel/native/Other.lean", "import Lake\nimport Mathlib\n")
        errors = check_boundaries(self.root)
        for expected in ["forbidden import VastitasStorageNative", "runtime must not import compiler",
                         "forbidden import Lake", "forbidden import Mathlib"]:
            self.assertTrue(any(expected in error for error in errors), expected)

    def test_native_runtime_dependencies_and_toolchain_are_pinned(self):
        self.native_package()
        self.write("lean-kernel/native/lean-toolchain", "leanprover/lean4:v4.34.0\n")
        self.write("lean-kernel/native/lake-manifest.json", json.dumps({"packages": [{"name": "mathlib"}]}))
        errors = check_boundaries(self.root)
        self.assertTrue(any("native storage runtime and kernel" in error for error in errors))
        self.assertTrue(any("native storage runtime must have no external" in error for error in errors))

    def numerical_package(self):
        self.native_package()
        self.write("lean-kernel/numerical/lean-toolchain", "leanprover/lean4:v4.35.0\n")
        self.write("lean-kernel/numerical/lakefile.lean", "import Lake\n")
        self.write("lean-kernel/numerical/VastitasGemmNative.lean", "import VastitasStorageNative\n")
        self.write("lean-kernel/numerical/lake-manifest.json", json.dumps({"packages": [{
            "type": "path", "name": "vastitas_storage_native", "dir": "../native"}]}))

    def test_gemm_runtime_does_not_enter_normal_compiler_or_storage(self):
        self.numerical_package()
        self.assertEqual(check_boundaries(self.root), [])
        for path in ["lean-kernel/VastitasKernel/Core.lean", "lean-kernel/native/Extra.lean"]:
            self.write(path, "import VastitasGemmNative\n")
        self.write("lean-kernel/numerical/Extra.lean", "import VastitasKernel.Storage\nimport Mathlib\n")
        errors = check_boundaries(self.root)
        self.assertEqual(sum("forbidden import VastitasGemmNative" in e for e in errors), 2)
        self.assertTrue(any("forbidden import VastitasKernel.Storage" in e for e in errors))
        self.assertTrue(any("forbidden import Mathlib" in e for e in errors))

    def test_gemm_runtime_cannot_redirect_its_native_dependency(self):
        self.numerical_package()
        self.write("lean-kernel/numerical/lake-manifest.json", json.dumps({"packages": [{
            "type": "path", "name": "vastitas_storage_native", "dir": "../forged"}]}))
        self.write("lean-kernel/numerical/lean-toolchain", "leanprover/lean4:v4.34.0\n")
        errors = check_boundaries(self.root)
        self.assertTrue(any("sibling native storage" in e for e in errors))
        self.assertTrue(any("numerical runtime and kernel" in e for e in errors))

    def test_root_and_oracle_toolchains_must_match_kernel(self):
        self.write("lean-toolchain", "leanprover/lean4:v4.34.0\n")
        self.write("lean/lean-toolchain", "leanprover/lean4:v4.34.0\n")
        self.write("lean/lake-manifest.json", json.dumps({"packages": [{"name": "mathlib", "rev": MATHLIB_REVISION}]}))
        errors = check_boundaries(self.root)
        self.assertTrue(any("root and kernel" in error for error in errors))
        self.assertTrue(any("kernel and oracle" in error for error in errors))

    def test_oracle_revision_remains_pinned(self):
        self.write("lean/lean-toolchain", "leanprover/lean4:v4.35.0\n")
        self.write("lean/lake-manifest.json", json.dumps({"packages": [{"name": "mathlib", "rev": "wrong"}]}))
        self.assertIn("oracle mathlib must be pinned to the v4.35.0 commit", check_boundaries(self.root))


if __name__ == "__main__":
    unittest.main()
