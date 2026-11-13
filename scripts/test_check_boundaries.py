"""Regression checks for the dependency-boundary CI gate."""
import json
from pathlib import Path
import tempfile
import unittest

from check_boundaries import check_boundaries, lean_imports, module_allowed


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
        self.write("lean-kernel/lakefile.toml", 'name = "vastitas_kernel"\n[leanOptions]\nwarningAsError = true\n')
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
        self.write("lean-kernel/VastitasKernel/AlgebraRuntime.lean", "import VastitasKernel.AlgebraBasis\n")
        self.write("lean-kernel/lake-manifest.json", json.dumps({"packages": [{"name": "mathlib"}]}))
        errors = check_boundaries(self.root)
        self.assertTrue(any("no external Lake" in error for error in errors))
        self.assertEqual(sum("runtime must not import" in error for error in errors), 4)

    def test_runtime_may_import_only_other_runtimes(self):
        self.write("lean-kernel/VastitasKernel/SmoothRuntime.lean", "import VastitasKernel.AlgebraRuntime\n")
        self.assertEqual(check_boundaries(self.root), [])
        self.write("lean-kernel/VastitasKernel/SmoothRuntime.lean",
                   "import VastitasKernel.AlgebraRuntime\nimport VastitasKernel.SmoothDeclarations\n")
        errors = check_boundaries(self.root)
        self.assertEqual(errors, ["runtime must not import compiler module VastitasKernel.SmoothDeclarations"])

    def test_algebra_fixture_library_cannot_enter_the_compiler(self):
        self.write("lean-kernel/VastitasAlgebraTest/BasisRegression.lean",
                   "import VastitasKernel.AlgebraBasis\nimport Lean.Data.Json\n")
        self.assertEqual(check_boundaries(self.root), [])
        self.write("lean-kernel/VastitasKernel/AlgebraBasis.lean",
                   "import VastitasAlgebraTest.BasisRegression\n")
        self.assertTrue(any("forbidden import VastitasAlgebraTest.BasisRegression" in error
                            for error in check_boundaries(self.root)))

    def test_public_source_fixture_cannot_enter_the_compiler(self):
        self.write("lean-kernel/VastitasPublicTest/AuthorityRegression.lean",
                   "import VastitasKernel.LegacySource\nimport Lean\n")
        self.assertEqual(check_boundaries(self.root), [])
        self.write("lean-kernel/VastitasKernel/Core.lean",
                   "import VastitasPublicTest.AuthorityRegression\n")
        self.assertTrue(any("forbidden import VastitasPublicTest.AuthorityRegression" in error
                            for error in check_boundaries(self.root)))

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
        self.write("lean-kernel/numerical/lakefile.lean",
                   'import Lake\nrequire vastitas_storage_native from "../native"\n')
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

    def test_executable_lakefiles_reject_unlocked_and_redirected_requirements(self):
        self.numerical_package()
        required = 'require vastitas_storage_native from "../native"'
        for package, valid in [('native', ''), ('numerical', required)]:
            for added in ['require mathlib from git "https://example.invalid/mathlib" @ "master"',
                          'require /- hidden -/ mathlib from "../mathlib"',
                          'require\n mathlib from "../mathlib"']:
                with self.subTest(package=package, added=added):
                    self.write(f'lean-kernel/{package}/lakefile.lean', f'import Lake\n{valid}\n{added}\n')
                    self.assertTrue(any('unsupported dependency in lakefile.lean' in e
                                        for e in check_boundaries(self.root)))
            self.write(f'lean-kernel/{package}/lakefile.lean', f'import Lake\n{valid}\n')
        for declaration in [required.replace('../native', '../forged'),
                            required + ' with NameMap.empty', required + '\n' + required, '']:
            self.write('lean-kernel/numerical/lakefile.lean', f'import Lake\n{declaration}\n')
            self.assertTrue(any('unsupported dependency in lakefile.lean' in e
                                for e in check_boundaries(self.root)))

    def test_dependency_words_inside_comments_and_strings_are_not_commands(self):
        self.numerical_package()
        self.write('lean-kernel/numerical/lakefile.lean', '''import Lake
/- require forged /- require another -/ -/
def example := "require mathlib from \\"../wrong\\""
require /- existing local dependency -/ vastitas_storage_native from "../native" -- require wrong
''')
        self.assertEqual(check_boundaries(self.root), [])

    def test_char_literals_and_interpolations_cannot_conceal_a_require(self):
        # A quote character literal once opened a fake string that hid the
        # following require from the scanner (#567).
        self.numerical_package()
        required = 'require vastitas_storage_native from "../native"'
        for hiding in ["def q : Char := '\"'\nrequire evil from \"../../elsewhere\"\ndef r : Char := '\"'",
                       "def q := '\\''\nrequire evil from \"../../elsewhere\"",
                       "def q := '\\u{22}'\nrequire evil from \"../../elsewhere\"",
                       'def q := s!"{"\\""}"\nrequire evil from "../../elsewhere"',
                       'def q := s!"-I{pkg.dir / "../native"}"\nrequire evil from "../../elsewhere"']:
            with self.subTest(hiding=hiding):
                self.write('lean-kernel/numerical/lakefile.lean', f'import Lake\n{required}\n{hiding}\n')
                self.assertTrue(any('unsupported dependency in lakefile.lean' in e
                                    for e in check_boundaries(self.root)))
        for unsupported in ["def q := 'ab'", "def q := '", 'def q := r#"x"#', 'def q := r"x"',
                            'def q := s!"{"', 'def q := "unmatched { brace"',
                            # Without `!` a brace is ambiguous: an ordinary literal or a
                            # prefixless interpolation could each conceal a require.
                            'def x := "{"\nrequire evil from "../../evil"\ndef y := "}"',
                            'def q := throwError "{"\\""}"\nrequire evil from "../../elsewhere"']:
            with self.subTest(unsupported=unsupported):
                self.write('lean-kernel/numerical/lakefile.lean', f'import Lake\n{required}\n{unsupported}\n')
                self.assertTrue(any('cannot check lakefile.lean dependencies' in e
                                    for e in check_boundaries(self.root)))
        self.write('lean-kernel/numerical/lakefile.lean', f"""import Lake
def q : Char := '"'
def p' := s!"-I{{pkg.dir / "../native"}} {{'}}'}}"
{required}
""")
        self.assertEqual(check_boundaries(self.root), [])

    def test_root_and_oracle_toolchains_must_match_kernel(self):
        self.oracle_package()
        self.write("lean-toolchain", "leanprover/lean4:v4.34.0\n")
        self.write("lean/lean-toolchain", "leanprover/lean4:v4.34.0\n")
        errors = check_boundaries(self.root)
        self.assertTrue(any("root and kernel" in error for error in errors))
        self.assertTrue(any("kernel and oracle" in error for error in errors))

    def oracle_package(self):
        self.write("lean/lean-toolchain", "leanprover/lean4:v4.35.0\n")
        self.write("lean/lakefile.toml", '''name = "vastitas_oracle"
[leanOptions]
warningAsError = true
[[require]]
name = "vastitas_kernel"
path = "../lean-kernel"
''')
        self.write("lean/lake-manifest.json", json.dumps({"packages": [{
            "type": "path", "scope": "", "name": "vastitas_kernel",
            "manifestFile": "lake-manifest.json", "inherited": False,
            "dir": "../lean-kernel", "copy": False, "configFile": "lakefile.toml",
        }]}))
        self.write("lean/VastitasOracle.lean", "import VastitasOracle.Core\n")
        self.write("lean/VastitasOracle/Core.lean", "import VastitasKernel.Runtime\nimport Init.Data.Rat.Lemmas\n")

    def assert_boundary_error(self, expected):
        errors = check_boundaries(self.root)
        self.assertTrue(any(expected in error for error in errors), errors)

    def test_oracle_uses_only_core_and_actual_local_kernel(self):
        self.oracle_package()
        self.write("lean/VastitasOracle/Promotion.lean", "import VastitasPromotion.Fixture\nimport Std\nimport Lean\n")
        self.assertEqual(check_boundaries(self.root), [])

    def test_oracle_imports_use_the_existing_header_scanner(self):
        self.oracle_package()
        for source in [
            "import Mathlib\n",
            "import Std Mathlib.Data.Rat.Defs\n",
            "module\npublic /- nested /- comment -/ -/ meta import all «Mathlib».Data.List.Sort\n",
            "import Std import Mathlib\n",
            "import VastitasBridge\n",
            "import VastitasOracleExtra\n",
        ]:
            with self.subTest(source=source):
                self.write("lean/VastitasOracle/Core.lean", source)
                self.assert_boundary_error("forbidden import")

    def test_oracle_comments_and_strings_are_not_dependencies(self):
        self.oracle_package()
        self.write("lean/VastitasOracle/Core.lean", '''/- import Mathlib /- nested -/ -/
import Init
-- import Mathlib
def description := "import Mathlib"
''')
        self.assertEqual(check_boundaries(self.root), [])

    def test_oracle_malformed_import_fails_closed(self):
        self.oracle_package()
        self.write("lean/VastitasOracle/Core.lean", "import /- unterminated")
        self.assert_boundary_error("unterminated block comment")

    def test_transitive_import_through_oracle_helper_is_rejected(self):
        self.oracle_package()
        self.write("lean/VastitasOracle/Core.lean", "import VastitasOracle.Helper\n")
        self.write("lean/VastitasOracle/Helper.lean", "import Mathlib.Data.Rat.Defs\n")
        self.assert_boundary_error("lean/VastitasOracle/Helper.lean: forbidden import Mathlib")

    def test_transitive_import_through_kernel_is_rejected(self):
        self.oracle_package()
        self.write("lean-kernel/VastitasKernel/Runtime.lean", "import Mathlib\n")
        self.assert_boundary_error("lean-kernel/VastitasKernel/Runtime.lean: forbidden import Mathlib")

    def test_direct_and_inherited_lake_dependencies_are_rejected(self):
        self.oracle_package()
        path = self.root / "lean/lake-manifest.json"
        original = path.read_text()
        for inherited in [False, True]:
            for name in ["mathlib", "innocent_wrapper", "batteries"]:
                with self.subTest(inherited=inherited, name=name):
                    manifest = json.loads(original)
                    manifest["packages"].append({
                        "name": name, "type": "git", "inherited": inherited,
                        "url": "https://github.com/leanprover-community/mathlib4.git",
                    })
                    path.write_text(json.dumps(manifest))
                    self.assert_boundary_error("complete manifest, including transitive dependencies")

    def test_renamed_or_redirected_kernel_dependency_is_rejected(self):
        self.oracle_package()
        path = self.root / "lean/lake-manifest.json"
        original = path.read_text()
        for changes in [
            {"type": "git", "url": "https://github.com/leanprover-community/mathlib4.git"},
            {"dir": "../lean-bridge"}, {"name": "mathlib"},
            {"configFile": "lakefile.lean"}, {"manifestFile": "unchecked.json"},
            {"inherited": True},
        ]:
            with self.subTest(changes=changes):
                manifest = json.loads(original)
                manifest["packages"][0].update(changes)
                path.write_text(json.dumps(manifest))
                self.assert_boundary_error("only the local ../lean-kernel")

    def test_stale_lock_does_not_hide_new_direct_or_transitive_require(self):
        self.oracle_package()
        for directory in ["lean", "lean-kernel"]:
            with self.subTest(directory=directory):
                path = self.root / directory / "lakefile.toml"
                original = path.read_text()
                path.write_text(original + '''\n[[require]]
name = "mathlib"
git = "https://github.com/leanprover-community/mathlib4.git"
rev = "v4.35.0"
''')
                self.assert_boundary_error("(lakefile.toml)")
                path.write_text(original)

    def test_kernel_transitive_lock_is_checked_independently_of_oracle_lock(self):
        self.oracle_package()
        self.write("lean-kernel/lake-manifest.json", json.dumps({"packages": [
            {"name": "mathlib", "inherited": True},
        ]}))
        self.assert_boundary_error("lean-kernel must have no external Lake")

    def test_executable_lake_config_cannot_bypass_declarative_boundary(self):
        self.oracle_package()
        for directory in ["lean", "lean-kernel"]:
            with self.subTest(directory=directory):
                self.write(f"{directory}/lakefile.lean", "import Lake\n")
                self.assert_boundary_error("executable lakefile.lean is not allowed")
                (self.root / directory / "lakefile.lean").unlink()

    def test_missing_malformed_or_incomplete_locks_fail_closed(self):
        self.oracle_package()
        for directory in ["lean", "lean-kernel"]:
            path = self.root / directory / "lake-manifest.json"
            original = path.read_text()
            for text in ["{", "{}", "[]", '{"packages": null}']:
                with self.subTest(directory=directory, text=text):
                    path.write_text(text)
                    self.assertTrue(check_boundaries(self.root))
            path.unlink()
            self.assert_boundary_error("cannot check Lake dependencies")
            path.write_text(original)

    def test_kernel_and_oracle_builds_turn_warnings_into_errors(self):
        self.oracle_package()
        self.assertEqual(check_boundaries(self.root), [])
        for directory in ["lean", "lean-kernel"]:
            with self.subTest(directory=directory):
                path = self.root / directory / "lakefile.toml"
                original = path.read_text()
                for replacement in ["", "warningAsError = false\n", 'warningAsError = "true"\n']:
                    path.write_text(original.replace("warningAsError = true\n", replacement))
                    self.assert_boundary_error("must set leanOptions.warningAsError = true")
                path.write_text(original.replace("[leanOptions]\nwarningAsError = true\n",
                                                 "leanOptions = [\"warningAsError\"]\n"))
                self.assert_boundary_error("must set leanOptions.warningAsError = true")
                path.write_text(original)
        self.assertEqual(check_boundaries(self.root), [])

    def test_missing_or_malformed_lake_configs_fail_closed(self):
        self.oracle_package()
        for directory in ["lean", "lean-kernel"]:
            path = self.root / directory / "lakefile.toml"
            original = path.read_text()
            path.write_text("[[require]")
            self.assert_boundary_error("cannot check Lake dependencies")
            path.unlink()
            self.assert_boundary_error("cannot check Lake dependencies")
            path.write_text(original)

    def bridge_package(self):
        revision = "56a005855ea17e0b0958f73ec801ae140b0a1679"
        url = "https://github.com/leanprover-community/mathlib4.git"
        self.write("lean-bridge/lean-toolchain", "leanprover/lean4:v4.35.0\n")
        self.write("lean-bridge/lakefile.toml", f'''name = "vastitas_bridge"
[[require]]
name = "mathlib"
git = "{url}"
rev = "{revision}"

[[require]]
name = "vastitas_kernel"
path = "../lean-kernel"

[[require]]
name = "vastitas_oracle"
path = "../lean"

[[lean_lib]]
name = "VastitasBridge"
''')
        local = [{
            "type": "path", "scope": "", "name": name,
            "manifestFile": "lake-manifest.json", "inherited": False,
            "dir": directory, "copy": False, "configFile": "lakefile.toml",
        } for name, directory in [("vastitas_oracle", "../lean"),
                                  ("vastitas_kernel", "../lean-kernel")]]
        self.write("lean-bridge/lake-manifest.json", json.dumps({"packages": [{
            "name": "mathlib", "type": "git", "url": url, "rev": revision,
            "inherited": False, "subDir": None,
        }] + local}))
        self.write("lean-bridge/VastitasBridge.lean", "import Mathlib\n")

    def test_optional_bridge_does_not_relax_compiler_or_oracle_boundary(self):
        self.oracle_package()
        self.bridge_package()
        self.assertEqual(check_boundaries(self.root), [])
        for directory in ["lean-kernel/VastitasKernel", "lean/VastitasOracle"]:
            with self.subTest(directory=directory):
                path = f"{directory}/BridgeLeak.lean"
                self.write(path, "import VastitasBridge\nimport Mathlib\n")
                self.assert_boundary_error(f"{path}: forbidden import VastitasBridge")
                self.assert_boundary_error(f"{path}: forbidden import Mathlib")
                (self.root / path).unlink()
        for source in ["import VastitasPromotion.Fixture\n", "import Lake\n",
                       "import VastitasBridgeExtra\n", "import VastitasOracleExtra\n"]:
            with self.subTest(source=source):
                self.write("lean-bridge/VastitasBridge.lean", source)
                self.assert_boundary_error("lean-bridge/VastitasBridge.lean: forbidden import")

    def test_bridge_may_read_kernel_and_oracle_one_way(self):
        self.oracle_package()
        self.bridge_package()
        self.write("lean-bridge/VastitasBridge.lean", "import Mathlib\nimport VastitasBridge.Kernel\n")
        self.write("lean-bridge/VastitasBridge/Kernel.lean",
                   "import VastitasKernel.AlgebraRuntime\nimport VastitasOracle.AlgebraBasis\n"
                   "import Mathlib\n")
        self.assertEqual(check_boundaries(self.root), [])
        self.write("lean/VastitasOracle/Leak.lean", "import VastitasBridge.Kernel\n")
        self.assert_boundary_error("lean/VastitasOracle/Leak.lean: forbidden import VastitasBridge")

    def test_bridge_path_dependencies_are_exactly_kernel_and_oracle(self):
        self.oracle_package()
        self.bridge_package()
        path = self.root / "lean-bridge/lake-manifest.json"
        original = path.read_text()
        for index in [1, 2]:
            for changes in [
                {"dir": "../lean-bridge"}, {"dir": "../other"}, {"name": "wrapper"},
                {"copy": True}, {"inherited": True}, {"configFile": "lakefile.lean"},
                {"manifestFile": "unchecked.json"}, {"scope": "leanprover-community"},
            ]:
                with self.subTest(index=index, changes=changes):
                    manifest = json.loads(original)
                    manifest["packages"][index].update(changes)
                    path.write_text(json.dumps(manifest))
                    self.assert_boundary_error("path dependencies must be exactly")
        for packages in [lambda p: p[:2], lambda p: p + [dict(p[1], name="vastitas_extra")]]:
            with self.subTest(packages=packages):
                manifest = json.loads(original)
                manifest["packages"] = packages(manifest["packages"])
                path.write_text(json.dumps(manifest))
                self.assert_boundary_error("path dependencies must be exactly")
        path.write_text(original)
        config = self.root / "lean-bridge/lakefile.toml"
        original = config.read_text()
        for old, new in [('path = "../lean"\n', 'path = "../lean-bridge"\n'),
                         ('name = "vastitas_oracle"\npath = "../lean"\n', ""),
                         ('path = "../lean-kernel"', 'git = "https://example.org/kernel.git"')]:
            with self.subTest(old=old):
                config.write_text(original.replace(old, new))
                self.assert_boundary_error("and the local ../lean-kernel and ../lean packages")

    def test_bridge_cannot_redirect_or_unpin_mathlib(self):
        self.bridge_package()
        path = self.root / "lean-bridge/lake-manifest.json"
        original = path.read_text()
        for changes in [
            {"url": "https://example.org/fork.git"}, {"rev": "main"},
            {"rev": "0" * 40}, {"type": "path", "dir": "../lean"},
            {"name": "wrapper"}, {"inherited": True}, {"subDir": "other"},
        ]:
            with self.subTest(changes=changes):
                manifest = json.loads(original)
                manifest["packages"][0].update(changes)
                path.write_text(json.dumps(manifest))
                self.assert_boundary_error("lean-bridge")
        path.write_text(original)
        config = self.root / "lean-bridge/lakefile.toml"
        config.write_text(config.read_text().replace(
            "56a005855ea17e0b0958f73ec801ae140b0a1679", "main"))
        self.assert_boundary_error("only the pinned Mathlib reference")

    def test_bridge_transitive_dependencies_must_be_locked_git_commits(self):
        self.bridge_package()
        path = self.root / "lean-bridge/lake-manifest.json"
        manifest = json.loads(path.read_text())
        inherited = {"name": "helper", "type": "git", "rev": "a" * 40, "inherited": True}
        manifest["packages"].append(inherited)
        path.write_text(json.dumps(manifest))
        self.assertEqual(check_boundaries(self.root), [])
        for changes in [{"rev": "main"}, {"type": "svn"}, {"inherited": False}]:
            with self.subTest(changes=changes):
                manifest["packages"][-1] = inherited | changes
                path.write_text(json.dumps(manifest))
                self.assert_boundary_error("lock every dependency")
        manifest["packages"][-1] = inherited | {"type": "path"}
        path.write_text(json.dumps(manifest))
        self.assert_boundary_error("path dependencies must be exactly")
        manifest["packages"][-1] = manifest["packages"][0]
        path.write_text(json.dumps(manifest))
        self.assert_boundary_error("duplicate package names")

    def test_bridge_missing_lock_toolchain_drift_and_executable_override_fail(self):
        self.bridge_package()
        self.write("lean-bridge/lean-toolchain", "leanprover/lean4:v4.34.0\n")
        self.assert_boundary_error("bridge and kernel must use the same Lean toolchain")
        self.write("lean-bridge/lakefile.lean", "import Lake\n")
        self.assert_boundary_error("lean-bridge: executable lakefile.lean")
        path = self.root / "lean-bridge/lake-manifest.json"
        for text in ["{", "{}", "[]", '{"packages": null}', '{"packages": []}']:
            with self.subTest(text=text):
                path.write_text(text)
                self.assert_boundary_error("lean-bridge")
        path.unlink()
        self.assert_boundary_error("lean-bridge: cannot check pinned dependencies")

    def test_bridge_has_no_executable_and_one_library(self):
        self.bridge_package()
        self.assertEqual(check_boundaries(self.root), [])
        path = self.root / "lean-bridge/lakefile.toml"
        original = path.read_text()
        for extra, message in [
            ('\n[[lean_exe]]\nname = "audit"\nroot = "Audit"\n', "must not declare an executable target"),
            ('\n[[lean_lib]]\nname = "Other"\n', "exactly the library VastitasBridge"),
        ]:
            with self.subTest(extra=extra):
                path.write_text(original + extra)
                self.assert_boundary_error(message)
        for library in ['name = "VastitasBridge"\nroots = ["Other"]\n',
                        'name = "VastitasBridge"\nglobs = ["VastitasBridge.+"]\n',
                        'name = "Other"\n']:
            with self.subTest(library=library):
                path.write_text(original.replace('name = "VastitasBridge"\n', library))
                self.assert_boundary_error("exactly the library VastitasBridge")
        for key in ['srcDir = "src2"\n', 'buildDir = "out"\n', 'moreLinkArgs = ["-x"]\n']:
            with self.subTest(key=key):
                path.write_text(key + original)
                self.assert_boundary_error("unexpected Lake configuration keys")
        path.write_text(original)
        self.assertEqual(check_boundaries(self.root), [])

    def test_every_bridge_source_is_in_the_root_closure(self):
        self.bridge_package()
        self.write("lean-bridge/VastitasBridge.lean", "import Mathlib\nimport VastitasBridge.A\n")
        self.write("lean-bridge/VastitasBridge/A.lean", "import VastitasBridge.B.C\n")
        self.write("lean-bridge/VastitasBridge/B/C.lean", "import Mathlib\n")
        self.assertEqual(check_boundaries(self.root), [])
        self.write("lean-bridge/VastitasBridge/Loose.lean", "import Mathlib\ntheorem t : False := sorry\n")
        self.assert_boundary_error(
            "lean-bridge/VastitasBridge/Loose.lean: not imported by VastitasBridge.lean")
        self.write("lean-bridge/VastitasBridge/B/C.lean", "import Mathlib\nimport VastitasBridge.Loose\n")
        self.assertEqual(check_boundaries(self.root), [])
        self.write("lean-bridge/VastitasBridge/B/C.lean",
                   "import Mathlib\nimport VastitasBridge.Loose\nimport VastitasBridge.«D.E»\n")
        self.write("lean-bridge/VastitasBridge/D.E.lean", "import Mathlib\n")
        self.assertEqual(check_boundaries(self.root), [])
        (self.root / "lean-bridge/VastitasBridge.lean").unlink()
        self.assert_boundary_error("missing root module VastitasBridge.lean")

    def manifest(self, directory, dependencies=""):
        """A package manifest under `directory` with the given [dependencies] lines."""
        self.write(f"{directory}/Vastitas.toml",
                   f'[package]\nname = "p"\nversion = "0.1.0"\nroot = "mod.vast"\n\n[dependencies]\n{dependencies}')

    def library_packages(self):
        """The layout of the std and nature packages (ADR 0002 §1)."""
        self.manifest("stdlib", 'geometry_library = { path = "src/geometry" }\n'
                                'differential_library = { path = "src/differential" }\n')
        self.manifest("stdlib/src/geometry")
        self.manifest("stdlib/src/differential", 'geometry = { path = "../geometry" }\n')
        self.manifest("nature", 'std = { path = "../stdlib" }\n')

    def test_std_and_nature_manifests_follow_the_library_boundary(self):
        self.library_packages()
        self.assertEqual(check_boundaries(self.root), [])
        # nature may depend on any package inside stdlib/ and nature/.
        self.manifest("nature/extra", 'geometry = { path = "../../stdlib/src/geometry" }\n'
                                      'nature = { path = ".." }\n')
        self.assertEqual(check_boundaries(self.root), [])

    def test_a_std_to_nature_edge_is_rejected(self):
        self.library_packages()
        for directory, path in [("stdlib", "../nature"), ("stdlib/src/differential", "../../../nature")]:
            with self.subTest(directory=directory):
                original = (self.root / directory / "Vastitas.toml").read_text()
                self.write(f"{directory}/Vastitas.toml", original + f'nature = {{ path = "{path}" }}\n')
                self.assert_boundary_error(
                    f"{directory}/Vastitas.toml: dependency `nature` on {path} leaves stdlib/; "
                    "a stdlib/ manifest may depend only on packages inside stdlib/")
                self.write(f"{directory}/Vastitas.toml", original)
        self.assertEqual(check_boundaries(self.root), [])

    def test_nature_depends_on_nothing_outside_std_and_nature(self):
        self.library_packages()
        for path in ["../monad", "../lean-kernel", "../examples/packages/demo", "/"]:
            with self.subTest(path=path):
                self.manifest("nature", f'std = {{ path = "../stdlib" }}\nother = {{ path = "{path}" }}\n')
                self.assert_boundary_error(
                    f"nature/Vastitas.toml: dependency `other` on {path} leaves stdlib/ and nature/")

    def test_relative_segments_and_symbolic_links_cannot_hide_an_edge(self):
        self.library_packages()
        self.manifest("stdlib/src/geometry", 'escape = { path = "../../../stdlib/../nature" }\n')
        self.assert_boundary_error("dependency `escape` on ../../../stdlib/../nature leaves stdlib/")
        self.manifest("stdlib/src/geometry")
        (self.root / "stdlib/src/link").symlink_to(self.root / "nature", target_is_directory=True)
        self.manifest("stdlib/src/geometry", 'linked = { path = "../link" }\n')
        self.assert_boundary_error("dependency `linked` on ../link leaves stdlib/")
        # The compiler locates a package by its canonical manifest, so a linked
        # manifest in a directory inside stdlib/ is the package it links to.
        (self.root / "stdlib/src/link").unlink()
        (self.root / "stdlib/src/alias").mkdir()
        (self.root / "stdlib/src/alias/Vastitas.toml").symlink_to(self.root / "nature/Vastitas.toml")
        self.manifest("stdlib/src/geometry", 'aliased = { path = "../alias" }\n')
        self.assert_boundary_error("dependency `aliased` on ../alias leaves stdlib/")

    def test_malformed_library_manifests_fail_closed(self):
        self.library_packages()
        for dependencies, expected in [
            ('nature = "../nature"\n', "dependency `nature` must have the form"),
            ('nature = { version = "1" }\n', "dependency `nature` must have the form"),
            ('nature = { path = 1 }\n', "dependency `nature` must have the form"),
        ]:
            with self.subTest(dependencies=dependencies):
                self.manifest("stdlib/src/geometry", dependencies)
                self.assert_boundary_error(f"stdlib/src/geometry/Vastitas.toml: {expected}")
        self.write("stdlib/src/geometry/Vastitas.toml", "dependencies = 1\n[package]\n")
        self.assert_boundary_error("stdlib/src/geometry/Vastitas.toml: [dependencies] must be a table")
        self.write("stdlib/src/geometry/Vastitas.toml", "[package\n")
        self.assert_boundary_error("stdlib/src/geometry/Vastitas.toml: cannot check library dependencies")

    def test_actual_library_manifests_pass_and_reject_a_std_to_nature_edge(self):
        repository = Path(__file__).resolve().parents[1]
        manifests = [manifest for family in ("stdlib", "nature")
                     for manifest in sorted((repository / family).rglob("Vastitas.toml"))]
        self.assertTrue(any(m.relative_to(repository).as_posix() == "stdlib/Vastitas.toml" for m in manifests))
        for manifest in manifests:
            self.write(manifest.relative_to(repository).as_posix(), manifest.read_text())
        self.assertEqual(check_boundaries(self.root), [])
        original = (self.root / "stdlib/Vastitas.toml").read_text()
        self.write("stdlib/Vastitas.toml", original + 'nature = { path = "../nature" }\n')
        self.assert_boundary_error("stdlib/Vastitas.toml: dependency `nature` on ../nature leaves stdlib/")


if __name__ == "__main__":
    unittest.main()
