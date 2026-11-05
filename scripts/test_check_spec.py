"""Regressions for scripts/check_spec.py: each case breaks one rule of a valid fixture."""
import json
import os
from pathlib import Path, PurePosixPath
import stat
import tempfile
import unittest
from unittest import mock

import check_spec
from check_spec import cargo_run, discover_run, every_pull_request, plain_commands, plain_set, python_tests, \
    run_steps, rust_tests


HASH = "sha256:" + "a" * 64
OTHER_HASH = "sha256:" + "b" * 64

SPEC = '''
[spec]
id = "demo"
title = "std::demo"
subject = "std::demo"
description = "Laws of a demonstration module."

[property."demo.identity"]
title = "Identity"
subject = "std::demo::id"
statement = "id(x) = x for every x."
specified_in = "[Identity](rules.md#identity)"
example = "id(3) = 3"
example_test = "tests/demo.rs::identity_runs"

[property."demo.identity".claim.oracle]
status = "proved-oracle"
evidence = ["VastitasOracle.Demo.id_eq"]
premises = []
assumes = ["frontend"]
enforced_by = [{ definition = "VastitasKernel.Check.check", code = "E_DEMO" }]

[property."demo.identity".claim.bridge]
status = "proved-bridge"
evidence = ["VastitasBridge.Demo.id_eq"]
premises = ["x is a real number"]

[property."demo.identity".claim.test]
status = "tested"
evidence = ["tests/demo.rs::identity_runs", "scripts/test_demo.py::DemoTests::test_identity",
            "VastitasKernel.DemoRegression"]

[property."demo.identity".claim.ignored]
status = "tested"
evidence = ["tests/demo.rs::ignored_but_run"]

[property."demo.identity".claim.trust]
status = "assumed"
evidence = ["frontend"]

[property."demo.identity".claim.native]
status = "not-claimed"
reason = "Native refinement is outside the profile."

[property."demo.linear"]
title = "Linearity"
subject = "std::demo::id"
statement = "id is linear."
specified_in = "[Identity](rules.md)"
example = "id(2x) = 2 id(x)"
example_not_executed = "no test exercises linearity"

[property."demo.linear".claim.proof]
status = "planned"
issue = 1
'''

REGISTRY = '''
[assumption.frontend]
title = "Frontend parsing"
statement = "The frontend parses every source faithfully."

[assumption.unused]
title = "Unused"
statement = "No claim rests on this."
'''

WORKFLOW = '''
name: CI
on:
  pull_request:
  push:
    branches: [main]
jobs:
  test:
    runs-on: ubuntu-latest
    steps:
      - run: cargo test --locked --all-targets
      - name: Ignored tests
        run: |
          cargo test --locked --test demo ignored_but_run -- --ignored
      - name: Python tests
        run: python3 -m unittest discover -s scripts -p 'test_*.py'
      - run: bash scripts/check_kernel_regressions.sh
'''

RUST = '''#[test]
fn identity_runs() {}

#[test]
#[ignore = "needs a tool"]
fn ignored_but_run() {}

#[test]
#[ignore]
fn ignored_never_run() {}

fn helper() {}
'''

PYTHON = '''import unittest


class DemoTests(unittest.TestCase):
    def test_identity(self):
        pass
'''

SKIPPED_PYTHON = '''import unittest


class SkippedTests(unittest.TestCase):
    @unittest.skip("never")
    def test_skipped(self):
        pass
'''


BRIDGE_CLAIM = '''[property."demo.identity".claim.bridge]
status = "proved-bridge"
evidence = ["VastitasBridge.Demo.id_eq"]
premises = ["x is a real number"]
'''


def pins(environment, entries):
    return check_spec.format_pins(environment, entries)


ORACLE_PINS = [
    {"name": "VastitasKernel.Check.check", "module": "VastitasKernel.Check", "kind": "definition"},
    {"name": "VastitasOracle.Demo.id_eq", "module": "VastitasOracle.Demo", "kind": "theorem", "statement": HASH},
]
BRIDGE_PINS = [
    {"name": "VastitasBridge.Demo.id_eq", "module": "VastitasBridge.Demo", "kind": "theorem", "statement": HASH},
]

FILES = {
    "docs/spec/demo.toml": SPEC,
    "docs/spec/assumptions.toml": REGISTRY,
    "docs/spec/pins/oracle.json": pins("oracle", ORACLE_PINS),
    "docs/spec/pins/bridge.json": pins("bridge", BRIDGE_PINS),
    "docs/rules.md": "# Rules\n\n## Identity\n",
    "docs/appendix/diagnostics.md": "| `E_DEMO` | A demonstration code |\n",
    "docs/SUMMARY.md": "- [std::demo](spec/demo.md)\n- [Assumptions](spec/assumptions.md)\n",
    "Cargo.toml": '[package]\nname = "vastitas"\n',
    "tests/demo.rs": RUST,
    "scripts/test_demo.py": PYTHON,
    "scripts/test_skipped.py": SKIPPED_PYTHON,
    "scripts/check_kernel_regressions.sh": "#!/usr/bin/env bash\nset -euo pipefail\n"
                                           "lake -d lean-kernel build \\\n  VastitasKernel.DemoRegression\n",
    "lean-kernel/VastitasKernel/DemoRegression.lean": "",
    "lean-kernel/VastitasKernel/Check.lean": "",
    "lean/VastitasOracle/Demo.lean": "",
    "lean-bridge/VastitasBridge/Demo.lean": "",
    ".github/workflows/ci.yml": WORKFLOW,
}


class FixtureTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory(prefix="vastitas-check-spec-")
        self.root = Path(self.directory.name)
        for path, contents in FILES.items():
            self.put(path, contents)
        check_spec.write(self.root, check_spec.load(self.root, []))

    def tearDown(self):
        self.directory.cleanup()

    def put(self, path, contents):
        file = self.root / path
        file.parent.mkdir(parents=True, exist_ok=True)
        file.write_text(contents, encoding="utf-8")

    def edit(self, path, old, new, count=1):
        file = self.root / path
        text = file.read_text(encoding="utf-8")
        self.assertIn(old, text, f"fixture text to replace is missing from {path}")
        file.write_text(text.replace(old, new, count), encoding="utf-8")

    def errors(self, regenerate=True):
        if regenerate:
            check_spec.write(self.root, check_spec.load(self.root, []))
        return check_spec.check(self.root)[0]

    def assertRejected(self, *fragments, regenerate=True):
        errors = self.errors(regenerate)
        joined = "\n".join(errors)
        for fragment in fragments:
            self.assertIn(fragment, joined, f"expected {fragment!r} among:\n{joined}")
        return errors

    def test_valid_fixture_passes(self):
        self.assertEqual(self.errors(regenerate=False), [])

    def test_unqualified_theorem(self):
        self.edit("docs/spec/demo.toml", '"VastitasOracle.Demo.id_eq"]', '"id_eq"]')
        self.assertRejected("`id_eq` is not a fully qualified theorem name under VastitasOracle")

    def test_theorem_from_another_environment(self):
        self.edit("docs/spec/demo.toml", '"VastitasOracle.Demo.id_eq"]', '"VastitasBridge.Demo.id_eq"]')
        self.assertRejected("`VastitasBridge.Demo.id_eq` is not a fully qualified theorem name under VastitasOracle")

    def test_unpinned_theorem(self):
        self.edit("docs/spec/demo.toml", '"VastitasOracle.Demo.id_eq"]',
                  '"VastitasOracle.Demo.id_eq", "VastitasOracle.Demo.absent"]')
        self.assertRejected("`VastitasOracle.Demo.absent` is cited but not pinned",
                            "--update-statements oracle")

    def test_stale_pin(self):
        self.edit("docs/spec/demo.toml", 'evidence = ["VastitasBridge.Demo.id_eq"]',
                  'evidence = ["VastitasBridge.Demo.id_eq"]\nnote = "kept"')
        self.put("docs/spec/pins/bridge.json", pins("bridge", BRIDGE_PINS + [
            {"name": "VastitasBridge.Demo.old", "module": "VastitasBridge.Demo", "kind": "theorem",
             "statement": OTHER_HASH}]))
        self.assertRejected("`VastitasBridge.Demo.old` is pinned but no claim cites it")

    def test_missing_test_function(self):
        self.edit("docs/spec/demo.toml", '"tests/demo.rs::identity_runs", "scripts',
                  '"tests/demo.rs::absent", "scripts')
        self.assertRejected("tests/demo.rs has no #[test] function `absent`")

    def test_helper_function_is_not_a_test(self):
        self.edit("docs/spec/demo.toml", '"tests/demo.rs::identity_runs", "scripts',
                  '"tests/demo.rs::helper", "scripts')
        self.assertRejected("tests/demo.rs has no #[test] function `helper`")

    def test_missing_test_file(self):
        self.edit("docs/spec/demo.toml", '"tests/demo.rs::identity_runs", "scripts',
                  '"tests/missing.rs::identity_runs", "scripts')
        self.assertRejected("the test file tests/missing.rs does not exist")

    def test_missing_python_test(self):
        self.edit("docs/spec/demo.toml", "test_demo.py::DemoTests::test_identity",
                  "test_demo.py::DemoTests::test_absent")
        self.assertRejected("scripts/test_demo.py has no unittest test method `DemoTests.test_absent`")

    def test_skipped_python_test(self):
        self.edit("docs/spec/demo.toml", "test_demo.py::DemoTests::test_identity",
                  "test_skipped.py::SkippedTests::test_skipped")
        self.assertRejected("unittest may skip `scripts/test_skipped.py::SkippedTests::test_skipped` or expect it to fail")

    def test_python_tests_in_a_module_that_may_skip_or_filter_tests(self):
        # The reviews of #655 found skips through a base class and a load_tests
        # hook. Any use of these names in the module, or in the __init__.py of a
        # package above it, makes all of its tests not count.
        cited = "unittest may skip `scripts/test_demo.py::DemoTests::test_identity` or expect it to fail"
        for path, old, new in (
                ("scripts/test_demo.py", "class DemoTests(unittest.TestCase):",
                 "@unittest.skip('never')\nclass BaseTests(unittest.TestCase):\n    pass\n\n\n"
                 "class DemoTests(BaseTests):"),
                ("scripts/test_demo.py", "class DemoTests(unittest.TestCase):",
                 "def load_tests(loader, tests, pattern):\n    return unittest.TestSuite()\n\n\n"
                 "class DemoTests(unittest.TestCase):"),
                ("scripts/test_demo.py", "import unittest\n", "import unittest\nfrom unittest import skip as never\n"),
                ("scripts/test_demo.py", "        pass\n", "        pass\n\n    test_identity = unittest.skip('x')(test_identity)\n"),
                ("scripts/test_demo.py", "        pass\n", "        pass\n\n\nclass OtherTests(unittest.TestCase):\n"
                 "    @unittest.skipUnless(False, 'never')\n    def test_other(self):\n        pass\n"),
                ("scripts/test_demo.py", "        pass\n", "        pass\n\n    @unittest.expectedFailure\n"
                 "    def test_broken(self):\n        self.fail()\n"),
                ("scripts/test_demo.py", "        pass\n", "        self.skipTest('later')\n")):
            with self.subTest(new=new):
                self.put("scripts/test_demo.py", PYTHON)
                self.edit(path, old, new)
                self.assertRejected(cited)
        self.put("scripts/test_demo.py", PYTHON)
        self.put("scripts/__init__.py", "def load_tests(loader, tests, pattern):\n    return tests\n")
        self.assertRejected(cited)

    def test_python_tests_that_a_class_body_or_the_module_disables(self):
        # The review of #655 found that `test_identity = None` removes the method from discovery.
        cited = "unittest may skip `scripts/test_demo.py::DemoTests::test_identity` or expect it to fail"
        for addition in ("    test_identity = None\n", "    del test_identity\n",
                         "\n\nDemoTests.test_identity = None\n", "\n\ndel DemoTests.test_identity\n",
                         "\n\nsetattr(DemoTests, 'test_identity', None)\n"):
            with self.subTest(addition=addition):
                self.put("scripts/test_demo.py", PYTHON + addition)
                self.assertRejected(cited)

    def test_async_python_tests_count_only_in_an_async_test_case(self):
        # The review of #655 found that unittest never awaits an async test of a TestCase.
        self.edit("scripts/test_demo.py", "    def test_identity(self):", "    async def test_identity(self):")
        self.assertRejected("unittest may skip `scripts/test_demo.py::DemoTests::test_identity` or expect it to fail")
        self.edit("scripts/test_demo.py", "unittest.TestCase", "unittest.IsolatedAsyncioTestCase")
        self.assertEqual(self.errors(), [])

    def test_python_test_that_no_step_discovers(self):
        self.put("tools/test_extra.py", PYTHON)
        self.edit("docs/spec/demo.toml", "scripts/test_demo.py::DemoTests::test_identity",
                  "tools/test_extra.py::DemoTests::test_identity")
        self.assertRejected("no CI step runs `tools/test_extra.py::DemoTests::test_identity`")

    def test_ignored_test_that_no_step_runs(self):
        self.edit("docs/spec/demo.toml", '["tests/demo.rs::ignored_but_run"]',
                  '["tests/demo.rs::ignored_never_run"]')
        self.assertRejected("`tests/demo.rs::ignored_never_run` is #[ignore]d, and no CI step passes "
                            "--ignored for it")

    def test_ignored_step_must_select_the_test(self):
        self.edit(".github/workflows/ci.yml", "--test demo ignored_but_run", "--test other ignored_but_run")
        self.assertRejected("`tests/demo.rs::ignored_but_run` is #[ignore]d")

    def test_steps_of_workflows_without_pull_requests_do_not_count(self):
        self.edit(".github/workflows/ci.yml", "  pull_request:\n", "")
        self.assertRejected("no CI step runs `tests/demo.rs::identity_runs`",
                            "no CI step runs scripts/check_kernel_regressions.sh")

    def test_regression_module_that_the_script_does_not_build(self):
        self.edit("docs/spec/demo.toml", '"VastitasKernel.DemoRegression"]', '"VastitasKernel.OtherRegression"]')
        self.assertRejected("`VastitasKernel.OtherRegression` is not a module that "
                            "scripts/check_kernel_regressions.sh builds")

    def test_example_without_test_or_mark(self):
        self.edit("docs/spec/demo.toml", 'example_not_executed = "no test exercises linearity"\n', "")
        self.assertRejected('[property."demo.linear"]: give exactly one of `example_test`')

    def test_example_with_test_and_mark(self):
        self.edit("docs/spec/demo.toml", 'example_test = "tests/demo.rs::identity_runs"',
                  'example_test = "tests/demo.rs::identity_runs"\nexample_not_executed = "both"')
        self.assertRejected('[property."demo.identity"]: give exactly one of `example_test`')

    def test_example_test_must_resolve(self):
        self.edit("docs/spec/demo.toml", 'example_test = "tests/demo.rs::identity_runs"',
                  'example_test = "tests/demo.rs::ignored_never_run"')
        self.assertRejected("example_test: `tests/demo.rs::ignored_never_run` is #[ignore]d")

    def test_unknown_diagnostic_code(self):
        self.edit("docs/spec/demo.toml", 'code = "E_DEMO"', 'code = "E_UNKNOWN"')
        self.assertRejected("unknown diagnostic code `E_UNKNOWN`")

    def test_unpinned_kernel_definition(self):
        self.edit("docs/spec/demo.toml", '"VastitasKernel.Check.check"', '"VastitasKernel.Check.absent"')
        self.assertRejected("`VastitasKernel.Check.absent` is cited but not pinned",
                            "`VastitasKernel.Check.check` is pinned but no claim cites it")

    def test_kernel_definition_outside_the_kernel(self):
        self.edit("docs/spec/demo.toml", '"VastitasKernel.Check.check"', '"VastitasOracle.Demo.check"')
        self.assertRejected("`definition` must be a fully qualified kernel definition under VastitasKernel")

    def test_tested_evidence_under_proved(self):
        self.edit("docs/spec/demo.toml", 'evidence = ["VastitasOracle.Demo.id_eq"]',
                  'evidence = ["VastitasOracle.Demo.id_eq", "tests/demo.rs::identity_runs"]')
        self.assertRejected("`tests/demo.rs::identity_runs` is Tested evidence; a Proved (oracle) claim "
                            "cites theorems under VastitasOracle")

    def test_regression_module_under_proved(self):
        self.edit("docs/spec/demo.toml", 'evidence = ["VastitasBridge.Demo.id_eq"]',
                  'evidence = ["VastitasBridge.Demo.id_eq", "VastitasKernel.DemoRegression"]')
        self.assertRejected("`VastitasKernel.DemoRegression` is Tested evidence; a Proved (bridge) claim")

    def test_theorem_under_tested(self):
        self.edit("docs/spec/demo.toml", '"VastitasKernel.DemoRegression"]', '"VastitasOracle.Demo.id_eq"]')
        self.assertRejected("`VastitasOracle.Demo.id_eq` is not a module that scripts/check_kernel_regressions.sh builds")

    def test_unknown_assumption(self):
        self.edit("docs/spec/demo.toml", 'evidence = ["frontend"]', 'evidence = ["toolchain"]')
        self.assertRejected("claim.trust: unknown assumption `toolchain`")

    def test_unknown_assumption_in_assumes(self):
        self.edit("docs/spec/demo.toml", 'assumes = ["frontend"]', 'assumes = ["toolchain"]')
        self.assertRejected("unknown assumption `toolchain` in `assumes`")

    def test_planned_without_issue(self):
        self.edit("docs/spec/demo.toml", "issue = 1\n", "")
        self.assertRejected("claim.proof: missing `issue`")

    def test_planned_issue_must_be_positive(self):
        self.edit("docs/spec/demo.toml", "issue = 1\n", "issue = 0\n")
        self.assertRejected("`issue` must be a positive issue number")

    def test_not_claimed_without_reason(self):
        self.edit("docs/spec/demo.toml", 'reason = "Native refinement is outside the profile."\n', "")
        self.assertRejected("claim.native: missing `reason`")

    def test_proved_without_premises(self):
        self.edit("docs/spec/demo.toml", "premises = []\n", "")
        self.assertRejected("claim.oracle: missing `premises`")

    def test_evidence_on_a_planned_claim(self):
        self.edit("docs/spec/demo.toml", "issue = 1\n", 'issue = 1\nevidence = ["tests/demo.rs::identity_runs"]\n')
        self.assertRejected("claim.proof: unknown key `evidence`")

    def test_unknown_status(self):
        self.edit("docs/spec/demo.toml", 'status = "not-claimed"', 'status = "implemented"')
        self.assertRejected("unknown status 'implemented'")

    def test_unknown_key(self):
        self.edit("docs/spec/demo.toml", 'premises = ["x is a real number"]',
                  'premises = ["x is a real number"]\nevidnce = []')
        self.assertRejected("claim.bridge: unknown key `evidnce`")

    def test_duplicate_property_id(self):
        self.put("docs/spec/other.toml", SPEC.replace('id = "demo"', 'id = "other"', 1))
        self.edit("docs/SUMMARY.md", "- [Assumptions]", "- [std::demo](spec/other.md)\n- [Assumptions]")
        self.assertRejected('[property."demo.identity"]: duplicate property id', "must begin with `other.`")

    def test_duplicate_file_id(self):
        self.put("docs/spec/other.toml", SPEC.replace('"demo.', '"demo.copy.'))
        self.edit("docs/SUMMARY.md", "- [Assumptions]", "- [std::demo](spec/other.md)\n- [Assumptions]")
        self.assertRejected("the file id `demo` is also used by docs/spec/demo.toml")

    def test_duplicate_toml_table_is_invalid(self):
        self.edit("docs/spec/demo.toml", '[property."demo.linear"]',
                  '[property."demo.identity"]\ntitle = "Again"\n\n[property."demo.linear"]')
        self.assertRejected("docs/spec/demo.toml: invalid TOML")

    def test_reserved_symbol_record(self):
        self.edit("docs/spec/demo.toml", "[spec]", '[symbol."std::demo::id"]\nproperties = []\n\n[spec]')
        self.assertRejected("`symbol` records are reserved for the std admission manifest (#285)")

    def test_specified_in_must_name_a_chapter(self):
        self.edit("docs/spec/demo.toml", "(rules.md#identity)", "(missing.md#identity)")
        self.assertRejected("names docs/missing.md, which does not exist")

    def test_specified_in_must_be_one_link(self):
        self.edit("docs/spec/demo.toml", '"[Identity](rules.md#identity)"', '"the rules chapter"')
        self.assertRejected("`specified_in` must be one Markdown link to a book chapter")

    def test_pin_with_a_malformed_statement(self):
        self.put("docs/spec/pins/oracle.json", pins("oracle", [
            ORACLE_PINS[0], dict(ORACLE_PINS[1], statement="sha256:xyz")]))
        self.assertRejected("`statement` must be sha256: followed by 64 lower-case hex digits")

    def test_pin_of_the_wrong_kind(self):
        self.put("docs/spec/pins/oracle.json", pins("oracle", [
            ORACLE_PINS[0], {"name": "VastitasOracle.Demo.id_eq", "module": "VastitasOracle.Demo",
                             "kind": "definition"}]))
        self.assertRejected("`VastitasOracle.Demo.id_eq` is not a fully qualified name under VastitasKernel")

    def test_pin_without_a_source_module(self):
        self.put("docs/spec/pins/oracle.json", pins("oracle", [
            ORACLE_PINS[0], dict(ORACLE_PINS[1], module="VastitasOracle.Missing")]))
        self.assertRejected("the module `VastitasOracle.Missing` of `VastitasOracle.Demo.id_eq` has no source file")

    def test_pin_imports_must_match_its_modules(self):
        data = json.loads(FILES["docs/spec/pins/oracle.json"])
        data["imports"] = ["VastitasOracle.Demo"]
        self.put("docs/spec/pins/oracle.json", json.dumps(data))
        self.assertRejected("`imports` must list exactly the pinned modules, sorted")

    def test_bridge_pins_resolve_no_definitions(self):
        self.put("docs/spec/pins/bridge.json", pins("bridge", BRIDGE_PINS + [
            {"name": "VastitasKernel.Check.check", "module": "VastitasKernel.Check", "kind": "definition"}]))
        self.assertRejected("the bridge environment resolves no kernel definitions")

    def test_stale_chapter(self):
        self.edit("docs/spec/demo.md", "id(x) = x for every x.", "id(x) = x.")
        self.assertRejected("docs/spec/demo.md: out of date", regenerate=False)

    def test_chapter_without_a_spec_file(self):
        self.put("docs/spec/extra.md", "# Extra\n")
        self.assertRejected("docs/spec/extra.md: no spec file generates this chapter")

    def test_contents_must_list_each_chapter(self):
        self.edit("docs/SUMMARY.md", "- [Assumptions](spec/assumptions.md)\n", "")
        self.assertRejected("docs/SUMMARY.md: does not list the generated chapter spec/assumptions.md")

    def test_write_removes_only_generated_chapters(self):
        self.put("docs/spec/extra.md", f"# Extra\n\n{check_spec.MARKER} from docs/spec/extra.toml. -->\n")
        self.put("docs/spec/notes.md", "# Notes\n")
        check_spec.write(self.root, check_spec.load(self.root, []))
        self.assertFalse((self.root / "docs/spec/extra.md").exists())
        self.assertTrue((self.root / "docs/spec/notes.md").exists())

    def rejects_with_step(self, step, fragment="no CI step runs `tests/demo.rs::identity_runs`"):
        """Replace the step that runs every Rust test, then expect `fragment`."""
        self.edit(".github/workflows/ci.yml", "      - run: cargo test --locked --all-targets\n", step)
        self.assertRejected(fragment)

    def test_folded_run_values_do_not_count(self):
        self.rejects_with_step("      - run: >\n          cargo test --locked\n          --all-targets\n")

    def test_run_values_over_several_plain_lines_do_not_count(self):
        self.rejects_with_step("      - run: cargo test --locked\n          --all-targets\n")

    def test_commented_and_echoed_commands_do_not_run(self):
        self.rejects_with_step("      - run: |\n          echo skipped; # cargo test --locked --all-targets\n"
                               "          echo cargo test --locked --all-targets\n")

    def test_here_document_bodies_do_not_run(self):
        self.rejects_with_step("      - run: |\n          cat <<'EOF'\n          cargo test --locked --all-targets\n"
                               "          EOF\n")

    def test_commands_whose_failure_is_ignored_do_not_count(self):
        self.rejects_with_step("      - run: cargo test --locked --all-targets || true\n")
        self.edit(".github/workflows/ci.yml", "cargo test --locked --all-targets || true",
                  "if cargo test --locked --all-targets; then echo ok; fi")
        self.assertRejected("no CI step runs `tests/demo.rs::identity_runs`")

    def test_commands_that_may_not_run_or_whose_failure_may_pass_do_not_count(self):
        # The reviews of #655 found shell forms in which a command may not run,
        # or bash ignores its failure. A step counts only up to its first line
        # that is not plain.
        for script in (
                "if false; then cargo test --locked --all-targets; fi",
                "while false; do cargo test --locked --all-targets; done",
                "for x in a; do cargo test --locked --all-targets; done",
                "case $x in a) cargo test --locked --all-targets;; esac",
                "cargo() (:)\ncargo test --locked --all-targets",
                "true && cargo test --locked --all-targets",
                "cargo test --locked --all-targets || true",
                "cargo test --locked --all-targets &",
                "! cargo test --locked --all-targets",
                "{ cargo test --locked --all-targets; } || true",
                "(cargo test --locked --all-targets) || true",
                "cargo test --locked --all-targets 2>&1 | tee log",
                "echo $(cargo test --locked --all-targets)",
                "x=$(cargo test --locked --all-targets)",
                "while read -r l; do :; done < <(cargo test --locked --all-targets)",
                "tests=(cargo test --locked --all-targets)",
                "echo `true; cargo test --locked --all-targets`",
                "${{ 'exit' }} 0\ncargo test --locked --all-targets",
                "X=exit\n$X 0\ncargo test --locked --all-targets",
                "exit 0\ncargo test --locked --all-targets",
                "exec true\ncargo test --locked --all-targets",
                "source env.sh\ncargo test --locked --all-targets",
                "trap 'exit 0' ERR\ncargo test --locked --all-targets",
                "set -n\ncargo test --locked --all-targets",
                "set -o noexec\ncargo test --locked --all-targets",
                "set +e\ncargo test --locked --all-targets",
                "set -o +e\ncargo test --locked --all-targets",
                "hash -p /usr/bin/true cargo\ncargo test --locked --all-targets",
                "PATH=/nowhere cargo test --locked --all-targets",
                "echo $'a\\'b'\necho ' ; cargo test --locked --all-targets ; '",
                "echo \"|\" cargo test --locked --all-targets",
                "v=${GITHUB_REF#refs/}; if [ \"$v\" = never ]; then\n  cargo test --locked --all-targets\nfi",
                "cargo test --locked --all-targets --features=a#b || true",
                "# note \\\nif false; then\n  cargo test --locked --all-targets\nfi",
                "cat <<- EOF\nx\n\ncargo test --locked --all-targets\nEOF",
                "cat <<EOF\n  EOF\ncargo test --locked --all-targets\nEOF",
                "cat <<A <<B\nB\nA\ncargo test --locked --all-targets\nB",
                "# ${{ env.Q }}\ncargo test --locked --all-targets",
                "echo '${{ env.Q }}'\ncargo test --locked --all-targets"):
            with self.subTest(script=script):
                body = "".join(f"          {line}\n" for line in script.split("\n"))
                self.put(".github/workflows/ci.yml", WORKFLOW.replace(
                    "      - run: cargo test --locked --all-targets\n", f"      - run: |\n{body}"))
                self.assertRejected("no CI step runs `tests/demo.rs::identity_runs`")

    def test_plain_lines_before_a_test_count(self):
        self.edit(".github/workflows/ci.yml", "jobs:\n", "defaults:\n  run:\n    shell: bash\njobs:\n")
        self.edit(".github/workflows/ci.yml", "      - run: cargo test --locked --all-targets\n",
                  "      - run: |\n          # Build first.\n          set -eu -o pipefail\n          cd scripts\n"
                  "          cd ..\n          echo 'building: now'\n          python3 scripts/build.py \\\n"
                  "            --check\n          cargo test --locked \\\n            --all-targets\n")
        self.assertEqual(self.errors(), [])

    def test_steps_that_their_job_or_environment_may_change_do_not_count(self):
        step = "      - run: cargo test --locked --all-targets\n"
        for edits in (
                [("runs-on: ubuntu-latest", "runs-on: windows-latest")],
                [("runs-on: ubuntu-latest", "runs-on: ${{ vars.RUNNER }}")],
                [("runs-on: ubuntu-latest", "runs-on: [self-hosted, linux]")],
                [("runs-on: ubuntu-latest\n", "runs-on: ${{ matrix.os }}\n    strategy:\n      matrix:\n"
                  "        os: [ubuntu-latest]\n        include:\n          - os: windows-latest\n")],
                [("jobs:\n", "jobs:\n  gate:\n    if: false\n    runs-on: ubuntu-latest\n    steps:\n"
                  "      - run: true\n"), ("  test:\n", "  test:\n    needs: gate\n")],
                [(step, step + "        shell: sh\n")],
                [(step, step + "        env:\n          BASH_ENV: /tmp/exit.sh\n")],
                [("    steps:\n", "    env:\n      PATH: /nowhere\n    steps:\n")],
                [("jobs:\n", "env:\n  LD_PRELOAD: /tmp/stub.so\njobs:\n")],
                [("jobs:\n", "env:\n  CARGO_TARGET_X86_64_UNKNOWN_LINUX_GNU_RUNNER: 'true'\njobs:\n")],
                [("    steps:\n", "    env:\n      PYTHONPATH: shadow\n    steps:\n")],
                [("    runs-on: ubuntu-latest\n", "    runs-on: ubuntu-latest\n    runs-on: windows-latest\n")],
                [("runs-on: ubuntu-latest\n", "runs-on: ${{ matrix.os }}\n    strategy:\n      matrix:\n"
                  "        os: [ubuntu-latest]\n        exclude:\n          - os: ubuntu-latest\n")],
                [("    steps:\n", "    steps:\n      - run: echo \"BASH_ENV=/tmp/exit.sh\" >> \"$GITHUB_ENV\"\n")],
                [(step, "      - \"i\\x66\": false\n        run: cargo test --locked --all-targets\n")],
                [(step, "      - !!str if: false\n        run: cargo test --locked --all-targets\n")],
                [(step, "      - run: >\n          cargo test --locked --all-targets\n")],
                # The second review of #655: a reader that stopped early, defaults
                # that are not block mappings, containers and unsecure commands.
                [("    steps:\n", "    steps:\n"), ("bash scripts/check_kernel_regressions.sh\n",
                  "bash scripts/check_kernel_regressions.sh\n    name: 'CI\n      job'\n    if: false\n")],
                [("jobs:\n", "defaults: {run: {shell: 'bash {0}'}}\njobs:\n")],
                [("    steps:\n", "    defaults:\n      run:\n        shell: sh\n    steps:\n")],
                [("    steps:\n", "    defaults:\n      run:\n        working-directory: experiments\n"
                  "    steps:\n")],
                [("    runs-on: ubuntu-latest\n", "    runs-on: ubuntu-latest\n    container:\n"
                  "      image: ubuntu:24.04\n")],
                [("jobs:\n", "env:\n  ACTIONS_ALLOW_UNSECURE_COMMANDS: true\njobs:\n")],
                [("    steps:\n", "    env: ${{ fromJSON(vars.ENV) }}\n    steps:\n")],
                [("    steps:\n", "    steps:\n      - run: echo \"X=1\" >> \"$GITHUB_ENV\"\n      - run: true\n")],
                [("  test:\n", "  test:\n    needs:\n      - a: b\n")],
                [("jobs:\n", "jobs:\n  gate:\n    needs: test\n    runs-on: ubuntu-latest\n    steps:\n"
                  "      - run: true\n"), ("  test:\n", "  test:\n    needs: gate\n")],
                [("cargo test --locked --all-targets\n",
                  "cargo test --locked --workspace --exclude 'v*' --all-targets\n")],
                # The soundness review of 11b204c: whitespace that YAML reads
                # differently, keys in another case, RUSTFLAGS and `..`.
                [(step, "      - run: cargo test --locked --all-targets # x\u0085        if: false\n")],
                [("    steps:\n", "    # note\u2028    if: false\n    steps:\n")],
                [(step, "      - run: cargo test --locked --all-targets \u3000\n")],
                [(step, step + "          \u00a0\n")],
                [(step, step + "        If: false\n")],
                [(step, step + "        Shell: sh\n")],
                [("jobs:\n", "env:\n  RUSTFLAGS: --cfg x\njobs:\n")],
                [(step, step + "        working-directory: link/..\n")],
                [(step, "      - run: 'cargo' test --locked --all-targets\n")],
                # The review of #656: keys in another case in triggers, needed jobs
                # and matrices, symbolic links and CARGO_ variables.
                [("jobs:\n", "jobs:\n  gate:\n    If: false\n    runs-on: ubuntu-latest\n    steps:\n"
                  "      - run: true\n"), ("  test:\n", "  test:\n    needs: gate\n")],
                [("  pull_request:\n", "  pull_request:\n    Paths: [docs/**]\n")],
                [("  pull_request:\n", "  Pull_Request:\n")],
                [("runs-on: ubuntu-latest\n", "runs-on: ${{ matrix.os }}\n    strategy:\n      matrix:\n"
                  "        os: [ubuntu-latest]\n        Exclude:\n          - os: ubuntu-latest\n")],
                [("    runs-on: ubuntu-latest\n", "    Runs-On: ubuntu-latest\n    runs-on: ubuntu-latest\n")],
                [("jobs:\n", "Defaults:\n  run:\n    shell: sh\njobs:\n")],
                [(step, step + "        Env:\n          BASH_ENV: /tmp/exit.sh\n")],
                [("    steps:\n", "    steps:\n      - Run: echo \"X=1\" >> \"$GITHUB_ENV\"\n")],
                [("jobs:\n", "env:\n  CARGO_ENCODED_RUSTFLAGS: x\njobs:\n")],
                [("jobs:\n", "env:\n  CARGO_HOME: .cargo-home\njobs:\n")],
                # The soundness review of #656: HOME, and YAML anchors and aliases.
                [("jobs:\n", "env:\n  HOME: fakehome\njobs:\n")],
                [("    steps:\n", "    steps:\n      - name: &s echo \"BASH_ENV=/tmp/x\" >> \"$GITHUB_ENV\"\n"
                  "        run: *s\n")]):
            with self.subTest(edits=edits):
                workflow = WORKFLOW
                for old, new in edits:
                    self.assertIn(old, workflow)
                    workflow = workflow.replace(old, new, 1)
                self.put(".github/workflows/ci.yml", workflow)
                self.assertRejected("no CI step runs `tests/demo.rs::identity_runs`")

    def test_steps_of_a_job_that_needs_an_unconditional_job_count(self):
        self.edit(".github/workflows/ci.yml", "jobs:\n", "jobs:\n  build:\n    runs-on: macos-latest\n"
                  "    steps:\n      - run: true\n")
        self.edit(".github/workflows/ci.yml", "  test:\n", "  test:\n    needs: [build]\n")
        self.assertEqual(self.errors(), [])

    def test_commands_that_run_no_cited_test(self):
        rust, python = "no CI step runs `tests/demo.rs::identity_runs`", \
            "no CI step runs `scripts/test_demo.py::DemoTests::test_identity`"
        for old, new, fragment in (
                ("cargo test --locked --all-targets\n", "cargo test --locked --all-targets --help\n", rust),
                ("cargo test --locked --all-targets\n", "cargo test --locked --all-targets -- -h\n", rust),
                ("cargo test --locked --all-targets\n", "cargo test --locked --doc\n", rust),
                ("cargo test --locked --all-targets\n", "env cargo test --locked --all-targets\n", rust),
                ("python3 -m unittest", "python3 -cpass -m unittest", python),
                ("-p 'test_*.py'", "-p 'test_*.py' --help", python),
                ("-p 'test_*.py'", "-p 'test_*.py' -t .", python),
                ("-p 'test_*.py'", "-p 'test_*.py' --unknown", python),
                ("cargo test --locked --all-targets\n", "cargo test --locked --all-targets --target x\n", rust),
                ("cargo test --locked --all-targets\n", "cargo test --locked --all-targets --config x\n", rust),
                ("cargo test --locked --all-targets\n",
                 "cargo test --locked --all-targets -- --exclude-should-panic\n", rust),
                ("bash scripts/check_kernel_regressions.sh", "bash -n scripts/check_kernel_regressions.sh",
                 "no CI step runs scripts/check_kernel_regressions.sh"),
                ("cargo test --locked --all-targets\n",
                 "cargo test --locked --workspace --exclude vastitas@0.1.0 --all-targets\n", rust),
                ("discover -s scripts", "discover scripts -s experiments", python),
                ("      - run: bash scripts/check_kernel_regressions.sh\n",
                 "      - run: bash check_kernel_regressions.sh\n        working-directory: scripts\n",
                 "no CI step runs scripts/check_kernel_regressions.sh"),
                ("bash scripts/check_kernel_regressions.sh", "bash link/../scripts/check_kernel_regressions.sh",
                 "no CI step runs scripts/check_kernel_regressions.sh")):
            with self.subTest(new=new):
                self.put(".github/workflows/ci.yml", WORKFLOW.replace(old, new, 1))
                self.assertRejected(fragment)

    def test_conditional_steps_and_jobs_do_not_count(self):
        self.rejects_with_step("      - run: cargo test --locked --all-targets\n"
                               "        if: github.event_name == 'push'\n")
        self.edit(".github/workflows/ci.yml", "        if: github.event_name == 'push'\n",
                  "        continue-on-error: true\n")
        self.assertRejected("no CI step runs `tests/demo.rs::identity_runs`")
        self.edit(".github/workflows/ci.yml", "        continue-on-error: true\n", "")
        self.edit(".github/workflows/ci.yml", "  test:\n", "  test:\n    if: false\n")
        self.assertRejected("no CI step runs `tests/demo.rs::identity_runs`")

    def test_filtered_pull_request_triggers_do_not_count(self):
        self.edit(".github/workflows/ci.yml", "  pull_request:\n", "  pull_request:\n    paths: ['docs/**']\n")
        self.assertRejected("no CI step runs `tests/demo.rs::identity_runs`")

    def test_steps_in_another_directory_do_not_count(self):
        self.rejects_with_step("      - run: cargo test --locked --all-targets\n"
                               "        working-directory: experiments\n")
        self.edit(".github/workflows/ci.yml", "      - run: cargo test --locked --all-targets\n"
                  "        working-directory: experiments\n",
                  "      - run: cd experiments && cargo test --locked --all-targets\n")
        self.assertRejected("no CI step runs `tests/demo.rs::identity_runs`")

    def test_build_only_and_listing_steps_do_not_run_tests(self):
        self.rejects_with_step("      - run: cargo test --locked --all-targets --no-run\n")
        self.edit(".github/workflows/ci.yml", "--all-targets --no-run", "--all-targets -- --list")
        self.assertRejected("no CI step runs `tests/demo.rs::identity_runs`")

    def test_regression_script_must_be_run(self):
        self.edit(".github/workflows/ci.yml", "bash scripts/check_kernel_regressions.sh",
                  "shellcheck scripts/check_kernel_regressions.sh")
        self.assertRejected("no CI step runs scripts/check_kernel_regressions.sh")

    def test_regression_builds_whose_failure_is_ignored_do_not_count(self):
        # The review of #655 found that the scan of the script ignored this.
        for script in ("set -euo pipefail\nif lake -d lean-kernel build VastitasKernel.DemoRegression; then\n"
                       "  echo ignored\nfi\n",
                       "set -euo pipefail\nlake -d lean-kernel build VastitasKernel.DemoRegression || true\n",
                       "lake -d lean-kernel build VastitasKernel.DemoRegression\necho done\n",
                       "nohup set -e\nlake -d lean-kernel build VastitasKernel.DemoRegression\n",
                       "set -e 2>/dev/null\nlake -d lean-kernel build VastitasKernel.DemoRegression\n",
                       "set -euo pipefail\n# off for now\rlake -d lean-kernel build VastitasKernel.DemoRegression\n",
                       "set -euo pipefail\nlake -d lean-kernel build --help VastitasKernel.DemoRegression\n",
                       "set -euo pipefail\ncd lean-kernel\nlake -d lean-kernel build VastitasKernel.DemoRegression\n"):
            with self.subTest(script=script):
                self.put("scripts/check_kernel_regressions.sh", "#!/usr/bin/env bash\n" + script)
                self.assertRejected("`VastitasKernel.DemoRegression` is not a module that "
                                    "scripts/check_kernel_regressions.sh builds")

    def test_regression_script_may_go_to_the_repository_root(self):
        self.put("scripts/check_kernel_regressions.sh", "#!/usr/bin/env bash\nset -euo pipefail\n"
                 "cd \"$(dirname \"$0\")/..\"\nlake -d lean-kernel build \\\n  VastitasKernel.DemoRegression\n")
        self.assertEqual(self.errors(), [])

    def test_commented_regression_modules_are_not_built(self):
        self.edit("docs/spec/demo.toml", '"VastitasKernel.DemoRegression"]', '"VastitasKernel.OldRegression"]')
        self.put("lean-kernel/VastitasKernel/OldRegression.lean", "")
        self.edit("scripts/check_kernel_regressions.sh", "lake -d lean-kernel build",
                  "# Retired; lake -d lean-kernel build VastitasKernel.OldRegression\nlake -d lean-kernel build")
        self.assertRejected("`VastitasKernel.OldRegression` is not a module that "
                            "scripts/check_kernel_regressions.sh builds")

    def test_conditionally_compiled_tests_do_not_count(self):
        self.edit("tests/demo.rs", "#[test]\nfn identity_runs() {}",
                  "#[test]\n#[cfg(feature = \"none\")]\nfn identity_runs() {}")
        self.assertRejected("`tests/demo.rs::identity_runs` is compiled only under a #[cfg(...)] condition")

    def test_rust_tests_that_libtest_may_not_build_or_collect(self):
        # The review of #655 found a cfg that cfg_attr adds; a test inside a
        # function is no test, and Cargo.toml may build the file differently.
        for old, new, fragment in (
                ("#[test]\nfn identity_runs() {}", "#[test]\n#[cfg_attr(all(), cfg(any()))]\nfn identity_runs() {}",
                 "`tests/demo.rs::identity_runs` is compiled only under a #[cfg(...)] condition"),
                ("#[test]\nfn identity_runs() {}", "#![cfg_attr(all(), cfg(any()))]\n#[test]\nfn identity_runs() {}",
                 "`tests/demo.rs::identity_runs` is compiled only under a #[cfg(...)] condition"),
                ("#[test]\nfn identity_runs() {}", "fn outer() {\n    #[test]\n    fn identity_runs() {}\n}",
                 "tests/demo.rs has no #[test] function `identity_runs`")):
            with self.subTest(new=new):
                self.put("tests/demo.rs", RUST)
                self.edit("tests/demo.rs", old, new)
                self.assertRejected(fragment)
        self.put("tests/demo.rs", RUST)
        for manifest in ('[package]\nname = "vastitas"\nautotests = false\n',
                         '[package]\nname = "vastitas"\n\n[[test]]\nname = "demo"\nharness = false\n',
                         '[package]\nname = "vastitas"\n\n[[test]]\nname = "demo"\nrequired-features = ["x"]\n'):
            with self.subTest(manifest=manifest):
                self.put("Cargo.toml", manifest)
                self.assertRejected("Cargo.toml sets `autotests = false` or lists tests/demo.rs under [[test]]")

    def test_repository_files_that_change_which_tests_run(self):
        # The soundness review of 11b204c: a local unittest shadows the standard
        # library under `python3 -m`, and Cargo may not run the root tests at all.
        rust = "Cargo.toml has no root package that `cargo test` runs by default"
        for files, fragment in (
                ({"unittest.py": "import sys\nsys.exit(0)\n"},
                 "no CI step runs `scripts/test_demo.py::DemoTests::test_identity`"),
                ({"Cargo.toml": "[workspace]\nmembers = []\n"}, rust),
                ({"Cargo.toml": '[package]\nname = "vastitas"\n\n[workspace]\ndefault-members = ["other"]\n'}, rust),
                ({".cargo/config.toml": "[target.'cfg(all())']\nrunner = \"true\"\n"}, rust),
                ({".cargo/config": "[target.'cfg(all())']\nrunner = \"true\"\n"}, rust),
                ({"Cargo.toml": '[package]\nname = "vastitas"\n\n[workspace]\ndefault-members = ["."]\n'}, rust),
                ({"Cargo.toml": '[package]\nname = "vastitas"\n\n[[test]]\nname = "demo"\npath = "tests/other.rs"\n'},
                 "Cargo.toml sets `autotests = false` or lists tests/demo.rs under [[test]]")):
            with self.subTest(files=files):
                for name, contents in FILES.items():
                    self.put(name, contents)
                for name in ("unittest.py", ".cargo/config.toml", ".cargo/config"):
                    if (self.root / name).exists():
                        (self.root / name).unlink()
                for name, contents in files.items():
                    self.put(name, contents)
                self.assertRejected(fragment)

    def test_workflow_files_that_are_symbolic_links_do_not_count(self):
        self.put("workflow.yml", WORKFLOW)
        (self.root / ".github/workflows/ci.yml").unlink()
        os.symlink("../../workflow.yml", self.root / ".github/workflows/ci.yml")
        self.assertRejected("no CI step runs `tests/demo.rs::identity_runs`")

    def test_workflow_directories_that_are_symbolic_links_do_not_count(self):
        for link in (".github", ".github/workflows"):
            with self.subTest(link=link):
                self.setUp()
                os.rename(self.root / link, self.root / "moved")
                os.symlink(os.path.relpath(self.root / "moved", (self.root / link).parent), self.root / link)
                self.assertRejected("no CI step runs `tests/demo.rs::identity_runs`")

    def test_modules_that_shadow_the_standard_library(self):
        # The review of #656: any standard-library name in the working directory wins under `python3 -m`.
        python = "no CI step runs `scripts/test_demo.py::DemoTests::test_identity`"
        for name in ("argparse.py", "unittest/__init__.py", "fnmatch.pyc", "sitecustomize.py"):
            with self.subTest(name=name):
                self.setUp()
                self.put(name, "import sys\nsys.exit(0)\n")
                self.assertRejected(python)
        self.setUp()
        self.put("experiments/argparse.py", "")
        self.edit(".github/workflows/ci.yml", "        run: python3 -m unittest discover -s scripts -p 'test_*.py'\n",
                  "        run: python3 -m unittest discover -s ../scripts -p 'test_*.py'\n"
                  "        working-directory: experiments\n")
        self.assertRejected(python)
        self.setUp()
        self.put("argparse", "")
        self.put("unittest/data.txt", "")
        self.assertEqual(self.errors(), [])

    def test_directories_through_a_symbolic_link_do_not_count(self):
        # The soundness review of #656: programs see a link's target, while the reader follows its name.
        python = "no CI step runs `scripts/test_demo.py::DemoTests::test_identity`"
        step = "        run: python3 -m unittest discover -s scripts -p 'test_*.py'\n"
        for new in ("        run: python3 -m unittest discover -s ../scripts -p 'test_*.py'\n"
                    "        working-directory: link\n",
                    "        run: |\n          cd link\n          python3 -m unittest discover -s ../scripts -p 'test_*.py'\n",
                    "        run: python3 -m unittest discover -s linked -p 'test_*.py'\n"):
            with self.subTest(new=new):
                self.setUp()
                self.put("experiments/foo/.keep", "")
                os.symlink("experiments/foo", self.root / "link")
                os.symlink("scripts", self.root / "linked")
                self.edit(".github/workflows/ci.yml", step, new)
                self.assertRejected(python)

    def test_standard_library_names_in_the_start_directory(self):
        self.put("scripts/difflib.py", "import sys\nsys.exit(0)\n")
        self.assertRejected("no CI step runs `scripts/test_demo.py::DemoTests::test_identity`")

    def test_regression_script_runs_as_a_path_from_the_root(self):
        self.edit(".github/workflows/ci.yml", "bash scripts/check_kernel_regressions.sh",
                  "bash ./scripts/check_kernel_regressions.sh")
        self.assertEqual(self.errors(), [])

    def test_python_tests_whose_class_or_base_the_module_rebinds(self):
        cited = "unittest may skip `scripts/test_demo.py::DemoTests::test_identity` or expect it to fail"
        for source in (PYTHON.replace("import unittest\n", "import unittest\n\n\nclass TestCase:\n    pass\n")
                       .replace("(unittest.TestCase)", "(TestCase)"),
                       PYTHON + "\n\ndel DemoTests\n", PYTHON + "\n\nDemoTests = None\n",
                       PYTHON.replace("import unittest\n", "import mock as unittest\n"),
                       PYTHON.replace("import unittest\n", "import unittest\nfrom helpers import TestCase\n"),
                       # The review of #656.
                       PYTHON + "\n\n(DemoTests := None)\n", PYTHON + "\n\nfor DemoTests in [None]:\n    pass\n",
                       PYTHON + "\n\nwith open(__file__) as DemoTests:\n    pass\n",
                       PYTHON + "\n\ntry:\n    pass\nexcept ValueError as DemoTests:\n    pass\n",
                       PYTHON + "\n\nimport os as DemoTests\n", PYTHON + "\n\ndef DemoTests():\n    pass\n",
                       PYTHON + "\n\nglobals()['DemoTests'] = None\n", PYTHON + "\n\nexec('del DemoTests')\n",
                       PYTHON + "\n\ntype.__setattr__(DemoTests, 'test_identity', None)\n",
                       PYTHON + "\n\nTestCase = object\n", PYTHON + "\n\ndef TestCase():\n    pass\n",
                       PYTHON.replace("import unittest\n", "import unittest\nfrom unittest import TestCase as "
                                      "IsolatedAsyncioTestCase\n"),
                       PYTHON.replace("    def test_identity", "    @print\n    def test_identity"),
                       PYTHON.replace("class DemoTests", "@print\nclass DemoTests"),
                       PYTHON.replace("(unittest.TestCase)", "(unittest.TestCase, metaclass=type)"),
                       PYTHON.replace("        pass\n", "        pass\n\n    def run(self, result=None):\n"
                                      "        return result\n"),
                       # The soundness review of #656.
                       PYTHON.replace("import unittest\n", "import unittest\nfrom helpers import *\n"),
                       PYTHON + "\n\nAlias = DemoTests\nAlias.test_identity = None\n",
                       PYTHON + "\n\nunittest.TestCase.run = lambda *arguments: None\n",
                       PYTHON + "\n\nmatch None:\n    case DemoTests:\n        pass\n"):
            with self.subTest(source=source):
                self.put("scripts/test_demo.py", source)
                self.assertRejected(cited)
        # A base from another module is no unittest base that the check reads.
        for base in ("helpers.TestCase", "helpers.Mixin, unittest.TestCase"):
            with self.subTest(base=base):
                self.put("scripts/test_demo.py", PYTHON.replace("import unittest\n", "import unittest\nimport helpers\n")
                         .replace("(unittest.TestCase)", f"({base})"))
                self.assertRejected("scripts/test_demo.py has no unittest test method `DemoTests.test_identity`")

    def test_python_tests_that_import_unittest_plainly_count(self):
        for source in (PYTHON.replace("import unittest\n", "from unittest import TestCase\n")
                       .replace("(unittest.TestCase)", "(TestCase)"),
                       PYTHON.replace("import unittest\n", "import unittest\nimport re\n\nPATTERN = re.compile('x')\n")):
            with self.subTest(source=source):
                self.put("scripts/test_demo.py", source)
                self.assertEqual(self.errors(), [])

    def test_rust_tests_with_attributes_that_the_check_does_not_read(self):
        unread = "`tests/demo.rs::identity_runs`, an enclosing module or its file carries an attribute"
        for old, new in (("#[test]\nfn identity_runs() {}", "#[my_crate::attr]\n#[test]\nfn identity_runs() {}"),
                         ("#[test]\nfn identity_runs() {}", "#[test]\n#[cfg_attr(miri, tokio::test)]\nfn identity_runs() {}"),
                         ("#[test]\nfn identity_runs() {}", "#![my_attr]\n#[test]\nfn identity_runs() {}")):
            with self.subTest(new=new):
                self.put("tests/demo.rs", RUST.replace(old, new))
                self.assertRejected(unread)

    def test_rust_tests_inside_macros_are_not_tests(self):
        for body in ("never!(\n    #[test]\n    fn identity_runs() {}\n);",
                     "never!(\n    vec![1];\n    #[test]\n    fn identity_runs() {}\n);",
                     "macro_rules! unused (\n    () => (\n        #[test]\n        fn identity_runs() {}\n    );\n);",
                     "macro_rules! unused {\n    () => (\n        #[test]\n        fn identity_runs() {}\n    );\n}",
                     # The soundness review of #656: spaces, raw identifiers and other letters.
                     "never ! (\n    #[test]\n    fn identity_runs() {}\n);",
                     "macro_rules ! m (\n    () => (\n        #[test]\n        fn identity_runs() {}\n    );\n);",
                     "macro_rules! r#m (\n    () => (\n        #[test]\n        fn identity_runs() {}\n    );\n);",
                     "\u00f1ever!(\n    #[test]\n    fn identity_runs() {}\n);"):
            with self.subTest(body=body):
                self.put("tests/demo.rs", RUST.replace("#[test]\nfn identity_runs() {}", body))
                self.assertRejected("tests/demo.rs has no #[test] function `identity_runs`")

    def test_tests_in_comments_are_not_tests(self):
        self.edit("tests/demo.rs", "#[test]\nfn identity_runs() {}", "/*\n#[test]\nfn identity_runs() {}\n*/")
        self.assertRejected("tests/demo.rs has no #[test] function `identity_runs`")

    def test_nested_tests_have_module_paths(self):
        self.edit("tests/demo.rs", "#[test]\nfn identity_runs() {}",
                  "mod inner {\n    #[test]\n    fn identity_runs() {}\n}")
        self.assertRejected("tests/demo.rs has no #[test] function `identity_runs`")
        self.edit("docs/spec/demo.toml", '"tests/demo.rs::identity_runs", "scripts',
                  '"tests/demo.rs::inner::identity_runs", "scripts')
        self.edit("docs/spec/demo.toml", 'example_test = "tests/demo.rs::identity_runs"',
                  'example_test = "tests/demo.rs::inner::identity_runs"')
        self.assertEqual(self.errors(), [])

    def test_python_tests_need_a_test_case(self):
        self.edit("scripts/test_demo.py", "class DemoTests(unittest.TestCase):", "class DemoTests:")
        self.assertRejected("scripts/test_demo.py has no unittest test method `DemoTests.test_identity`")

    def test_status_of_the_wrong_type(self):
        self.edit("docs/spec/demo.toml", 'status = "not-claimed"', 'status = ["not-claimed"]')
        self.assertRejected("unknown status ['not-claimed']")

    def test_titles_hold_no_markup(self):
        self.edit("docs/spec/demo.toml", 'title = "Identity"', 'title = "Identity] of x"')
        self.assertRejected("`title` must not contain")
        self.edit("docs/spec/demo.toml", 'title = "Identity] of x"', 'title = "Identity"')
        self.edit("docs/spec/assumptions.toml", 'title = "Frontend parsing"', 'title = "Frontend <b>parsing</b>"')
        self.assertRejected("[assumption.frontend]: `title` must not contain")

    def test_subjects_hold_no_backquotes(self):
        self.edit("docs/spec/demo.toml", 'subject = "std::demo::id"\nstatement = "id(x) = x for every x."',
                  'subject = "id `x` y"\nstatement = "id(x) = x for every x."')
        self.assertRejected("`subject` must not contain a backquote")

    def drop_bridge_claim(self):
        self.edit("docs/spec/demo.toml", BRIDGE_CLAIM, "")

    def test_pins_of_an_environment_without_citations(self):
        self.drop_bridge_claim()
        self.assertRejected("docs/spec/pins/bridge.json: no claim cites a name of the bridge environment")
        (self.root / "docs/spec/pins/bridge.json").unlink()
        self.assertEqual(self.errors(), [])

    def test_unsorted_and_repeated_pins(self):
        self.put("docs/spec/pins/oracle.json", json.dumps({
            "format": 1, "environment": "oracle", "imports": ["VastitasKernel.Check", "VastitasOracle.Demo"],
            "entries": [ORACLE_PINS[1], ORACLE_PINS[0], ORACLE_PINS[1]]}))
        self.assertRejected("entries must be sorted by name", "`VastitasOracle.Demo.id_eq` is pinned twice")

    def test_malformed_enforced_by(self):
        self.edit("docs/spec/demo.toml", 'code = "E_DEMO" }]', 'code = "demo" }]')
        self.assertRejected("`code` must be a diagnostic code such as E_METRIC")
        self.edit("docs/spec/demo.toml",
                  'enforced_by = [{ definition = "VastitasKernel.Check.check", code = "demo" }]',
                  'enforced_by = []')
        self.assertRejected("`enforced_by` must be a non-empty list of tables")

    def fake_lake(self, report):
        """A `lake` on PATH that writes the value of the expression `report` as the
        resolver's report; the expression sees the request as `request`."""
        directory = self.root / "fakebin"
        directory.mkdir(exist_ok=True)
        lake = directory / "lake"
        lake.write_text("#!/usr/bin/env python3\nimport json, os\n"
                        f"report = {report!r}\n"
                        "request = json.load(open(os.environ['VASTITAS_SPEC_INPUT']))\n"
                        "facts = eval(report)\n"
                        "json.dump(facts, open(os.environ['VASTITAS_SPEC_REPORT'], 'w'))\n"
                        "raise SystemExit(1 if facts['problems'] else 0)\n", encoding="utf-8")
        lake.chmod(lake.stat().st_mode | stat.S_IEXEC)
        for name in ("lean", "lean-bridge"):
            (self.root / name).mkdir(exist_ok=True)
        return mock.patch.dict(os.environ, {"PATH": f"{directory}{os.pathsep}{os.environ['PATH']}"})

    def test_update_statements_pins_what_the_resolver_reports(self):
        (self.root / "docs/spec/pins/oracle.json").unlink()
        report = ("{'format': 1, 'environment': 'oracle', 'problems': [], 'entries': ["
                  "dict({'name': e['name'], 'kind': e['kind'], 'module': e['name'].rsplit('.', 1)[0]}, "
                  "**({'statement': 'sha256:' + 'c' * 64} if e['kind'] == 'theorem' else {})) "
                  "for e in request['entries']]}")
        with self.fake_lake(report):
            self.assertEqual(check_spec.update_statements(self.root, "oracle"), 0)
        pins = json.loads((self.root / "docs/spec/pins/oracle.json").read_text(encoding="utf-8"))
        self.assertEqual([entry["name"] for entry in pins["entries"]],
                         ["VastitasKernel.Check.check", "VastitasOracle.Demo.id_eq"])
        self.assertEqual(self.errors(), [])

    def test_update_statements_writes_nothing_on_problems(self):
        before = (self.root / "docs/spec/pins/oracle.json").read_text(encoding="utf-8")
        report = "{'format': 1, 'environment': 'oracle', 'entries': [], 'problems': ['x: depends on sorryAx']}"
        with self.fake_lake(report):
            self.assertEqual(check_spec.update_statements(self.root, "oracle"), 1)
        self.assertEqual((self.root / "docs/spec/pins/oracle.json").read_text(encoding="utf-8"), before)

    def test_update_statements_without_citations_removes_the_pins(self):
        self.drop_bridge_claim()
        self.assertEqual(check_spec.update_statements(self.root, "bridge"), 0)
        self.assertFalse((self.root / "docs/spec/pins/bridge.json").exists())

    def test_update_statements_stops_on_specification_errors(self):
        self.edit("docs/spec/demo.toml", 'status = "not-claimed"', 'status = "implemented"')
        self.assertEqual(check_spec.update_statements(self.root, "oracle"), 1)

    def test_text_outside_code_is_escaped(self):
        self.edit("docs/spec/demo.toml", 'statement = "id(x) = x for every x."',
                  'statement = "id: Pair<Int> -> Pair<Int> keeps `Pair<Int>` & more."')
        self.assertEqual(self.errors(), [])
        chapter = (self.root / "docs/spec/demo.md").read_text(encoding="utf-8")
        self.assertIn("id: Pair&lt;Int&gt; -&gt; Pair&lt;Int&gt; keeps `Pair<Int>` &amp; more.", chapter)

    def test_unmatched_backquote(self):
        self.edit("docs/spec/demo.toml", 'statement = "id(x) = x for every x."', 'statement = "`id(x) = x"')
        self.assertRejected("`statement` has an unmatched backquote")

    def test_chapter_contents(self):
        chapter = (self.root / "docs/spec/demo.md").read_text(encoding="utf-8")
        for fragment in (
                '<a id="demo.identity"></a>',
                "| [Identity](#demo.identity) | Proved (oracle), Proved (bridge), Tested, Tested, Assumed, "
                "Not claimed |",
                "- Rule: [Identity](../rules.md#identity)",
                "- `oracle`: [Proved (oracle)](../specifications.md#proved-oracle)",
                f"    - [`VastitasOracle.Demo`]({check_spec.BLOB}lean/VastitasOracle/Demo.lean): "
                "`VastitasOracle.Demo.id_eq`",
                "  - Premises: none",
                "  - Assumes: [Frontend parsing](assumptions.md#assumption.frontend)",
                "  - Enforced by: `VastitasKernel.Check.check` in [`VastitasKernel.Check`]",
                "which reports `E_DEMO`",
                "    - x is a real number",
                f"    - `identity_runs` in [`tests/demo.rs`]({check_spec.BLOB}tests/demo.rs)",
                "    - `DemoTests.test_identity` in [`scripts/test_demo.py`]",
                "  - Evidence: [Frontend parsing](assumptions.md#assumption.frontend)",
                "  - Reason: Native refinement is outside the profile.",
                "  - Issue: [#1](https://github.com/MGYamada/Vastitas/issues/1)",
                "- Not executed: no test exercises linearity"):
            self.assertIn(fragment, chapter)
        registry = (self.root / "docs/spec/assumptions.md").read_text(encoding="utf-8")
        self.assertIn('<a id="assumption.frontend"></a>', registry)
        self.assertIn("- [`demo.identity`](demo.md#demo.identity) (`oracle`)", registry)
        self.assertIn("- [`demo.identity`](demo.md#demo.identity) (`trust`)", registry)
        self.assertIn("No claim cites this assumption.", registry)


class ParserTests(unittest.TestCase):
    def test_cargo_targets_filters_and_ignored(self):
        run = cargo_run("--locked --test numerical_source --test tensor_source -- --ignored".split())
        self.assertEqual((run.every_test, run.targets, run.ignored),
                         (False, {"numerical_source", "tensor_source"}, "only"))
        self.assertTrue(run.runs("tensor_source", "anything", True))
        self.assertFalse(run.runs("tensor_source", "anything", False))
        self.assertFalse(run.runs("examples", "anything", True))
        run = cargo_run("--locked --all-targets".split())
        self.assertTrue(run.runs("examples", "a", False))
        self.assertFalse(run.runs("examples", "a", True))
        run = cargo_run("--locked --test promotion stdlib_ir_matches_proof_fixture".split())
        self.assertTrue(run.runs("promotion", "stdlib_ir_matches_proof_fixture", False))
        self.assertFalse(run.runs("promotion", "another_test", False))
        run = cargo_run("--locked -- --include-ignored --skip slow --skip=heavy".split())
        self.assertTrue(run.runs("any", "fast", True) and run.runs("any", "fast", False))
        self.assertFalse(run.runs("any", "slow_case", False) or run.runs("any", "heavy_case", False))
        self.assertTrue(cargo_run("-- --exact a::b".split()).runs("t", "a::b", False))
        self.assertFalse(cargo_run("-- --exact b".split()).runs("t", "a::b", False))
        self.assertFalse(cargo_run("--lib".split()).runs("examples", "a", False))
        self.assertTrue(cargo_run("--test=demo".split()).runs("demo", "a", False))
        for arguments in ("--all-targets --no-run", "-- --list", "-p other", "--manifest-path x/Cargo.toml",
                          "--help", "-h", "-- --help", "--doc", "--workspace --exclude vastitas", "--target x",
                          "--config x", "-Z x", "-j4", "-- --exclude-should-panic", "-- --format json", "--test",
                          "--workspace --exclude v*", "-- --bench", "--workspace --exclude other"):
            self.assertFalse(cargo_run(arguments.split(), "vastitas").runs("demo", "a", False), arguments)
        self.assertTrue(cargo_run("-p vastitas --manifest-path Cargo.toml".split(), "vastitas")
                        .runs("demo", "a", False))

    def test_unittest_discover(self):
        here = PurePosixPath(".")
        run = discover_run(["-s", "scripts", "-p", "test_*.py"], here)
        self.assertTrue(run.runs("scripts/test_demo.py", "DemoTests", "test_identity"))
        self.assertFalse(run.runs("tools/test_demo.py", "DemoTests", "test_identity"))
        run = discover_run(["-s", "scripts", "-p", "test_diagnostic_reference.py", "-v"], here)
        self.assertFalse(run.runs("scripts/test_demo.py", "DemoTests", "test_identity"))
        run = discover_run(["-s", "./experiments/trees/", "-p", "test_*.py", "-k", "identity"], here)
        self.assertTrue(run.runs("experiments/trees/test_a.py", "Tests", "test_identity"))
        self.assertFalse(run.runs("experiments/trees/test_a.py", "Tests", "test_other"))
        run = discover_run(["--start-directory=scripts", "--pattern=test_demo.py"], here)
        self.assertTrue(run.runs("scripts/test_demo.py", "DemoTests", "test_identity"))
        self.assertFalse(run.runs("scripts/test_other.py", "DemoTests", "test_identity"))
        self.assertTrue(discover_run(["-sscripts", "-ptest_*.py"], here).runs("scripts/test_a.py", "A", "test_a"))
        self.assertTrue(discover_run(["scripts", "test_*.py"], here).runs("scripts/test_a.py", "A", "test_a"))
        self.assertTrue(discover_run(["-s", "."], PurePosixPath("scripts")).runs("scripts/test_a.py", "A", "test_a"))
        self.assertTrue(discover_run(["-v", "-f", "--durations", "3", "-s", "scripts"], here)
                        .runs("scripts/test_a.py", "A", "test_a"))
        for arguments in (["--help"], ["-h"], ["-s", "scripts", "-t", "."], ["--top-level-directory=."],
                          ["scripts", "test_*.py", "."], ["-s"], ["--unknown"], ["-x"],
                          ["scripts", "-s", "experiments"], ["-p", "x", "scripts", "test_*.py"]):
            self.assertIsNone(discover_run(arguments, here), arguments)
        self.assertTrue(discover_run(["scripts", "-p", "test_*.py"], here).runs("scripts/test_a.py", "A", "test_a"))
        for arguments in ():
            self.assertIsNone(discover_run(arguments, here), arguments)

    def test_pull_request_triggers(self):
        self.assertTrue(every_pull_request({"pull_request": None, "push": None}))
        self.assertTrue(every_pull_request(["push", "pull_request"]))
        self.assertTrue(every_pull_request("pull_request"))
        self.assertFalse(every_pull_request({"pull_request": {"paths": ["a"]}}))
        self.assertFalse(every_pull_request({"pull_request": {"branches": ["main"]}}))
        self.assertFalse(every_pull_request({"push": {"branches": ["pull_request"]}}))
        self.assertFalse(every_pull_request({"workflow_dispatch": {"inputs": {"pull_request": {}}}}))

    def test_run_steps(self):
        workflow = "\n".join([
            "on:", "  pull_request:", "defaults:", "  run:", "    shell: bash", "jobs:",
            "  a:", "    runs-on: ${{ matrix.os }}", "    strategy:", "      matrix:",
            "        os: [ubuntu-latest, macos-latest]", "    steps:",
            "      - run: cargo test --lib",
            "      - run: >-", "          folded", "          text",
            "      - name: In a directory", "        working-directory: lean", "        run: |",
            "          lake build",
            "      - if: always()", "        run: skipped",
            "      - uses: actions/checkout@v4",
            "      - run: echo x >> \"$GITHUB_PATH\"",
            "      - run: after a write to GITHUB_PATH",
            "  b:", "    runs-on: ubuntu-latest", "    continue-on-error: true", "    steps:", "      - run: skipped",
            "  c:", "    runs-on: ubuntu-latest", "    needs: [b]", "    steps:", "      - run: skipped", ""])
        self.assertEqual(list(run_steps(workflow)),
                         [("cargo test --lib", PurePosixPath(".")), ("lake build\n", PurePosixPath("lean")),
                          ("echo x >> \"$GITHUB_PATH\"", PurePosixPath("."))])
        self.assertEqual(list(run_steps(workflow.replace("    shell: bash", "    shell: pwsh"))), [])
        self.assertEqual(list(run_steps(workflow.replace("  c:", "  'c':"))), [])

    def test_plain_commands(self):
        def commands(script, errexit=True, origin=None):
            return [(words, str(directory), counted)
                    for words, directory, counted in plain_commands(script, PurePosixPath("."), errexit, origin)]
        self.assertEqual(commands("# comment\n\necho 'a b' c=d\ncargo test \\\n  --lib"),
                         [(["echo", "a b", "c=d"], ".", True), (["cargo", "test", "--lib"], ".", True)])
        self.assertEqual(commands("cd sub\nmake\ncd ..\nmake"), [(["make"], "sub", True), (["make"], ".", True)])
        self.assertEqual(commands("set +e\ncd sub\nmake\nset -e\nmake"),
                         [(["make"], "None", False), (["make"], "None", True)])
        for script in ("make | tee log", "A=1 make", "export A=1", 'make "x"', "make\tx", "cd -P sub",
                       "cargo test \\\n# no", "time make", "{ make; }"):
            with self.subTest(script=script):
                self.assertEqual(commands(f"make\n{script}\nmake"), [(["make"], ".", True)])
        self.assertEqual(commands("make", errexit=False), [(["make"], ".", False)])
        self.assertEqual(commands("set -euo pipefail\nmake", errexit=False), [(["make"], ".", True)])
        self.assertEqual(commands('cd "$(dirname "$0")/.."\nmake', origin=PurePosixPath("scripts")),
                         [(["make"], ".", True)])
        self.assertEqual(commands('cd "$(dirname "$0")/.."\nmake'), [])
        for word in sorted(check_spec.SHELL_WORDS - check_spec.PLAIN_BUILTINS - {"cd", "set"}):
            with self.subTest(word=word):
                self.assertEqual(commands(f"make\n{word} x\nmake"), [(["make"], ".", True)])
        for script in ("$X 0", "make *", "printf -v PATH /tmp/fake", "command set +e"):
            with self.subTest(script=script):
                self.assertEqual(commands(f"make\n{script}\nmake"), [(["make"], ".", True)])
        self.assertEqual(commands("echo -e\nmake", errexit=False), [(["echo", "-e"], ".", False), (["make"], ".", False)])
        self.assertEqual(commands("set -x\nmake", errexit=False), [(["make"], ".", False)])
        self.assertEqual(commands("cargo test\\\n--lib"), [])
        self.assertEqual(commands("cd /tmp\nmake"), [(["make"], "None", True)])
        self.assertEqual(commands("make\n# ${{ x }}\nmake"), [(["make"], ".", True)])
        self.assertEqual(plain_set(["-euo", "pipefail"]), [(True, "errexit"), (True, "nounset"), (True, "pipefail")])
        self.assertEqual(plain_set(["+o", "errexit"]), [(False, "errexit")])
        for arguments in (["-n"], ["-o", "noexec"], ["-o", "+e"], ["-Qe"], ["-o"], [], ["--", "-e"], ["-t"],
                          ["-", "-e"]):
            self.assertIsNone(plain_set(arguments), arguments)

    def test_yaml_subset_rejects_keys_that_it_does_not_read(self):
        for text in ('jobs:\n  "a": 1\n', "jobs:\n  ? a\n  : 1\n", "jobs:\n  !!str a: 1\n", "jobs:\n  <<: *x\n",
                     'jobs:\n  a:\n    - "i\\x66": false\n', "jobs:\n\ta: 1\n"):
            with self.subTest(text=text):
                with self.assertRaises(check_spec.YamlError):
                    check_spec.yaml_load(text)
        self.assertIsInstance(check_spec.yaml_load("a: >\n  b\n  c\n")["a"], check_spec.Folded)
        self.assertIsInstance(check_spec.yaml_load("a: b\n  c\n")["a"], check_spec.Folded)
        self.assertNotIsInstance(check_spec.yaml_load("a: |\n  b\n")["a"], check_spec.Folded)
        self.assertEqual(check_spec.yaml_load('a:\n  - "b: c"\n'), {"a": ["b: c"]})
        self.assertEqual(check_spec.yaml_load("a: 'b' # 'c'\n"), {"a": "b"})
        self.assertEqual(check_spec.yaml_load('a: "b\\"c"\n'), {"a": 'b"c'})
        self.assertEqual(check_spec.yaml_load("a: 'b''c'\n"), {"a": "b'c"})
        self.assertEqual(check_spec.yaml_load('a: "b\\/c"\n'), {"a": "b/c"})
        for text in ("a: 'b\n  c'\nd: 1\n", "a:\n  - b\n c: 1\n", "a: [b,\n  c]\n", "a: 'b' c\n",
                     'a: "b\\nc"\n', "a: b\u0085c: d\n", "a: b\u3000\n", "a: b\x0cc\n",
                     "a: &x b\n", "a: *x\n", "a: !!str b\n", "a:\n  - *x\n", "a: [*x]\n"):
            with self.subTest(text=text):
                with self.assertRaises(check_spec.YamlError):
                    check_spec.yaml_load(text)

    def test_rust_attributes(self):
        source = "\n".join([
            "#[test]", "// note", "#[cfg(unix)]", "pub fn a() {}",
            "#[test]", '#[ignore = "x"]', "fn b() {}",
            "#[cfg(test)]", "fn c() {}",
            "#[test] fn d() {}",
            "#[test]", '#[cfg_attr(not(feature = "x"), ignore)]', "fn e() {}",
            "#[test]", "#[should_panic(", '    expected = "x"', ")]", "fn f() {}",
            "#[cfg(test)]", "mod tests {", "    #[test]", "    fn g() {}", "}",
            "/* #[test]", "fn h() {} */",
            'const S: &str = r#"', "#[test]", 'fn i() {}"#;',
            "fn helper<'a>(x: &'a str) -> char { '{' }",
            "#[test]", "fn j() {}",
            "#[test]", "#[serial]", "fn k() {}",
            "#[test]", "#[cfg_attr(miri, my_crate::attr)]", "fn l() {}",
            "#[test]", "#[allow(dead_code)]", "#[cfg_attr(unix, allow(unused))]", "fn m() {}",
            "#[my_crate::wrap]", "mod wrapped {", "    #[test]", "    fn n() {}", "}", ""])
        self.assertEqual(rust_tests(source), {
            "a": (False, True, False), "b": (True, False, False), "d": (False, False, False),
            "e": (True, False, False), "f": (False, False, False), "tests::g": (False, False, False),
            "j": (False, False, False), "k": (False, False, True), "l": (False, False, True),
            "m": (False, False, False), "wrapped::n": (False, False, True)})
        self.assertEqual(rust_tests("#![my_attr]\n#[test]\nfn o() {}\n"), {"o": (False, False, True)})
        self.assertEqual(rust_tests("#![allow(unused)]\n#![feature(x)]\n#[test]\nfn p() {}\n"),
                         {"p": (False, False, False)})

    def test_python_skips(self):
        source = "\n".join([
            "import unittest",
            "@unittest.skip('x')", "class A(unittest.TestCase):", "    def test_a(self): pass",
            "class B(unittest.TestCase):",
            "    @unittest.skipIf(True, 'y')", "    def test_b(self): pass",
            "    @unittest.skipIf(ROOT is None, 'y')", "    def test_c(self): pass",
            "    def helper(self): pass",
            "class Helper:", "    def test_d(self): pass",
            "class C(B):", "    def test_e(self): pass", ""])
        self.assertEqual(python_tests(source), {
            ("A", "test_a"): True, ("B", "test_b"): True, ("B", "test_c"): True,
            ("C", "test_b"): True, ("C", "test_c"): True, ("C", "test_e"): True})
        plain = "import unittest\nclass H(unittest.TestCase):\n    def test_k(self): pass\n" \
                "class I(H):\n    def test_l(self): pass\n"
        self.assertEqual(python_tests(plain), {("H", "test_k"): False, ("I", "test_k"): False, ("I", "test_l"): False})
        for line in ("def setUpModule():\n    raise unittest.SkipTest('x')", "load_tests = None",
                     "from unittest import expectedFailure", "X = unittest.case.skipTest"):
            with self.subTest(line=line):
                self.assertEqual(python_tests(f"{plain}{line}\n"),
                                 {("H", "test_k"): True, ("I", "test_k"): True, ("I", "test_l"): True})

    def test_yaml_subset_reads_the_repository_workflows(self):
        for path in sorted((check_spec.ROOT / ".github/workflows").glob("*.yml")):
            tree = check_spec.yaml_load(path.read_text(encoding="utf-8"))
            self.assertIsInstance(tree.get("jobs"), dict, path.name)
            for job in tree["jobs"].values():
                for step in job.get("steps") or []:
                    self.assertIsInstance(step, dict, path.name)
                    self.assertTrue("run" in step or "uses" in step, (path.name, step))

    def test_repository_workflows(self):
        repository = check_spec.Repository(check_spec.ROOT)
        errors = []
        repository.check_test("tests/promotion.rs::stdlib_ir_matches_proof_fixture", "here", errors)
        repository.check_test("VastitasKernel.MetricFormRegression", "here", errors)
        repository.check_test("scripts/test_check_spec.py::ParserTests::test_repository_workflows", "here", errors)
        self.assertEqual(errors, [])


if __name__ == "__main__":
    unittest.main()
