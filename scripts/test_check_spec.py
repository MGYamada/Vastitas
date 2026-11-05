"""Regressions for scripts/check_spec.py: each case breaks one rule of a valid fixture."""
import json
from pathlib import Path
import tempfile
import unittest

import check_spec
from check_spec import cargo_run, discover_run, pull_request_trigger, python_tests, rust_tests


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

    @unittest.skip("never")
    def test_skipped(self):
        pass
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
    "tests/demo.rs": RUST,
    "scripts/test_demo.py": PYTHON,
    "scripts/check_kernel_regressions.sh": "#!/usr/bin/env bash\nlake -d lean-kernel build \\\n"
                                           "  VastitasKernel.DemoRegression\n",
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
        self.assertRejected("scripts/test_demo.py has no test method `DemoTests.test_absent`")

    def test_skipped_python_test(self):
        self.edit("docs/spec/demo.toml", "test_demo.py::DemoTests::test_identity",
                  "test_demo.py::DemoTests::test_skipped")
        self.assertRejected("`scripts/test_demo.py::DemoTests::test_skipped` is skipped unconditionally")

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
        self.assertEqual((run.every_test, run.targets, run.ignored), (False, {"numerical_source", "tensor_source"}, "only"))
        self.assertTrue(run.runs("tensor_source", "anything", True))
        self.assertFalse(run.runs("tensor_source", "anything", False))
        self.assertFalse(run.runs("examples", "anything", True))
        run = cargo_run("--locked --all-targets".split())
        self.assertTrue(run.runs("examples", "a", False))
        self.assertFalse(run.runs("examples", "a", True))
        run = cargo_run("--locked --test promotion stdlib_ir_matches_proof_fixture".split())
        self.assertTrue(run.runs("promotion", "stdlib_ir_matches_proof_fixture", False))
        self.assertFalse(run.runs("promotion", "another_test", False))
        run = cargo_run("--locked -- --include-ignored --skip slow".split())
        self.assertTrue(run.runs("any", "fast", True) and run.runs("any", "fast", False))
        self.assertFalse(run.runs("any", "slow_case", False))
        self.assertFalse(cargo_run("--lib".split()).runs("examples", "a", False))
        self.assertTrue(cargo_run("--test=demo".split()).runs("demo", "a", False))

    def test_unittest_discover(self):
        run = discover_run(["-s", "scripts", "-p", "test_*.py"])
        self.assertTrue(run.runs("scripts/test_demo.py", "DemoTests", "test_identity"))
        self.assertFalse(run.runs("tools/test_demo.py", "DemoTests", "test_identity"))
        run = discover_run(["-s", "scripts", "-p", "test_diagnostic_reference.py", "-v"])
        self.assertFalse(run.runs("scripts/test_demo.py", "DemoTests", "test_identity"))
        run = discover_run(["-s", "./experiments/trees/", "-p", "test_*.py", "-k", "identity"])
        self.assertTrue(run.runs("experiments/trees/test_a.py", "Tests", "test_identity"))
        self.assertFalse(run.runs("experiments/trees/test_a.py", "Tests", "test_other"))

    def test_pull_request_triggers(self):
        self.assertTrue(pull_request_trigger("on:\n  pull_request:\n  push:\n"))
        self.assertTrue(pull_request_trigger("on:\n  push:\n    paths: ['a']\n  pull_request:\n    paths:\n"))
        self.assertTrue(pull_request_trigger("on: [push, pull_request]\n"))
        self.assertFalse(pull_request_trigger("on:\n  push:\n    branches: [main]\n  workflow_dispatch:\n"))
        self.assertFalse(pull_request_trigger("on: push\njobs:\n  pull_request:\n"))

    def test_rust_attributes(self):
        tests = rust_tests('#[test]\n// note\n#[cfg(unix)]\npub fn a() {}\n#[test]\n#[ignore = "x"]\nfn b() {}\n'
                           "#[cfg(test)]\nfn c() {}\n")
        self.assertEqual(tests, {"a": False, "b": True})

    def test_python_skips(self):
        tests = python_tests("import unittest\n@unittest.skip('x')\nclass A(unittest.TestCase):\n"
                             "    def test_a(self): pass\nclass B(unittest.TestCase):\n"
                             "    @unittest.skipIf(True, 'y')\n    def test_b(self): pass\n"
                             "    def helper(self): pass\n")
        self.assertEqual(tests, {("A", "test_a"): True, ("B", "test_b"): False})

    def test_repository_workflows(self):
        repository = check_spec.Repository(check_spec.ROOT)
        errors = []
        repository.check_test("tests/promotion.rs::stdlib_ir_matches_proof_fixture", "here", errors)
        repository.check_test("VastitasKernel.MetricFormRegression", "here", errors)
        repository.check_test("scripts/test_check_spec.py::ParserTests::test_repository_workflows", "here", errors)
        self.assertEqual(errors, [])


if __name__ == "__main__":
    unittest.main()
