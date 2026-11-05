"""Structural and fail-closed execution tests for examples/corpus.toml."""

from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest import mock

import capture_emit
import check_conformance_corpus as corpus


class ConformanceCorpusTests(unittest.TestCase):
    def fixture(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        repo = Path(temporary.name)
        examples = repo / "examples"
        (examples / "book" / "values").mkdir(parents=True)
        (examples / "book" / "values" / "one.vast").write_text("fn main() -> Int { 1 }\n")
        (examples / "corpus.toml").write_text(
            'schema_version = 1\n[[case]]\nid = "book.values.one"\n'
            'kind = "source"\npath = "book/values/one.vast"\nexpect = "accept"\n'
        )
        return examples, repo

    def test_all_tracked_examples_have_one_manifest_entry(self):
        cases = corpus.load_cases()
        self.assertEqual(len(cases), 45)
        self.assertEqual(sum(c["kind"] == "package" for c in cases), 33)
        self.assertEqual(sum(c["expect"] == "reject" for c in cases), 2)
        self.assertEqual(len({c["id"] for c in cases}), len(cases))

    def test_unindexed_source_is_not_silently_ignored(self):
        examples, root = self.fixture()
        corpus.load_cases(examples, root)
        (examples / "book" / "values" / "orphan.vast").write_text("fn main() -> Int { 2 }\n")
        with self.assertRaisesRegex(ValueError, "unregistered Vastitas source"):
            corpus.load_cases(examples, root)

    def test_duplicate_ids_and_escaping_paths_fail_closed(self):
        examples, root = self.fixture()
        manifest = examples / "corpus.toml"
        original = manifest.read_text()
        manifest.write_text(original + "[[case]]" + original.split("[[case]]", 1)[1])
        with self.assertRaisesRegex(ValueError, "duplicate case id"):
            corpus.load_cases(examples, root)
        manifest.write_text(original.replace('book/values/one.vast', '../README.md'))
        with self.assertRaisesRegex(ValueError, "escaping path"):
            corpus.load_cases(examples, root)

    def test_rejections_check_both_exit_status_and_diagnostic(self):
        case = {"id": "reject.names.missing", "path": "reject/names/missing.vast",
                "kind": "source", "expect": "reject", "diagnostic": "E_NAME"}
        with mock.patch.object(corpus.subprocess, "run") as run:
            run.return_value = subprocess.CompletedProcess([], 1, b"", b"E_NAME: unknown name")
            corpus.execute(case, Path("/fake/compiler"))
            run.return_value = subprocess.CompletedProcess([], 0, b"", b"E_NAME: unknown name")
            with self.assertRaisesRegex(ValueError, "expected rejection"):
                corpus.execute(case, Path("/fake/compiler"))
            run.return_value = subprocess.CompletedProcess([], 1, b"", b"E_TYPE: mismatch")
            with self.assertRaisesRegex(ValueError, "expected rejection"):
                corpus.execute(case, Path("/fake/compiler"))
            run.return_value = subprocess.CompletedProcess(
                [], 1, b"", b"E_TYPE: wrong type\nnote: E_NAME: this is not the first error"
            )
            with self.assertRaisesRegex(ValueError, "expected rejection"):
                corpus.execute(case, Path("/fake/compiler"))

    def test_emit_capture_covers_the_same_accepted_cases(self):
        expected = {c["id"] for c in corpus.load_cases() if c["expect"] == "accept"}
        captures = capture_emit.corpus()
        actual = {name.split("/", 1)[1] for name, _ in captures
                  if name.startswith(("example/book.", "package/package."))}
        self.assertEqual(actual, expected)
        self.assertEqual(len({name for name, _ in captures}), len(captures))


if __name__ == "__main__":
    unittest.main()
