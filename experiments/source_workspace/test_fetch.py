from contextlib import redirect_stderr, redirect_stdout
import hashlib
import io
import json
import subprocess
from pathlib import Path
import tempfile
import unittest
from unittest import mock

import fetch


class VerifiedFetchTests(unittest.TestCase):
    def setUp(self):
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        self.root = Path(tmp.name)
        self.name = "example"
        self.directory = self.root / "results" / self.name
        self.directory.mkdir(parents=True)
        self.data = b"known archive bytes"
        self.digest = hashlib.sha256(self.data).hexdigest()
        self.commit = "a" * 40
        self.catalog = {"schema": 1, "records": {self.name: {"git_commit": self.commit, "git_blob": "b" * 40}}}
        self.catalog_file = self.root / "archive-sources.json"
        self.catalog_file.write_text(json.dumps(self.catalog))
        self.manifest = {"schema": 1, "archive": "evidence.zip", "sha256": self.digest, "bytes": len(self.data)}
        self.manifest_file = self.directory / "artifact-manifest.json"
        self.manifest_file.write_text(json.dumps(self.manifest))
        self.record = fetch.load_record(self.name, self.root)

    def test_sparse_download_is_verified_and_then_reused_offline(self):
        with mock.patch.object(fetch, "urlopen", return_value=io.BytesIO(self.data)) as remote:
            dest = fetch.fetch(self.record)
            self.assertEqual(dest.read_bytes(), self.data)
            self.assertEqual(fetch.fetch(self.record), dest)
        remote.assert_called_once_with(self.record.url, timeout=120)
        self.assertIn("/" + self.commit + "/", self.record.url)

    def test_local_archive_populates_content_addressed_cache_without_network(self):
        self.record.archive.write_bytes(self.data)
        with mock.patch.object(fetch, "urlopen") as remote:
            cached = fetch.fetch(self.record, self.root / "cache")
            self.assertEqual(cached.name, self.digest + ".zip")
            self.assertEqual(cached.read_bytes(), self.data)
            remote.assert_not_called()

    def test_all_restores_then_resumes_only_the_missing_record(self):
        second = self.root / "results" / "second"
        second.mkdir()
        (second / "artifact-manifest.json").write_text(json.dumps(self.manifest))
        self.catalog["records"]["second"] = {"release_tag": "sample", "asset": "second.zip"}
        self.catalog_file.write_text(json.dumps(self.catalog))
        with redirect_stdout(io.StringIO()), redirect_stderr(io.StringIO()):
            with mock.patch.object(fetch, "urlopen", side_effect=[io.BytesIO(self.data), io.BytesIO(b"short")]):
                self.assertEqual(fetch.main(["--all"], self.root), 1)
            self.assertEqual(self.record.archive.read_bytes(), self.data)
            self.assertFalse((second / "evidence.zip").exists())
            with mock.patch.object(fetch, "urlopen", return_value=io.BytesIO(self.data)) as remote:
                self.assertEqual(fetch.main(["--all"], self.root), 0)
                remote.assert_called_once_with(fetch.load_record("second", self.root).url, timeout=120)
            with self.assertRaises(SystemExit):
                fetch.main(["--all", self.name], self.root)
        self.assertEqual((second / "evidence.zip").read_bytes(), self.data)

    def test_bad_streams_and_interrupted_read_publish_nothing(self):
        class Interrupted(io.BytesIO):
            def read(self, count):
                if self.tell():
                    raise OSError("connection lost")
                return super().read(1)

        for stream in (io.BytesIO(self.data[:-1]), io.BytesIO(self.data + b"!"),
                       io.BytesIO(b"x" * len(self.data)), Interrupted(self.data)):
            with self.subTest(stream=stream), mock.patch.object(fetch, "urlopen", return_value=stream):
                with self.assertRaises((ValueError, OSError)):
                    fetch.fetch(self.record)
                self.assertFalse(self.record.archive.exists())
                self.assertEqual(list(self.directory.glob(".vastitas-evidence-*")), [])

    def test_corrupt_existing_destination_is_preserved(self):
        self.record.archive.write_bytes(b"other data")
        with mock.patch.object(fetch, "urlopen") as remote:
            with self.assertRaises(ValueError):
                fetch.fetch(self.record)
            remote.assert_not_called()
        self.assertEqual(self.record.archive.read_bytes(), b"other data")

    def test_concurrent_winner_is_rechecked(self):
        for data in (self.data, b"corrupt"):
            with self.subTest(valid=data == self.data):
                def publish_first(_src, dest):
                    dest.write_bytes(data)
                    raise FileExistsError
                with mock.patch.object(fetch, "urlopen", return_value=io.BytesIO(self.data)), \
                     mock.patch.object(fetch.os, "link", side_effect=publish_first):
                    if data == self.data:
                        self.assertEqual(fetch.fetch(self.record), self.record.archive)
                    else:
                        with self.assertRaises(ValueError):
                            fetch.fetch(self.record)
                self.assertEqual(self.record.archive.read_bytes(), data)
                self.record.archive.unlink()

    def test_origins_and_filenames_are_restricted(self):
        for origin in ({"git_commit": "main", "git_blob": "b" * 40}, {"git_commit": self.commit}, {"url": "http://example.invalid"},
                       {"release_tag": "records", "asset": "../secret"}, {"git_commit": self.commit, "x": 1}):
            with self.subTest(origin=origin), self.assertRaises(ValueError):
                fetch.source_url(self.name, origin)
        self.assertEqual(fetch.source_url(self.name, {"release_tag": "evidence-v1", "asset": "sample.zip"}),
                         "https://github.com/MGYamada/Vastitas/releases/download/evidence-v1/sample.zip")
        for name in ("../example", "unknown"):
            with self.subTest(name=name), self.assertRaises(ValueError):
                fetch.load_record(name, self.root)
        for change in ({"archive": "../evidence.zip"}, {"bytes": True}, {"sha256": "aa"}):
            self.manifest_file.write_text(json.dumps({**self.manifest, **change}))
            with self.subTest(change=change), self.assertRaises(ValueError):
                fetch.load_record(self.name, self.root)

    def test_catalog_covers_the_retained_manifests(self):
        catalog = json.loads((fetch.HERE / "archive-sources.json").read_text())
        names = {p.parent.name for p in (fetch.HERE / "results").glob("*/artifact-manifest.json")}
        self.assertEqual(set(catalog["records"]), names)
        for name in names:
            self.assertGreater(fetch.load_record(name).size, 0)

    def test_sparse_git_index_keeps_exact_historical_blobs(self):
        root = fetch.HERE.parents[1]
        if not (root / ".git").exists():
            self.skipTest("no Git index in a source export")
        prefix = "experiments/source_workspace/results/"
        records = json.loads((fetch.HERE / "archive-sources.json").read_text())["records"]
        expected = {prefix + name + "/evidence.zip": origin["git_blob"]
                    for name, origin in records.items() if "git_commit" in origin}
        index = subprocess.check_output(["git", "ls-files", "--stage", "-z", "--",
                                         prefix + "*/evidence.zip"], cwd=root)
        actual = {}
        for entry in index.decode().split("\0"):
            if entry:
                info, path = entry.split("\t", 1)
                mode, blob, stage = info.split()
                self.assertEqual((mode, stage), ("100644", "0"))
                actual[path] = blob
        self.assertEqual(actual, expected)
