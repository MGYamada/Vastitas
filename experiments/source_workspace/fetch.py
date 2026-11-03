#!/usr/bin/env python3
"""Fetch one retained source-workspace archive and verify its existing manifest."""
import argparse
import hashlib
from http.client import HTTPException
import json
import os
from pathlib import Path
import re
import sys
import tempfile
from typing import NamedTuple
from urllib.request import urlopen

HERE = Path(__file__).resolve().parent
REPOSITORY = "MGYamada/Vastitas"
SAFE_NAME = re.compile(r"[A-Za-z0-9][A-Za-z0-9._-]*")
CHUNK = 1 << 20


class Record(NamedTuple):
    archive: Path
    size: int
    digest: str
    url: str


def source_url(name, origin):
    if not isinstance(origin, dict):
        raise ValueError("invalid archive origin")
    if set(origin) == {"git_commit", "git_blob"}:
        commit, blob = origin["git_commit"], origin["git_blob"]
        if all(isinstance(x, str) and re.fullmatch(r"[0-9a-f]{40}", x) for x in (commit, blob)):
            return (f"https://raw.githubusercontent.com/{REPOSITORY}/{commit}/"
                    f"experiments/source_workspace/results/{name}/evidence.zip")
    if set(origin) == {"release_tag", "asset"}:
        tag, asset = origin["release_tag"], origin["asset"]
        if all(isinstance(x, str) and SAFE_NAME.fullmatch(x) for x in (tag, asset)):
            return f"https://github.com/{REPOSITORY}/releases/download/{tag}/{asset}"
    raise ValueError("expected an immutable Git revision or a named repository release asset")


def load_record(name, root=HERE):
    if not SAFE_NAME.fullmatch(name):
        raise ValueError("invalid record name")
    catalog = json.loads((root / "archive-sources.json").read_text(encoding="utf-8"))
    if (type(catalog) is not dict or type(catalog.get("schema")) is not int
            or catalog["schema"] != 1 or not isinstance(catalog.get("records"), dict)):
        raise ValueError("invalid archive source catalog")
    if name not in catalog["records"]:
        raise ValueError(f"unknown retained record: {name}")
    directory = root / "results" / name
    manifest = json.loads((directory / "artifact-manifest.json").read_text(encoding="utf-8"))
    if (type(manifest) is not dict or type(manifest.get("schema")) is not int
            or manifest["schema"] != 1 or manifest.get("archive") != "evidence.zip"
            or type(manifest.get("bytes")) is not int or manifest["bytes"] <= 0
            or not isinstance(manifest.get("sha256"), str)
            or not re.fullmatch(r"[0-9a-f]{64}", manifest["sha256"])):
        raise ValueError("invalid retained archive manifest")
    return Record(directory / "evidence.zip", manifest["bytes"], manifest["sha256"],
                  source_url(name, catalog["records"][name]))


def verify_stream(source, record, output=None):
    digest = hashlib.sha256()
    count = 0
    while block := source.read(min(CHUNK, record.size - count + 1)):
        count += len(block)
        if count > record.size:
            raise ValueError("archive exceeds the manifest byte count")
        digest.update(block)
        if output is not None:
            output.write(block)
    if count != record.size:
        raise ValueError("archive is shorter than its manifest")
    if digest.hexdigest() != record.digest:
        raise ValueError("archive SHA-256 differs from its manifest")


def fetch(record, cache_dir=None):
    target = record.archive if cache_dir is None else cache_dir / f"{record.digest}.zip"
    if target.exists():
        with target.open("rb") as source:
            verify_stream(source, record)
        return target
    target.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix=".vastitas-evidence-", dir=target.parent) as work:
        payload = Path(work) / "payload"
        source = record.archive.open("rb") if record.archive.is_file() else urlopen(record.url, timeout=120)
        with source, payload.open("wb") as output:
            verify_stream(source, record, output)
        try:
            os.link(payload, target)
        except FileExistsError:
            # A concurrent fetch may have completed first. Verify the winner.
            with target.open("rb") as existing:
                verify_stream(existing, record)
    return target


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("record", help="retained record directory name")
    parser.add_argument("--cache-dir", type=Path, help="use a SHA-256-named cache file")
    args = parser.parse_args()
    try:
        print(fetch(load_record(args.record), args.cache_dir))
    except (OSError, HTTPException, ValueError) as error:
        print(f"cannot fetch verified evidence: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
