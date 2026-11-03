#!/usr/bin/env python3
"""Check the rendered book's local links and reconstruct the preserved draft."""

import hashlib
from html.parser import HTMLParser
import json
from pathlib import Path
from urllib.parse import unquote, urlsplit


ROOT = Path(__file__).resolve().parents[1]


def verify_bytes(data, size, digest, label):
    if len(data) != size or hashlib.sha256(data).hexdigest() != digest:
        raise ValueError(f"{label}: preserved bytes differ from the source record")


def check_draft(directory):
    record = json.loads((directory / "source-record.json").read_bytes())
    sections = record["sections"]
    if [s["section"] for s in sections] != ["preface", *map(str, range(1, 19))]:
        raise ValueError("the draft must contain the preface followed by sections 1–18")
    original = bytearray()
    for entry in sections:
        name = entry["section"]
        document = (directory / entry["file"]).read_bytes()
        start = f"<!-- draft-v0.3:{name}:start -->\n".encode()
        end = f"<!-- draft-v0.3:{name}:end -->".encode()
        if document.count(start) != 1 or document.count(end) != 1:
            raise ValueError(f"{name}: expected one marked source block")
        block, found, _ = document.partition(start)[2].partition(end)
        if not found:
            raise ValueError(f"{name}: end marker precedes start marker")
        if name == "preface":
            for old, new in record["toc_destination_rewrites"].items():
                if block.count(new.encode()) != 1:
                    raise ValueError(f"preface: missing or duplicate table-of-contents link {new}")
                block = block.replace(new.encode(), old.encode(), 1)
        verify_bytes(block, entry["original_bytes"], entry["original_sha256"], name)
        original.extend(block)
    verify_bytes(original, record["source_bytes"], record["source_sha256"], "complete draft")
    print(f"Verified {len(sections)} draft blocks and all {len(original):,} original bytes")


class Page(HTMLParser):
    def __init__(self, file):
        super().__init__()
        self.anchors = set()
        self.links = []
        self.feed(file.read_text(encoding="utf-8"))
        self.close()

    def handle_starttag(self, tag, attrs):
        for key, value in attrs:
            if key == "id" or (tag == "a" and key == "name"):
                self.anchors.add(value)
            if key in ("href", "src") and value:
                self.links.append(value)


def check_html(directory):
    directory = directory.resolve(strict=True)
    pages = {file: Page(file) for file in directory.rglob("*.html")}
    opening = directory / "index.html"
    roadmap = directory / "guide/historical-roadmap.html"
    if opening not in pages or roadmap not in pages:
        raise ValueError("the opening page and roadmap must both be rendered")
    count = 0
    linked_from_opening = False
    for source, page in pages.items():
        for link in page.links:
            url = urlsplit(link)
            if url.scheme or url.netloc:
                continue
            target = (source.parent / unquote(url.path)).resolve() if url.path else source
            if target.is_dir():
                target = target / "index.html"
            if not target.is_relative_to(directory) or not target.is_file():
                raise ValueError(f"{source.relative_to(directory)}: missing book target {link}")
            if target in pages and url.fragment and unquote(url.fragment) not in pages[target].anchors:
                raise ValueError(f"{source.relative_to(directory)}: missing book anchor {link}")
            if source == opening and target == roadmap:
                linked_from_opening = True
            count += 1
    if not linked_from_opening:
        raise ValueError("the opening page must link to the roadmap")
    print(f"Checked {count} local links and assets across {len(pages)} rendered HTML pages")


if __name__ == "__main__":
    check_draft(ROOT / "docs/design")
    check_html(ROOT / "target/book")
