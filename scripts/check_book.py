#!/usr/bin/env python3
"""Verify that every active Markdown chapter is listed, rendered and linked."""

from collections import Counter
from html.parser import HTMLParser
import re
from pathlib import Path
from urllib.parse import unquote, urlsplit


ROOT = Path(__file__).resolve().parents[1]


def check_contents(source, output):
    summary = source / "SUMMARY.md"
    links = re.findall(r"^\s*(?:[-*]\s+)?\[[^\]]+\]\(([^ )]+)\)\s*$", summary.read_text(encoding="utf-8"), re.M)
    chapters = Counter(links)
    expected = {p.relative_to(source).as_posix() for p in source.rglob("*.md") if p != summary}
    missing = sorted(expected - chapters.keys())
    unknown = sorted(chapters.keys() - expected)
    repeated = sorted(name for name, count in chapters.items() if count != 1)
    if missing or unknown or repeated:
        raise ValueError(f"contents mismatch: unlisted={missing}, absent={unknown}, duplicates={repeated}")
    if links[:2] != ["README.md", "guide/historical-roadmap.md"]:
        raise ValueError("the opening navigation must begin with the entrypoint and roadmap")
    for name in chapters:
        path = Path(name)
        rendered = (path.with_name("index.html") if path.name == "README.md" else path.with_suffix(".html"))
        if not (output / rendered).is_file():
            raise ValueError(f"chapter was not rendered: {name}")
    print(f"Verified all {len(chapters)} active Markdown chapters against the contents and generated files")


class Page(HTMLParser):
    def __init__(self, file):
        super().__init__()
        self.anchors = set()
        self.links = []
        self.formulas = 0
        self.tex_annotations = 0
        self.feed(file.read_text(encoding="utf-8"))
        self.close()

    def handle_starttag(self, tag, attrs):
        if tag == "math":
            self.formulas += 1
        if tag == "annotation" and ("encoding", "application/x-tex") in attrs:
            self.tex_annotations += 1
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
        if page.formulas != page.tex_annotations:
            raise ValueError(f"{source.relative_to(directory)}: missing original TeX annotation")
        for link in page.links:
            url = urlsplit(link)
            if url.netloc == "github.com":
                repo_path = re.match(r"^/MGYamada/Vastitas/(?:blob|tree)/main/(.+)$", url.path)
                if repo_path and not (ROOT / unquote(repo_path[1])).exists():
                    raise ValueError(f"{source.relative_to(directory)}: absent repository target {link}")
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
    for mathematical_page in ("daleckii-krein.html", "reference/analysis-and-effects.html"):
        if not pages[directory / mathematical_page].formulas:
            raise ValueError(f"{mathematical_page}: expected rendered mathematical notation")
    print(f"Checked {count} local links and assets across {len(pages)} rendered HTML pages")


if __name__ == "__main__":
    check_contents(ROOT / "docs", ROOT / "target/book")
    check_html(ROOT / "target/book")
