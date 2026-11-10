#!/usr/bin/env python3
"""Verify the book: its contents, rendering, links, includes, titles, style and Syntax blocks."""

from collections import Counter
from dataclasses import dataclass
from html.parser import HTMLParser
import os
import re
import subprocess
import tomllib
from pathlib import Path
from urllib.parse import unquote, urlsplit


ROOT = Path(__file__).resolve().parents[1]

# Chapters written by the style guide (docs/development/documentation.md#style-guide).
# The title and style checks apply to them. The last step of the book rewrite
# applies both checks to every chapter and removes this list.
CONVERTED = frozenset({
    "guide/smooth-geometry.md",
    "language/notation.md",
    "language/lexical-structure.md",
    "language/programs.md",
    "language/items.md",
    "language/functions.md",
    "language/statements.md",
    "language/expressions.md",
    "language/types.md",
    "language/geometric-types.md",
    "language/names-and-paths.md",
    "language/modules.md",
    "packages.md",
    "language/edit-authority.md",
    "stage1a.md",
    "stage1b.md",
    "internals/checking-pipeline.md",
    "storage-ownership.md",
    "storage/resource-programs.md",
    "internals/resource-checking.md",
    "linalg/maps-and-gemm.md",
    "linalg/transforms-and-metrics.md",
    "linalg/networks-and-packing.md",
    "internals/numerical-backend.md",
    "language/smooth-declarations.md",
    "specifications.md",
    "spec/std-differential.md",
    "spec/reverse-core.md",
    "spec/std-geometry-metric.md",
    "spec/metric-evidence.md",
    "spec/std-arithmetic-generic.md",
    "spec/assumptions.md",
    "development/documentation.md",
    "development/primitives.md",
    "appendix/glossary.md",
})

# Delivery records keep their original wording, as the style guide says.
ARCHIVED = frozenset({
    "stage1-completion.md",
    "stage1-acceptance.md",
    "stage2-acceptance.md",
    "stage3-acceptance.md",
    "reverse-core-acceptance.md",
})

# The parts of SUMMARY.md, by their part title. Chapters before the first part
# title form the guide.
PARTS = {
    "Vastitas Reference": "reference",
    "How the compiler is checked": "internals",
    "Appendices": "appendix",
}

REPOSITORY = "MGYamada/Vastitas"

# Nonterminals that Syntax blocks use before the Reference chapter that owns
# the construct defines them, by that chapter. Remove an entry when its
# chapter gains the production.
PENDING_NONTERMINALS = {
    "IndexedDeclaration": "the geometry-declarations chapter",
}


@dataclass(frozen=True)
class Chapter:
    title: str
    path: str
    part: str


def read_contents(source):
    """Return the chapters of SUMMARY.md in order, each with its part."""
    chapters = []
    part = "guide"
    for line in (source / "SUMMARY.md").read_text(encoding="utf-8").splitlines():
        heading = re.match(r"^# (.+?)\s*$", line)
        if heading and heading[1] != "Summary":
            if heading[1] not in PARTS:
                raise ValueError(f"SUMMARY.md: unknown part title {heading[1]!r}")
            part = PARTS[heading[1]]
        link = re.match(r"^\s*(?:[-*]\s+)?\[([^\]]+)\]\(([^ )]+)\)\s*$", line)
        if link:
            chapters.append(Chapter(link[1], link[2], part))
    return chapters


def check_contents(source, output):
    chapters = read_contents(source)
    links = [chapter.path for chapter in chapters]
    text = (source / "SUMMARY.md").read_text(encoding="utf-8")
    counts = Counter(links)
    summary = source / "SUMMARY.md"
    expected = {p.relative_to(source).as_posix() for p in source.rglob("*.md") if p != summary}
    missing = sorted(expected - counts.keys())
    unknown = sorted(counts.keys() - expected)
    repeated = sorted(name for name, count in counts.items() if count != 1)
    if missing or unknown or repeated:
        raise ValueError(f"contents mismatch: unlisted={missing}, absent={unknown}, duplicates={repeated}")
    if links[:2] != ["README.md", "guide/getting-started.md"]:
        raise ValueError("the contents must begin with the Introduction and then Getting Started")
    if not re.search(r"^\[Introduction\]\(README\.md\)\s*$", text, re.M):
        raise ValueError("the Introduction must be an unnumbered prefix chapter")
    if not re.search(r"^- \[Getting Started\]\(guide/getting-started\.md\)\s*$", text, re.M):
        raise ValueError("Getting Started must be the first numbered chapter")
    for name in counts:
        if not (output / rendered_path(name)).is_file():
            raise ValueError(f"chapter was not rendered: {name}")
    print(f"Verified all {len(counts)} active Markdown chapters against the contents and generated files")
    return chapters


def rendered_path(name):
    path = Path(name)
    return path.with_name("index.html") if path.name == "README.md" else path.with_suffix(".html")


# --- Titles -------------------------------------------------------------------

def expected_title(chapter):
    """The H1 of a chapter is its title in SUMMARY.md; "X: Name" in the appendices is "Appendix X: Name"."""
    letter = re.fullmatch(r"([A-Z]): (.+)", chapter.title)
    if chapter.part == "appendix" and letter:
        return f"Appendix {letter[1]}: {letter[2]}"
    return chapter.title


def check_titles(source, chapters, converted=CONVERTED):
    listed = {chapter.path for chapter in chapters}
    stale = sorted(converted - listed)
    if stale:
        raise ValueError(f"converted chapters absent from SUMMARY.md: {stale}")
    errors = []
    for chapter in chapters:
        if chapter.path not in converted:
            continue
        lines = [line for line in (source / chapter.path).read_text(encoding="utf-8").splitlines() if line.strip()]
        title = f"# {expected_title(chapter)}"
        if not lines or lines[0] != title:
            found = lines[0] if lines else "an empty file"
            errors.append(f"{chapter.path}: the first line must be {title!r}, found {found!r}")
    if errors:
        raise ValueError("chapter titles differ from SUMMARY.md:\n  " + "\n  ".join(errors))
    print(f"Checked the titles of {len(converted)} converted chapters against SUMMARY.md")


# --- Style ----------------------------------------------------------------------

FENCE = re.compile(r"^(`{3,}|~{3,})")
CODE_SPAN = re.compile(r"(`+)(.+?)\1")
WORDS = re.compile(r"\b(now|currently|new|newly|deliberately|actually)\b", re.I)
SHOULD = re.compile(r"\bshould\b", re.I)
STAGE = re.compile(r"\bStages? \d")
PROTOCOL = re.compile(r"\b[Pp]rotocols? (?:versions? )?\d")
ISSUE_LINK = re.compile(rf"https://github\.com/{REPOSITORY}/(?:issues|pull)/\d+")
ISSUE_NUMBER = re.compile(r"(?<![\w&/#])#\d+\b")
COMMIT = re.compile(r"\b(?=[0-9a-f]*\d)(?=[0-9a-f]*[a-f])[0-9a-f]{7,40}\b")
THEOREM = re.compile(r"\bVastitas(?:Kernel|Oracle|Bridge|Spec)\.[A-Z]")


def unquote_prefix(line):
    """Remove the blockquote markers that begin a line."""
    return re.sub(r"^\s*(?:>\s?)+", "", line)


def scan(text):
    """Yield each line outside code blocks with its line number, section and block context."""
    fence = None
    section = ""
    note = False
    for number, line in enumerate(text.splitlines(), 1):
        body = unquote_prefix(line)
        marker = FENCE.match(body.lstrip())
        if fence:
            if marker and marker[1][0] == fence[0] and len(marker[1]) >= len(fence) and not body.lstrip()[len(marker[1]):].strip():
                fence = None
            continue
        if marker:
            fence = marker[1]
            continue
        quoted = line.lstrip().startswith(">")
        if not quoted:
            note = False
        elif body.startswith("**Implementation note.**"):
            note = True
        heading = re.match(r"^(#{1,6}) (.+)$", line)
        if heading and len(heading[1]) <= 2:
            section = heading[2].strip()
        yield number, line, section, note


def prose(line):
    """Remove code spans, link targets, HTML, math, include directives and quoted mentions from a line."""
    line = re.sub(r"\{\{#[^}]*\}\}", " ", line)
    line = CODE_SPAN.sub(" ", line)
    line = re.sub(r"\]\([^)]*\)", "]", line)
    line = re.sub(r"<[^>]*>", " ", line)
    line = re.sub(r"\$\$.*?\$\$|\$[^$]*\$", " ", line)
    line = re.sub(r"\"[^\"]*\"|“[^”]*”", " ", line)
    return line


def style_errors(path, text, part):
    """Return the style-guide violations of one chapter in the given part."""
    errors = []
    generated = path.startswith("spec/")

    def report(number, message):
        errors.append(f"{path}:{number}: {message}")

    for number, line, section, note in scan(text):
        words = prose(line)
        for match in WORDS.finditer(words):
            report(number, f"the style guide bans {match[0]!r}")
        linked = ISSUE_LINK.search(line) or ISSUE_NUMBER.search(words)
        if part in ("guide", "reference") and linked:
            report(number, "issue and pull request references belong in the appendices and internals History sections")
        if part == "internals" and linked and not generated and section != "History":
            report(number, "an internals chapter links issues and pull requests only in its History section")
        if part in ("guide", "reference") and STAGE.search(words):
            report(number, "the guide and the Reference do not name Stages")
        if part == "guide" and PROTOCOL.search(words):
            report(number, "the guide does not name wire-protocol versions")
        if part == "reference" and not note and PROTOCOL.search(words):
            report(number, "the Reference names wire-protocol versions only in implementation notes")
        if part == "reference" and SHOULD.search(words):
            report(number, "normative text uses must, must not or may, never should")
        if part == "guide":
            if COMMIT.search(CODE_SPAN.sub(r"\2", line)) and not re.search(r"\]\([^)]*$", line):
                report(number, "the guide does not cite commit hashes")
            if THEOREM.search(line):
                report(number, "the guide does not name theorems")
    if part == "guide" and path != "README.md" and not re.search(r"^## See also\s*$(?![\s\S]*^## )", text, re.M):
        errors.append(f"{path}: a guide chapter ends with a '## See also' section")
    return errors


def check_style(source, chapters, converted=CONVERTED):
    errors = []
    for chapter in chapters:
        if chapter.path in converted and chapter.path not in ARCHIVED:
            errors += style_errors(chapter.path, (source / chapter.path).read_text(encoding="utf-8"), chapter.part)
    if errors:
        raise ValueError("style guide violations:\n  " + "\n  ".join(errors))
    print(f"Checked the style of {len(converted - ARCHIVED)} converted chapters by part")


# --- Includes -------------------------------------------------------------------

INCLUDE = re.compile(r"(\\?)\{\{#(include|rustdoc_include|playground)\s+([^}\s]+)[^}]*\}\}")


def include_errors(chapter, text, source):
    errors = []
    for match in INCLUDE.finditer(text):
        if match[1]:
            continue
        file, _, selector = match[3].partition(":")
        target = Path(os.path.normpath((source / chapter).parent / file))
        where = f"{chapter}: {{{{#{match[2]} {match[3]}}}}}"
        if not target.is_file():
            errors.append(f"{where}: no such file")
            continue
        content = target.read_text(encoding="utf-8")
        if not selector:
            continue
        lines = re.fullmatch(r"(\d*)(?::(\d*))?", selector)
        if lines:
            last = max(int(n) for n in lines.groups() if n) if any(lines.groups()) else 0
            if last > len(content.splitlines()):
                errors.append(f"{where}: the file has {len(content.splitlines())} lines")
        elif not (re.search(rf"\bANCHOR:\s*{re.escape(selector)}\b", content)
                  and re.search(rf"\bANCHOR_END:\s*{re.escape(selector)}\b", content)):
            errors.append(f"{where}: no ANCHOR/ANCHOR_END pair named {selector!r}")
    return errors


def code_blocks(text):
    """Yield (line number, label, lines) for each fenced code block, also inside block quotes."""
    lines = text.splitlines()
    index = 0
    while index < len(lines):
        body = unquote_prefix(lines[index]).lstrip()
        marker = FENCE.match(body)
        if marker:
            start = index
            label = body[len(marker[1]):].strip()
            content = []
            index += 1
            while index < len(lines):
                inner = unquote_prefix(lines[index])
                closing = FENCE.match(inner.lstrip())
                if closing and closing[1][0] == marker[1][0] and len(closing[1]) >= len(marker[1]) \
                        and not inner.lstrip()[len(closing[1]):].strip():
                    break
                content.append(inner)
                index += 1
            yield start + 1, label, content
        index += 1


MAIN = re.compile(r"\s*(?:pub\s+)?(?:resource\s+)?fn\s+main\s*\(")


def program_errors(chapter, text):
    """A complete program in a chapter comes from a tested file through an include directive."""
    errors = []
    for number, label, content in code_blocks(text):
        if label in ("", "vast", "text") and any(MAIN.match(line) for line in content):
            errors.append(f"{chapter}:{number}: a complete program is included from a tested file "
                          "under examples/ (style guide, Examples)")
    return errors


BOOK_EXAMPLES = ("examples/book", "examples/reject")


def check_includes(source, chapters, root=ROOT):
    errors = []
    count = 0
    included = set()
    for chapter in chapters:
        text = (source / chapter.path).read_text(encoding="utf-8")
        for match in INCLUDE.finditer(text):
            if not match[1]:
                count += 1
                included.add(Path(os.path.normpath((source / chapter.path).parent / match[3].partition(":")[0])))
        errors += include_errors(chapter.path, text, source)
        if chapter.path not in ARCHIVED:
            errors += program_errors(chapter.path, text)
    for directory in BOOK_EXAMPLES:
        for file in sorted((root / directory).rglob("*")):
            hidden = any(part.startswith(".") for part in file.relative_to(root).parts)
            # A rejected package's manifest is part of the test, not of the text.
            if file.name == "Vastitas.toml" and file.is_relative_to(root / "examples/reject/packages"):
                continue
            if file.is_file() and not hidden and Path(os.path.normpath(file)) not in included:
                errors.append(f"{file.relative_to(root)}: no chapter includes this example")
    if errors:
        raise ValueError("failed include directives or untested programs:\n  " + "\n  ".join(errors))
    print(f"Resolved {count} include directives; every program in the book is included from examples/")


# --- Syntax blocks --------------------------------------------------------------

PRODUCTION = re.compile(r"^([A-Za-z][A-Za-z0-9_]*) ->(?: (.*))?$")
TERMINAL = re.compile(r"`([^`]+)`")
SYMBOL = re.compile(r"\b([A-Z][A-Za-z0-9_]*)\b")


def syntax_blocks(text):
    """Yield (line number, productions) for each Syntax block of a chapter."""
    lines = text.splitlines()
    index = 0
    while index < len(lines):
        if lines[index].strip() == "> **Syntax**":
            start = index
            index += 1
            while index < len(lines) and unquote_prefix(lines[index]).strip() == "":
                index += 1
            body = unquote_prefix(lines[index]).strip() if index < len(lines) else ""
            if body != "```text":
                raise ValueError(f"line {start + 1}: a Syntax block holds one code block labelled text")
            productions = []
            index += 1
            while index < len(lines) and unquote_prefix(lines[index]).strip() != "```":
                content = unquote_prefix(lines[index])
                if not lines[index].lstrip().startswith(">"):
                    raise ValueError(f"line {start + 1}: an unterminated Syntax block")
                if content.strip():
                    if content[:1].isspace() and productions:
                        productions[-1] = (productions[-1][0], productions[-1][1] + " " + content.strip())
                    elif PRODUCTION.match(content):
                        productions.append((index + 1, content.strip()))
                    else:
                        raise ValueError(f"line {index + 1}: not a production: {content.strip()!r}")
                index += 1
            yield start + 1, productions
        index += 1


def parser_vocabulary(root):
    """The punctuation that the lexer produces and the names that the parser compares tokens with."""
    sources = [root / "src/frontend.rs", *sorted((root / "src/frontend").glob("*.rs"))]
    text = "\n".join(path.read_text(encoding="utf-8") for path in sources)
    lexer = (root / "src/frontend.rs").read_text(encoding="utf-8")
    operators = re.search(r'let Some\(op\) = \[([^\]]*)\]', lexer)
    characters = re.search(r'else if "([^"]+)"\.contains\(ch\)', lexer)
    if not operators or not characters:
        raise ValueError("src/frontend.rs: the lexer's operator and punctuation lists were not found")
    symbols = set(re.findall(r'"([^"]+)"', operators[1])) | set(characters[1])
    names = set(re.findall(r'"([A-Za-z_][A-Za-z0-9_]*)"', text))
    return symbols, names


def syntax_errors(chapters, source, root, pending=frozenset(PENDING_NONTERMINALS)):
    symbols, names = parser_vocabulary(root)
    definitions = {}
    uses = []
    errors = []
    for chapter in chapters:
        text = (source / chapter.path).read_text(encoding="utf-8")
        try:
            blocks = list(syntax_blocks(text))
        except ValueError as error:
            errors.append(f"{chapter.path}:{error}")
            continue
        if blocks and chapter.part != "reference":
            errors.append(f"{chapter.path}: Syntax blocks belong in the Vastitas Reference")
        illustration = chapter.path == "language/notation.md"
        for _, productions in blocks:
            for number, production in productions:
                name, body = PRODUCTION.match(production).groups()
                body = body or ""
                where = f"{chapter.path}:{number}"
                if not illustration:
                    if name in definitions:
                        errors.append(f"{where}: {name} is also defined at {definitions[name]}")
                    definitions.setdefault(name, where)
                lexical = name.isupper()
                for terminal in TERMINAL.findall(body):
                    known = terminal in names if re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", terminal) else terminal in symbols
                    if not lexical and not known:
                        errors.append(f"{where}: the parser in src/frontend*.rs has no token `{terminal}`")
                if not illustration:
                    uses += [(symbol, where) for symbol in SYMBOL.findall(TERMINAL.sub(" ", body))]
    for symbol, where in uses:
        if symbol not in definitions and symbol not in pending:
            errors.append(f"{where}: {symbol} has no production in the Vastitas Reference")
    for symbol in sorted(pending & definitions.keys()):
        errors.append(f"{definitions[symbol]}: {symbol} is defined; remove it from PENDING_NONTERMINALS")
    return errors, len(definitions)


def check_syntax(source, chapters, root=ROOT):
    errors, count = syntax_errors(chapters, source, root)
    if errors:
        raise ValueError("Syntax blocks disagree with the parser or the Reference:\n  " + "\n  ".join(errors))
    print(f"Checked the Syntax blocks of the Reference ({count} productions) against the parser")


# --- Rendered pages and links ---------------------------------------------------

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


def repository_errors(link, root=ROOT):
    """Check a link into this repository on GitHub: its revision, path and line range."""
    url = urlsplit(link)
    match = re.match(rf"^/{REPOSITORY}/(?:blob|tree)/([^/]+)/(.+)$", url.path)
    if url.netloc != "github.com" or not match:
        return []
    revision, path = match[1], unquote(match[2]).rstrip("/")
    if revision == "main":
        target = root / path
        if not target.exists():
            return [f"absent repository target {link}"]
        lines = re.fullmatch(r"L(\d+)(?:-L(\d+))?", url.fragment)
        if lines and target.is_file():
            last = int(lines[2] or lines[1])
            if last > len(target.read_text(encoding="utf-8", errors="replace").splitlines()):
                return [f"line range beyond the end of the file {link}"]
        return []
    # rev-parse reads only commits and trees, which a blobless clone holds.
    found = subprocess.run(["git", "-C", str(root), "rev-parse", "--verify", "--quiet", f"{revision}:{path}"],
                           capture_output=True)
    if found.returncode:
        return [f"absent repository target at {revision} {link}"]
    return []


def check_html(directory):
    directory = directory.resolve(strict=True)
    pages = {file: Page(file) for file in directory.rglob("*.html")}
    opening = directory / "index.html"
    roadmap = directory / "guide/historical-roadmap.html"
    if opening not in pages or roadmap not in pages:
        raise ValueError("the opening page and roadmap must both be rendered")
    count = 0
    outside = 0
    linked_from_opening = False
    checked = {}
    for source, page in pages.items():
        if page.formulas != page.tex_annotations:
            raise ValueError(f"{source.relative_to(directory)}: missing original TeX annotation")
        for link in page.links:
            url = urlsplit(link)
            if url.netloc == "github.com":
                if link not in checked:
                    checked[link] = repository_errors(link)
                if checked[link]:
                    raise ValueError(f"{source.relative_to(directory)}: {checked[link][0]}")
                outside += 1
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
    print(f"Checked {outside} links into the repository ({len(checked)} distinct)")
    return pages


def redirect_errors(pages, directory, config, source):
    """Check that every redirect of a retired chapter leads to a rendered page and anchor."""
    errors = []
    redirects = config.get("output", {}).get("html", {}).get("redirect", {})
    for old, new in redirects.items():
        retired = old.lstrip("/").partition("#")[0]
        url = urlsplit(new)
        # The redirect page resolves its target against its own URL.
        target = ((directory / retired).parent / unquote(url.path)).resolve()
        if (directory / retired).resolve() not in pages:
            errors.append(f"book.toml: the redirect page for {old} was not rendered")
        if (source / retired).with_suffix(".md").exists():
            errors.append(f"book.toml: {old} redirects a chapter that still exists")
        if target not in pages:
            errors.append(f"book.toml: {old} redirects to a missing page {new}")
        elif url.fragment and url.fragment not in pages[target].anchors:
            errors.append(f"book.toml: {old} redirects to a missing anchor {new}")
    return errors, len(redirects)


def check_redirects(pages, directory, root=ROOT):
    config = tomllib.loads((root / "book.toml").read_text(encoding="utf-8"))
    errors, count = redirect_errors(pages, directory.resolve(), config, root / "docs")
    if errors:
        raise ValueError("redirects of retired chapters do not resolve:\n  " + "\n  ".join(errors))
    print(f"Checked {count} redirects of retired chapters")


# A path to a chapter from the repository root, a relative one through `../`,
# or a link to the chapter on GitHub.
BOOK_REFERENCE = re.compile(r"(?:(?<=\.\./)|(?<=/(?:blob|tree)/main/)|(?<![\w./-]))"
                            r"docs/([A-Za-z0-9_./-]+\.md)(?:#([A-Za-z0-9_-]+))?")


# Recorded experiment runs keep the chapter paths they ran with, and the unit
# tests of the checkers build books of their own.
UNCHECKED_REFERENCES = (re.compile(r"^experiments/[^/]+/results/"), re.compile(r"^scripts/test_[^/]+\.py$"))


def tracked_files(root):
    listed = subprocess.run(["git", "-C", str(root), "ls-files", "-z"], capture_output=True, check=True)
    names = [name for name in listed.stdout.decode().split("\0") if name and not name.startswith("docs/")]
    return [root / name for name in names if not any(pattern.match(name) for pattern in UNCHECKED_REFERENCES)]


def reference_errors(files, pages, root, output):
    """Check that each `docs/<chapter>.md#anchor` named outside the book names a chapter and an anchor."""
    errors = []
    count = 0
    for file in files:
        try:
            text = file.read_text(encoding="utf-8")
        except (UnicodeDecodeError, IsADirectoryError, FileNotFoundError):
            continue
        for number, line in enumerate(text.splitlines(), 1):
            for match in BOOK_REFERENCE.finditer(line):
                count += 1
                page = (output / rendered_path(match[1])).resolve()
                where = f"{file.relative_to(root)}:{number}"
                if match[1] == "SUMMARY.md" and not match[2]:
                    continue
                if not (root / "docs" / match[1]).is_file() or page not in pages:
                    errors.append(f"{where}: docs/{match[1]} is not a chapter of the book")
                elif match[2] and match[2] not in pages[page].anchors:
                    errors.append(f"{where}: docs/{match[1]} has no anchor #{match[2]}")
    return errors, count


def check_references(pages, root, output):
    errors, count = reference_errors(tracked_files(root), pages, root, output.resolve())
    if errors:
        raise ValueError("references to the book from outside it do not resolve:\n  " + "\n  ".join(errors))
    print(f"Resolved {count} references to book chapters from files outside docs/")


if __name__ == "__main__":
    source = ROOT / "docs"
    output = ROOT / "target/book"
    chapters = check_contents(source, output)
    check_titles(source, chapters)
    check_style(source, chapters)
    check_includes(source, chapters)
    check_syntax(source, chapters)
    pages = check_html(output)
    check_redirects(pages, output)
    check_references(pages, ROOT, output)
