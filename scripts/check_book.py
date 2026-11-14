#!/usr/bin/env python3
"""Verify the book: its contents, rendering, links, includes, titles, style, Syntax blocks, grammar summary and limits.

The productions of the grammar summary must derive the source files of the
examples, as `scripts/book_grammar.py` recognizes them;
`scripts/check_grammar_derivations.py` checks the other direction with the
compiler.
"""

from collections import Counter
from html.parser import HTMLParser
import os
import json
import re
import subprocess
import tomllib
from pathlib import Path
from urllib.parse import unquote, urlsplit

import book_grammar
# The tests of this script read Chapter, read_contents and syntax_blocks through it.
from book_markdown import PRODUCTION, Chapter, code_blocks, expected_title, outside_code, read_contents, \
    syntax_blocks, unquote_prefix
import grammar_summary


ROOT = Path(__file__).resolve().parents[1]

# The title and style checks apply to every chapter of SUMMARY.md apart from the
# delivery records, which keep their original wording, as the style guide
# (docs/development/documentation.md#style-guide) says.
ARCHIVED = frozenset({
    "stage1-completion.md",
    "stage1-acceptance.md",
    "stage2-acceptance.md",
    "stage3-acceptance.md",
    "reverse-core-acceptance.md",
})

REPOSITORY = "MGYamada/Vastitas"

# Nonterminals that Syntax blocks use before the Reference chapter that owns
# the construct defines them, by that chapter. Remove an entry when its
# chapter gains the production.
PENDING_NONTERMINALS = {}


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

def check_titles(source, chapters, archived=ARCHIVED):
    listed = {chapter.path for chapter in chapters}
    stale = sorted(archived - listed)
    if stale:
        raise ValueError(f"archived chapters absent from SUMMARY.md: {stale}")
    errors = []
    checked = 0
    for chapter in chapters:
        if chapter.path in archived:
            continue
        checked += 1
        lines = [line for line in (source / chapter.path).read_text(encoding="utf-8").splitlines() if line.strip()]
        title = f"# {expected_title(chapter)}"
        if not lines or lines[0] != title:
            found = lines[0] if lines else "an empty file"
            errors.append(f"{chapter.path}: the first line must be {title!r}, found {found!r}")
    if errors:
        raise ValueError("chapter titles differ from SUMMARY.md:\n  " + "\n  ".join(errors))
    print(f"Checked the titles of {checked} chapters against SUMMARY.md")


# --- Style ----------------------------------------------------------------------

CODE_SPAN = re.compile(r"(`+)(.+?)\1")
WORDS = re.compile(r"\b(now|currently|new|newly|deliberately|actually)\b", re.I)
INTENSIFIERS = re.compile(r"\b(actual|simply|very|really)\b", re.I)
SHOULD = re.compile(r"\bshould\b", re.I)
STAGE = re.compile(r"\bStages? \d")
PROTOCOL = re.compile(r"\b[Pp]rotocols? (?:versions? )?\d")
ISSUE_LINK = re.compile(rf"https://github\.com/{REPOSITORY}/(?:issues|pull)/\d+")
ISSUE_NUMBER = re.compile(r"(?<![\w&/#])#\d+\b")
COMMIT = re.compile(r"\b(?=[0-9a-f]*\d)(?=[0-9a-f]*[a-f])[0-9a-f]{7,40}\b")
THEOREM = re.compile(r"\bVastitas(?:Kernel|Oracle|Bridge|Spec)\.[A-Z]")


def scan(text):
    """Yield each line outside code blocks with its line number, section and block context."""
    section = ""
    note = False
    for index, line in outside_code(text.splitlines()):
        quoted = line.lstrip().startswith(">")
        if not quoted:
            note = False
        elif unquote_prefix(line).startswith("**Implementation note.**"):
            note = True
        heading = re.match(r"^(#{1,6}) (.+)$", line)
        if heading and len(heading[1]) <= 2:
            section = heading[2].strip()
        yield index + 1, line, section, note


def prose(line):
    """Remove code spans, link targets, HTML, math, include directives and quoted mentions from a line."""
    line = re.sub(r"\{\{#[^}]*\}\}", " ", line)
    line = CODE_SPAN.sub(" ", line)
    line = re.sub(r"\]\([^)]*\)", "]", line)
    line = re.sub(r"<[^>]*>", " ", line)
    line = re.sub(r"\$\$.*?\$\$|\$[^$]*\$", " ", line)
    line = re.sub(r"\"[^\"]*\"|“[^”]*”", " ", line)
    return line


def style_errors(path, text, part, reference=None):
    """Return the style-guide violations of one chapter in the given part.

    reference is the set of the paths of the Reference chapters, which the
    See also section of a guide chapter links; None skips that rule.
    """
    errors = []
    generated = path.startswith("spec/")

    def report(number, message):
        errors.append(f"{path}:{number}: {message}")

    for number, line, section, note in scan(text):
        words = prose(line)
        for match in WORDS.finditer(words):
            report(number, f"the style guide bans {match[0]!r}")
        if part in ("guide", "reference"):
            for match in INTENSIFIERS.finditer(words):
                report(number, f"the style guide bans the intensifier {match[0]!r}")
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
    if part == "guide" and path != "README.md":
        see_also = re.search(r"^## See also\s*$(?![\s\S]*^## )([\s\S]*)", text, re.M)
        if not see_also:
            errors.append(f"{path}: a guide chapter ends with a '## See also' section")
        elif reference is not None and not linked_chapters(path, see_also[1], text) & reference:
            errors.append(f"{path}: the See also section links no chapter of the Vastitas Reference")
    return errors


HTML_COMMENT = re.compile(r"<!--[\s\S]*?(?:-->|$)")
INLINE_LINK = re.compile(r"\]\(\s*<?([^)\s>]+)>?(?:\s+[\"'(][^)]*)?\)")
REFERENCE_LINK = re.compile(r"\[((?:[^\[\]]|\[[^\]]*\])+)\](?:\s?\[([^\]]*)\])?(?![(:])")
LINK_DEFINITION = re.compile(r"^ {0,3}\[([^\]]+)\]:\s*<?(\S+?)>?(?:\s+.*)?$", re.M)


def label_key(label):
    return re.sub(r"\s+", " ", label).strip().lower()


def linked_chapters(path, text, chapter=None):
    """The chapters that the Markdown links of a text in the chapter at path name, as paths in the book.

    The links are inline links and reference links, whose definitions may lie
    anywhere in the chapter. A link in code or in an HTML comment links nothing.
    """
    def visible(markdown):
        markdown = HTML_COMMENT.sub(" ", markdown)
        markdown = "\n".join(line for _, line, _, _ in scan(markdown))
        return CODE_SPAN.sub(" ", markdown)

    definitions = {label_key(label): target for label, target in LINK_DEFINITION.findall(visible(chapter or text))}
    shown = visible(text)
    found = INLINE_LINK.findall(shown)
    for match in REFERENCE_LINK.finditer(shown):
        label = label_key(match[2] or match[1])
        if label in definitions:
            found.append(definitions[label])
    targets = set()
    for target in found:
        url = urlsplit(target)
        if not url.scheme and not url.netloc and url.path.endswith(".md"):
            targets.add(os.path.normpath(os.path.join(os.path.dirname(path), unquote(url.path))).replace(os.sep, "/"))
    return {"README.md" if target == "index.md" else target for target in targets}


# --- Definitions and the glossary -------------------------------------------------

GLOSSARY = "appendix/glossary.md"
# Strong emphasis, with asterisks or with underscores, inside a paragraph.
BOLD = re.compile(r"\*\*(?=\S)(.+?)(?<=\S)\*\*|(?<!\w)__(?=\S)(.+?)(?<=\S)__(?!\w)")
# Bold text in a Reference chapter that defines no term, with the reason.
NOT_DEFINITIONS = {
    "Syntax": "the label of a Syntax block",
    "Implementation note.": "the label of an implementation note",
    "must": "a rule word, which Notation defines",
    "must not": "a rule word, which Notation defines",
    "may": "a rule word, which Notation defines",
    "is an error (`E_CODE`)": "a rule word, which Notation defines",
}


def term_forms(term):
    """The forms of a term under which the glossary may list it: as written, without code marks, singular."""
    key = re.sub(r"\s+", " ", term.replace("`", "")).strip().rstrip(".:,;").lower()
    forms = {key}
    if key.endswith("ices"):
        forms |= {key[:-4] + "ex", key[:-4] + "ix"}
    if key.endswith("ies"):
        forms.add(key[:-3] + "y")
    if key.endswith("es"):
        forms.add(key[:-2])
    if key.endswith("s") and not key.endswith("ss"):
        forms.add(key[:-1])
    return forms


BLOCK_START = re.compile(r"^(?:#{1,6} |[-*+] |\d+\. |\|)")


def paragraphs(text):
    """Yield the paragraphs outside code blocks as [(line number, text of the line)], quote marks removed.

    A blank line, a code block, a heading, a list item, a table row and the
    edge of a block quote end a paragraph.
    """
    current = []
    for number, line, _, _ in scan(text):
        body = unquote_prefix(line).strip()
        quoted = line.lstrip().startswith(">")
        if current and (not body or number != current[-1][0] + 1 or BLOCK_START.match(body)
                        or quoted != current[-1][2]):
            yield [(n, b) for n, b, _ in current]
            current = []
        if body:
            current.append((number, body, quoted))
            if re.match(r"^#{1,6} |\|", body):
                yield [(number, body)]
                current = []
    if current:
        yield [(n, b) for n, b, _ in current]


def bold_terms(text):
    """Yield (line number, term) for each term in strong emphasis outside code, also across line breaks."""
    for paragraph in paragraphs(text):
        joined = " ".join(body for _, body in paragraph)
        # Asterisks and underscores in a code span mark no emphasis; keep the length of the text.
        masked = CODE_SPAN.sub(lambda match: re.sub(r"[*_]", " ", match[0]), joined)
        starts = []
        offset = 0
        for number, body in paragraph:
            starts.append((offset, number))
            offset += len(body) + 1
        for match in BOLD.finditer(masked):
            number = max(start for start in starts if start[0] <= match.start())[1]
            yield number, joined[match.start(1) if match[1] else match.start(2):
                                 match.end(1) if match[1] else match.end(2)].strip()


def glossary_terms(text):
    """The terms of the glossary: the title of each entry and the terms that an entry sets in bold."""
    terms = set()
    for heading in re.findall(r"^## (.+?)\s*$", text, re.M):
        terms |= term_forms(heading)
    for _, term in bold_terms(text):
        terms |= term_forms(term)
    return terms


def definition_errors(path, text, part, glossary):
    """A term that a Reference chapter sets in bold, where it defines the term, has a glossary entry."""
    if part != "reference":
        return []
    errors = []
    for number, term in bold_terms(text):
        if term not in NOT_DEFINITIONS and not term_forms(term) & glossary:
            errors.append(f"{path}:{number}: the bold term {term!r} has no entry in the glossary ({GLOSSARY})")
    return errors


def check_style(source, chapters, archived=ARCHIVED):
    errors = []
    checked = 0
    reference = {chapter.path for chapter in chapters if chapter.part == "reference"}
    glossary_file = source / GLOSSARY
    glossary = glossary_terms(glossary_file.read_text(encoding="utf-8")) if glossary_file.is_file() else set()
    for chapter in chapters:
        if chapter.path not in archived:
            checked += 1
            text = (source / chapter.path).read_text(encoding="utf-8")
            errors += style_errors(chapter.path, text, chapter.part, reference)
            errors += definition_errors(chapter.path, text, chapter.part, glossary)
    if errors:
        raise ValueError("style guide violations:\n  " + "\n  ".join(errors))
    print(f"Checked the style of {checked} chapters by part; bold text that defines no term: "
          + ", ".join(repr(term) for term in NOT_DEFINITIONS))


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


MAIN = re.compile(r"\s*(?:pub\s+)?(?:resource\s+)?fn\s+main\s*\(")
# The beginning of a named function, resource function or method; an abstract
# method has no body, and a lambda has no name.
DEFINITION = re.compile(r"^[ \t]*(?:pub\s+)?(?:resource\s+)?(?:fn|method)\s+"
                        r"[A-Za-z_][A-Za-z0-9_]*(?:\s*::\s*[A-Za-z_][A-Za-z0-9_]*)*\s*\(", re.M)
# What stands between the parameters and the body: a result type, `returns (…)`
# and `requires (…)`, without a blank line, `;` or `=`.
SIGNATURE_REST = re.compile(r"(?:[^{};=\n]|\n(?![ \t]*\n))*?\{")
# A diagnostic line of a program: a place in a file, which may hold spaces but
# no quotes, with an optional line and column, and a code. A form such as `MANIFEST:
# E_MANIFEST: message` names no file, and a diagnostic without a place is
# about a command, which no rejected program records.
DIAGNOSTIC_LINE = re.compile(r"^\s*[^\s:'\"`$][^:\n'\"`$]*\.[A-Za-z0-9]+(?::\d+:\d+)?: E_[A-Z][A-Z0-9_]*: ")


def complete_definitions(text):
    """Yield the offset of each named function or method of a text whose signature a body follows."""
    for match in DEFINITION.finditer(text):
        depth = 0
        for index in range(match.end() - 1, len(text)):
            depth += {"(": 1, ")": -1}.get(text[index], 0)
            if depth == 0:
                break
        else:
            continue
        if SIGNATURE_REST.match(text, index + 1):
            yield match.start()


def program_errors(chapter, text):
    """A complete program, function or diagnostic in a chapter comes from a tested file through an include."""
    errors = []
    for number, label, content in code_blocks(text):
        typed = [line for line in content if not INCLUDE.search(line)]
        if label in ("", "vast", "text") and any(MAIN.match(line) for line in typed):
            errors.append(f"{chapter}:{number}: a complete program is included from a tested file "
                          "under examples/ (style guide, Examples)")
        elif label in ("", "vast") and next(complete_definitions("\n".join(typed)), None) is not None:
            errors.append(f"{chapter}:{number}: a complete function or method is included from a tested file "
                          "under examples/ with an ANCHOR (style guide, Examples)")
        if any(DIAGNOSTIC_LINE.match(line) for line in typed):
            errors.append(f"{chapter}:{number}: the diagnostic of a rejected program is included from its "
                          ".stderr file (style guide, Examples)")
    for match in INCLUDE.finditer(text):
        selector = match[3].partition(":")[2]
        if not match[1] and selector and re.fullmatch(r"\d*(?::\d*)?", selector):
            errors.append(f"{chapter}: {{{{#{match[2]} {match[3]}}}}} selects lines; mark the part with "
                          "ANCHOR comments and include it by name (style guide, Examples)")
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

TERMINAL = re.compile(r"`([^`]+)`")
SYMBOL = re.compile(r"\b([A-Z][A-Za-z0-9_]*)\b")


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
        for _, productions, _ in blocks:
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


# --- Grammar summary ------------------------------------------------------------

def check_grammar(source, chapters):
    """The grammar summary holds the productions of the Syntax blocks of the Reference, as generated."""
    errors = grammar_summary.errors(source, chapters)
    if errors:
        raise ValueError("the grammar summary is not fresh:\n  " + "\n  ".join(errors))
    print(f"Checked that the generated chapter {grammar_summary.CHAPTER} is fresh")


# --- The examples against the productions -----------------------------------------

# The source files that the productions must derive from SourceFile: every
# .vast file under these directories, apart from what the recorded
# diagnostics of a rejected program decide.
PARSED_SOURCES = ("examples", "stdlib/src", "nature")
REJECTED = "examples/reject"
# A file of a rejected program with one of these codes must not parse.
PARSE_CODES = frozenset({"E_PARSE", "E_LEX"})
# A file of a rejected program with one of these codes may parse or not, with the reason.
UNDECIDED_CODES = {
    "E_UNSUPPORTED": "the code reports syntax that the language does not have, such as a type name that no "
                     "chapter defines, and also rules on text that the productions derive",
    "E_RESERVED": "the code reports a reserved name, which the productions derive as an identifier, and a "
                  "keyword such as while where a name stands, which they do not derive",
}
# Files whose recorded code does not follow from the productions, with the rule that gives the code.
PARSE_EXCEPTIONS = {
    "examples/reject/expressions/chained-comparison.vast": (
        True, "Expressions, Operator expressions: a comparison must not be an operand of another comparison "
              "without parentheses (E_PARSE); the productions derive the text"),
    "examples/reject/packages/smooth-pullback-mode/main.vast": (
        False, "Smooth affine declarations, Reverse-pass primitives: a mode other than saved or recomputed is "
               "an error (E_TYPE); the production lists the two modes"),
}
RECORDED = re.compile(r"^(\S+?\.vast):\d+:\d+: (E_[A-Z][A-Z0-9_]*): ", re.M)


def recorded_codes(root):
    """{source file: the codes that the recorded diagnostics of the rejected programs give at it}."""
    codes = {}
    for record in sorted((root / REJECTED).rglob("*.stderr")):
        for path, code in RECORDED.findall(record.read_text(encoding="utf-8")):
            codes.setdefault(path, set()).add(code)
    return codes


def parse_errors(root, grammar, exceptions=PARSE_EXCEPTIONS, sources=PARSED_SOURCES):
    """Parse every source file with the productions; return (errors, parsed, rejected, skipped)."""
    codes = recorded_codes(root)
    errors = []
    parsed = rejected = 0
    skipped = []
    files = sorted(file for directory in sources for file in (root / directory).rglob("*.vast")
                   if not any(part.startswith(".") for part in file.relative_to(root).parts))
    for file in files:
        name = file.relative_to(root).as_posix()
        recorded = codes.get(name, set())
        source = book_grammar.read(file)
        failure = grammar.parse(source)
        if name in exceptions:
            expected, reason = exceptions[name]
            if (failure is None) != expected:
                errors.append(f"{name}: PARSE_EXCEPTIONS says that the productions "
                              f"{'derive' if expected else 'do not derive'} the file, which is no longer so; "
                              "remove the entry")
            skipped.append(f"{name}: {reason}")
            continue
        if recorded & PARSE_CODES:
            rejected += 1
            if failure is None:
                errors.append(f"{name}: the compiler reports {sorted(recorded & PARSE_CODES)[0]}, "
                              "but the productions derive the file")
            continue
        undecided = sorted(recorded & UNDECIDED_CODES.keys())
        if undecided:
            skipped.append(f"{name}: {undecided[0]}, {UNDECIDED_CODES[undecided[0]]}")
            continue
        parsed += 1
        if failure:
            errors.append(f"{name}:{failure.where(source)}: {failure.message}")
    return errors, parsed, rejected, skipped


def check_parse(source, root=ROOT):
    """The productions of the grammar summary derive the source files of the examples from SourceFile."""
    grammar = book_grammar.Grammar(book_grammar.read_productions(
        (source / book_grammar.GRAMMAR_CHAPTER).read_text(encoding="utf-8")))
    if grammar.errors:
        raise ValueError("the productions of the grammar summary do not form a grammar:\n  "
                         + "\n  ".join(grammar.errors))
    errors, parsed, rejected, skipped = parse_errors(root, grammar)
    if errors:
        raise ValueError("the productions disagree with the examples:\n  " + "\n  ".join(errors))
    print(f"Parsed {parsed} source files of {' and '.join(PARSED_SOURCES)} with the productions from "
          f"{book_grammar.START}; {rejected} rejected files with {' or '.join(sorted(PARSE_CODES))} do not parse")
    print("  The tokenizer reads in prose: " + ", ".join(book_grammar.PROSE_FORMS) + "; it splits "
          + ", ".join(f"{token} into {' '.join(parts)}" for token, (parts, _) in book_grammar.SPLIT_TOKENS.items())
          + " after type arguments")
    print(f"  Skipped {len(skipped)} files:")
    for entry in skipped:
        print(f"    {entry}")


# --- Limits ---------------------------------------------------------------------

LIMITS_CHAPTER = "appendix/limits.md"
LIMITS_FILE = "lean-kernel/compiler-limits.json"
# A table row whose first cell is one name in code font; its second cell is the value.
LIMIT_ROW = re.compile(r"^\| `([A-Za-z][A-Za-z0-9]*)` \| ([^|]*) \|")
# A value as the appendix writes it: 4096 or 1,000,000.
LIMIT_VALUE = re.compile(r"[0-9]{1,3}(?:,[0-9]{3})+|[0-9]+")


def limit_value(cell):
    """The number that a value cell gives, or None for a cell that is no number."""
    cell = cell.strip()
    return int(cell.replace(",", "")) if LIMIT_VALUE.fullmatch(cell) else None


def limit_errors(text, limits):
    """Each key of the limits file has a row, and every row of a key carries the value of the file.

    A row whose first cell is another name in code font and whose value is a
    number names no key of the file, which is an error too.
    """
    errors = []
    listed = set()
    for number, line in enumerate(text.splitlines(), 1):
        row = LIMIT_ROW.match(line)
        if not row:
            continue
        key, value = row[1], limit_value(row[2])
        where = f"{LIMITS_CHAPTER}:{number}"
        if key in limits:
            listed.add(key)
            if value is None:
                errors.append(f"{where}: the value of `{key}` must be the number {limits[key]} "
                              f"of {LIMITS_FILE}, not {row[2].strip()!r}")
            elif limits[key] != value:
                errors.append(f"{where}: `{key}` is {limits[key]} in {LIMITS_FILE}, not {value}")
        elif value is not None:
            errors.append(f"{where}: `{key}` is no key of {LIMITS_FILE}")
    errors += [f"{LIMITS_CHAPTER}: no row gives the limit `{key}` of {LIMITS_FILE}"
               for key in limits if key not in listed]
    return errors


def check_limits(source, root=ROOT):
    limits = json.loads((root / LIMITS_FILE).read_text(encoding="utf-8"))
    errors = limit_errors((source / LIMITS_CHAPTER).read_text(encoding="utf-8"), limits)
    if errors:
        raise ValueError("Appendix D disagrees with the limits file:\n  " + "\n  ".join(errors))
    print(f"Checked the {len(limits)} limits of {LIMITS_FILE} against Appendix D")


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


def repository_files(root):
    """The paths of the files that Git tracks in the checkout at root."""
    listed = subprocess.run(["git", "-C", str(root), "ls-files", "-z"], capture_output=True, check=True)
    return [name for name in listed.stdout.decode().split("\0") if name]


def tracked_files(root):
    names = [name for name in repository_files(root) if not name.startswith("docs/")]
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


# --- Repository paths in the chapters ----------------------------------------------

# Paths that a chapter names in code although Git tracks no file under them, with the reason.
UNTRACKED_PATHS = {
    "lean-kernel/.lake": "the build directory of the kernel, which Git ignores",
    "stdlib/target": "the generated standard-library package, which Git ignores",
    "stdlib/indexed": "a retired facade, which the chapters name as removed",
}
# A word with a placeholder or a wildcard names a pattern of paths, not a path.
PATH_PATTERN = re.compile(r"[<>{}*?\[\]$]")


def path_errors(chapters, source, files, untracked=UNTRACKED_PATHS):
    """Check that each repository path in a code span of a chapter names a tracked file or directory.

    A word of a code span names a repository path when it begins with a
    top-level directory of the tracked files and a slash. A line number, a
    test name after `:` or `::` and an anchor after `#` are not part of the
    path. A path under `src/` counts only when it names a `.rs` file, because
    the sources of a package, such as `src/lib.vast`, begin the same way.
    Return (errors, the number of paths checked).
    """
    known = set()
    for name in files:
        parts = name.split("/")
        known.update("/".join(parts[:length]) for length in range(1, len(parts) + 1))
    roots = tuple(sorted({name.split("/")[0] + "/" for name in files if "/" in name}))
    errors = []
    count = 0
    used = set()
    for chapter in chapters:
        text = (source / chapter.path).read_text(encoding="utf-8")
        for number, line, _, _ in scan(text):
            for span in CODE_SPAN.finditer(line):
                for word in span[2].split():
                    if not word.startswith(roots) or PATH_PATTERN.search(word):
                        continue
                    path = re.split(r"[:#]", word, maxsplit=1)[0].rstrip("/")
                    if path.startswith("src/") and not path.endswith(".rs"):
                        continue
                    entry = next((entry for entry in untracked if path == entry or path.startswith(entry + "/")), None)
                    if entry is not None:
                        used.add(entry)
                        continue
                    count += 1
                    if path not in known:
                        errors.append(f"{chapter.path}:{number}: `{word}` names no file or directory that Git tracks")
    for entry in untracked:
        if entry in known:
            errors.append(f"UNTRACKED_PATHS: Git tracks {entry}; remove the entry")
        elif entry not in used:
            errors.append(f"UNTRACKED_PATHS: no chapter names {entry}; remove the entry")
    return errors, count


def check_paths(source, chapters, root=ROOT):
    errors, count = path_errors(chapters, source, repository_files(root))
    if errors:
        raise ValueError("code spans of the chapters name missing repository paths:\n  " + "\n  ".join(errors))
    print(f"Checked {count} repository paths in the code spans of {len(chapters)} chapters against the tracked files")


if __name__ == "__main__":
    source = ROOT / "docs"
    output = ROOT / "target/book"
    chapters = check_contents(source, output)
    check_titles(source, chapters)
    check_style(source, chapters)
    check_includes(source, chapters)
    check_syntax(source, chapters)
    check_grammar(source, chapters)
    check_parse(source)
    check_limits(source)
    pages = check_html(output)
    check_redirects(pages, output)
    check_references(pages, ROOT, output)
    check_paths(source, chapters)
