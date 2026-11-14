"""The Markdown of the book, as the checkers of the book read it.

`scripts/check_book.py`, `scripts/grammar_summary.py` and
`scripts/book_grammar.py` share these readers: the chapters of SUMMARY.md
with their parts and titles, the fenced code blocks of a chapter, and the
productions of its Syntax blocks.
"""

from dataclasses import dataclass
import re


# The parts of SUMMARY.md, by their part title. Chapters before the first part
# title form the guide.
PARTS = {
    "Vastitas Reference": "reference",
    "How the compiler is checked": "internals",
    "Appendices": "appendix",
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


def expected_title(chapter):
    """The H1 of a chapter is its title in SUMMARY.md; "X: Name" in the appendices is "Appendix X: Name"."""
    letter = re.fullmatch(r"([A-Z]): (.+)", chapter.title)
    if chapter.part == "appendix" and letter:
        return f"Appendix {letter[1]}: {letter[2]}"
    return chapter.title


# --- Fenced code blocks ---------------------------------------------------------

FENCE = re.compile(r"^(`{3,}|~{3,})")


def unquote_prefix(line):
    """Remove the blockquote markers that begin a line."""
    return re.sub(r"^\s*(?:>\s?)+", "", line)


def fences(lines):
    """Yield (start, end, label) for each fenced code block of the lines of a chapter, also inside block quotes.

    start is the index of the line that opens the block, and end is the index
    of the line that closes it, or len(lines) for a block that runs to the end.
    A line of three or more backquotes or tildes, which a label may follow,
    opens a block. A line of the same character, at least as long and with no
    text after it, closes the block.
    """
    index = 0
    while index < len(lines):
        body = unquote_prefix(lines[index]).lstrip()
        marker = FENCE.match(body)
        if marker:
            start = index
            index += 1
            while index < len(lines):
                inner = unquote_prefix(lines[index]).lstrip()
                closing = FENCE.match(inner)
                if closing and closing[1][0] == marker[1][0] and len(closing[1]) >= len(marker[1]) \
                        and not inner[len(closing[1]):].strip():
                    break
                index += 1
            yield start, index, body[len(marker[1]):].strip()
        index += 1


def outside_code(lines):
    """Yield (index, line) for each line that no fenced code block holds; the fences belong to their block."""
    code = {index for start, end, _ in fences(lines) for index in range(start, end + 1)}
    for index, line in enumerate(lines):
        if index not in code:
            yield index, line


def code_blocks(text):
    """Yield (line number, label, lines) for each fenced code block, also inside block quotes."""
    lines = text.splitlines()
    for start, end, label in fences(lines):
        yield start + 1, label, [unquote_prefix(line) for line in lines[start + 1:end]]


# --- Syntax blocks --------------------------------------------------------------

PRODUCTION = re.compile(r"^([A-Za-z][A-Za-z0-9_]*) ->(?: (.*))?$")


def syntax_blocks(text):
    """Yield (line number, productions, lines) for each Syntax block of a chapter.

    The productions are (line number, text) with their continuation lines
    joined. The lines are those of the code block of the Syntax block as the
    chapter writes them, without the quote marks and the trailing whitespace.
    """
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
            first = index
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
            yield start + 1, productions, [unquote_prefix(line).rstrip() for line in lines[first:index]]
        index += 1
