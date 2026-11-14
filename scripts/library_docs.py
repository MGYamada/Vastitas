#!/usr/bin/env python3
"""Check that the API reference pages of the libraries list exactly the exports of their modules.

Each module directory of `stdlib/src/` and `nature/src/`, which holds a
`mod.vast`, has a page under `docs/` of its library at the same path:
`stdlib/src/geometry/scheme/` has `stdlib/docs/geometry/scheme.md`. The root
module of a library has `docs/README.md`: `nature/src/mod.vast`, and the
entrypoint of `stdlib` that `scripts/build_stdlib_package.py` generates. The
modules that the script generates from the flat sources of
`stdlib/src/arithmetic/`, whose functions and generics become `pub`, have
`stdlib/docs/arithmetic.md`; it names the function `f` of the module
`std::arithmetic::m` as `m::f`.

A page lists the names in the first column of its tables whose header is
`| Name | Kind | Contract |`. A Name cell is one code span that begins with
the name, such as `Point<X, S>` or `pullback(f, x, eta)`. The check fails
when a public item of a module (`pub indexed`, `pub fn`, `pub generic`,
`pub mod` or `pub use`) is missing from the page of the module, when a page
lists a name that its module does not export, and when a relative link of a
Markdown file of a library names no file.
"""
import re
import sys
from pathlib import Path
from urllib.parse import unquote, urlsplit

import build_stdlib_package as generator

ROOT = Path(__file__).resolve().parents[1]
LIBRARIES = ("stdlib", "nature")
HEADER = ["Name", "Kind", "Contract"]

COMMENT = re.compile(r"//[^\n]*")
PUB = re.compile(r"\bpub\b")
# A public item at the start of a line, and the name that it exports.
PUBLIC = re.compile(
    r"^pub\s+(?:indexed\s+[a-z_]+\s+(?P<indexed>\w+)"
    r"|(?:fn|generic)\s+(?P<function>\w+)"
    r"|mod\s+(?P<module>\w+)\s*;"
    r"|use\s+(?P<path>\w+(?:::\w+)*)(?:\s+as\s+(?P<alias>\w+))?\s*;)",
    re.M,
)
CELL = re.compile(r"(?<!\\)\|")
NAME = re.compile(r"`(?P<name>[A-Za-z_]\w*(?:::[A-Za-z_]\w*)*)(?:[<(][^`]*)?`")
CODE_SPAN = re.compile(r"(`+).+?\1")
LINK = re.compile(r"\]\(\s*<?([^)\s>]+)>?(?:\s+[\"'(][^)]*)?\)")


def exports(source):
    """(the names that the public items of a source export, the errors of the items it cannot read)."""
    text = COMMENT.sub("", source)
    names, errors = [], []
    for match in PUB.finditer(text):
        item = PUBLIC.match(text, match.start())
        if item is None:
            line = text.count("\n", 0, match.start()) + 1
            errors.append(f"line {line}: this check reads no public item here; extend scripts/library_docs.py")
            continue
        names.append(item["indexed"] or item["function"] or item["module"] or item["alias"]
                     or item["path"].rsplit("::", 1)[-1])
    return names, errors


def outside_code(text):
    """Yield (line number, line) for each line outside fenced code blocks."""
    fence = None
    for number, line in enumerate(text.splitlines(), 1):
        marker = re.match(r"^\s*(```+|~~~+)", line)
        if marker:
            if fence is None:
                fence = marker[1]
            elif marker[1].startswith(fence):
                fence = None
            continue
        if fence is None:
            yield number, line


def cells(line):
    stripped = line.strip()
    if not (stripped.startswith("|") and stripped.endswith("|")):
        return None
    return [cell.strip() for cell in CELL.split(stripped)[1:-1]]


def listed(text):
    """(the names of the Name columns of a page with their line numbers, the errors of their rows)."""
    names, errors = [], []
    lines = list(outside_code(text))
    index = 0
    while index < len(lines):
        number, line = lines[index]
        index += 1
        if cells(line) != HEADER:
            continue
        delimiter = cells(lines[index][1]) if index < len(lines) else None
        if not delimiter or not all(re.fullmatch(r":?-+:?", cell) for cell in delimiter):
            errors.append(f"line {number}: the header row of a table needs a delimiter row")
            continue
        index += 1
        while index < len(lines) and cells(lines[index][1]) is not None:
            number, row = lines[index]
            index += 1
            columns = cells(row)
            name = NAME.fullmatch(columns[0]) if columns else None
            if len(columns) != len(HEADER) or name is None or not all(columns[1:]):
                errors.append(f"line {number}: a row needs one code span that begins with a name, a kind "
                              "and a contract")
                continue
            names.append((name["name"], number))
    return names, errors


def link_errors(path, root):
    """The relative links of a Markdown file that name no file or directory."""
    errors = []
    for number, line in outside_code(path.read_text(encoding="utf-8")):
        for target in LINK.findall(CODE_SPAN.sub(" ", line)):
            url = urlsplit(target)
            if url.scheme or url.netloc or not url.path:
                continue
            if not (path.parent / unquote(url.path)).exists():
                errors.append(f"{path.relative_to(root)}:{number}: the link {target} names no file")
    return errors


def modules(root, library):
    """{page: (module, its exported names, the errors of its sources)} of one library."""
    src = root / library / "src"
    docs = root / library / "docs"
    found = {}
    if not src.is_dir():
        return found, [f"{library}/src: no source directory"]
    errors = []
    sources = sorted(src.rglob("*.vast"))
    # The flat sources from which scripts/build_stdlib_package.py generates std::arithmetic.
    flat = {src / "arithmetic" / f"{name}.vast" for name, _ in generator.ARITHMETIC} if library == "stdlib" else set()
    for path in sources:
        if path.name != "mod.vast" and path not in flat:
            errors.append(f"{path.relative_to(root)}: a source file other than mod.vast or a flat arithmetic "
                          "source, which this check maps to no page")
    for path in sources:
        if path.name != "mod.vast":
            continue
        directory = path.parent.relative_to(src)
        page = docs / ("README.md" if directory == Path(".") else f"{directory.as_posix()}.md")
        names, unread = exports(path.read_text(encoding="utf-8"))
        found[page] = (path.relative_to(root).as_posix(), names,
                       [f"{path.relative_to(root)}: {error}" for error in unread])
    if library == "stdlib":
        try:
            generated = {name: text.decode("utf-8") for name, text in generator.package_sources(root).items()}
        except OSError as error:
            return found, errors + [f"stdlib/src/arithmetic: {error}"]
        for page, entry, prefix in [(docs / "README.md", "lib.vast", None),
                                    (docs / "arithmetic.md", "arithmetic.vast", "arithmetic")]:
            names, unread = exports(generated[entry])
            where = f"stdlib/target/package/{entry} (generated)"
            problems = [f"{where}: {error}" for error in unread]
            if prefix:
                for module in list(names):
                    inner, more = exports(generated[f"{prefix}/{module}.vast"])
                    names += [f"{module}::{name}" for name in inner]
                    problems += [f"stdlib/target/package/{prefix}/{module}.vast (generated): {error}" for error in more]
            found[page] = (where, names, problems)
    return found, errors


def check(root=ROOT, libraries=LIBRARIES):
    """Return (the errors, the number of pages, the number of names)."""
    errors = []
    pages = 0
    count = 0
    for library in libraries:
        found, problems = modules(root, library)
        errors += problems
        docs = root / library / "docs"
        for page, (module, exported, unread) in sorted(found.items()):
            errors += unread
            where = page.relative_to(root)
            if not page.is_file():
                errors.append(f"{where}: missing; it lists the exports of {module}")
                continue
            pages += 1
            names, rows = listed(page.read_text(encoding="utf-8"))
            errors += [f"{where}: {error}" for error in rows]
            seen = {}
            for name, number in names:
                if name in seen:
                    errors.append(f"{where}:{number}: {name} is listed twice")
                seen.setdefault(name, number)
                if name not in exported:
                    errors.append(f"{where}:{number}: {name} is not exported by {module}")
            for name in exported:
                if name not in seen:
                    errors.append(f"{where}: {module} exports {name}, which the page does not list")
            count += len(seen)
        for page in sorted(docs.rglob("*.md")) if docs.is_dir() else []:
            if page not in found:
                errors.append(f"{page.relative_to(root)}: lists the exports of no module of {library}")
        for path in sorted((root / library).rglob("*.md")):
            if "target" not in path.relative_to(root / library).parts:
                errors += link_errors(path, root)
    return errors, pages, count


def main():
    errors, pages, count = check()
    if errors:
        print("The library pages differ from the exports of their modules:\n  " + "\n  ".join(errors),
              file=sys.stderr)
        return 1
    print(f"Checked {count} exported names on {pages} library pages against the modules of "
          f"{' and '.join(LIBRARIES)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
