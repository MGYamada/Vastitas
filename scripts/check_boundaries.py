#!/usr/bin/env python3
"""Check compiler/oracle dependencies without loading the Lean toolchain."""
import json
from pathlib import Path
import re
import sys
from typing import NamedTuple


MATHLIB_REVISION = "56a005855ea17e0b0958f73ec801ae140b0a1679"
_SEGMENT = r"(?:[^\W\d][\w']*|«[^»]*»)"
_NAME = re.compile(rf"{_SEGMENT}(?:\.{_SEGMENT})*")
_SEGMENTS = re.compile(_SEGMENT)
# A declaration can follow the header on the same line. Additional module
# names on an import line are checked conservatively, even though Lean 4.35
# normally accepts one module per import command.
_COMMANDS = {
    "import", "public", "meta", "module", "prelude", "def", "theorem",
    "lemma", "abbrev", "axiom", "opaque", "example", "instance", "class",
    "structure", "inductive", "mutual", "namespace", "open", "section",
    "end", "noncomputable", "private", "protected", "unsafe", "partial",
    "variable", "variables", "universe", "universes", "set_option",
    "attribute", "syntax", "macro", "macro_rules", "elab", "elab_rules",
    "initialize", "builtin_initialize", "local", "scoped", "export",
}


class _Token(NamedTuple):
    text: str
    line: int
    is_name: bool


def _header_tokens(source):
    """Lazily tokenize the header, skipping nested and line comments.

    Stop scanning at the first declaration: strings, quotations, and new
    declaration syntax need not be interpreted by this dependency checker.
    """
    position = 0
    line = 1
    while position < len(source):
        if source[position].isspace():
            line += source[position] == "\n"
            position += 1
            continue
        if source.startswith("--", position):
            end = source.find("\n", position)
            position = len(source) if end < 0 else end
            continue
        if source.startswith("/-", position):
            depth = 1
            position += 2
            while depth:
                if position >= len(source):
                    raise ValueError("unterminated block comment in Lean header")
                if source.startswith("/-", position):
                    depth += 1
                    position += 2
                elif source.startswith("-/", position):
                    depth -= 1
                    position += 2
                else:
                    line += source[position] == "\n"
                    position += 1
            continue
        match = _NAME.match(source, position)
        if match:
            text = match.group(0)
            yield _Token(text, line, True)
            position = match.end()
            line += text.count("\n")
        else:
            yield _Token(source[position], line, False)
            position += 1


def lean_imports(source):
    """Read header imports, including public/meta/import-all variants."""
    tokens = iter(_header_tokens(source))
    eof = _Token("", 0, False)
    current = next(tokens, eof)

    def consume():
        nonlocal current
        token = current
        current = next(tokens, eof)
        return token

    if current.text == "module":
        consume()
    if current.text == "prelude":
        consume()
    imports = []
    while current != eof:
        if current.text == "public":
            consume()
        if current.text == "meta":
            consume()
        if current.text != "import":
            break
        consume()
        if current.text == "all":
            consume()
        if not current.is_name or current.text in _COMMANDS:
            raise ValueError("missing module name in Lean import")
        first = consume()
        imports.append(first.text)
        while (current.is_name and current.line == first.line
               and current.text not in _COMMANDS):
            imports.append(consume().text)
    return imports


def module_allowed(name, roots):
    """Match actual namespace components, including quoted identifiers."""
    if not _NAME.fullmatch(name):
        return False
    first = _SEGMENTS.match(name).group(0)
    if first.startswith("«"):
        first = first[1:-1]
    return first in roots


def check_boundaries(root):
    root = Path(root)
    kernel = root / "lean-kernel"
    errors = []
    manifest = json.loads((kernel / "lake-manifest.json").read_text())
    if manifest.get("packages"):
        errors.append("lean-kernel must have no external Lake package dependencies")
    runtime = kernel / "VastitasKernel" / "Runtime.lean"
    runtimes = {runtime, kernel / "VastitasKernel" / "IndexedRuntime.lean"}
    native = kernel / "native"
    if native.exists():
        native_manifest = json.loads((native / "lake-manifest.json").read_text())
        if native_manifest.get("packages"):
            errors.append("native storage runtime must have no external Lake package dependencies")
        if (native / "lean-toolchain").read_text().strip() != (kernel / "lean-toolchain").read_text().strip():
            errors.append("native storage runtime and kernel must use the same Lean toolchain")
        native_runtime = native / "VastitasStorageNative" / "Runtime.lean"
        runtimes.add(native_runtime)
        if not native_runtime.is_file():
            errors.append("native storage runtime source is missing")
    if not runtime.is_file():
        errors.append("kernel runtime source is missing")
    for source in kernel.rglob("*.lean"):
        if ".lake" in source.parts:
            continue
        try:
            imports = lean_imports(source.read_text())
        except ValueError as error:
            errors.append(f"{source.relative_to(root)}: {error}")
            continue
        for name in imports:
            allowed = {"Init", "Std", "Lean", "VastitasKernel"}
            if source.is_relative_to(native):
                allowed = {"Init", "Std", "VastitasStorageNative"}
                if source == native / "lakefile.lean":
                    allowed = {"Lake"}
            if source.is_relative_to(kernel / "VastitasPromotion"):
                allowed.add("VastitasPromotion")
            if not module_allowed(name, allowed):
                errors.append(f"{source.relative_to(root)}: forbidden import {name}")
            if source in runtimes:
                if not module_allowed(name, {"Init", "Std"}):
                    errors.append(f"runtime must not import compiler module {name}")
    kernel_toolchain = (kernel / "lean-toolchain").read_text().strip()
    root_toolchain = root / "lean-toolchain"
    if root_toolchain.exists() and root_toolchain.read_text().strip() != kernel_toolchain:
        errors.append("root and kernel must use the same Lean toolchain")
    oracle = root / "lean"
    if oracle.exists():
        if (oracle / "lean-toolchain").read_text().strip() != kernel_toolchain:
            errors.append("kernel and oracle must use the same Lean toolchain")
        oracle_manifest = json.loads((oracle / "lake-manifest.json").read_text())
        mathlib = next((p for p in oracle_manifest["packages"] if p["name"] == "mathlib"), None)
        if not mathlib or mathlib.get("rev") != MATHLIB_REVISION:
            errors.append("oracle mathlib must be pinned to the v4.35.0 commit")
    return errors


def main():
    try:
        errors = check_boundaries(Path(__file__).resolve().parents[1])
    except (OSError, ValueError, KeyError) as error:
        errors = [f"cannot check dependency boundaries: {error}"]
    if errors:
        print("\n".join(errors), file=sys.stderr)
        return 1
    print("compiler/oracle dependency boundaries verified")
    return 0


if __name__ == "__main__":
    sys.exit(main())
