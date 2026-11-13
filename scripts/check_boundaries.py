#!/usr/bin/env python3
"""Check compiler/oracle dependencies without loading the Lean toolchain."""
import json
from pathlib import Path
import re
import sys
import tomllib
from typing import NamedTuple


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


def _skip_char(source, position):
    """Skip a Lean character literal such as `'a'`, `'\\''` or `'\\u{22}'`.

    A quote that does not start a well-formed literal is rejected: otherwise
    `'"'` would open a fake string that conceals the following tokens.
    """
    start = position
    position += 1
    if source.startswith("\\u{", position):
        end = source.find("}", position)
        position = len(source) if end < 0 else end + 1
    elif source.startswith("\\x", position):
        position += 4
    elif source.startswith("\\", position):
        position += 2
    else:
        position += 1
    if not source.startswith("'", position) or "\n" in source[start:position]:
        raise ValueError("unsupported Lean character literal")
    return position + 1


def _skip_string(source, position, line):
    """Skip a string literal, including `s!`-style interpolations and nested strings.

    A string after `!` (`s!`, `m!`, `f!`) is scanned as interpolated. Any other
    string with an unescaped `{` is rejected: it could be an ordinary literal
    (`"{"`) or a prefixless interpolation (`throwError "{…}"`), and guessing
    either way lets a later or nested quote conceal tokens. Raw strings
    (`r"..."`, `r#"..."#`) are rejected rather than interpreted.
    """
    prefix = position
    while prefix > 0 and source[prefix - 1] == "#":
        prefix -= 1
    if prefix > 0 and source[prefix - 1] == "r" and (
            prefix == 1 or not (source[prefix - 2].isalnum() or source[prefix - 2] in "_'.")):
        raise ValueError("unsupported Lean raw string")
    interpolated = position > 0 and source[position - 1] == "!"
    position += 1
    while True:
        if position >= len(source):
            raise ValueError("unterminated Lean string")
        character = source[position]
        if character == '"':
            return position + 1, line
        if character == "\\":
            line += source[position + 1:position + 2] == "\n"
            position += 2
            continue
        if character == "{":
            if not interpolated:
                raise ValueError("unescaped brace in a Lean string; escape it or use s!")
            position, line = _skip_interpolation(source, position + 1, line)
            continue
        line += character == "\n"
        position += 1


def _skip_interpolation(source, position, line):
    """Skip a `{term}` inside an interpolated string, through its closing brace."""
    depth = 1
    while True:
        if position >= len(source):
            raise ValueError("unterminated Lean string interpolation")
        character = source[position]
        if character == '"':
            position, line = _skip_string(source, position, line)
        elif character == "'" and not (position > 0 and (source[position - 1].isalnum()
                                                          or source[position - 1] in "_'")):
            position = _skip_char(source, position)
        elif character == "{":
            depth += 1
            position += 1
        elif character == "}":
            depth -= 1
            position += 1
            if depth == 0:
                return position, line
        else:
            line += character == "\n"
            position += 1


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
        if source[position] == '"':
            start, start_line = position, line
            position, line = _skip_string(source, position, line)
            yield _Token(source[start:position], start_line, False)
            continue
        if source[position] == "'":
            start = position
            position = _skip_char(source, position)
            yield _Token(source[start:position], line, False)
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


def check_lake_dependencies(package, label, errors, *, oracle=False):
    """Enforce the current closed Lake graph, including inherited packages.

    Oracle may require only the checked local kernel, which has no package
    dependencies. Checking both the declarative config
    and the complete lockfile rejects stale locks, renamed/forked packages and
    transitive Mathlib without resolving or trusting external package code.
    Future local packages require an explicit boundary-policy amendment.
    """
    if (package / "lakefile.lean").exists():
        errors.append(f"{label}: executable lakefile.lean is not allowed; use lakefile.toml")
    try:
        config = tomllib.loads((package / "lakefile.toml").read_text())
        manifest = json.loads((package / "lake-manifest.json").read_text())
        required = [{"name": "vastitas_kernel", "path": "../lean-kernel"}] if oracle else []
        locked = [{
            "type": "path", "scope": "", "name": "vastitas_kernel",
            "manifestFile": "lake-manifest.json", "inherited": False,
            "dir": "../lean-kernel", "copy": False, "configFile": "lakefile.toml",
        }] if oracle else []
        policy = ("only the local ../lean-kernel Lake dependency" if oracle
                  else "no external Lake package dependencies")
        if config.get("require", []) != required:
            errors.append(f"{label} must have {policy} (lakefile.toml)")
        options = config.get("leanOptions", {})
        if not isinstance(options, dict) or options.get("warningAsError") is not True:
            errors.append(f"{label} must set leanOptions.warningAsError = true, so that warnings "
                          "such as a declaration using sorry fail the build")
        if not isinstance(manifest, dict) or manifest.get("packages") != locked:
            errors.append(f"{label} must have {policy} (complete manifest, including transitive dependencies)")
    except (OSError, ValueError) as error:
        errors.append(f"{label}: cannot check Lake dependencies: {error}")


_BRIDGE_PATH_DEPENDENCIES = [
    {"type": "path", "scope": "", "name": name, "manifestFile": "lake-manifest.json",
     "inherited": False, "dir": directory, "copy": False, "configFile": "lakefile.toml"}
    for name, directory in [("vastitas_kernel", "../lean-kernel"), ("vastitas_oracle", "../lean")]
]


def check_mathematical_bridge(root, kernel_toolchain, errors):
    """The optional theorem package has its own pinned Mathlib graph.

    The bridge may also read the actual kernel and Oracle sources through the
    two local path dependencies ../lean-kernel and ../lean. The dependency is
    one way: the compiler and Oracle checks above still forbid Mathlib and
    VastitasBridge imports, and their own Lake graphs are unchanged.
    """
    bridge = root / "lean-bridge"
    if not bridge.exists():
        return
    if (bridge / "lakefile.lean").exists():
        errors.append("lean-bridge: executable lakefile.lean is not allowed; use lakefile.toml")
    try:
        if (bridge / "lean-toolchain").read_text().strip() != kernel_toolchain:
            errors.append("bridge and kernel must use the same Lean toolchain")
        config = tomllib.loads((bridge / "lakefile.toml").read_text())
        manifest = json.loads((bridge / "lake-manifest.json").read_text())
        url = "https://github.com/leanprover-community/mathlib4.git"
        revision = "56a005855ea17e0b0958f73ec801ae140b0a1679"
        if config.get("require", []) != [
            {"name": "mathlib", "git": url, "rev": revision},
            {"name": "vastitas_kernel", "path": "../lean-kernel"},
            {"name": "vastitas_oracle", "path": "../lean"},
        ]:
            errors.append("lean-bridge must require only the pinned Mathlib reference "
                          "and the local ../lean-kernel and ../lean packages")
        packages = manifest.get("packages") if isinstance(manifest, dict) else None
        if not isinstance(packages, list) or not packages or any(
            not isinstance(p, dict) for p in packages
        ):
            errors.append("lean-bridge must lock every dependency to a Git commit; only Mathlib is direct")
            return
        local = [p for p in packages if p.get("type") == "path"]
        remote = [p for p in packages if p.get("type") != "path"]
        if sorted(local, key=lambda p: str(p.get("name"))) != _BRIDGE_PATH_DEPENDENCIES:
            errors.append("lean-bridge path dependencies must be exactly ../lean-kernel and ../lean")
        if not remote or any(
            p.get("type") != "git"
            or not isinstance(p.get("name"), str)
            or not isinstance(p.get("rev"), str)
            or not re.fullmatch(r"[0-9a-f]{40}", p["rev"])
            or p.get("inherited") is not (p.get("name") != "mathlib")
            for p in remote
        ):
            errors.append("lean-bridge must lock every dependency to a Git commit; only Mathlib is direct")
        else:
            mathlib = [p for p in remote if p["name"] == "mathlib"]
            if len(mathlib) != 1 or any(
                p.get("url") != url or p["rev"] != revision or p.get("subDir") is not None
                for p in mathlib
            ):
                errors.append("lean-bridge manifest must contain the pinned Mathlib reference")
        names = [p.get("name") for p in packages]
        if len(set(map(str, names))) != len(names):
            errors.append("lean-bridge manifest must not contain duplicate package names")
        # Proof only (ADR 0001, section 9, condition 4): one library whose root
        # is the module that Audit.lean imports, and no executable.
        if "lean_exe" in config:
            errors.append("lean-bridge must not declare an executable target (lean_exe)")
        # The closure check below reads lean-bridge/VastitasBridge.lean, so every
        # key that could move the sources or add a target or a build step is
        # refused, not only the ones known to do so.
        unexpected = sorted(set(config) - {
            "name", "version", "license", "licenseFiles", "defaultTargets",
            "require", "lean_lib", "leanOptions", "lean_exe"})
        if unexpected:
            errors.append(f"lean-bridge: unexpected Lake configuration keys {unexpected}")
        if config.get("lean_lib") != [{"name": "VastitasBridge"}]:
            errors.append("lean-bridge must declare exactly the library VastitasBridge, "
                          "with its default root")
    except (OSError, ValueError) as error:
        errors.append(f"lean-bridge: cannot check pinned dependencies: {error}")
    for source in bridge.rglob("*.lean"):
        if ".lake" in source.parts:
            continue
        try:
            imports = lean_imports(source.read_text())
        except ValueError as error:
            errors.append(f"{source.relative_to(root)}: {error}")
            continue
        for name in imports:
            if not module_allowed(name, {
                "Init", "Std", "Lean", "Mathlib", "VastitasBridge",
                "VastitasKernel", "VastitasOracle",  # one-way implementation correspondence
            }):
                errors.append(f"{source.relative_to(root)}: forbidden import {name}")
    check_bridge_closure(root, bridge, errors)


def bridge_module_path(bridge, name):
    """The source file of a VastitasBridge module, or None for another package."""
    parts = [part[1:-1] if part.startswith("«") else part for part in _SEGMENTS.findall(name)]
    if not parts or parts[0] != "VastitasBridge":
        return None
    path = bridge.joinpath(*parts)
    return path.with_name(path.name + ".lean")  # a segment «A.B» names the file A.B.lean


def check_bridge_closure(root, bridge, errors):
    """Every bridge source is in the import closure of the root module.

    `Audit.lean` audits the declarations that `import VastitasBridge` reaches. A
    source under `VastitasBridge/` that the root does not reach is neither built
    nor audited, so a `sorry` in it would pass unseen.
    """
    start = bridge / "VastitasBridge.lean"
    if not start.exists():
        errors.append("lean-bridge: missing root module VastitasBridge.lean")
        return
    reached, pending = set(), [start]
    while pending:
        source = pending.pop()
        if source in reached:
            continue
        reached.add(source)
        try:
            imports = lean_imports(source.read_text())
        except (OSError, ValueError):
            continue  # reported by the import check above
        for name in imports:
            path = bridge_module_path(bridge, name)
            if path is not None and path.exists():
                pending.append(path)
    for source in sorted((bridge / "VastitasBridge").rglob("*.lean")):
        if ".lake" not in source.parts and source not in reached:
            errors.append(f"{source.relative_to(root)}: not imported by VastitasBridge.lean, "
                          "so neither built nor audited")


def check_executable_lake_dependencies(package, label, required, errors):
    """Audit the closed literal require declarations, not arbitrary Lean execution.

    These two trusted executable configs use one-line literal requirements.
    Reject unsupported forms instead of guessing at computed dependency paths.
    Comments, strings, interpolations and character literals cannot manufacture
    or conceal a require token.
    """
    try:
        lines = {}
        for token in _header_tokens((package / "lakefile.lean").read_text()):
            lines.setdefault(token.line, []).append(token)
        declarations = [[t.text for t in tokens] for tokens in lines.values()
                        if any(t.is_name and t.text == "require" for t in tokens)]
        if declarations != required:
            errors.append(f"{label}: unsupported dependency in lakefile.lean; expected {required}")
    except (OSError, ValueError) as error:
        errors.append(f"{label}: cannot check lakefile.lean dependencies: {error}")


def check_boundaries(root):
    root = Path(root)
    kernel = root / "lean-kernel"
    errors = []
    check_lake_dependencies(kernel, "lean-kernel", errors)
    runtime = kernel / "VastitasKernel" / "Runtime.lean"
    runtimes = {runtime, kernel / "VastitasKernel" / "IndexedRuntime.lean",
                kernel / "VastitasKernel" / "AlgebraRuntime.lean",
                kernel / "VastitasKernel" / "SmoothRuntime.lean"}
    # Runtime modules may import each other, but nothing else from the compiler.
    runtime_modules = {"VastitasKernel." + source.stem for source in runtimes
                       if source.parent == kernel / "VastitasKernel"}
    native = kernel / "native"
    numerical = kernel / "numerical"
    if native.exists():
        check_executable_lake_dependencies(native, "native storage runtime", [], errors)
        native_manifest = json.loads((native / "lake-manifest.json").read_text())
        if native_manifest.get("packages"):
            errors.append("native storage runtime must have no external Lake package dependencies")
        if (native / "lean-toolchain").read_text().strip() != (kernel / "lean-toolchain").read_text().strip():
            errors.append("native storage runtime and kernel must use the same Lean toolchain")
        native_runtime = native / "VastitasStorageNative" / "Runtime.lean"
        runtimes.add(native_runtime)
        if not native_runtime.is_file():
            errors.append("native storage runtime source is missing")
    if (numerical / "VastitasGemmNative.lean").exists():
        check_executable_lake_dependencies(numerical, "numerical runtime", [
            ["require", "vastitas_storage_native", "from", '"../native"']], errors)
        numerical_manifest = json.loads((numerical / "lake-manifest.json").read_text())
        dependencies = numerical_manifest.get("packages", [])
        if len(dependencies) != 1 or any(
            p.get("type") != "path" or p.get("name") != "vastitas_storage_native"
            or p.get("dir") != "../native" for p in dependencies
        ):
            errors.append("numerical runtime must depend only on the sibling native storage runtime")
        if (numerical / "lean-toolchain").read_text().strip() != (kernel / "lean-toolchain").read_text().strip():
            errors.append("numerical runtime and kernel must use the same Lean toolchain")
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
            if source.is_relative_to(numerical):
                allowed = {"Init", "Std", "VastitasStorageNative", "VastitasGemmNative"}
                if source == numerical / "lakefile.lean":
                    allowed = {"Lake"}
            if source.is_relative_to(kernel / "VastitasPromotion"):
                allowed.add("VastitasPromotion")
            if source.is_relative_to(kernel / "VastitasStorageTest"):
                allowed.add("VastitasStorageTest")
            if not module_allowed(name, allowed):
                errors.append(f"{source.relative_to(root)}: forbidden import {name}")
            if source in runtimes:
                if not module_allowed(name, {"Init", "Std"}) and name not in runtime_modules:
                    errors.append(f"runtime must not import compiler module {name}")
    kernel_toolchain = (kernel / "lean-toolchain").read_text().strip()
    root_toolchain = root / "lean-toolchain"
    if root_toolchain.exists() and root_toolchain.read_text().strip() != kernel_toolchain:
        errors.append("root and kernel must use the same Lean toolchain")
    oracle = root / "lean"
    if oracle.exists():
        if (oracle / "lean-toolchain").read_text().strip() != kernel_toolchain:
            errors.append("kernel and oracle must use the same Lean toolchain")
        check_lake_dependencies(oracle, "oracle", errors, oracle=True)
        for source in oracle.rglob("*.lean"):
            if ".lake" in source.parts:
                continue
            try:
                imports = lean_imports(source.read_text())
            except ValueError as error:
                errors.append(f"{source.relative_to(root)}: {error}")
                continue
            for name in imports:
                if not module_allowed(name, {
                    "Init", "Std", "Lean", "VastitasKernel", "VastitasOracle",
                    "VastitasPromotion",  # existing actual-source promotion fixture
                }):
                    errors.append(f"{source.relative_to(root)}: forbidden import {name}")
    check_mathematical_bridge(root, kernel_toolchain, errors)
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
