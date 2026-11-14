"""The tests of a checkout, as scripts/check_spec.py reads them.

`rust_tests` finds the `#[test]` functions of a Rust file that libtest
collects, and `python_tests` the test methods of a unittest module, each with
whether it may not run as written. `python_shadows` tells whether a directory
holds a module whose name the standard library uses.
"""
import ast
import importlib.machinery
from pathlib import Path
import re
import sys


RUST_RAW = re.compile(r'(b?)r(#*)"')
RUST_CHAR = re.compile(r"'(?:\\(?:x[0-9a-fA-F]{2}|u\{[0-9a-fA-F]{1,6}\}|.)|[^\\'\n])'")
RUST_TOKEN = re.compile(r"#!?\[|\bmod\s+([A-Za-z_]\w*)\s*\{|\bfn\s+([A-Za-z_]\w*)|[{};]")
RUST_NAME = re.compile(r"\s*([A-Za-z_][\w:]*)")


def rust_blank(source):
    """The source without comments, with the contents of string and character
    literals removed. Newlines stay."""
    out, i, n = [], 0, len(source)

    def identifier_before(index):
        return index > 0 and (source[index - 1].isalnum() or source[index - 1] == "_")

    while i < n:
        if source.startswith("//", i):
            end = source.find("\n", i)
            i = n if end < 0 else end
            continue
        if source.startswith("/*", i):
            depth, i = 1, i + 2
            while i < n and depth:
                if source.startswith("/*", i):
                    depth, i = depth + 1, i + 2
                elif source.startswith("*/", i):
                    depth, i = depth - 1, i + 2
                else:
                    out.append("\n" if source[i] == "\n" else "")
                    i += 1
            continue
        raw = RUST_RAW.match(source, i)
        if raw and not identifier_before(i):
            end = source.find('"' + raw.group(2), raw.end())
            end = n if end < 0 else end + 1 + len(raw.group(2))
            out.append('""' + "\n" * source.count("\n", i, end))
            i = end
            continue
        if source[i] == '"' or source.startswith('b"', i) and not identifier_before(i):
            j = i + (2 if source[i] == "b" else 1)
            while j < n and source[j] != '"':
                j += 2 if source[j] == "\\" else 1
            out.append('""' + "\n" * source.count("\n", i, j))
            i = j + 1
            continue
        if source[i] == "'":
            match = RUST_CHAR.match(source, i)
            if match:
                out.append("' '")
                i = match.end()
                continue
        out.append(source[i])
        i += 1
    return "".join(out)


RUST_MACRO = re.compile(r"\bmacro_rules\s*!\s*(?:r#)?[^\W\d]\w*\s*[({\[]|\b(?:r#)?[^\W\d]\w*\s*!\s*[({\[]")


def rust_without_macros(text):
    """`text` with the body of every macro definition and invocation blanked,
    newlines kept: a test inside one exists only if the macro expands it."""
    out, index = [], 0
    for match in RUST_MACRO.finditer(text):
        if match.start() < index:
            continue
        depth, end = 0, len(text)
        for position in range(match.end() - 1, len(text)):
            if text[position] in "({[":
                depth += 1
            elif text[position] in ")}]":
                depth -= 1
                if depth == 0:
                    end = position
                    break
        out.append(text[index:match.end()])
        out.append(re.sub(r"[^\n]", " ", text[match.end():end]))
        index = end
    return "".join(out) + text[index:]


def rust_closing(text, start):
    depth = 0
    for index in range(start, len(text)):
        if text[index] == "[":
            depth += 1
        elif text[index] == "]":
            depth -= 1
            if depth == 0:
                return index
    return len(text) - 1


def rust_attribute(attribute):
    match = RUST_NAME.match(attribute)
    return match.group(1) if match else ""


# Attributes that leave a test, its modules and its file as libtest collects
# them. `cfg`, `cfg_attr`, `test`, `ignore` and `should_panic` are read apart.
RUST_ATTRIBUTES = {"allow", "deny", "doc", "expect", "forbid", "inline", "must_use", "rustfmt::skip",
                   "track_caller", "warn"}


def rust_arguments(attribute):
    """The top-level, comma-separated arguments of an attribute such as `cfg_attr(a, b(c, d))`."""
    start = attribute.find("(")
    if start < 0 or not attribute.rstrip().endswith(")"):
        return []
    items, depth, current = [], 0, ""
    for char in attribute[start + 1:attribute.rstrip().rfind(")")]:
        if char in "([{":
            depth += 1
        elif char in ")]}":
            depth -= 1
        if char == "," and depth == 0:
            items.append(current.strip())
            current = ""
        else:
            current += char
    return [item for item in items + [current.strip()] if item]


def rust_effects(attributes, allowed):
    """(ignored, conditional, unread) for the attributes of an item. `ignore`,
    or a `cfg_attr` that adds it, ignores it. A `cfg` other than `cfg(test)`,
    or a `cfg_attr` that adds a `cfg`, makes it conditional. Any other
    attribute outside `allowed`, added by `cfg_attr` or not, leaves it unread:
    an attribute macro, for example, may change or remove a test."""
    ignored = conditional = unread = False
    for attribute in attributes:
        name = rust_attribute(attribute)
        added = rust_arguments(attribute)[1:] if name == "cfg_attr" else [attribute]
        if name == "cfg_attr" and not added:
            unread = True
        for item in added:
            inner = rust_attribute(item)
            if inner == "cfg":
                conditional = conditional or name == "cfg_attr" or re.sub(r"\s", "", item) != "cfg(test)"
            elif inner == "ignore":
                ignored = True
            elif inner not in allowed:
                unread = True
    return ignored, conditional, unread


def rust_tests(source):
    """Map the libtest name of each `#[test]` function, such as `a::b`, to
    (ignored, conditional, unread), as `rust_effects` reads the attributes of
    the function, its enclosing modules and its file. A function may also
    carry `test` and `should_panic`, and a file `feature`; any attribute
    outside RUST_ATTRIBUTES and those leaves the test unread. A `#[test]`
    function inside another item, such as a function body, or inside a macro
    definition or invocation, is no test: libtest does not collect it, or only
    an expansion would define it."""
    text = rust_without_macros(rust_blank(source))
    found, stack, pending, whole_file, index = {}, [], [], (False, False), 0
    while True:
        match = RUST_TOKEN.search(text, index)
        if not match:
            return found
        token, index = match.group(0), match.end()
        if token.startswith("#"):
            end = rust_closing(text, match.end() - 1)
            body, index = text[match.end():end], end + 1
            if token != "#![":
                pending.append(body)
            else:
                _, conditional, unread = rust_effects([body], RUST_ATTRIBUTES | {"feature"})
                if stack:
                    stack[-1] = (stack[-1][0], stack[-1][1], stack[-1][2] or conditional, stack[-1][3] or unread)
                else:
                    whole_file = (whole_file[0] or conditional, whole_file[1] or unread)
            continue
        if match.group(1):
            _, conditional, unread = rust_effects(pending, RUST_ATTRIBUTES)
            stack.append((True, match.group(1), conditional, unread))
        elif match.group(2):
            if all(frame[0] for frame in stack) and any(re.sub(r"\s", "", a) == "test" for a in pending):
                path = "::".join([frame[1] for frame in stack if frame[0]] + [match.group(2)])
                ignored, conditional, unread = rust_effects(pending, RUST_ATTRIBUTES | {"test", "should_panic"})
                found[path] = (ignored, whole_file[0] or any(frame[2] for frame in stack) or conditional,
                               whole_file[1] or any(frame[3] for frame in stack) or unread)
        elif token == "{":
            stack.append((False, None, False, False))
        elif token == "}" and stack:
            stack.pop()
        pending = []


# Names that a test module must leave bound to unittest's own objects.
UNITTEST_NAMES = {"IsolatedAsyncioTestCase", "TestCase", "unittest"}
# Names whose use in a module may keep unittest from running its test methods
# as written, or make a failure pass.
PYTHON_SKIPS = {"SkipTest", "__unittest_expecting_failure__", "__unittest_skip__", "expectedFailure", "load_tests",
                "skip", "skipIf", "skipTest", "skipUnless"}
# Names and attributes through which code can rebind, create or delete what the check reads.
PYTHON_DYNAMIC_NAMES = {"__builtins__", "__import__", "builtins", "compile", "delattr", "eval", "exec", "globals",
                        "importlib", "locals", "setattr", "vars"}
PYTHON_DYNAMIC_ATTRIBUTES = {"__bases__", "__builtins__", "__class__", "__delattr__", "__dict__", "__mro__",
                             "__setattr__", "modules"}
# Methods through which a test class can replace how unittest calls its tests.
PYTHON_HARNESS = {"__call__", "__getattr__", "__getattribute__", "__init__", "__init_subclass__", "__new__", "debug",
                  "run"}


def python_skips(source):
    """Whether a module names a member of PYTHON_SKIPS anywhere, in any use, or
    uses a name of PYTHON_DYNAMIC_NAMES or an attribute of
    PYTHON_DYNAMIC_ATTRIBUTES."""
    return any(isinstance(node, ast.Name) and (node.id in PYTHON_SKIPS or node.id in PYTHON_DYNAMIC_NAMES)
               or isinstance(node, ast.Attribute) and (node.attr in PYTHON_SKIPS
                                                       or node.attr in PYTHON_DYNAMIC_ATTRIBUTES)
               or isinstance(node, ast.alias) and (node.name.split(".")[-1] in PYTHON_SKIPS
                                                   or node.name.split(".")[0] in PYTHON_DYNAMIC_NAMES)
               or isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)) and node.name in PYTHON_SKIPS
               for node in ast.walk(ast.parse(source)))


def python_bindings(module):
    """(name, node) for each name that the module binds or unbinds, in any scope."""
    for node in ast.walk(module):
        if isinstance(node, ast.Name) and isinstance(node.ctx, (ast.Store, ast.Del)):
            yield node.id, node
        elif isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
            yield node.name, node
        elif isinstance(node, ast.alias):
            yield node.asname or node.name.split(".")[0], node
        elif isinstance(node, ast.ExceptHandler) and node.name:
            yield node.name, node
        elif isinstance(node, (ast.Global, ast.Nonlocal)):
            yield from ((name, node) for name in node.names)
        elif isinstance(node, (ast.MatchAs, ast.MatchStar)) and node.name:
            yield node.name, node
        elif isinstance(node, ast.MatchMapping) and node.rest:
            yield node.rest, node


def python_tests(source):
    """(class, method) of the test methods of the unittest test cases of a
    module, mapped to whether unittest may skip them, not run them as written,
    or expect them to fail.

    A test case is a module-level class whose bases are `unittest.TestCase`,
    `unittest.IsolatedAsyncioTestCase`, those names imported from unittest, or
    other test cases of the module. Every test of the module counts as not run
    when `python_skips` holds; when anything other than these classes and the
    plain imports `import unittest` and `from unittest import ...` binds or
    unbinds a class name or a name of UNITTEST_NAMES, in any form and scope,
    or a star import from any module but unittest may; when a class name is
    used as a value rather than as a base; when code assigns or deletes an
    attribute or item of a class or of a name of UNITTEST_NAMES, or deletes
    any attribute; and when a test case or one of its methods has a decorator,
    a test case has keywords such as `metaclass`, or one defines a method of
    PYTHON_HARNESS. A test name that a class body assigns or deletes rather
    than defines, and an `async def` test of a class that is no
    IsolatedAsyncioTestCase, which unittest never awaits, count as not run
    too."""
    module = ast.parse(source)
    classes = {node.name: node for node in module.body if isinstance(node, ast.ClassDef)}
    kinds = {"TestCase", "IsolatedAsyncioTestCase", "unittest.TestCase", "unittest.IsolatedAsyncioTestCase"}

    def base_names(node):
        return [f"unittest.{base.attr}" if isinstance(base, ast.Attribute) and isinstance(base.value, ast.Name)
                and base.value.id == "unittest" else base.id if isinstance(base, ast.Name) else "?"
                for base in node.bases]

    def test_case(name, wanted=kinds, seen=()):
        node = classes.get(name)
        return node is not None and name not in seen and bool(node.bases) and all(
            base in kinds or base in classes and test_case(base, kinds, seen + (name,))
            for base in base_names(node)) and any(
            base in wanted or base in classes and test_case(base, wanted, seen + (name,)) for base in base_names(node))

    def methods(name, seen=()):
        """Each test name of the class, mapped to "sync", "async" or "unknown"
        when the class body assigns or deletes it."""
        node = classes.get(name)
        if node is None or name in seen:
            return {}
        found = {}
        for base in reversed(base_names(node)):
            found.update(methods(base, seen + (name,)))
        for item in node.body:
            if isinstance(item, (ast.FunctionDef, ast.AsyncFunctionDef)) and item.name.startswith("test"):
                found[item.name] = "async" if isinstance(item, ast.AsyncFunctionDef) else "sync"
            elif isinstance(item, (ast.Assign, ast.AnnAssign, ast.AugAssign, ast.Delete)):
                targets = item.targets if isinstance(item, (ast.Assign, ast.Delete)) else [item.target]
                for target in targets:
                    for leaf in ast.walk(target):
                        if isinstance(leaf, ast.Name) and leaf.id.startswith("test"):
                            found[leaf.id] = "unknown"
        return found

    definitions = {id(node) for node in classes.values() if node.name not in UNITTEST_NAMES}
    imports = {id(alias) for node in ast.walk(module) if isinstance(node, ast.Import)
               for alias in node.names if alias.name == "unittest" and alias.asname is None}
    imports |= {id(alias) for node in ast.walk(module)
                if isinstance(node, ast.ImportFrom) and node.module == "unittest" and not node.level
                for alias in node.names if alias.asname is None}
    rebinds = any((name in classes or name in UNITTEST_NAMES or name == "*") and id(node) not in definitions | imports
                  for name, node in python_bindings(module))

    def root(node):
        while isinstance(node, (ast.Attribute, ast.Subscript)):
            node = node.value
        return node.id if isinstance(node, ast.Name) else None

    changes = any(isinstance(target, (ast.Attribute, ast.Subscript)) and (
        root(target) in classes or root(target) in UNITTEST_NAMES or isinstance(node, ast.Delete))
        for node in ast.walk(module) if isinstance(node, (ast.Assign, ast.AnnAssign, ast.AugAssign, ast.Delete))
        for target in (node.targets if isinstance(node, (ast.Assign, ast.Delete)) else [node.target]))
    bases = {id(base) for node in classes.values() for base in node.bases}
    aliases = any(isinstance(node, ast.Name) and isinstance(node.ctx, ast.Load) and node.id in classes
                  and id(node) not in bases for node in ast.walk(module))
    cases = [node for name, node in classes.items() if test_case(name)]
    harness = any(node.decorator_list or node.keywords or any(
        isinstance(item, (ast.FunctionDef, ast.AsyncFunctionDef))
        and (item.decorator_list or item.name in PYTHON_HARNESS) for item in node.body) for node in cases)
    skips = python_skips(source) or rebinds or changes or aliases or harness
    return {(name, method): skips or kind == "unknown"
            or kind == "async" and not test_case(name, {"IsolatedAsyncioTestCase", "unittest.IsolatedAsyncioTestCase"})
            for name in classes if test_case(name) for method, kind in methods(name).items()}


PYTHON_STARTUP = {"sitecustomize", "usercustomize"}


def python_shadows(directory):
    """Whether `directory` holds a module or package whose name a module of the
    standard library, or Python's start-up, uses: a file with a suffix of
    `importlib.machinery.all_suffixes()`, or `NAME/__init__.py`."""
    names = sys.stdlib_module_names | PYTHON_STARTUP
    suffixes = tuple(importlib.machinery.all_suffixes())
    try:
        entries = list(Path(directory).iterdir())
    except OSError:
        return False
    return any(entry.name.split(".")[0] in names and (
        entry.is_file() and entry.name.endswith(suffixes)
        or entry.is_dir() and (entry / "__init__.py").exists()) for entry in entries)
