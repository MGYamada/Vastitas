"""The CI steps that run tests, as scripts/check_spec.py reads them.

A Tested claim needs a CI step that runs each of its tests. The workflows are
read with a subset of YAML that covers GitHub workflows, and each `run:` step
only as far as its lines are plain. Both are conservative: a form they do not
read counts as not running a test, and so does a step that a condition, a
continue-on-error flag or a filtered pull_request trigger may skip.

`yaml_load` reads the subset, `run_steps` the steps of a workflow that every
pull request runs, `plain_commands` the plain commands of a shell script, and
`cargo_run` and `discover_run` the tests that `cargo test` and
`python3 -m unittest discover` run.
"""
from dataclasses import dataclass
import fnmatch
import os
from pathlib import PurePosixPath
import re


YAML_KEY = re.compile(r"([A-Za-z0-9_][A-Za-z0-9_.-]*)[ ]*:(?:[ ]+|$)")


YAML_QUOTED = re.compile(r"""(?:"(?:[^"\\]|\\.)*"|'(?:[^']|'')*')[ ]*(?:#.*)?""")


class YamlError(ValueError):
    """A workflow form that the YAML subset does not read."""


class Folded(str):
    """A scalar that YAML folds from several lines."""


class YamlLines:
    def __init__(self, text):
        self.lines = text.split("\n")
        self.index = 0

    def current(self):
        while self.index < len(self.lines):
            line = self.lines[self.index]
            if line.strip() and not line.strip().startswith("#"):
                if "\t" in line[:len(line) - len(line.lstrip())]:
                    raise YamlError("a tab in indentation")
                return line
            self.index += 1
        return None


def yaml_indent(line):
    return len(line) - len(line.lstrip(" "))


def yaml_plain(text):
    match = re.search(r"\s#", text)
    return (text[:match.start()] if match else text).rstrip()


YAML_SINGLE = re.compile(r"'((?:[^']|'')*)'")
YAML_DOUBLE = re.compile(r'"((?:[^"\\]|\\["\\/])*)"')


def yaml_scalar(text):
    """A plain or quoted scalar. A quoted scalar ends at its closing quote, and
    only a comment may follow it; a double-quoted scalar may escape only `"`,
    `\\` and `/`. An anchor, an alias, a tag and anything else raise
    YamlError."""
    text = text.strip()
    if text[:1] in ("&", "*", "!"):
        raise YamlError(f"an anchor, alias or tag in {text!r}")
    if text[:1] in ("'", '"'):
        match = (YAML_SINGLE if text[0] == "'" else YAML_DOUBLE).match(text)
        if not match or not re.fullmatch(r"[ \t]*(?:#.*)?", text[match.end():]):
            raise YamlError(f"an unread quoted scalar {text!r}")
        if text[0] == "'":
            return match.group(1).replace("''", "'")
        return re.sub(r'\\(["\\/])', r"\1", match.group(1))
    return yaml_plain(text)


def yaml_key(content):
    """The plain key of a mapping entry and the text after it. A quoted,
    explicit, tagged, anchored or merge key raises YamlError."""
    match = YAML_KEY.match(content)
    if not match:
        raise YamlError(f"an unread mapping key in {content!r}")
    return match.group(1), content[match.end():]


def yaml_node(lines, indent):
    line = lines.current()
    if line is None or yaml_indent(line) < indent:
        return None
    if line.lstrip().startswith("- ") or line.strip() == "-":
        return yaml_sequence(lines, yaml_indent(line))
    return yaml_mapping(lines, yaml_indent(line))


def yaml_mapping(lines, indent):
    result = {}
    while True:
        line = lines.current()
        if line is None or yaml_indent(line) != indent or line.lstrip().startswith("- "):
            return result
        key, rest = yaml_key(line.strip())
        if key in result:
            raise YamlError(f"a repeated key {key!r}")
        lines.index += 1
        result[key] = yaml_value(lines, indent, rest)


def yaml_value(lines, indent, rest):
    rest = rest.strip()
    if rest[:1] in ("&", "*", "!"):
        raise YamlError(f"an anchor, alias or tag in {rest!r}")
    if not rest or rest.startswith("#"):
        line = lines.current()
        if line is not None and (yaml_indent(line) > indent
                                 or yaml_indent(line) == indent and line.lstrip().startswith("- ")):
            return yaml_node(lines, yaml_indent(line))
        return None
    if rest[0] in "|>":
        header = yaml_plain(rest)
        return yaml_block(lines, indent, rest[0], "-" if "-" in header else "")
    if rest[0] in "'\"":
        return yaml_scalar(rest)
    if rest[0] == "[":
        text = yaml_plain(rest)
        inner = text[1:-1] if text.endswith("]") else "["
        if any(c in inner for c in "[]{}"):
            return text
        return [yaml_scalar(item) for item in inner.split(",") if item.strip()]
    if rest[0] == "{":
        return yaml_plain(rest)
    parts = [yaml_plain(rest)]
    while lines.index < len(lines.lines):
        line = lines.lines[lines.index]
        if not line.strip() or yaml_indent(line) <= indent or line.lstrip().startswith("#"):
            break
        parts.append(yaml_plain(line.strip()))
        lines.index += 1
    return Folded(" ".join(parts)) if len(parts) > 1 else parts[0]


def yaml_block(lines, indent, style, chomping):
    body = []
    while lines.index < len(lines.lines):
        line = lines.lines[lines.index]
        if line.strip() and yaml_indent(line) <= indent:
            break
        body.append(line)
        lines.index += 1
    while body and not body[-1].strip():
        body.pop()
    margin = min((yaml_indent(line) for line in body if line.strip()), default=0)
    body = [line[margin:] for line in body]
    end = "" if chomping == "-" else "\n"
    if style == "|":
        return "\n".join(body) + end
    return Folded(yaml_fold(body) + end)


def yaml_fold(body):
    folded, previous = "", None
    for line in body:
        if not line:
            folded += "\n"
        elif line[0] == " " or previous is None or previous == "" or previous[0] == " ":
            folded += ("\n" if folded and not folded.endswith("\n") else "") + line
        else:
            folded += " " + line
        previous = line
    return folded


def yaml_sequence(lines, indent):
    items = []
    while True:
        line = lines.current()
        if line is None or yaml_indent(line) != indent or not (line.lstrip().startswith("- ")
                                                               or line.strip() == "-"):
            return items
        content = line.lstrip()[1:].lstrip()
        column = len(line) - len(content)
        lines.index += 1
        if not content:
            items.append(yaml_node(lines, indent + 1))
            continue
        if not YAML_KEY.match(content):
            if not YAML_QUOTED.fullmatch(content) and re.search(r":(?:[ ]|$)", content):
                raise YamlError(f"an unread mapping key in {content!r}")
            items.append(yaml_scalar(content))
            continue
        key, rest = yaml_key(content)
        item = {key: yaml_value(lines, column, rest)}
        others = yaml_mapping(lines, column)
        if key in others:
            raise YamlError(f"a repeated key {key!r}")
        item.update(others)
        items.append(item)


def yaml_load(text):
    """Block mappings and sequences, plain, quoted and block scalars, and flow
    sequences of scalars; other flow collections stay text. A scalar folded
    from several lines is Folded. YamlError reports a form outside the subset,
    including a repeated key, which GitHub rejects, a line that the subset
    does not reach, such as a quoted scalar over several lines, and whitespace
    other than spaces, tabs and newlines, such as NEL, which YAML 1.1 reads as
    a line break."""
    odd = next((c for c in text if c.isspace() and c not in " \t\n"), None)
    if odd is not None:
        raise YamlError(f"the whitespace {odd!r}, which YAML and Python read differently")
    lines = YamlLines(text)
    tree = yaml_node(lines, 0)
    if lines.current() is not None:
        raise YamlError(f"an unread line {lines.current()!r}")
    return tree


FILTERS = ("paths", "paths-ignore", "branches", "branches-ignore", "types")


def every_pull_request(triggers):
    """Whether the `on:` value starts the workflow for every pull request."""
    if isinstance(triggers, str):
        return triggers == "pull_request"
    if isinstance(triggers, list):
        return "pull_request" in triggers
    if isinstance(triggers, dict) and "pull_request" in triggers:
        config = triggers["pull_request"]
        return config is None or isinstance(config, dict) and not any(key in config for key in FILTERS)
    return False


def may_skip(value):
    """Whether a `continue-on-error` value can be true."""
    return value is not None and str(value).strip().lower() != "false"


def unix_job(job):
    """Whether every runner that `job` may use is a GitHub-hosted Linux or macOS
    runner, `ubuntu-…` or `macos-…`, where a `run:` step uses bash by default.
    A `${{ matrix.KEY }}` runner takes the literal values of KEY in the job's
    matrix, with those that `include` adds; a matrix with `exclude` is not
    read. A job in a `container` runs on the container's image instead."""
    if "container" in job:
        return False
    labels = job.get("runs-on")
    if isinstance(labels, str):
        match = re.fullmatch(r"\$\{\{\s*matrix\.([A-Za-z0-9_-]+)\s*\}\}", labels.strip())
        if match:
            strategy = job.get("strategy")
            matrix = strategy.get("matrix") if isinstance(strategy, dict) else None
            include = matrix.get("include") or [] if isinstance(matrix, dict) and "exclude" not in matrix else None
            if not isinstance(include, list) or not all(isinstance(entry, dict) for entry in include):
                return False
            values = matrix.get(match.group(1), [])
            labels = (values if isinstance(values, list) else [values]) + [
                entry[match.group(1)] for entry in include if match.group(1) in entry]
        else:
            labels = [labels]
    return isinstance(labels, list) and bool(labels) and all(
        isinstance(label, str) and label.startswith(("ubuntu-", "macos-")) for label in labels)


# Variables that change how bash starts, reads or finds commands, how programs
# load, or how cargo and Python build and run tests: a test runner, a compiler
# wrapper, a cross target or a Python path.
SHELL_ENVIRONMENT = {"ACTIONS_ALLOW_UNSECURE_COMMANDS", "BASH_ENV", "BASHOPTS", "CDPATH", "ENV", "GLOBIGNORE",
                     "HOME", "IFS", "PATH", "POSIXLY_CORRECT", "PS4", "SHELLOPTS"}
ENVIRONMENT_PREFIXES = ("BASH_FUNC_", "LD_", "DYLD_", "RUST", "PYTHON")


# The workflow keys that run_steps reads.
GITHUB_KEYS = {"branches", "branches-ignore", "container", "continue-on-error", "defaults", "env", "exclude", "if",
               "include", "jobs", "matrix", "needs", "on", "paths", "paths-ignore", "pull_request", "run", "runs-on",
               "shell", "steps", "strategy", "types", "working-directory"}


def exact_keys(*tables):
    """Whether no key of the mappings differs from one of GITHUB_KEYS only in case."""
    return not any(isinstance(table, dict) and any(
        isinstance(key, str) and key.lower() in GITHUB_KEYS and key not in GITHUB_KEYS for key in table)
        for table in tables)


def plain_environment(*tables):
    """Whether no `env:` table sets a variable of SHELL_ENVIRONMENT, one that
    starts with one of ENVIRONMENT_PREFIXES, or a CARGO_ variable other than
    the CARGO_TERM_ settings of terminal output."""
    return all(table is None or isinstance(table, dict) and not any(
        name in SHELL_ENVIRONMENT or name.startswith(ENVIRONMENT_PREFIXES)
        or name.startswith("CARGO_") and not name.startswith("CARGO_TERM_") for name in table)
        for table in tables)


def run_steps(workflow):
    """(script, directory) of each `run:` step that every pull request runs and
    whose failure fails the job. Neither the step nor its job, nor any job that
    it needs, has `if:` or a `continue-on-error` that can be true; `unix_job`
    holds; the step uses bash; its script is a single line or a literal block;
    `plain_environment` holds for the workflow, job and step; and no earlier
    step of the job names GITHUB_ENV or GITHUB_PATH, a textual rule. A workflow
    outside the YAML subset, or with `defaults` that are not block mappings,
    yields nothing, and so does a job with such `defaults`. A key that differs
    from one of GITHUB_KEYS only in case keeps its workflow, job or step from
    counting. A working directory with `..` is unknown."""
    try:
        tree = yaml_load(workflow)
    except YamlError:
        return
    if not isinstance(tree, dict) or not every_pull_request(tree.get("on")):
        return
    def defaults(table):
        """The `defaults.run` settings of a workflow or job, or None when they are not block mappings."""
        settings = table.get("defaults", {})
        run = settings.get("run", {}) if isinstance(settings, dict) else None
        return run if isinstance(run, dict) else None
    jobs = tree.get("jobs") if isinstance(tree.get("jobs"), dict) else {}
    def unconditional(name, seen=()):
        job = jobs.get(name) if isinstance(name, str) else None
        if not isinstance(job, dict) or name in seen or "if" in job or may_skip(job.get("continue-on-error")) \
                or not exact_keys(job):
            return False
        needs = job.get("needs", [])
        needs = [needs] if isinstance(needs, str) else needs
        return isinstance(needs, list) and all(unconditional(need, seen + (name,)) for need in needs)
    top = defaults(tree)
    triggers = tree.get("on")
    if top is None or not exact_keys(tree, tree.get("defaults"), top, triggers,
                                     triggers.get("pull_request") if isinstance(triggers, dict) else None):
        return
    for name, job in jobs.items():
        if not unconditional(name) or not unix_job(job) or defaults(job) is None:
            continue
        strategy = job.get("strategy")
        if not exact_keys(job, job.get("defaults"), defaults(job), strategy,
                          strategy.get("matrix") if isinstance(strategy, dict) else None):
            continue
        settings, tainted = dict(top, **defaults(job)), False
        for step in job.get("steps") or []:
            if isinstance(step, dict) and not exact_keys(step, step.get("env")):
                tainted = True
            script = step.get("run") if isinstance(step, dict) else None
            if not isinstance(script, str):
                continue
            countable = (not tainted and not isinstance(script, Folded) and "if" not in step and exact_keys(step)
                         and not may_skip(step.get("continue-on-error"))
                         and step.get("shell", settings.get("shell")) in (None, "bash")
                         and plain_environment(tree.get("env"), job.get("env"), step.get("env")))
            tainted = tainted or "GITHUB_ENV" in script or "GITHUB_PATH" in script
            if countable:
                directory = str(step.get("working-directory", settings.get("working-directory", ".")))
                yield script, None if ".." in PurePosixPath(directory).parts \
                    else shell_directory(PurePosixPath("."), directory)


PLAIN_WORD = r"(?:[A-Za-z0-9_./:=@%+,-]|'[^'\r\n]*')+"
PLAIN_LINE = re.compile(rf" *(?:{PLAIN_WORD}(?: +{PLAIN_WORD})*)?(?: *| +\\)")
PLAIN_COMMENT = re.compile(r" *(?:#.*)?")
# Bash reserved words and builtins. A plain command names none of them, except
# those in PLAIN_BUILTINS and `cd` and `set`, which the reader follows.
SHELL_WORDS = {
    "!", "[[", "]]", "{", "}", "case", "coproc", "do", "done", "elif", "else", "esac", "fi", "for", "function",
    "if", "in", "select", "then", "time", "until", "while", ".", ":", "[", "alias", "bg", "bind", "break",
    "builtin", "caller", "cd", "command", "compgen", "complete", "compopt", "continue", "declare", "dirs",
    "disown", "echo", "enable", "eval", "exec", "exit", "export", "false", "fc", "fg", "getopts", "hash", "help",
    "history", "jobs", "kill", "let", "local", "logout", "mapfile", "popd", "printf", "pushd", "pwd", "read",
    "readarray", "readonly", "return", "set", "shift", "shopt", "source", "suspend", "test", "times", "trap",
    "true", "type", "typeset", "ulimit", "umask", "unalias", "unset", "wait"}
PLAIN_BUILTINS = {":", "echo", "false", "pwd", "test", "true"}
SET_LETTERS = {"e": "errexit", "u": "nounset", "v": "verbose", "x": "xtrace"}
SET_OPTIONS = {"errexit", "nounset", "pipefail", "verbose", "xtrace"}
# In a script file, this line goes to the parent of the script's directory.
SCRIPT_PARENT = 'cd "$(dirname "$0")/.."'


def shell_directory(directory, target):
    """`directory / target`, or None when the result is unknown."""
    if directory is None or not target or target.startswith(("/", "~")) or any(c in target for c in "$`*?"):
        return None
    return PurePosixPath(os.path.normpath(str(directory / target)))


def plain_set(arguments):
    """The (on, option) switches of `set ARGUMENTS`, or None unless each
    argument switches options of SET_OPTIONS: `-e`, `-u`, `-v` and `-x` or
    their `+` forms, and `-o` or `+o` before an option name."""
    switches, pending = [], []
    for argument in arguments:
        if pending:
            if argument not in SET_OPTIONS:
                return None
            switches.append((pending.pop(0), argument))
        elif len(argument) > 1 and argument[0] in "-+" and all(c in SET_LETTERS or c == "o" for c in argument[1:]):
            for letter in argument[1:]:
                if letter == "o":
                    pending.append(argument[0] == "-")
                else:
                    switches.append((argument[0] == "-", SET_LETTERS[letter]))
        else:
            return None
    return switches if switches and not pending else None


def plain_commands(script, directory=PurePosixPath("."), errexit=True, origin=None):
    """(words, directory, counted) for each command other than `cd` and `set` of
    a shell script, before its first line that is not plain. A command counts
    when errexit is on, so that its failure fails the script.

    A plain line is blank, a comment, or words of letters, digits, `_./:=@%+,-`
    and single-quoted text, separated by spaces; a final ` \\` joins the next
    line. The first word of a command names a program or a member of
    PLAIN_BUILTINS, and has no `=`. `cd` with one directory that is no option
    is plain too: the reader follows a relative directory while errexit is on,
    and otherwise the directory becomes None, unknown. So is `set` with
    switches that `plain_set` reads. `origin`, the directory of a script file,
    makes SCRIPT_PARENT plain. A line with `${{`, which GitHub substitutes
    before bash runs, is not plain, even in a comment or a quote."""
    words = []
    for line in script.split("\n"):
        if "${{" in line:
            return
        if not words and PLAIN_COMMENT.fullmatch(line):
            continue
        if not words and origin is not None and line.strip(" ") == SCRIPT_PARENT:
            directory = shell_directory(origin, "..") if errexit else None
            continue
        if not PLAIN_LINE.fullmatch(line):
            return
        words += [re.sub(r"'([^']*)'", r"\1", word) for word in re.findall(PLAIN_WORD, line)]
        if line.endswith("\\"):
            continue
        switches = plain_set(words[1:]) if words[0] == "set" else None
        if words[0] == "cd" and len(words) == 2 and not words[1].startswith("-"):
            directory = shell_directory(directory, words[1]) if errexit else None
        elif switches is not None:
            errexit = {option: on for on, option in switches}.get("errexit", errexit)
        elif "=" not in words[0] and (words[0] in PLAIN_BUILTINS or words[0] not in SHELL_WORDS):
            yield words, directory, errexit
        else:
            return
        words = []


# The options of `cargo test` that the check reads. Any other option, such as
# --no-run, --doc, --help, --target or --config, runs no test as far as the
# check is concerned.
CARGO_FLAGS = {"--all", "--all-features", "--all-targets", "--benches", "--bins", "--examples", "--frozen",
               "--ignore-rust-version", "--keep-going", "--lib", "--locked", "--no-default-features", "--no-fail-fast",
               "--offline", "--quiet", "--release", "--tests", "--verbose", "--workspace", "-q", "-v", "-vv"}
CARGO_VALUES = {"--bench", "--bin", "--color", "--example", "--exclude", "--features", "--jobs", "--manifest-path",
                "--message-format", "--package", "--profile", "--target-dir", "--test", "-F", "-j", "-p"}
CARGO_TARGETS = {"--bench", "--benches", "--bin", "--bins", "--example", "--examples", "--lib"}
# The options of the libtest harness, after `--`, that the check reads. Any
# other option, such as --list, --help or --exclude-should-panic, runs no test.
LIBTEST_FLAGS = {"--exact", "--ignored", "--include-ignored", "--nocapture", "--quiet", "--show-output", "-q"}
LIBTEST_VALUES = {"--color", "--skip", "--test-threads"}


@dataclass
class CargoRun:
    every_test: bool
    targets: set
    ignored: str
    filters: list
    skips: list
    exact: bool
    runs_nothing: bool

    def runs(self, stem, name, ignored):
        if self.runs_nothing or not (self.every_test or stem in self.targets):
            return False
        if ignored and self.ignored == "exclude" or not ignored and self.ignored == "only":
            return False

        def matches(pattern):
            return name == pattern if self.exact else pattern in name

        if any(matches(skip) for skip in self.skips):
            return False
        return not self.filters or any(matches(item) for item in self.filters)


def cargo_run(arguments, package=None):
    """The tests that `cargo test ARGUMENTS` runs in the root package `package`.
    An option outside CARGO_FLAGS and CARGO_VALUES, or after `--` outside
    LIBTEST_FLAGS and LIBTEST_VALUES, makes it run nothing."""
    split = arguments.index("--") if "--" in arguments else len(arguments)
    run = CargoRun(False, set(), "exclude", [], [], False, False)
    selected = False

    def options(arguments, flags, values):
        """(name, value) for each option, with value None for a flag, or ("", word) for a positional word."""
        items = iter(arguments)
        for argument in items:
            name, equals, attached = argument.partition("=") if argument.startswith("--") else (argument, "", "")
            if name in values:
                value = attached if equals else next(items, None)
                if value is None:
                    run.runs_nothing = True
                    return
                yield name, value
            elif name in flags and not equals:
                yield name, None
            elif argument.startswith("-"):
                run.runs_nothing = True
            else:
                yield "", argument

    for name, value in options(arguments[:split], CARGO_FLAGS, CARGO_VALUES):
        if name in ("-p", "--package") and value != package or name == "--exclude":
            run.runs_nothing = True
        elif name == "--manifest-path" and os.path.normpath(value) != "Cargo.toml":
            run.runs_nothing = True
        elif name in ("--all-targets", "--tests"):
            run.every_test = selected = True
        elif name == "--test":
            selected = True
            run.targets.add(value)
        elif name in CARGO_TARGETS:
            selected = True
        elif not name:
            run.filters.append(value)
    if not selected:
        run.every_test = True
    for name, value in options(arguments[split + 1:], LIBTEST_FLAGS, LIBTEST_VALUES):
        if name == "--skip":
            run.skips.append(value)
        elif name == "--ignored":
            run.ignored = "only"
        elif name == "--include-ignored":
            run.ignored = "include"
        elif name == "--exact":
            run.exact = True
        elif not name:
            run.filters.append(value)
    return run


@dataclass
class DiscoverRun:
    start: PurePosixPath
    pattern: str
    selections: list

    def runs(self, path, test_class, method):
        path = PurePosixPath(path)
        if path.parent != self.start or not fnmatch.fnmatchcase(path.name, self.pattern):
            return False
        full = f"{path.stem}.{test_class}.{method}"
        return not self.selections or any(
            fnmatch.fnmatchcase(full, item) if "*" in item else item in full for item in self.selections)


DISCOVER_FLAGS = {"--buffer", "--catch", "--failfast", "--locals", "--quiet", "--verbose", "-b", "-c", "-f", "-q",
                  "-v"}
DISCOVER_SHORT = {"-k": "select", "-p": "pattern", "-s": "start"}
DISCOVER_LONG = {"--durations": "durations", "--pattern": "pattern", "--start-directory": "start"}


def discover_run(arguments, directory):
    """The tests that `python3 -m unittest discover ARGUMENTS` runs from
    `directory`, or None. An option outside DISCOVER_FLAGS, DISCOVER_SHORT and
    DISCOVER_LONG gives None: `--help` runs no test, and a top-level directory
    `-t` changes the names that `-k` matches. So does a start directory or a
    pattern given both as a positional word and as an option, because the last
    one wins."""
    found, positional, selections, given = {"start": ".", "pattern": "test*.py"}, [], [], set()
    items = iter(arguments)
    for argument in items:
        if argument in DISCOVER_FLAGS:
            continue
        if argument.startswith("--"):
            name, equals, attached = argument.partition("=")
            key, value = DISCOVER_LONG.get(name), attached if equals else None
        elif argument.startswith("-"):
            key, value = DISCOVER_SHORT.get(argument[:2]), argument[2:] or None
        else:
            positional.append(argument)
            continue
        value = value if value is not None else next(items, None)
        if key is None or value is None:
            return None
        if key == "select":
            selections.append(value)
        elif key != "durations":
            found[key] = value
            given.add(key)
    if len(positional) > 2 or any(key in given for key in ("start", "pattern")[:len(positional)]):
        return None
    found.update(zip(("start", "pattern"), positional))
    resolved = shell_directory(directory, found["start"])
    return DiscoverRun(resolved, found["pattern"], selections) if resolved is not None else None
