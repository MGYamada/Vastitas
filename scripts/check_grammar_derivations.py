#!/usr/bin/env python3
"""Derive texts from the productions of the Vastitas Reference and check them with the compiler.

    python3 scripts/check_grammar_derivations.py --compiler target/debug/vastitas

The script derives texts from the productions of the grammar summary
(`docs/appendix/grammar.md`), with a bounded depth and a fixed random seed,
and places each text in a small program as an item, a statement, an
expression, a type or a resource statement, in flat mode or in manifest mode.
It runs `vastitas check` on each program. A text that the productions derive
must never give a diagnostic of the parse class (`E_PARSE`, `E_LEX`,
`E_UNSUPPORTED`), unless a rule of the Reference forbids it: `RULES` names
each such rule, the place in the Reference that states it and the code that
it gives. `scripts/check_book.py` checks the other direction, that the
productions derive the examples.
"""

import argparse
from concurrent.futures import ThreadPoolExecutor
from dataclasses import dataclass, field
import random
import re
import subprocess
import sys
import tempfile
from pathlib import Path

import book_grammar
from book_grammar import Choice, Except, Range, Repeat, Sequence, Symbol, Terminal, is_lexical


PARSE_CODES = frozenset({"E_PARSE", "E_LEX", "E_UNSUPPORTED"})
DEPTH = 9
COUNT = 500
SEED = 746

# Names for IDENTIFIER: no strict keyword, no reserved name and no word that a
# construct spells. One IDENTIFIER in WORD_SHARE is instead a word that a
# construct spells, such as `scheme` or `Point`, which is an identifier
# everywhere else.
NAMES = ("a", "b", "c", "f", "g", "h", "k", "m", "n", "q", "r", "s", "t", "u", "v", "w", "x", "y", "z",
         "A", "B", "C", "F", "G", "H", "K", "L", "M", "N", "R", "S", "T", "U", "V", "W", "X", "Y", "Z")
WORD_SHARE = 4


@dataclass
class Node:
    name: str
    children: list = field(default_factory=list)

    def leaves(self):
        for child in self.children:
            if isinstance(child, Node):
                yield from child.leaves()
            else:
                yield child

    def nodes(self):
        yield self
        for child in self.children:
            if isinstance(child, Node):
                yield from child.nodes()


# --- Derivation -------------------------------------------------------------------

class Deriver:
    """Derives random texts from the productions, with a depth bound and coverage-directed choices."""

    def __init__(self, grammar, seed=SEED, depth=DEPTH):
        self.grammar = grammar
        self.random = random.Random(seed)
        self.depth = depth
        self.used = {}
        self.derived = set()
        self.points = {}
        for name, expression in grammar.productions.items():
            if not is_lexical(name):
                for item in book_grammar.symbols(expression):
                    if isinstance(item, (Choice, Repeat)):
                        self.points[id(item)] = (name, item)
        self.heights = self.compute_heights()
        self.distances = self.compute_distances()
        self.words = sorted({item.text for name, expression in grammar.productions.items() if not is_lexical(name)
                             for item in book_grammar.symbols(expression)
                             if isinstance(item, Terminal) and grammar.matches("IDENTIFIER", item.text)})

    def compute_distances(self):
        """{goal: {name: the least number of expansions from name to a node of goal}}."""
        parents = {}
        for name, expression in self.grammar.productions.items():
            if not is_lexical(name):
                for item in book_grammar.symbols(expression):
                    if isinstance(item, Symbol) and not is_lexical(item.name):
                        parents.setdefault(item.name, set()).add(name)
        distances = {}
        for goal in self.heights:
            found = {goal: 0}
            queue = [goal]
            for current in queue:
                for parent in sorted(parents.get(current, ())):
                    if parent not in found:
                        found[parent] = found[current] + 1
                        queue.append(parent)
            distances[goal] = found
        return distances

    def reach(self, expression, goal):
        """The least number of expansions from an expression to a node of goal, or None."""
        found = [self.distances[goal][item.name] for item in book_grammar.symbols(expression)
                 if isinstance(item, Symbol) and item.name in self.distances[goal]]
        return min(found) if found else None

    def compute_heights(self):
        """The least depth of a derivation of each nonterminal."""
        heights = {name: None for name in self.grammar.productions if not is_lexical(name)}
        changed = True
        while changed:
            changed = False
            for name in heights:
                height = self.height(self.grammar.productions[name], heights)
                if height is not None and (heights[name] is None or height + 1 < heights[name]):
                    heights[name] = height + 1
                    changed = True
        missing = sorted(name for name, height in heights.items() if height is None)
        if missing:
            raise ValueError(f"no finite derivation of {missing}")
        return heights

    def height(self, expression, heights):
        if isinstance(expression, (Terminal, Range)):
            return 0
        if isinstance(expression, Symbol):
            return 0 if is_lexical(expression.name) else heights[expression.name]
        if isinstance(expression, Sequence):
            parts = [self.height(item, heights) for item in expression.items]
            return None if None in parts else max(parts)
        if isinstance(expression, Choice):
            parts = [h for h in (self.height(item, heights) for item in expression.alternatives) if h is not None]
            return min(parts) if parts else None
        if isinstance(expression, Repeat):
            return 0 if expression.low == 0 else self.height(expression.item, heights)
        if isinstance(expression, Except):
            return 0
        raise ValueError(f"{book_grammar.render(expression)} is no item of a syntactic production")

    def pick(self, item, options, depth):
        """Choose among (key, height) options: within the depth bound, the least used most often."""
        fitting = [option for option in options if depth + option[1] <= self.depth]
        if not fitting:
            least = min(height for _, height in options)
            fitting = [option for option in options if option[1] == least]
        weights = [1 / (1 + self.used.get((id(item), key), 0)) ** 2 for key, _ in fitting]
        key = self.random.choices(fitting, weights)[0][0]
        self.used[(id(item), key)] = self.used.get((id(item), key), 0) + 1
        return key

    def options(self, item):
        """The alternatives of a choice, or the repetition counts that the derivation takes."""
        if isinstance(item, Choice):
            return range(len(item.alternatives))
        return range(item.low, (item.high if item.high is not None else item.low + 2) + 1)

    def goals(self):
        """Every nonterminal, then every option of every choice and repetition, in grammar order."""
        return [*(("node", name) for name in self.heights),
                *(("point", key, option) for key, (_, item) in self.points.items() for option in self.options(item))]

    def owner(self, goal):
        return goal[1] if goal[0] == "node" else self.points[goal[1]][0]

    def covered(self, goal):
        if goal[0] == "node":
            return goal[1] in self.derived
        return bool(self.used.get((goal[1], goal[2])))

    def derive(self, name, depth=0, goal=None):
        """A derivation of name; with a goal, one that reaches the goal by a shortest path.

        A goal ("node", N) is a node of N. A goal ("point", key, option) is a
        node of the production that holds the choice or repetition, which then
        takes the option there.
        """
        self.derived.add(name)
        node = Node(name)
        if goal and goal[0] == "node" and goal[1] == name:
            goal = None
        elif goal and goal[0] == "point" and self.points[goal[1]][0] == name:
            goal = ("inside", goal[1], goal[2])
        node.children = self.expand(self.grammar.productions[name], depth + 1, goal)
        return node

    def toward(self, expression, goal):
        """The distance from an expression to its goal, or None where it does not reach it."""
        if goal[0] == "inside":
            return 0 if any(id(item) == goal[1] for item in book_grammar.symbols(expression)) else None
        return self.reach(expression, self.owner(goal))

    def expand(self, expression, depth, goal=None):
        if isinstance(expression, Terminal):
            return [expression.text]
        if isinstance(expression, Symbol):
            if is_lexical(expression.name):
                return [self.token(expression.name)]
            return [self.derive(expression.name, depth, goal)]
        if isinstance(expression, Except):
            excluded = book_grammar.excluded_words(expression)
            while True:
                token = self.token(expression.item.name)
                if token not in excluded:
                    return [token]
        if isinstance(expression, Sequence):
            target = None
            if goal:
                reaches = [(self.toward(item, goal), index) for index, item in enumerate(expression.items)]
                target = min((pair for pair in reaches if pair[0] is not None), default=(None, None))[1]
            return [child for index, item in enumerate(expression.items)
                    for child in self.expand(item, depth, goal if index == target else None)]
        if isinstance(expression, Choice):
            options = [(index, self.height(item, self.heights))
                       for index, item in enumerate(expression.alternatives)]
            if goal and goal[0] == "inside" and goal[1] == id(expression):
                options, goal = [options[goal[2]]], None
            elif goal:
                reaches = [self.toward(item, goal) for item in expression.alternatives]
                least = min((distance for distance in reaches if distance is not None), default=None)
                options = [option for option, distance in zip(options, reaches) if distance == least]
            index = self.pick(expression, options, depth if not goal else -len(self.heights))
            return self.expand(expression.alternatives[index], depth, goal)
        if isinstance(expression, Repeat):
            inner = self.height(expression.item, self.heights)
            options = [(count, 0 if count == 0 else inner) for count in self.options(expression)]
            if goal and goal[0] == "inside" and goal[1] == id(expression):
                options, goal = [option for option in options if option[0] == goal[2]], None
            elif goal and self.toward(expression.item, goal) is not None:
                options = [option for option in options if option[0] > 0]
            else:
                goal = None
            count = self.pick(expression, options, depth if not goal else -len(self.heights))
            return [child for copy in range(count)
                    for child in self.expand(expression.item, depth, goal if copy == 0 else None)]
        raise ValueError(f"{book_grammar.render(expression)} is no item of a syntactic production")

    def token(self, name):
        """A token of a class: a name or a word for IDENTIFIER, otherwise a derivation of its lexical form."""
        if name == "IDENTIFIER":
            if self.words and self.random.randrange(WORD_SHARE) == 0:
                return self.random.choice(self.words)
            return self.random.choice(NAMES)
        for _ in range(100):
            text = self.lexical(self.grammar.productions[name])
            if self.grammar.matches(name, text) and len(self.grammar.tokenize(text)) == 1:
                return text
        raise ValueError(f"no token of {name} derived")

    def lexical(self, expression):
        if isinstance(expression, Terminal):
            return expression.text
        if isinstance(expression, Range):
            return chr(self.random.randint(ord(expression.low), ord(expression.high)))
        if isinstance(expression, Symbol):
            return self.lexical(self.grammar.productions[expression.name])
        if isinstance(expression, Sequence):
            return "".join(self.lexical(item) for item in expression.items)
        if isinstance(expression, Choice):
            return self.lexical(self.random.choice(expression.alternatives))
        if isinstance(expression, Repeat):
            high = expression.high if expression.high is not None else expression.low + 2
            return "".join(self.lexical(expression.item) for _ in range(self.random.randint(expression.low, high)))
        if isinstance(expression, Except):
            return self.lexical(expression.item)
        raise TypeError(expression)

    def coverage(self, contexts=None):
        """How many options of the choices and repetitions some derivation took, of those that the
        start symbols of the contexts reach."""
        starts = {context.start for context in contexts} if contexts else set(self.heights)
        options = [goal for goal in self.goals() if goal[0] == "point"
                   and any(start in self.distances[self.owner(goal)] for start in starts)]
        return sum(1 for goal in options if self.covered(goal)), len(options)


def render(tree):
    """The text of a derivation and the place (line, column) of the first token of each node, by id.

    Spaces separate the tokens, and a line ends after `;`, `{` and `}`.
    """
    out = []
    places = {}
    waiting = []
    line, column = 1, 1

    def walk(node):
        nonlocal line, column
        waiting.append(id(node))
        for child in node.children:
            if isinstance(child, Node):
                walk(child)
                continue
            for key in waiting:
                places[key] = (line, column)
            waiting.clear()
            out.append(child)
            if child in (";", "{", "}"):
                out.append("\n")
                line, column = line + 1, 1
            else:
                out.append(" ")
                column += len(child) + 1

    walk(tree)
    return "".join(out).strip(), places


def text(tree):
    return render(tree)[0]


# --- Contexts -------------------------------------------------------------------

@dataclass(frozen=True)
class Context:
    name: str
    start: str
    mode: str  # "flat" or "manifest"
    template: str

    def program(self, derived):
        body = "\n".join("    " + line for line in derived.splitlines())
        return self.template.replace("{indented}", body).replace("{text}", derived)

    def position(self, line, column):
        """The place in the program of a place in the derived text."""
        marker = "{indented}" if "{indented}" in self.template else "{text}"
        before = self.template[:self.template.index(marker)]
        lines = before.count("\n")
        if marker == "{indented}":
            return line + lines, column + 4
        return line + lines, column + (len(before) - before.rfind("\n") - 1 if line == 1 else 0)


CONTEXTS = (
    Context("item", "Item", "manifest", "{text}\n"),
    Context("item", "Item", "flat", "{text}\n"),
    Context("statement", "Statement", "manifest", "fn main() -> Int {\n{indented}\n    0\n}\n"),
    Context("statement", "Statement", "flat", "fn main() -> Int {\n{indented}\n    0\n}\n"),
    Context("expression", "Expression", "manifest", "fn main() -> Int {\n{indented}\n}\n"),
    Context("expression", "Expression", "flat", "fn main() -> Int {\n{indented}\n}\n"),
    Context("type", "Type", "manifest", "fn probe(value: {text}) -> Int {\n    0\n}\n"),
    Context("type", "Type", "flat", "fn probe(value: {text}) -> Int {\n    0\n}\n"),
    Context("resource statement", "ResourceStatement", "manifest",
            "resource fn probe() -> Int {\n{indented}\n    value {\n        0\n    }\n}\n"),
)

MANIFEST = '[package]\nname = "derived"\nversion = "0.1.0"\nroot = "src/main.vast"\n'


# --- Rules of the Reference that forbid derived texts ----------------------------

COMPARISONS = frozenset({"==", "!=", "<", "<=", ">", ">="})


def operator_chain(node):
    """The binary operators that join the operands of an operator expression without parentheses.

    A call binds more tightly than any operator, and a unary operator applies
    to the operand that follows it, so the chain continues through the
    callee of a call and the operand of a unary operator.
    """
    if node.name == "Expression":
        return operator_chain(node.children[0])
    if node.name == "OperatorExpression":
        if len(node.children) == 2:
            return operator_chain(node.children[1])
        left, operator, right = node.children
        return [*operator_chain(left), operator.children[0], *operator_chain(right)]
    if node.name == "CallExpression":
        return operator_chain(node.children[0])
    return []


def chained_comparison(tree, mode, grammar):
    for node in tree.nodes():
        if node.name == "OperatorExpression" and len(node.children) == 3:
            run = 0
            for operator in operator_chain(node):
                run = 0 if operator in ("&&", "||") else run + (operator in COMPARISONS)
                if run > 1:
                    yield node
                    break


FLAT_ITEMS = frozenset({"Function", "GenericDeclaration", "MethodDeclaration", "AbstractTypeDeclaration",
                        "SubtypeDeclaration", "AbstractMethodDeclaration"})


def flat_item(tree, mode, grammar):
    if mode == "flat":
        yield from (node for node in tree.nodes()
                    if node.name in ("VisibleItem", "HiddenItem") and node.children[0].name not in FLAT_ITEMS)


def flat_pub(tree, mode, grammar):
    if mode == "flat":
        yield from (node for node in tree.nodes() if node.name == "Item" and node.children[0] == "pub")


def has_path(node):
    return "::" in node.leaves()


def flat_expression_path(tree, mode, grammar):
    if mode == "flat":
        for node in tree.nodes():
            if node.name == "PathExpression" and has_path(node):
                yield node
            if node.name == "MethodDeclaration" and has_path(node.children[1]):
                yield node.children[1]
            if node.name == "AbstractMethodDeclaration" and has_path(node.children[2]):
                yield node.children[2]


# The constructs whose paths are selectors, parents or the parent of a subtype.
SELECTOR_PLACES = frozenset({"MethodParameter", "ContractKey", "AbstractParents", "SubtypeDeclaration"})


def flat_selector_path(tree, mode, grammar):
    if mode == "flat":
        yield from (child for node in tree.nodes() if node.name in SELECTOR_PLACES for child in node.children
                    if isinstance(child, Node) and child.name == "Path" and has_path(child))


def flat_generic_segment(tree, mode, grammar):
    if mode == "flat":
        yield from (node for node in tree.nodes() if node.name == "PathSegment" and node.children[0] == "generic")


# The type names of Types and Geometric types, and `Object`, with the
# production of the type that a name followed by `<` begins.
TYPE_NAMES = {"Nat": "ScalarType", "Int": "ScalarType", "Bool": "ScalarType", "Unit": "ScalarType",
              "Pair": "PairType", "Fn": "FunctionType", "Scheme": "SettingType", "CInfScheme": "SettingType",
              "Point": "PointType", "Morphism": "MorphismType", "Pointed": "PointedType", "Object": "ObjectType"}
# The parser reads the arguments of such a type as the arguments of that type,
# so the rules of the type give further codes: Pair types and Geometric types
# give E_TYPE for an element of a pair, an endpoint that names no object and
# the arguments of Pointed, and Types gives E_UNSUPPORTED for an input of Fn
# that names no type.
ARGUMENT_CODES = {"Pair": "E_TYPE", "Fn": "E_UNSUPPORTED", "Point": "E_TYPE", "Morphism": "E_TYPE",
                  "Pointed": "E_TYPE"}


def type_name_family(tree, mode, grammar):
    """An indexed type whose family is a type name, and whose text that type's own production does not derive."""
    for node in tree.nodes():
        if node.name == "IndexedType" and node.children[0] in TYPE_NAMES and node.children[1] == "<":
            words = " ".join(node.leaves())
            own = TYPE_NAMES[node.children[0]]
            if own == "ObjectType":
                parts = " ".join(list(node.leaves())[2:-1]).split(" , ")
                fits = len(parts) == 2 and all(part and grammar.parse(part, start="Path") is None for part in parts)
            else:
                fits = grammar.parse(words, start=own) is None
            if not fits:
                extra = ARGUMENT_CODES.get(node.children[0])
                yield node, frozenset({"E_PARSE", extra} if extra else {"E_PARSE"})


def flat_type_name_path(tree, mode, grammar):
    """In flat mode, a path in a type whose first segment is a type name, which begins that type."""
    if mode == "flat":
        yield from (node for node in tree.nodes() if node.name == "IndexedType" and node.children[1] == "::"
                    and node.children[0] in TYPE_NAMES and node.children[0] != "Object")


def flat_indexed_type(tree, mode, grammar):
    if mode == "flat":
        yield from (node for node in tree.nodes() if node.name == "IndexedType")


def flat_pack_type(tree, mode, grammar):
    if mode == "flat":
        yield from (node for node in tree.nodes() if node.name == "PackExpression" and isinstance(node.children[1], Node))


def flat_unpack_witness(tree, mode, grammar):
    if mode == "flat":
        yield from (node for node in tree.nodes() if node.name == "UnpackFields" and node.children[0] == "witness")


@dataclass(frozen=True)
class Rule:
    """A rule of the Reference: applies(tree, mode, grammar) yields each node that breaks it, or
    (node, codes) where the codes of the break differ from code."""
    name: str
    place: str
    code: str
    applies: object


# The rules of the Reference that make a derived text an error of the parse
# class, by the chapter and section that state each one, with the rule that
# gives the parser's E_NAME for a path of flat mode.
RULES = (
    Rule("chained comparison", "Expressions, Operator expressions: a comparison must not be an operand "
         "of another comparison without parentheses", "E_PARSE", chained_comparison),
    Rule("item of manifest mode in flat mode", "Items, Kinds of items: in flat mode an item of a kind "
         "that the table marks No is an error", "E_UNSUPPORTED", flat_item),
    Rule("pub in flat mode", "Items, Visibility: pub before an item is an error in flat mode",
         "E_UNSUPPORTED", flat_pub),
    Rule("path in an expression or a method name in flat mode", "Names and paths, Resolution: in flat "
         "mode a path with :: is E_PARSE in an expression and in the name of a method", "E_PARSE",
         flat_expression_path),
    Rule("path in a selector, a parent or a subtype in flat mode", "Names and paths, Resolution: in flat "
         "mode a path with :: is E_NAME in a selector, a parent or a subtype", "E_NAME", flat_selector_path),
    Rule("generic as a path segment in flat mode", "Names and paths, Resolution: in flat mode a path "
         "segment is an identifier, and generic as a segment is an error", "E_PARSE", flat_generic_segment),
    Rule("type name as the family of an indexed type", "Types, Indexed types: a name followed by < is an "
         "indexed type only when it is no type name of Types or Geometric types, and Object<…> has two paths; "
         "the rules of the type that the name begins give E_TYPE or E_UNSUPPORTED for its arguments",
         "E_PARSE", type_name_family),
    Rule("path that begins with a type name in a type in flat mode", "Types, Indexed types: in flat mode a "
         "path in a type whose first segment is a type name of Types or Geometric types is an error",
         "E_PARSE", flat_type_name_path),
    Rule("indexed type in flat mode", "Types, Indexed types: in flat mode an indexed type is an error",
         "E_UNSUPPORTED", flat_indexed_type),
    Rule("pack with a type in flat mode", "Expressions, Pack expressions: the form with a type must not "
         "occur in flat mode", "E_PARSE", flat_pack_type),
    Rule("unpack with a witness in flat mode", "Statements, unpack statements: in flat mode the witness "
         "form is an error", "E_PARSE", flat_unpack_witness),
)


def applicable(tree, mode, grammar, rules=RULES):
    """The rules that a derivation breaks, each with the first node that breaks it and the codes of the break."""
    found = []
    for rule in rules:
        first = next(iter(rule.applies(tree, mode, grammar)), None)
        if first is not None:
            node, codes = first if isinstance(first, tuple) else (first, frozenset({rule.code}))
            found.append((rule, node, codes))
    return found


# --- Cases ----------------------------------------------------------------------

@dataclass
class Case:
    number: int
    context: Context
    tree: Node
    derived: str
    program: str
    broken: list  # (rule, place in the program of the first node that breaks it, codes of the break)
    goal: object = None

    @property
    def rules(self):
        return [rule for rule, _, _ in self.broken]


def context_for(deriver, goal, contexts):
    """The context of manifest mode, where every construct exists, whose start symbol is nearest the goal."""
    owner = deriver.owner(goal)
    reach = [(deriver.distances[owner][context.start], index, context) for index, context in enumerate(contexts)
             if context.mode == "manifest" and context.start in deriver.distances[owner]]
    return min(reach, key=lambda entry: entry[:2])[2] if reach else None


def derive_cases(grammar, count=COUNT, seed=SEED, depth=DEPTH, contexts=CONTEXTS):
    """The derived texts in their contexts, in a fixed order for a seed.

    The first texts each reach a goal that no earlier text covers: a
    nonterminal or an option of a choice or a repetition. The other texts
    are free, and they take the contexts in turn, up to count texts in all.
    """
    deriver = Deriver(grammar, seed, depth)
    cases = []

    def add(context, goal):
        tree = deriver.derive(context.start, goal=goal)
        derived, places = render(tree)
        broken = [(rule, context.position(*places[id(node)]), codes)
                  for rule, node, codes in applicable(tree, context.mode, grammar)]
        cases.append(Case(len(cases), context, tree, derived, context.program(derived), broken, goal))

    for goal in deriver.goals():
        context = context_for(deriver, goal, contexts)
        if context and not deriver.covered(goal):
            add(context, goal)
    free = 0
    while len(cases) < count:
        add(contexts[free % len(contexts)], None)
        free += 1
    return cases, deriver


DIAGNOSTIC = re.compile(r"^(?:(?:(?:src/)?main\.vast:(\d+):(\d+)|[^\s:]+(?::\d+:\d+)?): )?(E_[A-Z][A-Z0-9_]*): ",
                        re.M)


def diagnostics(stderr):
    """The diagnostics of a run: (place in the program or None, code), in order."""
    return [((int(line), int(column)) if line else None, code)
            for line, column, code in DIAGNOSTIC.findall(stderr)]


def verdict(case, found):
    """None when the diagnostics agree with the productions and the rules, else the reason.

    A text that no rule forbids gives no code of the parse class. A text that
    a rule forbids gives a code of a break of a rule as its first diagnostic,
    unless that diagnostic is of another class and lies at or before the first
    place that breaks a rule: the frontend checks some rules on names and types
    while it parses, and it stops at the first error.
    """
    codes = [code for _, code in found]
    allowed = set().union(*(codes for _, _, codes in case.broken))
    wrong = [code for code in codes if code in PARSE_CODES and code not in allowed]
    if wrong:
        return f"the compiler gives {wrong[0]}"
    if case.broken:
        first = min(place for _, place, _ in case.broken)
        place, code = found[0] if found else (None, None)
        if code in allowed or (code not in PARSE_CODES and place is not None and place <= first):
            return None
        names = ", ".join(rule.name for rule in case.rules)
        return f"the text breaks the rules ({names}) at {first[0]}:{first[1]}, but the compiler gives " \
               f"{code or 'no diagnostic'}"
    return None


def exit_problem(status, found):
    """None when the exit status agrees with the diagnostics, else the reason.

    `vastitas check` exits with 0 when it accepts a program and with 1 when it
    rejects it with at least one diagnostic. Any other status (a panic, a signal,
    a time-out) or a rejection without a diagnostic is a failure of the compiler,
    whatever the text derives.
    """
    if status == 0 or (status == 1 and found):
        return None
    if status == 1:
        return "the compiler exits with status 1 and reports no diagnostic"
    if status is None:
        return "the compiler does not finish within the time-out"
    if status < 0:
        return f"the compiler ends by signal {-status}"
    return f"the compiler ends abnormally with status {status}"


def run(compiler, case, directory):
    """Check the program of a case. The result is (exit status or None for a time-out, stderr)."""
    root = Path(directory) / f"case-{case.number}"
    root.mkdir()
    if case.context.mode == "manifest":
        (root / "src").mkdir()
        (root / "Vastitas.toml").write_text(MANIFEST, encoding="utf-8")
        (root / "src/main.vast").write_text(case.program, encoding="utf-8")
        command = [compiler, "check", "--manifest-path", str(root / "Vastitas.toml")]
    else:
        (root / "main.vast").write_text(case.program, encoding="utf-8")
        command = [compiler, "check", str(root / "main.vast")]
    try:
        result = subprocess.run(command, capture_output=True, text=True, timeout=300)
    except subprocess.TimeoutExpired as expired:
        stderr = expired.stderr or ""
        if isinstance(stderr, bytes):
            stderr = stderr.decode("utf-8", "replace")
        return None, stderr
    return result.returncode, result.stderr.replace(str(root.resolve()) + "/", "").replace(str(root) + "/", "")


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("--compiler", required=True, help="the built vastitas executable")
    parser.add_argument("--count", type=int, default=COUNT, help=f"the number of texts (default {COUNT})")
    parser.add_argument("--seed", type=int, default=SEED, help=f"the random seed (default {SEED})")
    parser.add_argument("--depth", type=int, default=DEPTH, help=f"the depth bound (default {DEPTH})")
    parser.add_argument("--jobs", type=int, default=4, help="the number of compilers that run at once")
    parser.add_argument("--verbose", action="store_true", help="print every text and its diagnostics")
    arguments = parser.parse_args(argv)
    compiler = str(Path(arguments.compiler).resolve())
    grammar = book_grammar.load()
    cases, deriver = derive_cases(grammar, arguments.count, arguments.seed, arguments.depth)
    for case in cases:
        failure = grammar.parse(case.program)
        if failure:
            raise ValueError(f"derived text {case.number} does not parse with the productions: "
                             f"{failure.where(case.program)}: {failure.message}\n{case.program}")
    failures = []
    forbidden = 0
    with tempfile.TemporaryDirectory(prefix="vastitas-derived-") as directory:
        with ThreadPoolExecutor(arguments.jobs) as pool:
            outputs = list(pool.map(lambda case: run(compiler, case, directory), cases))
    for case, (status, stderr) in zip(cases, outputs):
        found = diagnostics(stderr)
        reason = exit_problem(status, found) or verdict(case, found)
        forbidden += bool(case.rules)
        if arguments.verbose:
            print(f"--- {case.number} {case.context.name} ({case.context.mode}): "
                  f"{[code for _, code in found] or 'checked'}")
            print(case.program)
        if reason:
            failures.append((case, reason, stderr))
    used, total = deriver.coverage(CONTEXTS)
    print(f"Derived {len(cases)} texts (seed {arguments.seed}, depth {arguments.depth}); they take {used} of "
          f"the {total} options of choices and repetitions that the contexts reach")
    print(f"{forbidden} texts break a rule of RULES; each gives a code of its break first, or an earlier error:")
    for rule in RULES:
        count = sum(rule in case.rules for case in cases)
        print(f"  {rule.name} ({rule.code}): {count} texts; {rule.place}")
    if failures:
        for case, reason, stderr in failures:
            print(f"\nText {case.number}, a {case.context.name} in {case.context.mode} mode: {reason}",
                  file=sys.stderr)
            print(case.program.rstrip(), file=sys.stderr)
            print(stderr.rstrip(), file=sys.stderr)
        print(f"\n{len(failures)} derived texts give a parse diagnostic that no rule allows, "
              "or make the compiler fail", file=sys.stderr)
        return 1
    print("No derived text gives a parse diagnostic that no rule allows")
    return 0


if __name__ == "__main__":
    sys.exit(main())
