#!/usr/bin/env python3
"""The productions of the Vastitas Reference as a recognizer.

The module reads the productions that the grammar summary
(`docs/appendix/grammar.md`) collects, in the notation of
`docs/language/notation.md`. It tokenizes source text as the Reference says
and recognizes a token sequence with the productions, with an Earley parser
that accepts every context-free grammar, including left-recursive and
ambiguous ones such as `Expression -> Expression BinaryOperator Expression`.

    python3 scripts/book_grammar.py FILE.vast...   parse files from SourceFile

`scripts/check_book.py` parses the examples with it, and
`scripts/check_grammar_derivations.py` derives texts from the same
productions and runs the compiler on them.
"""

from dataclasses import dataclass
from pathlib import Path
import re
import sys


ROOT = Path(__file__).resolve().parents[1]
GRAMMAR_CHAPTER = "appendix/grammar.md"
START = "SourceFile"

# The tokens of the Reference that have productions, in Lexical structure.
LEXER_CLASSES = ("IDENTIFIER_OR_KEYWORD", "INTEGER_LITERAL", "FLOAT_LITERAL", "PUNCTUATION")
KEYWORDS = "STRICT_KEYWORD"

# The forms that the Reference gives in prose and not as productions, because
# the notation has no class for the characters that they may hold. The
# tokenizer reads them as the named sections say.
PROSE_FORMS = {
    "whitespace": "Lexical structure, Source text: a character with the Unicode White_Space property "
                  "other than a line separator of the table",
    "line comment": "Lexical structure, Comments: from // to the end of the line",
    "string literal": "Lexical structure, Other literals: text between double quotes, to the end of the "
                      "file without a closing quote; no construct accepts it",
    "malformed number": "Lexical structure, Integer literals and Other literals: a number followed by a "
                        "letter or _ is one token that matches no production",
}

# A token that the parser may read as two tokens, with the rule that says so.
SPLIT_TOKENS = {
    ">=": ((">", "="), "Lexical structure, Punctuation: after the type arguments of a type, "
                       "the parser reads >= as > followed by ="),
}

# Unicode White_Space, and the characters that Source text excludes from it.
WHITE_SPACE = frozenset(map(chr, [*range(0x9, 0xE), 0x20, 0x85, 0xA0, 0x1680, *range(0x2000, 0x200B),
                                  0x2028, 0x2029, 0x202F, 0x205F, 0x3000]))
LINE_SEPARATORS = frozenset(map(chr, [0xB, 0xC, 0x1C, 0x1D, 0x1E, 0x85, 0x2028, 0x2029]))
DECEPTIVE = frozenset(map(chr, [0x61C, 0x200E, 0x200F, *range(0x202A, 0x202F), 0x200B,
                                *range(0x2060, 0x2070), 0xFEFF]))


# --- The notation ----------------------------------------------------------------

@dataclass(frozen=True)
class Terminal:
    text: str


@dataclass(frozen=True)
class Symbol:
    name: str


@dataclass(frozen=True)
class Sequence:
    items: tuple


@dataclass(frozen=True)
class Choice:
    alternatives: tuple


@dataclass(frozen=True)
class Repeat:
    item: object
    low: int
    high: object  # None: no bound


@dataclass(frozen=True)
class Except:
    item: object
    excluded: object


@dataclass(frozen=True)
class Range:
    low: str
    high: str


POSTFIX = {"?": (0, 1), "*": (0, None), "+": (1, None)}
NOTATION_TOKEN = re.compile(r"\s*(?:(`[^`]+`)|\[`([^`])`-`([^`])`\]|([A-Za-z_][A-Za-z0-9_]*)|([|()?*+]))")
PRODUCTION = re.compile(r"^([A-Za-z][A-Za-z0-9_]*) ->(?: (.*))?$")
LEXICAL_NAME = re.compile(r"[A-Z][A-Z0-9_]*")
SYNTACTIC_NAME = re.compile(r"[A-Z][A-Za-z0-9]*")


def is_lexical(name):
    """A name in UPPER_CASE defines a token class or another lexical form."""
    return bool(LEXICAL_NAME.fullmatch(name))


def notation_tokens(body):
    tokens = []
    position = 0
    body = body.rstrip()
    while position < len(body):
        match = NOTATION_TOKEN.match(body, position)
        if not match or match.end() == position:
            raise ValueError(f"cannot read the notation at {body[position:]!r}")
        position = match.end()
        if match[1]:
            tokens.append(("terminal", match[1][1:-1]))
        elif match[2]:
            tokens.append(("range", (match[2], match[3])))
        elif match[4]:
            tokens.append(("except", None) if match[4] == "except" else ("name", match[4]))
        else:
            tokens.append((match[5], None))
    return tokens


def parse_expression(body):
    """The expression of the right side of a production."""
    tokens = notation_tokens(body)
    position = 0

    def peek():
        return tokens[position][0] if position < len(tokens) else None

    def take():
        nonlocal position
        position += 1
        return tokens[position - 1]

    def choice():
        alternatives = [sequence()]
        while peek() == "|":
            take()
            alternatives.append(sequence())
        return alternatives[0] if len(alternatives) == 1 else Choice(tuple(alternatives))

    def sequence():
        items = []
        while peek() not in (None, "|", ")"):
            items.append(postfix())
        if not items:
            raise ValueError(f"an empty alternative in {body!r}")
        return items[0] if len(items) == 1 else Sequence(tuple(items))

    def postfix():
        item = primary()
        while peek() in POSTFIX:
            low, high = POSTFIX[take()[0]]
            item = Repeat(item, low, high)
        if peek() == "except":
            take()
            item = Except(item, primary())
        return item

    def primary():
        kind, value = take() if position < len(tokens) else (None, None)
        if kind == "terminal":
            return Terminal(value)
        if kind == "range":
            return Range(*value)
        if kind == "name":
            if not (is_lexical(value) or SYNTACTIC_NAME.fullmatch(value)):
                raise ValueError(f"{value!r} is no nonterminal and no token class")
            return Symbol(value)
        if kind == "(":
            inner = choice()
            if peek() != ")":
                raise ValueError(f"an unclosed group in {body!r}")
            take()
            return inner
        raise ValueError(f"expected an item in {body!r}, found {kind or 'the end'}")

    expression = choice()
    if position != len(tokens):
        raise ValueError(f"unexpected {tokens[position][0]!r} in {body!r}")
    return expression


def render(expression, top=True):
    """The expression in the notation, with the parentheses that it needs."""
    if isinstance(expression, Terminal):
        return f"`{expression.text}`"
    if isinstance(expression, Range):
        return f"[`{expression.low}`-`{expression.high}`]"
    if isinstance(expression, Symbol):
        return expression.name
    if isinstance(expression, Repeat):
        mark = {(0, 1): "?", (0, None): "*", (1, None): "+"}[(expression.low, expression.high)]
        inner = render(expression.item, False)
        if isinstance(expression.item, (Sequence, Choice, Except)):
            inner = f"( {render(expression.item)} )"
        return inner + mark
    if isinstance(expression, Except):
        return f"{render(expression.item, False)} except {render(expression.excluded, False)}"
    if isinstance(expression, Sequence):
        text = " ".join(f"( {render(item)} )" if isinstance(item, Choice) else render(item, False)
                        for item in expression.items)
        return text
    text = " | ".join(render(alternative) for alternative in expression.alternatives)
    return text if top else f"( {text} )"


def read_productions(text):
    """The productions of the code blocks labelled text of a chapter, in order: {name: expression}."""
    productions = {}
    lines = text.splitlines()
    index = 0
    while index < len(lines):
        if lines[index].strip() != "```text":
            index += 1
            continue
        index += 1
        current = None
        while index < len(lines) and lines[index].strip() != "```":
            line = lines[index]
            index += 1
            if not line.strip():
                continue
            if line[:1].isspace() and current:
                current[1].append(line.strip())
                continue
            match = PRODUCTION.match(line)
            if not match:
                raise ValueError(f"not a production: {line!r}")
            if match[1] in productions:
                raise ValueError(f"{match[1]} has two productions")
            current = (match[1], [match[2] or ""])
            productions[match[1]] = current[1]
        index += 1
    return {name: parse_expression(" ".join(parts)) for name, parts in productions.items()}


def symbols(expression):
    """Yield every item of an expression, depth first."""
    yield expression
    if isinstance(expression, Sequence):
        for item in expression.items:
            yield from symbols(item)
    elif isinstance(expression, Choice):
        for item in expression.alternatives:
            yield from symbols(item)
    elif isinstance(expression, Repeat):
        yield from symbols(expression.item)
    elif isinstance(expression, Except):
        yield from symbols(expression.item)
        yield from symbols(expression.excluded)


# --- Lexical forms ----------------------------------------------------------------

def lexical_regex(expression, productions, seen=()):
    """A regular expression for the fullmatch of a lexical expression.

    `x except y` may only be the whole right side of a production that no
    other lexical production names, because the regular expression checks it
    against the end of the text.
    """
    if isinstance(expression, Terminal):
        return re.escape(expression.text)
    if isinstance(expression, Range):
        return f"[{re.escape(expression.low)}-{re.escape(expression.high)}]"
    if isinstance(expression, Symbol):
        if expression.name in seen:
            raise ValueError(f"the lexical form {expression.name} refers to itself")
        if not is_lexical(expression.name) or expression.name not in productions:
            raise ValueError(f"a lexical form names {expression.name}, which is no lexical form")
        body = productions[expression.name]
        inner = (*seen, expression.name)
        if isinstance(body, Except):
            if seen:
                raise ValueError(f"{expression.name} uses except and may not be part of another lexical form")
            excluded = lexical_regex(body.excluded, productions, inner)
            return f"(?!(?:{excluded})\\Z)(?:{lexical_regex(body.item, productions, inner)})"
        return f"(?:{lexical_regex(body, productions, inner)})"
    if isinstance(expression, Sequence):
        return "".join(lexical_regex(item, productions, seen) for item in expression.items)
    if isinstance(expression, Choice):
        return "(?:" + "|".join(lexical_regex(item, productions, seen) for item in expression.alternatives) + ")"
    if isinstance(expression, Repeat):
        bound = {(0, 1): "?", (0, None): "*", (1, None): "+"}[(expression.low, expression.high)]
        return f"(?:{lexical_regex(expression.item, productions, seen)}){bound}"
    if isinstance(expression, Except):
        raise ValueError("except may only form the whole right side of a lexical production")
    raise TypeError(expression)


def alphabet(expression, productions):
    """The characters that a lexical expression may hold."""
    characters = set()
    for item in symbols(expression):
        if isinstance(item, Terminal):
            characters |= set(item.text)
        elif isinstance(item, Range):
            characters |= {chr(code) for code in range(ord(item.low), ord(item.high) + 1)}
        elif isinstance(item, Symbol) and item.name in productions:
            characters |= alphabet(productions[item.name], productions)
    return characters


def excluded_words(item):
    """The terminals that `CLASS except ...` excludes in a syntactic production, or None for another form.

    In a syntactic production, `except` excludes terminals from a token
    class, as in IDENTIFIER except `Base`: an identifier other than `Base`.
    """
    if not (isinstance(item.item, Symbol) and is_lexical(item.item.name)):
        return None
    excluded = item.excluded.alternatives if isinstance(item.excluded, Choice) else (item.excluded,)
    if not all(isinstance(word, Terminal) for word in excluded):
        return None
    return frozenset(word.text for word in excluded)


@dataclass(frozen=True)
class Token:
    kind: str  # a class of LEXER_CLASSES, "KEYWORD", "IDENTIFIER", "STRING_LITERAL" or "MALFORMED"
    text: str
    start: int
    end: int


class LexError(ValueError):
    def __init__(self, offset, message):
        super().__init__(message)
        self.offset = offset


class Grammar:
    """The productions of the Reference, with the tokenizer and the recognizer that they define."""

    def __init__(self, productions, start=START):
        self.productions = dict(productions)
        self.start = start
        self.errors = []
        for name, expression in self.productions.items():
            for item in symbols(expression):
                if isinstance(item, Symbol) and item.name not in self.productions:
                    self.errors.append(f"{name}: {item.name} has no production")
                if not is_lexical(name) and isinstance(item, Range):
                    self.errors.append(f"{name}: {render(item)} belongs in a lexical form")
                if not is_lexical(name) and isinstance(item, Except) and excluded_words(item) is None:
                    self.errors.append(f"{name}: {render(item)} must exclude terminals from a token class")
                if is_lexical(name) and isinstance(item, Symbol) and not is_lexical(item.name):
                    self.errors.append(f"{name}: the lexical form names the nonterminal {item.name}")
        if start not in self.productions:
            self.errors.append(f"the start symbol {start} has no production")
        missing = [name for name in (*LEXER_CLASSES, KEYWORDS) if name not in self.productions]
        if missing:
            self.errors.append(f"the tokens {missing} have no production")
        if self.errors:
            return
        self.token_classes = sorted({item.name for name, expression in self.productions.items()
                                     if not is_lexical(name)
                                     for item in symbols(expression)
                                     if isinstance(item, Symbol) and is_lexical(item.name)})
        self.patterns = {name: re.compile(lexical_regex(Symbol(name), self.productions))
                         for name in {*LEXER_CLASSES, KEYWORDS, *self.token_classes}}
        self.alphabets = {name: alphabet(self.productions[name], self.productions) for name in LEXER_CLASSES}
        for name, expression in self.productions.items():
            if is_lexical(name):
                continue
            for item in symbols(expression):
                if isinstance(item, Terminal):
                    try:
                        found = self.tokenize(item.text)
                    except LexError:
                        found = []
                    if len(found) != 1 or found[0].text != item.text:
                        self.errors.append(f"{name}: the terminal `{item.text}` is no token of Lexical structure")
        self.bnf = Bnf(self)

    # --- Tokens ---

    def matches(self, name, text):
        return bool(self.patterns[name].fullmatch(text))

    def longest(self, source, offset):
        """The longest token of a lexer class at the offset: (class, end), or None."""
        best = None
        for name in LEXER_CLASSES:
            allowed = self.alphabets[name]
            end = offset
            while end < len(source) and source[end] in allowed:
                end += 1
            for stop in range(end, offset, -1):
                if self.patterns[name].fullmatch(source, offset, stop):
                    if best is None or stop > best[1]:
                        best = (name, stop)
                    break
        return best

    def tokenize(self, source):
        """The tokens of a source text, as Lexical structure defines them."""
        tokens = []
        offset = 0
        if source.startswith("﻿"):
            raise LexError(0, "a byte order mark begins the file")
        while offset < len(source):
            ch = source[offset]
            if ch in LINE_SEPARATORS or (ch == "\r" and source[offset + 1:offset + 2] != "\n"):
                raise LexError(offset, f"the line separator U+{ord(ch):04X}")
            if ch in WHITE_SPACE:
                offset += 1
                continue
            if source.startswith("//", offset):
                end = source.find("\n", offset)
                end = len(source) if end < 0 else end
                for index in range(offset, end):
                    if source[index] in LINE_SEPARATORS or source[index] in DECEPTIVE:
                        raise LexError(index, f"U+{ord(source[index]):04X} in a comment")
                offset = end
                continue
            if source.startswith("/*", offset):
                raise LexError(offset, "a block comment")
            if ch == '"':
                end = source.find('"', offset + 1)
                end = len(source) if end < 0 else end + 1
                for index in range(offset, end):
                    if source[index] in LINE_SEPARATORS:
                        raise LexError(index, f"U+{ord(source[index]):04X} in a string literal")
                tokens.append(Token("STRING_LITERAL", source[offset:end], offset, end))
                offset = end
                continue
            if not ch.isascii():
                raise LexError(offset, f"the character U+{ord(ch):04X} outside comments and string literals")
            found = self.longest(source, offset)
            if found is None:
                raise LexError(offset, f"{ch!r} begins no token")
            kind, end = found
            if kind in ("INTEGER_LITERAL", "FLOAT_LITERAL") and end < len(source) \
                    and (source[end].isalnum() or source[end] == "_") and source[end].isascii():
                while end < len(source) and source[end].isascii() and (source[end].isalnum() or source[end] in "_."):
                    end += 1
                kind = "MALFORMED"
            text = source[offset:end]
            if kind == "IDENTIFIER_OR_KEYWORD":
                kind = "KEYWORD" if self.matches(KEYWORDS, text) else "IDENTIFIER"
            tokens.append(Token(kind, text, offset, end))
            offset = end
        return tokens

    def keys(self, token):
        """The terminals and token classes that a token matches."""
        keys = set()
        if token.kind in ("KEYWORD", "IDENTIFIER", "PUNCTUATION"):
            keys.add(("T", token.text))
        if token.kind in ("KEYWORD", "IDENTIFIER", "INTEGER_LITERAL", "FLOAT_LITERAL"):
            keys |= {("C", name) for name in self.token_classes if self.matches(name, token.text)}
        return frozenset(keys)

    def edges(self, tokens, end):
        """The token lattice: {position: [(next position, keys, token)]}, with the split tokens."""
        edges = {}
        for index, token in enumerate(tokens):
            following = tokens[index + 1].start if index + 1 < len(tokens) else end
            edges.setdefault(token.start, []).append((following, self.keys(token), token))
            if token.kind == "PUNCTUATION" and token.text in SPLIT_TOKENS:
                first, second = SPLIT_TOKENS[token.text][0]
                middle = token.start + len(first)
                edges[token.start].append((middle, frozenset({("T", first)}), token))
                edges.setdefault(middle, []).append((following, frozenset({("T", second)}), token))
        return edges

    # --- Recognition ---

    def parse(self, source, start=None):
        """None when the productions derive the source text from the start symbol, else the reason."""
        try:
            tokens = self.tokenize(source)
        except LexError as error:
            return Failure(error.offset, f"no token: {error}")
        return self.bnf.recognize(start or self.start, self.edges(tokens, len(source)), len(source))


@dataclass(frozen=True)
class Failure:
    offset: int
    message: str

    def where(self, source):
        line = source.count("\n", 0, self.offset) + 1
        column = self.offset - (source.rfind("\n", 0, self.offset) + 1) + 1
        return f"{line}:{column}"


class Bnf:
    """The productions as plain rules, with a helper nonterminal for each group and repetition."""

    def __init__(self, grammar):
        self.grammar = grammar
        self.rules = []
        self.helpers = 0
        for name, expression in grammar.productions.items():
            if not is_lexical(name):
                for alternative in self.alternatives(expression):
                    self.rules.append((name, alternative))
        self.by_name = {}
        for index, (name, _) in enumerate(self.rules):
            self.by_name.setdefault(name, []).append(index)
        self.nullable = set()
        changed = True
        while changed:
            changed = False
            for name, rhs in self.rules:
                if name not in self.nullable and all(s[0] == "N" and s[1] in self.nullable for s in rhs):
                    self.nullable.add(name)
                    changed = True
        first = {name: set() for name in self.by_name}
        changed = True
        while changed:
            changed = False
            for name, rhs in self.rules:
                before = len(first[name])
                first[name] |= self.first_of(rhs, first)
                changed |= len(first[name]) != before
        self.first = first
        # For each nonterminal: the rules that a token key may begin, and the rules that derive nothing.
        self.predict = {}
        for name, indices in self.by_name.items():
            table = {}
            empty = []
            for index in indices:
                rhs = self.rules[index][1]
                if all(s[0] == "N" and s[1] in self.nullable for s in rhs):
                    empty.append(index)
                for key in self.first_of(rhs, first):
                    table.setdefault(key, []).append(index)
            self.predict[name] = (table, empty)

    def first_of(self, rhs, first):
        keys = set()
        for kind, value in rhs:
            if kind == "X":
                keys.add(("C", value[0]))
                return keys
            if kind != "N":
                keys.add((kind, value))
                return keys
            keys |= first.get(value, set())
            if value not in self.nullable:
                return keys
        return keys

    def helper(self, alternatives):
        self.helpers += 1
        name = f"#{self.helpers}"
        for alternative in alternatives:
            self.rules.append((name, alternative))
        return ("N", name)

    def symbol(self, item):
        if isinstance(item, Terminal):
            return ("T", item.text)
        if isinstance(item, Symbol):
            return ("C", item.name) if is_lexical(item.name) else ("N", item.name)
        if isinstance(item, Choice):
            return self.helper(self.alternatives(item))
        if isinstance(item, Sequence):
            return self.helper([self.sequence(item)])
        if isinstance(item, Except):
            return ("X", (item.item.name, excluded_words(item)))
        if isinstance(item, Repeat):
            inner = self.sequence(item.item)
            if (item.low, item.high) == (0, 1):
                return self.helper([(), inner])
            self.helpers += 1
            name = f"#{self.helpers}"
            self.rules.append((name, inner if item.low else ()))
            self.rules.append((name, (("N", name), *inner)))
            return ("N", name)
        raise ValueError(f"{render(item)} is no item of a syntactic production")

    def sequence(self, expression):
        if isinstance(expression, Sequence):
            return tuple(symbol for item in expression.items for symbol in self.sequence(item))
        return (self.symbol(expression),)

    def alternatives(self, expression):
        if isinstance(expression, Choice):
            return [self.sequence(alternative) for alternative in expression.alternatives]
        return [self.sequence(expression)]

    def recognize(self, start, edges, end):
        rules = self.rules + [("", (("N", start),))]
        top = len(rules) - 1
        positions = sorted({*edges, end})
        sets = {position: [] for position in positions}
        seen = {position: set() for position in positions}
        waiting = {}
        furthest = positions[0]

        def add(position, item):
            if item not in seen[position]:
                seen[position].add(item)
                sets[position].append(item)

        add(positions[0], (top, 0, positions[0]))
        for position in positions:
            items = sets[position]
            if items:
                furthest = position
            outgoing = edges.get(position, ())
            keys = set().union(*(key for _, key, _ in outgoing)) if outgoing else set()
            waits = waiting.setdefault(position, {})
            predicted = set()
            index = 0
            while index < len(items):
                rule, dot, origin = items[index]
                index += 1
                lhs, rhs = rules[rule]
                if dot == len(rhs):
                    for parent, parent_dot, parent_origin in waiting[origin].get(lhs, ()):
                        add(position, (parent, parent_dot + 1, parent_origin))
                    continue
                kind, value = rhs[dot]
                if kind == "N":
                    waits.setdefault(value, []).append((rule, dot, origin))
                    if value not in predicted:
                        predicted.add(value)
                        table, empty = self.predict[value]
                        for key in keys:
                            for candidate in table.get(key, ()):
                                add(position, (candidate, 0, position))
                        for candidate in empty:
                            add(position, (candidate, 0, position))
                    if value in self.nullable:
                        add(position, (rule, dot + 1, origin))
                    continue
                for following, token_keys, _ in outgoing:
                    if (kind, value) in token_keys or (kind == "X" and ("C", value[0]) in token_keys
                                                       and not any(("T", word) in token_keys for word in value[1])):
                        add(following, (rule, dot + 1, origin))
        if (top, 1, positions[0]) in seen[end]:
            return None
        expected = sorted({rules[rule][1][dot] for rule, dot, _ in sets[furthest]
                           if dot < len(rules[rule][1]) and rules[rule][1][dot][0] != "N"}, key=str)
        found = next((token.text for _, _, token in edges.get(furthest, ())), None)
        shown = ", ".join(f"`{value}`" if kind == "T" else
                          f"{value[0]} except " + " | ".join(f"`{word}`" for word in sorted(value[1]))
                          if kind == "X" else value for kind, value in expected[:12])
        more = f" and {len(expected) - 12} more" if len(expected) > 12 else ""
        what = f"`{found}`" if found is not None else "the end of the text"
        return Failure(furthest, f"the productions derive no text with {what} here; "
                                 f"they expect {shown or 'nothing'}{more}")


def load(root=ROOT, start=START):
    """The grammar of the grammar summary of the book."""
    text = (root / "docs" / GRAMMAR_CHAPTER).read_text(encoding="utf-8")
    grammar = Grammar(read_productions(text), start)
    if grammar.errors:
        raise ValueError(f"docs/{GRAMMAR_CHAPTER}: " + "; ".join(grammar.errors))
    return grammar


def main(argv):
    grammar = load()
    failed = 0
    for name in argv:
        source = Path(name).read_text(encoding="utf-8")
        failure = grammar.parse(source)
        if failure:
            failed += 1
            print(f"{name}:{failure.where(source)}: {failure.message}")
        else:
            print(f"{name}: parsed")
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
