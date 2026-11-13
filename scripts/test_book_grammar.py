"""Regressions for scripts/book_grammar.py: the notation, the tokenizer and the recognizer."""
import textwrap
import unittest

import book_grammar
from book_grammar import Choice, Except, Grammar, Range, Repeat, Sequence, Symbol, Terminal


def grammar(text, start="Start"):
    """A grammar of the lexical forms of the Reference and the given syntactic productions."""
    lexical = textwrap.dedent("""
        ```text
        IDENTIFIER_OR_KEYWORD -> ( ASCII_LETTER | `_` ) ( ASCII_LETTER | ASCII_DIGIT | `_` )*
        IDENTIFIER -> IDENTIFIER_OR_KEYWORD except STRICT_KEYWORD
        ASCII_LETTER -> [`a`-`z`] | [`A`-`Z`]
        ASCII_DIGIT -> [`0`-`9`]
        STRICT_KEYWORD -> `fn` | `if` | `else` | `generic`
        INTEGER_LITERAL -> ASCII_DIGIT+
        FLOAT_LITERAL -> ASCII_DIGIT+ `.` ASCII_DIGIT* | `.` ASCII_DIGIT+
        PUNCTUATION -> `+` | `-` | `*` | `<` | `<=` | `>` | `>=` | `=` | `(` | `)` | `,` | `;` | `.` | `::`
        ```
        """)
    return Grammar(book_grammar.read_productions(lexical + textwrap.dedent(text)), start)


class NotationTests(unittest.TestCase):
    def test_postfix_binds_before_sequence_and_sequence_before_choice(self):
        self.assertEqual(book_grammar.parse_expression("`a` B? | ( `c` D )* `e`+"), Choice((
            Sequence((Terminal("a"), Repeat(Symbol("B"), 0, 1))),
            Sequence((Repeat(Sequence((Terminal("c"), Symbol("D"))), 0, None), Repeat(Terminal("e"), 1, None))),
        )))

    def test_except_ranges_and_punctuation_terminals(self):
        self.assertEqual(book_grammar.parse_expression("IDENTIFIER except `Base` | [`a`-`f`] `||` `*`"), Choice((
            Except(Symbol("IDENTIFIER"), Terminal("Base")),
            Sequence((Range("a", "f"), Terminal("||"), Terminal("*"))),
        )))

    def test_the_notation_renders_back(self):
        for body in ("`a` B? | ( `c` D )* `e`+", "`(` ( Type ( `,` Type )* `,`? )? `)`",
                     "IDENTIFIER except `Base` | `Base` `(` Marker `)`"):
            self.assertEqual(book_grammar.render(book_grammar.parse_expression(body)), body)

    def test_malformed_notation_fails(self):
        for body in ("( `a`", "`a` |", "lowercase", "`a` )", ""):
            with self.assertRaises(ValueError, msg=body):
                book_grammar.parse_expression(body)

    def test_productions_continue_on_indented_lines(self):
        productions = book_grammar.read_productions(textwrap.dedent("""
            Text outside the blocks.

            ```text
            Item -> `fn` Name
                | `mod` Name
            Name ->
                IDENTIFIER
            ```
            """))
        self.assertEqual(list(productions), ["Item", "Name"])
        self.assertEqual(book_grammar.render(productions["Item"]), "`fn` Name | `mod` Name")
        with self.assertRaisesRegex(ValueError, "Name has two productions"):
            book_grammar.read_productions("```text\nName -> `a`\nName -> `b`\n```\n")
        with self.assertRaisesRegex(ValueError, "not a production"):
            book_grammar.read_productions("```text\nA name\n```\n")


class TokenTests(unittest.TestCase):
    def setUp(self):
        self.grammar = grammar("```text\nStart -> IDENTIFIER\n```\n")

    def tokens(self, source):
        return [(token.kind, token.text) for token in self.grammar.tokenize(source)]

    def test_the_longest_token_wins(self):
        self.assertEqual(self.tokens("a<=b <c :: 1.5 .5 7 fn"), [
            ("IDENTIFIER", "a"), ("PUNCTUATION", "<="), ("IDENTIFIER", "b"), ("PUNCTUATION", "<"),
            ("IDENTIFIER", "c"), ("PUNCTUATION", "::"), ("FLOAT_LITERAL", "1.5"), ("FLOAT_LITERAL", ".5"),
            ("INTEGER_LITERAL", "7"), ("KEYWORD", "fn"),
        ])

    def test_comments_whitespace_and_strings_are_read_in_prose(self):
        self.assertEqual(self.tokens('a // ✓ comment\n　"text ✓" b'), [
            ("IDENTIFIER", "a"), ("STRING_LITERAL", '"text ✓"'), ("IDENTIFIER", "b")])
        self.assertEqual(self.tokens('"open'), [("STRING_LITERAL", '"open')])

    def test_a_number_before_a_letter_is_one_malformed_token(self):
        self.assertEqual(self.tokens("1.5f64 7x 0x1"), [("MALFORMED", "1.5f64"), ("MALFORMED", "7x"),
                                                        ("MALFORMED", "0x1")])

    def test_lexical_errors(self):
        for source in ("﻿a", "a b", "a\rb", "é", "a // ‮", "a /* b */", "a @ b"):
            with self.assertRaises(book_grammar.LexError, msg=repr(source)):
                self.grammar.tokenize(source)
        self.assertEqual(self.tokens("a\r\nb"), [("IDENTIFIER", "a"), ("IDENTIFIER", "b")])

    def test_a_terminal_must_be_a_token(self):
        bad = grammar("```text\nStart -> `=>` | `x y`\n```\n")
        self.assertEqual(bad.errors, ["Start: the terminal `=>` is no token of Lexical structure",
                                      "Start: the terminal `x y` is no token of Lexical structure"])

    def test_a_missing_production_is_reported(self):
        self.assertEqual(grammar("```text\nStart -> Missing\n```\n").errors, ["Start: Missing has no production"])
        self.assertIn("the start symbol Begin has no production",
                      grammar("```text\nStart -> `a`\n```\n", start="Begin").errors)


class RecognizerTests(unittest.TestCase):
    EXPRESSIONS = """
        ```text
        Start -> Statement*
        Statement -> `let` IDENTIFIER ( `:` Type )? `=` Expression `;`
        Type -> IDENTIFIER ( `<` IDENTIFIER `>` )?
        Expression -> INTEGER_LITERAL | IDENTIFIER | Expression `(` Arguments? `)`
            | Expression Operator Expression | `-` Expression
        Arguments -> Expression ( `,` Expression )* `,`?
        Operator -> `+` | `*` | `<` | `>`
        Endpoint -> IDENTIFIER except `Base` | `Base` `(` IDENTIFIER `)`
        ```
        """

    def setUp(self):
        self.grammar = grammar(self.EXPRESSIONS.replace("`:`", "`=`").replace("( `=` Type )?", "( `,` Type )?"))
        self.assertEqual(self.grammar.errors, [])

    def test_left_recursion_ambiguity_and_empty_derivations(self):
        for source in ("", "let a = 1;", "let a = f(1, -2 * g(),)(3) + 4 < 5; let b, T<U> = x;"):
            self.assertIsNone(self.grammar.parse(source), source)

    def test_a_failure_names_the_place_and_the_expected_tokens(self):
        source = "let a = 1;\nlet b = (;"
        failure = self.grammar.parse(source)
        self.assertEqual(failure.where(source), "2:9")
        self.assertIn("no text with `(` here", failure.message)
        self.assertIn("INTEGER_LITERAL", failure.message)
        self.assertIn("the end of the text", self.grammar.parse("let a = 1").message)
        self.assertIn("no token", self.grammar.parse("let a = @;").message)

    def test_a_keyword_is_no_identifier(self):
        self.assertIsNotNone(self.grammar.parse("let fn = 1;"))
        self.assertIsNotNone(self.grammar.parse("let a = generic;"))

    def test_split_token_after_type_arguments(self):
        self.assertIsNone(self.grammar.parse("let a, T<U>= 1;"))
        self.assertIsNone(self.grammar.parse("let a = b >= c;".replace(">=", "> -")))

    def test_except_excludes_a_word_of_a_token_class(self):
        for source, derived in (("x", True), ("Base(Q)", True), ("Base", False), ("fn", False)):
            self.assertEqual(self.grammar.parse(source, start="Endpoint") is None, derived, source)

    def test_except_must_exclude_terminals_from_a_token_class(self):
        bad = grammar("```text\nStart -> Name except `a`\nName -> IDENTIFIER\n```\n")
        self.assertEqual(bad.errors, ["Start: Name except `a` must exclude terminals from a token class"])


class BookGrammarTests(unittest.TestCase):
    def test_the_grammar_summary_forms_a_grammar(self):
        loaded = book_grammar.load()
        self.assertEqual(loaded.token_classes, ["FLOAT_LITERAL", "IDENTIFIER", "INTEGER_LITERAL"])
        valid = ("fn main() -> Int { let p: Pair<Int>= pair(1, 2); if a < b { 1 } else { 2 } }\n"
                 "fn g(x: Point<X, Base(QQ)>) -> Int { 0 }\n")
        self.assertIsNone(loaded.parse(valid))
        for invalid in ("fn main() -> Int { if a { 1 } }", "let a = 1;", "fn f() -> Int { 1.5 }"):
            self.assertIsNotNone(loaded.parse(invalid), invalid)
        # `Point<Base, X>` is an indexed type of the productions, which a rule of Types excludes.
        self.assertIsNone(loaded.parse("Point<Base, X>", start="Type"))
        self.assertIsNotNone(loaded.parse("Point<Base, X>", start="PointType"))


if __name__ == "__main__":
    unittest.main()
