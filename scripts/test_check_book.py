"""Regressions for scripts/check_book.py: each case breaks one rule of a valid fixture."""
from pathlib import Path
import subprocess
import tempfile
import textwrap
import unittest

import check_book
from check_book import Chapter


def write(root, files):
    for name, text in files.items():
        path = root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(textwrap.dedent(text).lstrip("\n"), encoding="utf-8")


class Fixture(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.root = Path(self.directory.name)
        self.addCleanup(self.directory.cleanup)


class ContentsTests(Fixture):
    SUMMARY = """
        # Summary

        [Introduction](README.md)

        - [Getting Started](guide/getting-started.md)

        # Vastitas Reference

        - [Notation](language/notation.md)

        # How the compiler is checked

        - [Verification boundaries](verification.md)

        # Appendices

        - [Appendix](appendix/README.md)
          - [G: Glossary](appendix/glossary.md)
        """

    def test_parts_follow_the_part_titles(self):
        write(self.root, {"SUMMARY.md": self.SUMMARY})
        parts = {chapter.path: chapter.part for chapter in check_book.read_contents(self.root)}
        self.assertEqual(parts, {
            "README.md": "guide",
            "guide/getting-started.md": "guide",
            "language/notation.md": "reference",
            "verification.md": "internals",
            "appendix/README.md": "appendix",
            "appendix/glossary.md": "appendix",
        })

    def test_an_unknown_part_title_is_rejected(self):
        write(self.root, {"SUMMARY.md": self.SUMMARY.replace("# Appendices", "# Extras")})
        with self.assertRaisesRegex(ValueError, "unknown part title 'Extras'"):
            check_book.read_contents(self.root)


class TitleTests(Fixture):
    def test_the_first_line_is_the_contents_title(self):
        write(self.root, {"language/notation.md": "# Notation\n", "appendix/glossary.md": "# Appendix G: Glossary\n"})
        chapters = [Chapter("Notation", "language/notation.md", "reference"),
                    Chapter("G: Glossary", "appendix/glossary.md", "appendix")]
        check_book.check_titles(self.root, chapters, frozenset())

    def test_a_different_title_is_rejected(self):
        write(self.root, {"language/notation.md": "\n# Grammar notation\n"})
        chapters = [Chapter("Notation", "language/notation.md", "reference")]
        with self.assertRaisesRegex(ValueError, "must be '# Notation', found '# Grammar notation'"):
            check_book.check_titles(self.root, chapters, frozenset())

    def test_an_appendix_title_names_its_letter(self):
        write(self.root, {"appendix/glossary.md": "# Glossary\n"})
        chapters = [Chapter("G: Glossary", "appendix/glossary.md", "appendix")]
        with self.assertRaisesRegex(ValueError, "Appendix G: Glossary"):
            check_book.check_titles(self.root, chapters, frozenset())

    def test_an_archived_chapter_must_be_listed(self):
        with self.assertRaisesRegex(ValueError, "archived chapters absent from SUMMARY.md"):
            check_book.check_titles(self.root, [], frozenset({"stage1-completion.md"}))

    def test_an_archived_chapter_keeps_its_title_and_its_wording(self):
        write(self.root, {"stage1-completion.md": "# Historical Stage 1 delivery record\n\nThe checker now rejects it.\n",
                          "language/notation.md": "# Notation\n\nA production names a construct.\n"})
        chapters = [Chapter("Stage 1 delivery and performance handoff", "stage1-completion.md", "appendix"),
                    Chapter("Notation", "language/notation.md", "reference")]
        archived = frozenset({"stage1-completion.md"})
        check_book.check_titles(self.root, chapters, archived)
        check_book.check_style(self.root, chapters, archived)

    def test_every_other_chapter_is_checked(self):
        write(self.root, {"guide/later.md": "# Another title\n\nThe checker now rejects it.\n\n## See also\n"})
        chapters = [Chapter("A later chapter", "guide/later.md", "guide")]
        with self.assertRaisesRegex(ValueError, "must be '# A later chapter'"):
            check_book.check_titles(self.root, chapters, frozenset())
        with self.assertRaisesRegex(ValueError, "style guide violations"):
            check_book.check_style(self.root, chapters, frozenset())


class StyleTests(unittest.TestCase):
    def errors(self, text, part="reference", path="language/items.md"):
        return check_book.style_errors(path, textwrap.dedent(text).lstrip("\n"), part)

    def test_banned_words_are_found_in_prose_only(self):
        found = self.errors("""
            The checker now rejects the call.
            A `new` identifier, the word "new" and [a link](new.md) are mentions.

            ```vast
            // a new comment
            ```
            """)
        self.assertEqual(found, ["language/items.md:1: the style guide bans 'now'"])

    def test_should_is_banned_in_the_reference(self):
        self.assertEqual(self.errors("A call should name its target.\n"),
                         ["language/items.md:1: normative text uses must, must not or may, never should"])
        self.assertEqual(self.errors("A call should name its target.\n", part="appendix", path="appendix/a.md"), [])

    def test_protocol_versions_appear_only_in_implementation_notes(self):
        self.assertEqual(len(self.errors("Protocol 7 adds indexed declarations.\n")), 1)
        self.assertEqual(self.errors("""
            > **Implementation note.** The decoder accepts protocol 7
            > and later.
            """), [])
        self.assertEqual(len(self.errors("""
            > **Implementation note.** The decoder runs first.

            Protocol 8 checks vectors.
            """)), 1)

    def test_the_reference_and_the_guide_name_no_stages_or_issues(self):
        for part, path in (("reference", "language/items.md"), ("guide", "guide/a.md")):
            found = self.errors("""
                Stage 1a adds dispatch, as #48 tracks.
                See [the tracker](https://github.com/MGYamada/Vastitas/issues/605).

                ## See also
                """, part, path)
            messages = [error.split(": ", 1)[1] for error in found]
            self.assertIn("the guide and the Reference do not name Stages", messages)
            self.assertEqual(messages.count(
                "issue and pull request references belong in the appendices and internals History sections"), 2)

    def test_internals_link_issues_only_in_history(self):
        text = """
            # Verification

            Proved in [#285](https://github.com/MGYamada/Vastitas/issues/285).

            ## History

            Delivered in [#285](https://github.com/MGYamada/Vastitas/issues/285).
            """
        self.assertEqual(self.errors(text, "internals", "verification.md"),
                         ["verification.md:3: an internals chapter links issues and pull requests only in its History section"])
        self.assertEqual(self.errors(text, "internals", "spec/demo.md"), [])

    def test_the_guide_names_no_hashes_theorems_or_protocols(self):
        found = self.errors("""
            Measured at `cc4922f` and proved by `VastitasOracle.Core.sound`.
            The kernel speaks protocols 2–9. A `Vastitas.toml` manifest is fine.

            ## See also
            """, "guide", "guide/a.md")
        self.assertEqual([error.split(": ", 1)[1] for error in found], [
            "the guide does not cite commit hashes",
            "the guide does not name theorems",
            "the guide does not name wire-protocol versions",
        ])

    def test_a_guide_chapter_ends_with_see_also(self):
        self.assertEqual(self.errors("# A\n\n## See also\n\n## More\n", "guide", "guide/a.md"),
                         ["guide/a.md: a guide chapter ends with a '## See also' section"])
        self.assertEqual(self.errors("# Introduction\n", "guide", "README.md"), [])

    def test_see_also_links_a_reference_chapter(self):
        reference = {"language/items.md", "stage1a.md"}
        check = lambda text, path="guide/a.md": check_book.style_errors(  # noqa: E731
            path, textwrap.dedent(text).lstrip("\n"), "guide", reference)
        self.assertEqual(check("""
            # A

            ## See also

            - [Items](../language/items.md#kinds-of-items) and [dispatch](../stage1a.md)
            """), [])
        self.assertEqual(check("""
            # A

            [Items](../language/items.md) in the body is no See also link.

            ## See also

            - [Another guide chapter](b.md), [the glossary](../appendix/glossary.md#item)
              and [the source](https://github.com/MGYamada/Vastitas/blob/main/src/frontend.rs)
            """), ["guide/a.md: the See also section links no chapter of the Vastitas Reference"])

    def test_see_also_reads_reference_links_and_skips_code_and_comments(self):
        reference = {"language/items.md"}
        check = lambda text: check_book.style_errors(  # noqa: E731
            "guide/a.md", textwrap.dedent(text).lstrip("\n"), "guide", reference)
        missing = ["guide/a.md: the See also section links no chapter of the Vastitas Reference"]
        for linked in ("- [Items][items] and [the glossary][]", "- [Items][]", "- [Items]", "- [the rules] [items]"):
            self.assertEqual(check(f"""
                # A

                ## See also

                {linked}

                [items]: ../language/items.md#kinds-of-items
                [Items]: ../language/items.md
                [the glossary]: ../appendix/glossary.md
                """), [], linked)
        for hidden in ("- `[Items](../language/items.md)` in code",
                       "- <!-- [Items](../language/items.md) -->[Glossary](../appendix/glossary.md)",
                       "- [Items][undefined]",
                       "```text\n[Items](../language/items.md)\n```"):
            self.assertEqual(check(f"# A\n\n## See also\n\n{hidden}\n"), missing, hidden)

    def test_intensifiers_are_banned_in_the_guide_and_the_reference(self):
        text = "The actual call is very simple, and it really runs.\nIt simply works.\n"
        for part, path in (("reference", "language/items.md"), ("guide", "README.md")):
            self.assertEqual([error.split(": ", 1)[1] for error in self.errors(text, part, path)], [
                "the style guide bans the intensifier 'actual'",
                "the style guide bans the intensifier 'very'",
                "the style guide bans the intensifier 'really'",
                "the style guide bans the intensifier 'simply'",
            ])
        # Code, quoted mentions and the other parts are not checked.
        self.assertEqual(self.errors('The word "very" and `actual_size` are mentions.\n'), [])
        self.assertEqual(self.errors(text, "internals", "verification.md"), [])
        self.assertEqual(self.errors(text, "appendix", "appendix/a.md"), [])


class DefinitionTests(unittest.TestCase):
    GLOSSARY = """
        # Appendix G: Glossary

        ## Bound index

        An argument of a field.

        ## Runtime owner

        Its loans are **runtime** loans.

        ## Capability

        A static fact.
        """

    def errors(self, text, part="reference"):
        glossary = check_book.glossary_terms(textwrap.dedent(self.GLOSSARY))
        return check_book.definition_errors("language/items.md", textwrap.dedent(text).lstrip("\n"), part, glossary)

    def test_a_defined_term_has_a_glossary_entry(self):
        self.assertEqual(self.errors("""
            A field applies the family to its **bound indices**. It may require
            **capabilities**, and **`Capability`** is the same term. These loans are **runtime**.
            """), [])

    def test_a_term_without_an_entry_fails(self):
        self.assertEqual(self.errors("A **loan** gives access to a view.\n\n```text\n**not prose**\n```\n"),
                         ["language/items.md:1: the bold term 'loan' has no entry in the glossary "
                          "(appendix/glossary.md)"])

    def test_a_term_that_wraps_across_lines_or_uses_underscores_is_found(self):
        self.assertEqual(self.errors("""
            A field applies the family to its **bound
            indices**, and a **stray
            loan** is a term.

            > A quoted **wrapped
            > term** and __another
            > stray__ term.

            A `**` or `__x__` in code marks nothing, and a list item ends the paragraph:

            - one **item
            - two** items
            """), [
            "language/items.md:2: the bold term 'stray loan' has no entry in the glossary (appendix/glossary.md)",
            "language/items.md:5: the bold term 'wrapped term' has no entry in the glossary (appendix/glossary.md)",
            "language/items.md:6: the bold term 'another stray' has no entry in the glossary (appendix/glossary.md)",
        ])

    def test_the_paragraphs_of_a_chapter(self):
        text = "# Title\n\nOne\ntwo\n> quoted\n> on\n\n```text\ncode\n```\nafter\n| a | b |\n- item\n  wrapped\n"
        self.assertEqual([[number for number, _ in paragraph] for paragraph in check_book.paragraphs(text)],
                         [[1], [3, 4], [5, 6], [11], [12], [13, 14]])

    def test_labels_and_rule_words_are_no_definitions(self):
        self.assertEqual(self.errors("""
            > **Syntax**

            > **Implementation note.** The kernel checks it.

            - **must** and **must not** state a requirement, and **may** a permission.
            - **is an error (`E_CODE`)** gives the code.
            """), [])

    def test_only_the_reference_is_checked(self):
        self.assertEqual(self.errors("A **loan** gives access.\n", "guide"), [])
        self.assertEqual(self.errors("**Acceptance example.** A loan.\n", "appendix"), [])

    def test_the_book_glossary_reads_its_entries(self):
        terms = check_book.glossary_terms((check_book.ROOT / "docs" / check_book.GLOSSARY).read_text())
        self.assertTrue({"abstract method", "loan", "fast like c", "lies within"} <= terms)


class IncludeTests(Fixture):
    def setUp(self):
        super().setUp()
        write(self.root, {
            "examples/book/a.vast": "// ANCHOR: main\nfn main() -> Int { 42 }\n// ANCHOR_END: main\n",
        })
        self.source = self.root / "docs"
        self.source.mkdir()

    def errors(self, text):
        return check_book.include_errors("guide/a.md", text, self.source)

    def test_includes_resolve_files_anchors_and_lines(self):
        self.assertEqual(self.errors("{{#include ../../examples/book/a.vast}}\n"
                                     "{{#include ../../examples/book/a.vast:main}}\n"
                                     "{{#include ../../examples/book/a.vast:2:3}}\n"
                                     "\\{{#include ../../examples/book/absent.vast}}\n"), [])

    def test_a_missing_file_anchor_or_line_fails(self):
        found = self.errors("{{#include ../../examples/book/absent.vast}}\n"
                            "{{#include ../../examples/book/a.vast:other}}\n"
                            "{{#include ../../examples/book/a.vast:2:9}}\n")
        self.assertEqual(len(found), 3)
        self.assertIn("no such file", found[0])
        self.assertIn("no ANCHOR/ANCHOR_END pair named 'other'", found[1])
        self.assertIn("the file has 3 lines", found[2])

    def test_a_complete_program_must_be_included(self):
        text = "```vast\nfn main() -> Int { 42 }\n```\n\n> ```text\n> fn main() -> Int { 0 }\n> ```\n\n" \
               "```vast\n{{#include ../../examples/book/a.vast}}\n```\n\n```sh\nprintf 'fn main() -> Int {}'\n```\n" \
               "\n```vast\npub resource fn main() -> Int { 0 }\n```\n"
        self.assertEqual([error.split(": ")[0] for error in check_book.program_errors("guide/a.md", text)],
                         ["guide/a.md:1", "guide/a.md:5", "guide/a.md:17"])

    def test_a_complete_function_must_be_included(self):
        text = "```vast\nfn sign(x: Int) -> Int {\n    x\n}\n```\n\n" \
               "```vast\nresource fn copy() -> Unit {\n    value { () }\n}\n```\n\n" \
               "```vast\nlet f = fn(x: Int) -> Int { x };\nlet s = if x < 0 { -1 } else { 1 };\n```\n\n" \
               "```vast\n{{#include ../../examples/book/a.vast:main}}\n```\n\n" \
               "```toml\nfn = 1\n```\n"
        self.assertEqual([error.split(": ")[0] for error in check_book.program_errors("guide/a.md", text)],
                         ["guide/a.md:1", "guide/a.md:7"])
        self.assertIn("a complete function or method is included", check_book.program_errors("guide/a.md", text)[0])

    def test_a_complete_method_or_a_signature_with_a_body_is_found(self):
        def found(block):
            return check_book.program_errors("guide/a.md", f"```vast\n{block}\n```\n")

        for block in ("method area(x: Int) -> Int requires (HasOrder) {\n    x\n}",
                      "generic area(x) {\n    domain (Int);\n}\n\nmethod area(x: Int) -> Int { x }",
                      "method geo::area(x: Int)\n    -> Int\n{\n    x\n}",
                      "resource fn copy(\n    a: Read<F64, 1, 1>,\n) returns (b: Owned<F64, 1>) -> Unit {\n"
                      "    value { () }\n}"):
            self.assertEqual(len(found(block)), 1, block)
            self.assertIn("a complete function or method is included", found(block)[0])
        for block in ("abstract method area(x: Int) -> Int {\n    domain (Int);\n}",
                      "generic area(x) {\n    domain (Int);\n}",
                      "fn area(x: Int) -> Int\n\nlet y = { 1 };",
                      "fn area(x: Int) -> Int;\n{ }",
                      "fn area(x: Int) -> Int\nlet y = { 1 };",
                      "let f = fn(x: Int) -> Int { x };"):
            self.assertEqual(found(block), [], block)

    def test_a_diagnostic_in_any_block_and_a_place_with_spaces(self):
        for block in ("```\nexamples/reject/a.vast:2:5: E_TYPE: expected Int\n```\n",
                      "```console\n$ vastitas check a.vast\na.vast:1:1: E_PARSE: expected `}`\n```\n",
                      "```text\nmy examples/a b.vast:1:1: E_NAME: unknown name\n```\n"):
            self.assertEqual(len(check_book.program_errors("guide/a.md", block)), 1, block)
        self.assertEqual(check_book.program_errors("guide/a.md", "```sh\necho 'a.vast:1:1: E_X: y'\n```\n"), [])

    def test_a_diagnostic_must_be_included_from_its_stderr_file(self):
        typed = "```text\nexamples/reject/a.vast:2:5: E_TYPE: expected Int, found Nat\n```\n"
        found = check_book.program_errors("guide/a.md", typed)
        self.assertEqual(found, ["guide/a.md:1: the diagnostic of a rejected program is included from its "
                                 ".stderr file (style guide, Examples)"])
        for text in (
            "```text\n{{#include ../../examples/reject/a.stderr}}\n```\n",
            # The forms of the diagnostic lines and a diagnostic without a place, about a command.
            "```text\nFILE:LINE:COLUMN: CODE: message\nMANIFEST: E_MANIFEST: message\n"
            "E_USAGE: unknown option --fast\n```\n",
            # A diagnostic in prose or in a shell block is no typed output.
            "The line `a.vast:1:1: E_TYPE: x` names the place.\n\n```sh\necho 'a.vast:1:1: E_X: y'\n```\n",
        ):
            self.assertEqual(check_book.program_errors("guide/a.md", text), [], text)
        manifest = "> ```text\n> examples/reject/packages/p/Vastitas.toml: E_MANIFEST: TOML parse error\n> ```\n"
        self.assertEqual(len(check_book.program_errors("guide/a.md", manifest)), 1)

    def test_an_include_selects_by_anchor(self):
        text = "{{#include ../../examples/book/a.vast:main}}\n{{#include ../../examples/book/a.vast}}\n" \
               "{{#include ../../examples/book/a.vast:2:3}}\n{{#include ../../examples/book/a.vast:2}}\n" \
               "\\{{#include ../../examples/book/a.vast:4:5}}\n"
        found = check_book.program_errors("guide/a.md", text)
        self.assertEqual(len(found), 2)
        self.assertIn("{{#include ../../examples/book/a.vast:2:3}} selects lines", found[0])
        self.assertIn("{{#include ../../examples/book/a.vast:2}} selects lines", found[1])

    def test_every_book_example_is_included(self):
        write(self.source, {"guide/a.md": "```vast\n{{#include ../../examples/book/a.vast}}\n```\n"})
        chapters = [Chapter("A", "guide/a.md", "guide")]
        check_book.check_includes(self.source, chapters, self.root)
        write(self.root, {"examples/book/.DS_Store": "metadata",
                          "examples/reject/packages/p/Vastitas.toml": "[package]\n"})
        check_book.check_includes(self.source, chapters, self.root)
        write(self.root, {"examples/book/Vastitas.toml": "[package]\n"})
        with self.assertRaisesRegex(ValueError, "examples/book/Vastitas.toml: no chapter includes"):
            check_book.check_includes(self.source, chapters, self.root)
        (self.root / "examples/book/Vastitas.toml").unlink()
        write(self.root, {"examples/reject/b.vast": "fn main() -> Int { true }\n"})
        with self.assertRaisesRegex(ValueError, "examples/reject/b.vast: no chapter includes this example"):
            check_book.check_includes(self.source, chapters, self.root)


class SyntaxTests(Fixture):
    LEXER = '''
        let x = if let Some(op) = ["->", "::"]
        } else if "(){},;".contains(ch) {
        token.is("fn") || token.is("pub")
        '''

    def setUp(self):
        super().setUp()
        write(self.root, {"src/frontend.rs": self.LEXER, "src/frontend/items.rs": 'consume("mod")\n'})
        self.source = self.root / "docs"

    def errors(self, chapters):
        write(self.source, chapters)
        listed = [Chapter(name, name, "reference" if name.startswith("language/") else "guide") for name in chapters]
        return check_book.syntax_errors(listed, self.source, self.root, pending=frozenset({"Pending"}))[0]

    BLOCK = """
        > **Syntax**
        >
        > ```text
        > Function -> `pub`? `fn` IDENTIFIER `(` `)` Block
        > Block -> `{` `}`
        >     | `{` Module `}`
        > Module -> `mod` IDENTIFIER `;`
        > IDENTIFIER -> ASCII_LETTER+
        > ASCII_LETTER -> `a` | `b`
        > ```
        """

    def test_a_valid_block_passes(self):
        self.assertEqual(self.errors({"language/items.md": self.BLOCK}), [])

    def test_an_unknown_terminal_fails(self):
        found = self.errors({"language/items.md": self.BLOCK.replace("`mod`", "`module`")})
        self.assertEqual(len(found), 1)
        self.assertIn("has no token `module`", found[0])

    def test_unknown_punctuation_fails(self):
        found = self.errors({"language/items.md": self.BLOCK.replace("`;`", "`=>`")})
        self.assertIn("has no token `=>`", found[0])

    def test_an_undefined_nonterminal_fails(self):
        found = self.errors({"language/items.md": self.BLOCK.replace("Block -> `{` `}`", "Block -> `{` Statement `}`")})
        self.assertEqual(found, ["language/items.md:5: Statement has no production in the Vastitas Reference"])

    def test_a_nonterminal_is_defined_once(self):
        found = self.errors({"language/items.md": self.BLOCK,
                             "language/modules.md": "> **Syntax**\n>\n> ```text\n> Module -> `mod` `;`\n> ```\n"})
        self.assertIn("Module is also defined at language/items.md:7", found[0])

    def test_syntax_blocks_belong_in_the_reference(self):
        found = self.errors({"guide/a.md": "> **Syntax**\n>\n> ```text\n> Block -> `{` `}`\n> ```\n"})
        self.assertEqual(found, ["guide/a.md: Syntax blocks belong in the Vastitas Reference"])

    def test_a_syntax_block_holds_productions_only(self):
        found = self.errors({"language/items.md": "> **Syntax**\n>\n> ```text\n> A function declaration\n> ```\n"})
        self.assertIn("not a production", found[0])

    def test_a_defined_nonterminal_leaves_the_pending_list(self):
        found = self.errors({"language/items.md": "> **Syntax**\n>\n> ```text\n> Pending -> `fn`\n> ```\n"})
        self.assertEqual(found, ["language/items.md:4: Pending is defined; remove it from PENDING_NONTERMINALS"])

    def test_the_real_parser_vocabulary_is_found(self):
        symbols, names = check_book.parser_vocabulary(check_book.ROOT)
        self.assertTrue({"->", "::", "(", ";", "^"} <= symbols)
        self.assertTrue({"fn", "pub", "use", "indexed", "generic"} <= names)


class GrammarTests(Fixture):
    LEXER = SyntaxTests.LEXER
    ITEMS = """
        # Items

        > **Syntax**
        >
        > ```text
        > Item -> Function
        > ```

        ## `fn` items

        > **Syntax**
        >
        > ```text
        > Function -> `pub`? `fn` IDENTIFIER `(` `)`
        >     `;`
        > IDENTIFIER -> ASCII_LETTER+
        > ASCII_LETTER -> `a` | `b`
        > ```

        ## Rules

        ```text
        ## Not a heading
        ```

        ## Rules

        > **Syntax**
        >
        > ```text
        > Module -> `mod` IDENTIFIER `;`
        > ```
        """
    NOTATION = """
        # Notation

        > **Syntax**
        >
        > ```text
        > Item -> `fn`
        > ```
        """

    def setUp(self):
        super().setUp()
        import grammar_summary
        self.grammar = grammar_summary
        write(self.root, {"src/frontend.rs": self.LEXER, "src/frontend/items.rs": 'consume("mod")\n'})
        self.source = self.root / "docs"
        write(self.source, {"language/notation.md": self.NOTATION, "language/items.md": self.ITEMS,
                            "guide/a.md": "# A\n"})
        self.chapters = [Chapter("A", "guide/a.md", "guide"),
                         Chapter("Notation", "language/notation.md", "reference"),
                         Chapter("Items", "language/items.md", "reference"),
                         Chapter("H: Grammar summary", "appendix/grammar.md", "appendix")]

    def generate(self):
        text, count = self.grammar.render(self.source, self.chapters)
        write(self.source, {"appendix/grammar.md": text})
        return text, count

    def test_the_summary_holds_the_productions_by_chapter_and_section(self):
        text, count = self.generate()
        self.assertEqual(count, 5)
        self.assertTrue(text.startswith("# Appendix H: Grammar summary\n"))
        self.assertIn("## Items\n\nChapter: [Items](../language/items.md).\n\n```text\nItem -> Function\n```\n", text)
        self.assertIn("[`fn` items](../language/items.md#fn-items):\n\n```text\n"
                      "Function -> `pub`? `fn` IDENTIFIER `(` `)`\n    `;`\n", text)
        # A repeated heading has the id that mdBook gives it, and a heading in a code block is none.
        self.assertIn("[Rules](../language/items.md#rules-1):\n\n```text\nModule -> `mod` IDENTIFIER `;`\n```\n", text)
        # The illustration of the notation chapter is no production of the language.
        self.assertNotIn("notation.md)", text.replace("notation.md#grammar)", ""))
        self.assertTrue(text.endswith("```\n"))

    def test_a_fresh_summary_passes_and_defines_nothing(self):
        self.generate()
        self.assertEqual(self.grammar.errors(self.source, self.chapters), [])
        check_book.check_grammar(self.source, self.chapters)
        # The summary holds no Syntax block, so its productions are no second definitions.
        self.assertEqual(list(check_book.syntax_blocks((self.source / "appendix/grammar.md").read_text())), [])
        self.assertEqual(check_book.syntax_errors(self.chapters, self.source, self.root), ([], 5))

    def test_a_stale_or_missing_summary_fails(self):
        self.assertEqual(self.grammar.errors(self.source, self.chapters),
                         ["appendix/grammar.md: missing; run `python3 scripts/grammar_summary.py --write`"])
        self.generate()
        write(self.source, {"language/items.md": self.ITEMS.replace("`mod` IDENTIFIER", "`pub`? `mod` IDENTIFIER")})
        self.assertEqual(self.grammar.errors(self.source, self.chapters),
                         ["appendix/grammar.md: out of date; run `python3 scripts/grammar_summary.py --write`"])
        with self.assertRaisesRegex(ValueError, "the grammar summary is not fresh"):
            check_book.check_grammar(self.source, self.chapters)
        self.generate()
        # An edit of the generated chapter by hand is stale too.
        path = self.source / "appendix/grammar.md"
        path.write_text(path.read_text() + "\nItem -> Module\n")
        self.assertEqual(len(self.grammar.errors(self.source, self.chapters)), 1)

    def test_the_summary_must_be_listed(self):
        self.assertEqual(self.grammar.errors(self.source, self.chapters[:-1]),
                         ["SUMMARY.md does not list appendix/grammar.md"])


class ParseTests(Fixture):
    GRAMMAR = """
        ```text
        SourceFile -> Item*
        Item -> `fn` IDENTIFIER `(` `)` `{` INTEGER_LITERAL `}`
        IDENTIFIER_OR_KEYWORD -> ( ASCII_LETTER | `_` ) ( ASCII_LETTER | ASCII_DIGIT | `_` )*
        IDENTIFIER -> IDENTIFIER_OR_KEYWORD except STRICT_KEYWORD
        ASCII_LETTER -> [`a`-`z`] | [`A`-`Z`]
        ASCII_DIGIT -> [`0`-`9`]
        STRICT_KEYWORD -> `fn`
        INTEGER_LITERAL -> ASCII_DIGIT+
        FLOAT_LITERAL -> ASCII_DIGIT+ `.` ASCII_DIGIT*
        PUNCTUATION -> `(` | `)` | `{` | `}` | `<`
        ```
        """

    def setUp(self):
        super().setUp()
        import book_grammar
        self.grammar = book_grammar.Grammar(book_grammar.read_productions(textwrap.dedent(self.GRAMMAR)))
        self.assertEqual(self.grammar.errors, [])
        write(self.root, {
            "examples/book/a.vast": "// A comment.\nfn a() { 1 }\n",
            "examples/packages/p/src/main.vast": "fn b() { 2 } fn c() { 3 }\n",
            "examples/reject/syntax/open.vast": "fn a() { 1\n",
            "examples/reject/syntax/open.stderr": "examples/reject/syntax/open.vast:2:1: E_PARSE: expected `}`\n",
            "examples/reject/types/wrong.vast": "fn a() { 1 }\n",
            "examples/reject/types/wrong.stderr": "examples/reject/types/wrong.vast:1:10: E_TYPE: expected Bool\n"
                                                  "examples/reject/types/wrong.vast:1:1: note: declared here\n",
            "examples/reject/types/name.vast": "fn a() { b }\n",
            "examples/reject/types/name.stderr": "examples/reject/types/name.vast:1:10: E_UNSUPPORTED: b\n",
        })

    def errors(self, exceptions=None):
        return check_book.parse_errors(self.root, self.grammar, exceptions or {}, ("examples",))

    def test_accepted_and_rejected_files(self):
        errors, parsed, rejected, skipped = self.errors()
        self.assertEqual((errors, parsed, rejected), ([], 3, 1))
        self.assertEqual(len(skipped), 1)
        self.assertIn("examples/reject/types/name.vast: E_UNSUPPORTED", skipped[0])

    def test_a_file_that_the_productions_do_not_derive_fails(self):
        write(self.root, {"examples/book/b.vast": "fn b() { x }\n"})
        errors = self.errors()[0]
        self.assertEqual(len(errors), 1)
        self.assertTrue(errors[0].startswith("examples/book/b.vast:1:10: the productions derive no text with `x`"))

    def test_a_parse_error_that_the_productions_derive_fails(self):
        write(self.root, {"examples/reject/syntax/open.vast": "fn a() { 1 }\n"})
        self.assertEqual(self.errors()[0], ["examples/reject/syntax/open.vast: the compiler reports E_PARSE, "
                                            "but the productions derive the file"])

    def test_an_exception_names_its_rule_and_must_hold(self):
        rule = "Expressions: the rule"
        errors, _, rejected, skipped = self.errors({"examples/reject/syntax/open.vast": (False, rule)})
        self.assertEqual((errors, rejected), ([], 0))
        self.assertIn(f"examples/reject/syntax/open.vast: {rule}", skipped)
        errors = self.errors({"examples/reject/syntax/open.vast": (True, rule)})[0]
        self.assertIn("PARSE_EXCEPTIONS says that the productions derive the file", errors[0])

    def test_the_book_examples_parse(self):
        check_book.check_parse(check_book.ROOT / "docs")


class LimitTests(unittest.TestCase):
    LIMITS = {"parseNesting": 64, "elaborationWork": 1000000}
    TABLE = """
        | Limit | Value | Counts |
        | --- | --- | --- |
        | `parseNesting` | 64 | Levels |
        | `value` blocks | 4096 | Blocks |
        | Loaded files | 8192 | Files |
        | `elaborationWork` | 1,000,000 | Units |
        | `elaborationWork` | 1,000,000 | The same limit in a second table |
        """

    def errors(self, table, limits=None):
        return check_book.limit_errors(textwrap.dedent(table), limits or self.LIMITS)

    def test_rows_with_the_values_of_the_file_pass(self):
        self.assertEqual(self.errors(self.TABLE), [])

    def test_another_value_fails(self):
        self.assertEqual(self.errors(self.TABLE.replace("| 64 |", "| 65 |")),
                         ["appendix/limits.md:4: `parseNesting` is 64 in lean-kernel/compiler-limits.json, not 65"])

    def test_every_row_of_a_key_carries_the_value_of_the_file(self):
        second = "| `elaborationWork` | 1,000,000 | The same limit in a second table |"
        self.assertEqual(self.errors(self.TABLE.replace(second, second.replace("1,000,000", "2,000,000"))),
                         ["appendix/limits.md:8: `elaborationWork` is 1000000 in lean-kernel/compiler-limits.json, "
                          "not 2000000"])
        # A value in another form is no value of the file: the row is not skipped.
        for form in ("1 million", "10^6", "1,000,000 units", "1000,000", ""):
            found = self.errors(self.TABLE.replace(second, second.replace("1,000,000", form)))
            self.assertEqual(found, ["appendix/limits.md:8: the value of `elaborationWork` must be the number "
                                     f"1000000 of lean-kernel/compiler-limits.json, not {form!r}"], form)
        # A row of a name that is no key and has no number is not a row of a limit.
        self.assertEqual(self.errors(self.TABLE + "| `E_LIMIT` | A program beyond a limit | Code |\n"), [])

    def test_a_missing_or_an_unknown_key_fails(self):
        self.assertEqual(self.errors(self.TABLE, {**self.LIMITS, "astDepth": 128}),
                         ["appendix/limits.md: no row gives the limit `astDepth` of lean-kernel/compiler-limits.json"])
        self.assertEqual(self.errors(self.TABLE.replace("`parseNesting`", "`parseDepth`")), [
            "appendix/limits.md:4: `parseDepth` is no key of lean-kernel/compiler-limits.json",
            "appendix/limits.md: no row gives the limit `parseNesting` of lean-kernel/compiler-limits.json",
        ])

    def test_the_appendix_agrees_with_the_limits_file(self):
        check_book.check_limits(check_book.ROOT / "docs")


class RedirectTests(Fixture):
    def setUp(self):
        super().setUp()
        self.output = (self.root / "book").resolve()
        write(self.output, {"old.html": "<p>Redirecting</p>", "language/new.html": '<h2 id="rules">Rules</h2>'})
        self.source = self.root / "docs"
        write(self.source, {"language/new.md": "# New\n"})
        self.pages = {path: check_book.Page(path) for path in self.output.rglob("*.html")}

    def errors(self, redirects):
        config = {"output": {"html": {"redirect": redirects}}}
        return check_book.redirect_errors(self.pages, self.output, config, self.source)[0]

    def test_a_redirect_leads_to_a_page_and_anchor(self):
        self.assertEqual(self.errors({"/old.html": "language/new.html",
                                      "/old.html#a": "language/new.html#rules"}), [])

    def test_a_broken_redirect_fails(self):
        self.assertEqual(self.errors({"/old.html#a": "language/new.html#absent",
                                      "/old.html#b": "language/absent.html",
                                      "/gone.html": "language/new.html"}), [
            "book.toml: /old.html#a redirects to a missing anchor language/new.html#absent",
            "book.toml: /old.html#b redirects to a missing page language/absent.html",
            "book.toml: the redirect page for /gone.html was not rendered",
        ])

    def test_a_redirect_target_is_relative_to_the_retired_page(self):
        write(self.output, {"guide/old.html": "<p>Redirecting</p>"})
        self.pages = {path: check_book.Page(path) for path in self.output.rglob("*.html")}
        self.assertEqual(self.errors({"/guide/old.html": "../language/new.html#rules"}), [])
        self.assertEqual(self.errors({"/guide/old.html": "language/new.html"}),
                         ["book.toml: /guide/old.html redirects to a missing page language/new.html"])

    def test_a_redirect_must_not_hide_a_chapter(self):
        write(self.source, {"old.md": "# Old\n"})
        self.assertEqual(self.errors({"/old.html": "language/new.html"}),
                         ["book.toml: /old.html redirects a chapter that still exists"])


class LinkTests(Fixture):
    def test_repository_links_resolve_on_main(self):
        good = "https://github.com/MGYamada/Vastitas/blob/main/scripts/check_book.py#L1-L2"
        self.assertEqual(check_book.repository_errors(good), [])
        self.assertEqual(check_book.repository_errors("https://github.com/MGYamada/Vastitas/issues/605"), [])
        absent = "https://github.com/MGYamada/Vastitas/blob/main/scripts/absent.py"
        self.assertIn("absent repository target", check_book.repository_errors(absent)[0])
        beyond = "https://github.com/MGYamada/Vastitas/blob/main/scripts/check_book.py#L100000"
        self.assertIn("line range beyond the end", check_book.repository_errors(beyond)[0])

    def test_repository_links_at_a_revision_resolve_in_the_history(self):
        head = subprocess.run(["git", "-C", str(check_book.ROOT), "rev-parse", "HEAD"],
                              capture_output=True, text=True, check=True).stdout.strip()
        present = f"https://github.com/MGYamada/Vastitas/blob/{head}/scripts/check_book.py"
        self.assertEqual(check_book.repository_errors(present), [])
        absent = f"https://github.com/MGYamada/Vastitas/blob/{head}/scripts/absent.py"
        self.assertIn("absent repository target at", check_book.repository_errors(absent)[0])
        missing = "https://github.com/MGYamada/Vastitas/blob/" + "0" * 40 + "/README.md"
        self.assertIn("absent repository target at", check_book.repository_errors(missing)[0])

    def test_references_from_outside_the_book_resolve(self):
        output = (self.root / "book").resolve()
        write(output, {"stage1a.html": '<h2 id="abstract-types">Abstract types</h2>'})
        write(self.root, {
            "docs/stage1a.md": "# Stage 1a\n",
            "tests/a.rs": "// docs/stage1a.md#abstract-types and docs/SUMMARY.md\n"
                          "// docs/stage1a.md#absent and docs/stage0.md\n"
                          "// ../../docs/stage1a.md and vendor/docs/notes.md\n",
        })
        pages = {output / "stage1a.html": check_book.Page(output / "stage1a.html")}
        errors, count = check_book.reference_errors([self.root / "tests/a.rs"], pages, self.root, output)
        self.maxDiff = None
        self.assertEqual(count, 5)
        self.assertEqual(errors, ["tests/a.rs:2: docs/stage1a.md has no anchor #absent",
                                  "tests/a.rs:2: docs/stage0.md is not a chapter of the book"])


class PathTests(Fixture):
    FILES = ["scripts/check_book.py", "tests/examples.rs", "src/frontend.rs", "src/frontend/items.rs",
             "docs/guide/a.md", "lean-kernel/VastitasKernel/Core.lean"]

    def errors(self, text, untracked=None):
        write(self.root, {"guide/a.md": text})
        return check_book.path_errors([Chapter("A", "guide/a.md", "guide")], self.root, self.FILES,
                                      {} if untracked is None else untracked)

    def test_tracked_files_and_directories_pass(self):
        text = """
            Run `python3 scripts/check_book.py` and read `tests/examples.rs::book_programs`,
            `src/frontend.rs:12`, `docs/guide/a.md#see-also`, `lean-kernel/` and `scripts`.
            """
        self.assertEqual(self.errors(text), ([], 5))

    def test_a_missing_path_fails(self):
        text = "See `docs/numerical-adapter.md`\nand run `python3 scripts/absent.py --check`.\n"
        self.assertEqual(self.errors(text), ([
            "guide/a.md:1: `docs/numerical-adapter.md` names no file or directory that Git tracks",
            "guide/a.md:2: `scripts/absent.py` names no file or directory that Git tracks",
        ], 2))

    def test_package_sources_patterns_and_code_blocks_name_no_path(self):
        text = """
            A package keeps `src/lib.vast` and `src/shapes/`, but `src/absent.rs` is a path.
            The specifications are `docs/spec/<name>.toml`, tested by `scripts/test_*.py`.

            ```sh
            python3 scripts/absent.py
            ```
            """
        self.assertEqual(self.errors(text), (
            ["guide/a.md:1: `src/absent.rs` names no file or directory that Git tracks"], 1))

    def test_an_untracked_path_needs_an_entry_that_a_chapter_uses(self):
        text = "The kernel is `lean-kernel/.lake/build/bin/vastitas-kernel`.\n"
        self.assertEqual(self.errors(text), (
            ["guide/a.md:1: `lean-kernel/.lake/build/bin/vastitas-kernel` names no file or directory that Git tracks"],
            1))
        self.assertEqual(self.errors(text, {"lean-kernel/.lake": "the build directory"}), ([], 0))
        self.assertEqual(self.errors(text, {"lean-kernel/.lake": "the build directory", "stdlib/target": "generated"}),
                         (["UNTRACKED_PATHS: no chapter names stdlib/target; remove the entry"], 0))
        self.assertEqual(self.errors(text, {"lean-kernel/.lake": "the build directory", "src/frontend": "tracked"}),
                         (["UNTRACKED_PATHS: Git tracks src/frontend; remove the entry"], 0))


if __name__ == "__main__":
    unittest.main()
