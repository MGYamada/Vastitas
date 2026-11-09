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
        check_book.check_titles(self.root, chapters, frozenset({"language/notation.md", "appendix/glossary.md"}))

    def test_a_different_title_is_rejected(self):
        write(self.root, {"language/notation.md": "\n# Grammar notation\n"})
        chapters = [Chapter("Notation", "language/notation.md", "reference")]
        with self.assertRaisesRegex(ValueError, "must be '# Notation', found '# Grammar notation'"):
            check_book.check_titles(self.root, chapters, frozenset({"language/notation.md"}))

    def test_an_appendix_title_names_its_letter(self):
        write(self.root, {"appendix/glossary.md": "# Glossary\n"})
        chapters = [Chapter("G: Glossary", "appendix/glossary.md", "appendix")]
        with self.assertRaisesRegex(ValueError, "Appendix G: Glossary"):
            check_book.check_titles(self.root, chapters, frozenset({"appendix/glossary.md"}))

    def test_a_converted_chapter_must_be_listed(self):
        with self.assertRaisesRegex(ValueError, "absent from SUMMARY.md"):
            check_book.check_titles(self.root, [], frozenset({"language/lexical-structure.md"}))


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

    def test_every_book_example_is_included(self):
        write(self.source, {"guide/a.md": "```vast\n{{#include ../../examples/book/a.vast}}\n```\n"})
        chapters = [Chapter("A", "guide/a.md", "guide")]
        check_book.check_includes(self.source, chapters, self.root)
        write(self.root, {"examples/book/.DS_Store": "metadata"})
        check_book.check_includes(self.source, chapters, self.root)
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
        return check_book.syntax_errors(listed, self.source, self.root, pending=frozenset())[0]

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

    def test_the_real_parser_vocabulary_is_found(self):
        symbols, names = check_book.parser_vocabulary(check_book.ROOT)
        self.assertTrue({"->", "::", "(", ";", "^"} <= symbols)
        self.assertTrue({"fn", "pub", "use", "indexed", "generic"} <= names)


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


if __name__ == "__main__":
    unittest.main()
