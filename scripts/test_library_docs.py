"""The API reference pages of the libraries against the exports of their modules."""
import tempfile
import unittest
from pathlib import Path

import build_stdlib_package as generator
import library_docs

TABLE = "| Name | Kind | Contract |\n| --- | --- | --- |\n"


def row(name, kind="primitive"):
    return f"| `{name}` | {kind} | A contract |\n"


class LibraryDocsTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)

    def write(self, path, text):
        target = self.root / path
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(text, encoding="utf-8")

    def nature(self, page):
        """A nature library with one library package, whose page has the given rows.

        The root module lies outside src/, at the root that the manifest names.
        """
        self.write("nature/Vastitas.toml", '[package]\nname = "n"\nversion = "0.1.0"\nroot = "lib.vast"\n')
        self.write("nature/lib.vast", "// The root.\npub use dimension_library as dimension;\n")
        self.write("nature/src/dimension/mod.vast",
                   "// pub indexed base_dimension Hidden; is a comment.\n"
                   "pub indexed family Reading(object(K))\n    = reading constraints(canonical(0));\n"
                   "pub indexed base_dimension L;\nindexed base_dimension Private;\n")
        self.write("nature/docs/README.md", TABLE + row("dimension", "module"))
        self.write("nature/docs/dimension.md", "# `nature::dimension`\n\n" + TABLE + page)

    def errors(self, libraries=("nature",)):
        return library_docs.check(self.root, libraries)[0]

    def test_the_repository_pages_list_every_export(self):
        errors, pages, names = library_docs.check()
        self.assertEqual(errors, [])
        self.assertGreater(pages, 0)
        self.assertGreater(names, 0)

    def test_matching_pages_pass(self):
        self.nature(row("Reading<X>", "family") + row("L", "base dimension"))
        self.assertEqual(self.errors(), [])

    def test_a_missing_name_fails(self):
        self.nature(row("Reading<X>", "family"))
        self.assertEqual(self.errors(), [
            "nature/docs/dimension.md: nature/src/dimension/mod.vast exports L, which the page does not list"])

    def test_an_extra_name_fails(self):
        # Neither a private declaration nor a name in a comment is an export.
        for extra in ("Private", "Hidden", "Speed"):
            with self.subTest(extra=extra):
                self.nature(row("Reading<X>", "family") + row("L", "base dimension") + row(extra, "quantity"))
                self.assertEqual(self.errors(), [
                    f"nature/docs/dimension.md:7: {extra} is not exported by nature/src/dimension/mod.vast"])

    def test_a_missing_page_and_a_page_of_no_module_fail(self):
        self.nature(row("Reading<X>", "family") + row("L", "base dimension"))
        (self.root / "nature/docs/dimension.md").rename(self.root / "nature/docs/units.md")
        errors = self.errors()
        self.assertIn("nature/docs/dimension.md: missing; it lists the exports of nature/src/dimension/mod.vast",
                      errors)
        self.assertIn("nature/docs/units.md: lists the exports of no module of nature", errors)

    def test_malformed_rows_unread_items_and_broken_links_fail(self):
        self.nature("| Reading | family | A contract |\n" + row("L", "base dimension"))
        self.write("nature/src/dimension/mod.vast", "pub indexed family Reading(object(K)) = reading;\n"
                   "pub indexed base_dimension L;\n    pub fn indented() -> Int { 0 }\n")
        self.write("nature/README.md", "[the page](docs/missing.md) and [the book](https://example.org/x.md)\n")
        errors = self.errors()
        self.assertTrue(any("dimension.md: line 5: a row needs one code span" in error for error in errors), errors)
        self.assertTrue(any("mod.vast: line 3: this check reads no public item here" in error for error in errors),
                        errors)
        self.assertIn("nature/README.md:1: the link docs/missing.md names no file", errors)

    def test_the_root_file_outside_src_has_the_root_page(self):
        self.nature(row("Reading<X>", "family") + row("L", "base dimension"))
        self.write("nature/lib.vast", "pub use dimension_library as dimension;\npub use other_library as other;\n")
        self.assertEqual(self.errors(), [
            "nature/docs/README.md: nature/lib.vast exports other, which the page does not list"])

    def test_generated_arithmetic_functions_are_public_exports(self):
        for name, _ in generator.ARITHMETIC:
            self.write(f"stdlib/src/arithmetic/{name}.vast", f"fn {name}_one() -> Int {{ 1 }}\n")
        self.write("stdlib/src/arithmetic/generic.vast",
                   "generic twice(value) {\n    domain (Int);\n}\nmethod twice(value: Int) -> Int { value }\n")
        self.write("stdlib/src/geometry/mod.vast", "pub indexed marker QQ;\n")
        self.write("stdlib/src/differential/mod.vast", "")
        self.write("stdlib/docs/README.md", TABLE + "".join(
            row(name, "module") for name in ["arithmetic", *(name for _, name in generator.LIBRARIES)]))
        self.write("stdlib/docs/geometry.md", TABLE + row("QQ", "marker"))
        self.write("stdlib/docs/differential.md", "No exports.\n")
        rows = [row("integers", "module"), row("integers::int_one()", "function"), row("naturals", "module"),
                row("naturals::nat_one()", "function"), row("generic", "module")]
        self.write("stdlib/docs/arithmetic.md", TABLE + "".join(rows))
        self.assertEqual(self.errors(("stdlib",)), [
            "stdlib/docs/arithmetic.md: stdlib/target/package/arithmetic.vast (generated) exports generic::twice, "
            "which the page does not list"])
        self.write("stdlib/docs/arithmetic.md", TABLE + "".join(rows) + row("generic::twice(value)", "generic"))
        self.assertEqual(self.errors(("stdlib",)), [])
        self.write("stdlib/src/arithmetic/float.vast", "fn float_one() -> Int { 1 }\n")
        self.assertEqual(self.errors(("stdlib",)), [
            "stdlib/src/arithmetic/float.vast: a source file other than mod.vast or a flat arithmetic source, "
            "which this check maps to no page"])


if __name__ == "__main__":
    unittest.main()
