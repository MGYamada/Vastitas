"""Rendering, validation and drift detection of the generated primitive table."""
import contextlib
import io
import json
from pathlib import Path
import re
import tempfile
import unittest

import check_primitive_table as table

ROOT = Path(__file__).resolve().parents[1]
FAMILY = re.compile(r'    PrimitiveFamily \{\n        op: "(\w+)",\n        algebraic: (true|false),\n(.*?)\n    \},', re.S)
FIELD = re.compile(r'\("(\w+)", WireKind::(\w+)\)')
VARIANTS = {variant: kind for kind, variant in table.KINDS.items()}


def read_table(text):
    """The families that the checked-in Rust table holds."""
    return [{"op": op, "algebraic": algebraic == "true",
             "fields": [{"name": name, "kind": VARIANTS[variant]} for name, variant in FIELD.findall(fields)]}
            for op, algebraic, fields in FAMILY.findall(text)]


def family(op, *fields, algebraic=True):
    return {"op": op, "algebraic": algebraic, "fields": [{"name": n, "kind": k} for n, k in fields]}


class PrimitiveTableTests(unittest.TestCase):
    def test_the_checked_in_table_is_a_rendering(self):
        # Without Lean: the file is exactly the rendering of the families it holds.
        text = (ROOT / table.TABLE).read_text(encoding="utf-8")
        families = read_table(text)
        self.assertEqual(table.validate(families), [])
        self.assertEqual(table.render(families), text)

    def test_fields_follow_the_rustfmt_layout(self):
        # The layouts that rustfmt 1.99.1 (edition 2024) keeps: two fields of
        # 60 columns on one line, 61 one per line; a single field on one line.
        def fields(*names):
            return [{"name": name, "kind": "pullback_mode" if name == "mode" else "path"} for name in names]
        self.assertEqual(table.render_fields(fields("aaaaaa", "b" * 12)),
                         ['        fields: &[("aaaaaa", WireKind::Path), ("bbbbbbbbbbbb", WireKind::Path)],'])
        self.assertEqual(table.render_fields(fields("aaaaaa", "b" * 13)),
                         ["        fields: &[", '            ("aaaaaa", WireKind::Path),',
                          '            ("bbbbbbbbbbbbb", WireKind::Path),', "        ],"])
        self.assertEqual(table.render_fields(fields("c" * 34)),
                         [f'        fields: &[("{"c" * 34}", WireKind::Path)],'])
        self.assertEqual(table.render_fields(fields("mode")), ['        fields: &[("mode", WireKind::PullbackMode)],'])
        self.assertEqual(table.render_fields([]), ["        fields: &[],"])

    def test_malformed_families_are_rejected(self):
        good = family("smooth_compose", ("family", "path"))
        cases = [
            ("duplicate op", [good, good]),
            ("unknown field kind", [family("x", ("family", "matrix"))]),
            ("unknown field kind", [family("x", ("family", ["path"]))]),
            ("lowercase identifier other than op", [family("x", ("op", "path"))]),
            ("lowercase identifier other than op", [family("x", (["family"], "path"))]),
            ("duplicate field", [family("x", ("family", "path"), ("family", "path"))]),
            ("longer than 34 characters", [family("x", ("f" * 35, "path"))]),
            ("algebraic must be", [dict(good, algebraic="yes")]),
            ("exactly the keys op", [{"op": "x", "fields": []}]),
            ("not a lowercase identifier", [family("Bad-op")]),
            ("non-empty JSON array", []),
        ]
        for message, families in cases:
            with self.subTest(message=message, families=families):
                errors = table.validate(families)
                self.assertTrue(any(message in error for error in errors), errors)

    def test_drift_fails_and_write_regenerates(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "src").mkdir()
            source = root / "families.json"
            source.write_text(json.dumps([family("descriptor", ("implementation", "path"), algebraic=False)]))
            arguments = ["--families", str(source)]
            with contextlib.redirect_stderr(io.StringIO()) as errors, contextlib.redirect_stdout(io.StringIO()):
                self.assertEqual(table.main(arguments, root), 1)
                self.assertIn("cannot read file", errors.getvalue())
                self.assertEqual(table.main(arguments + ["--write"], root), 0)
                self.assertEqual(table.main(arguments, root), 0)
                path = root / table.TABLE
                path.write_text(path.read_text().replace("false", "true"))
                self.assertEqual(table.main(arguments, root), 1)
                self.assertIn("differs from the kernel's families", errors.getvalue())


if __name__ == "__main__":
    unittest.main()
