"""Resource and identity regressions for the structured export name index."""
import json
from pathlib import Path
import tempfile
import tracemalloc
import unittest

import fast_check as fast


class ExportNameTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.image = Path(self.temp.name) / "closure.ndjson"
        self.standard = fast.STANDARD.read_bytes()
        rows = [json.loads(record) for record in self.standard.splitlines()]
        self.next_name = 1 + sum("in" in row for row in rows)
        self.next_expr = sum("ie" in row for row in rows)

    def write(self, records):
        with self.image.open("wb") as out:
            out.write(self.standard)
            for record in records:
                out.write(json.dumps(record).encode() + b"\n")

    def inspect(self, pending=None):
        return fast.inspect_closure(self.image, "Classical.choice", pending, expected_kind="axiom")

    def test_deep_names_fit_fixed_heap(self):
        for depth in (256, 2048, 8192):
            with self.subTest(depth=depth):
                self.write({"in": self.next_name + i, "str": {
                    "pre": self.next_name + i - 1 if i else 0, "str": "part"}}
                           for i in range(depth))
                tracemalloc.start()
                try:
                    report = self.inspect()
                    peak = tracemalloc.get_traced_memory()[1]
                finally:
                    tracemalloc.stop()
                self.assertEqual(report["standard_axioms"], sorted(fast.AXIOMS))
                self.assertLess(peak, 16 * 1024**2)

    def test_unresolved_numeric_and_string_components_stay_distinct(self):
        start = self.next_name
        self.write([
            {"in": start, "str": {"pre": 0, "str": "part.with.dot"}},
            {"in": start + 1, "num": {"pre": start, "i": 7}},
            {"in": start + 2, "str": {"pre": start, "str": "7"}},
            {"ie": self.next_expr, "const": {"name": start + 1, "us": []}},
            {"ie": self.next_expr + 1, "const": {"name": start + 2, "us": []}},
        ])
        pending = []
        self.inspect(pending)
        self.assertEqual(pending, [("part.with.dot", 7), ("part.with.dot", "7")])
        self.assertEqual([fast.mutual_root(parts) for parts in pending],
                         ["«part.with.dot».7", "«part.with.dot».«7»"])
        with self.assertRaisesRegex(ValueError, "missing 2 transitive declarations"):
            self.inspect()

    def test_one_dotted_name_cannot_redeclare_a_standard_axiom(self):
        self.write([
            {"in": self.next_name, "str": {"pre": 0, "str": "Classical.choice"}},
            {"axiom": {"name": self.next_name, "levelParams": [], "type": 0, "isUnsafe": False}},
        ])
        with self.assertRaisesRegex(ValueError, "nonstandard or ambiguously named axiom"):
            self.inspect()


if __name__ == "__main__":
    unittest.main()
