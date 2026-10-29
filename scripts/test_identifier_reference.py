from __future__ import annotations

import itertools
import random
import re
import string
import unittest
from pathlib import Path

from identifier_reference import (
    ESCAPE_PREFIX as P, IdentifierError, canonicalize_identifier as canon,
    is_start, is_continue, print_identifier as emit, read_identifier as read,
    validate_name,
)
from generate_identifier_unicode import generate, OUTPUT


def escaped_bytes(raw: bytes) -> bytes:
    # Construct adversarial wire tokens without using the production printer.
    return P.encode("ascii") + raw.hex().encode("ascii")


class CodecTests(unittest.TestCase):
    def rejects(self, raw: bytes, code: str | None = None) -> None:
        with self.assertRaises(IdentifierError) as caught:
            read(raw)
        if code:
            self.assertEqual(caught.exception.code, code)

    def test_golden_spellings(self):
        examples = {
            "λ": "__vastitas_id_cebb", "μ": "__vastitas_id_cebc",
            "µ": "__vastitas_id_c2b5", "K": "K", "K": "__vastitas_id_e284aa",
            "é": "__vastitas_id_c3a9", "e\u0301": "__vastitas_id_65cc81",
            "_u03bb": "_u03bb", "_λ": "__vastitas_id_5fcebb",
            "变量": "__vastitas_id_e58f98e9878f", "Ａ": "__vastitas_id_efbca1",
            "𝛌": "__vastitas_id_f09d9b8c", "_": "_",
        }
        for name, ascii_name in examples.items():
            with self.subTest(name=name):
                self.assertEqual(emit(name), ascii_name)
                self.assertEqual(read(ascii_name.encode("ascii")), name)
        self.assertEqual(len(set(examples.values())), len(examples))

    def test_exact_identity_no_normalization_or_casefolding(self):
        names = ("μ", "µ", "K", "K", "é", "e\u0301", "A", "a", "Ａ", "Α", "А")
        self.assertEqual(len({emit(name) for name in names}), len(names))
        for name in names:
            self.assertEqual(read(emit(name).encode("ascii")).encode("utf-8"), name.encode("utf-8"))

    def test_ascii_compatibility_exhaustive_short_names(self):
        first = string.ascii_letters + "_"
        rest = first + string.digits
        names = list(first) + [a + b for a, b in itertools.product(first, rest)]
        for name in names:
            self.assertEqual(emit(name), name)
            self.assertEqual(read(name.encode("ascii")), name)
        self.assertEqual(len(names), 3392)

    def test_no_new_default_ascii_length_limit(self):
        name = "valid_ascii_" + "x" * 100_000
        self.assertEqual(canon(name.encode("ascii")), name.encode("ascii"))

    def test_reserved_prefix_namespace(self):
        for name in ("__vastitas_internal", "__vastitas_λ", "__vastitas_id_cebb"):
            with self.subTest(name=name):
                with self.assertRaises(IdentifierError) as caught:
                    emit(name)  # Printer consumes a name, NOT a surface spelling.
                self.assertEqual(caught.exception.code, "E_RESERVED")
        self.rejects(b"__vastitas_internal", "E_RESERVED")
        self.rejects("__vastitas_λ".encode(), "E_RESERVED")
        self.assertEqual(read(b"__vastitas_id_cebb"), "λ")

    def test_ordinary_prefix_lookalikes_are_preserved(self):
        for name in ("_vastitas_id_cebb", "___vastitas_id_cebb", "__vastitas", "__Vastitas_id_cebb", "_u03bb"):
            self.assertEqual(emit(name), name)

    def test_noncanonical_ascii_encodings(self):
        for name in ("K", "lambda", "fn", "Int", "tensor", "_u03bb", "_"):
            with self.subTest(name=name):
                self.rejects(escaped_bytes(name.encode()), "E_NONCANONICAL")

    def test_encoded_reserved_and_nested_names(self):
        for name in ("__vastitas_private", "__vastitas_λ", "__vastitas_id_cebb"):
            self.rejects(escaped_bytes(name.encode()), "E_RESERVED")

    def test_malformed_hex_no_fallback(self):
        for suffix in (b"", b"c", b"CEBB", b"ceBb", b"cebb0", b"gg", b"ce bb", b"+cebb", b"cebb\n", "cebbλ".encode()):
            with self.subTest(suffix=suffix):
                self.rejects(P.encode() + suffix, "E_ESCAPE")

    def test_strict_utf8_rejects_overlong_surrogate_out_of_range(self):
        for raw in (b"\x80", b"\xce", b"\xc0\xaf", b"\xe0\x80\xaf", b"\xf0\x80\x80\x80", b"\xed\xa0\x80", b"\xf4\x90\x80\x80", b"\xff", b"\xfe"):
            self.rejects(raw, "E_UTF8")
            self.rejects(escaped_bytes(raw), "E_UTF8")
        with self.assertRaises(IdentifierError):
            emit("\ud800")

    def test_profile_rejections_raw_and_encoded(self):
        for name in ("", "1λ", "\u0301x", "a b", "a::b", "⊗", "≤", "🙂", "a\x00", "a\n", "a\u2028b", "a\u200cb", "a\u200db", "a\u202eb", "a\ufeffb", "a\ufe0fb", "a\u034fb", "\u115f", "\ue000", "\ufdd0", "\U0010ffff"):
            with self.subTest(name=repr(name)):
                self.rejects(name.encode())
                self.rejects(escaped_bytes(name.encode()))

    def test_admitted_scripts_and_combining_sequences(self):
        for name in ("λ", "μ2", "日本語", "变量", "مرحبا", "עברית", "अक्षर", "a\u0301", "a·b", "𝛌", "\U00020000", "a\u0661"):
            self.assertEqual(read(name.encode()), name)
            self.assertEqual(read(emit(name).encode()), name)

    def test_complete_token_only(self):
        self.rejects(b"__vastitas_id_cebb;", "E_ESCAPE")
        self.rejects(b"__vastitas_id_cebbZ", "E_ESCAPE")
        self.rejects(b"__vastitas_id_cebb00", "E_IDENTIFIER")
        self.assertEqual(read(b"__vastitas_id_cebb61"), "λa")

    def test_surface_aliasing_is_intentional(self):
        self.assertEqual(read("λ".encode()), read(b"__vastitas_id_cebb"))
        self.assertNotEqual(read("λ".encode()), read(b"_u03bb"))

    def test_decoded_byte_budget_is_closed_under_canonicalization(self):
        for name in ("a", "λ", "_λ", "e\u0301", "变量"):
            raw = name.encode()
            canonical = canon(raw, max_name_bytes=len(raw))
            self.assertEqual(canon(canonical, max_name_bytes=len(raw)), canonical)
            self.assertEqual(read(canonical, max_name_bytes=len(raw)), name)
            for spelling in (raw, canonical):
                with self.assertRaises(IdentifierError) as caught:
                    read(spelling, max_name_bytes=len(raw) - 1)
                self.assertEqual(caught.exception.code, "E_LIMIT")

    def test_budget_checked_before_unhex_and_invalid_budget(self):
        with self.assertRaises(IdentifierError) as caught:
            read(P.encode() + b"cebb" * 100_000, max_name_bytes=4)
        self.assertEqual(caught.exception.code, "E_LIMIT")
        for limit in (-1, True, 1.5):
            with self.assertRaises(ValueError):
                read(b"a", max_name_bytes=limit)

    def test_output_bound_and_generated_roundtrips(self):
        rng = random.Random(219220)
        starters = "aZ_λμµKKéＡ变量𝛌" + "\U00020000"
        continuers = starters + "019\u0301\u0661·"
        names = {rng.choice(starters) + "".join(rng.choice(continuers) for _ in range(rng.randrange(16))) for _ in range(20_000)}
        outputs: dict[str, str] = {}
        for name in names:
            raw = name.encode()
            spelling = emit(name)
            self.assertTrue(spelling.isascii())
            self.assertRegex(spelling, r"\A[A-Za-z_][A-Za-z_0-9]*\Z")
            self.assertEqual(read(spelling.encode()), name)
            self.assertEqual(canon(raw), spelling.encode())
            self.assertEqual(canon(canon(raw)), canon(raw))
            expected_length = len(raw) if name.isascii() else len(P) + 2 * len(raw)
            self.assertEqual(len(spelling), expected_length)
            self.assertEqual(outputs.setdefault(spelling, name), name)


class UnicodeTableTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        # Independent per-code-point oracle from the raw UCD, not generated ranges.
        cls.oracle = {prop: bytearray(0x110000) for prop in ("XID_Start", "XID_Continue", "Default_Ignorable_Code_Point")}
        source = Path(__file__).with_name("identifier_data") / "DerivedCoreProperties-16.0.0.txt"
        row = re.compile(r"^([0-9A-F]+)(?:\.\.([0-9A-F]+))?\s*;\s*(XID_Start|XID_Continue|Default_Ignorable_Code_Point)\s*(?:#|$)", re.MULTILINE)
        for match in row.finditer(source.read_text("utf-8")):
            lo, hi = int(match[1], 16), int(match[2] or match[1], 16)
            cls.oracle[match[3]][lo:hi + 1] = b"\1" * (hi - lo + 1)

    def test_regenerated_table_and_ucd_counts(self):
        self.assertEqual(OUTPUT.read_text("utf-8"), generate())
        self.assertEqual(sum(self.oracle["XID_Start"]), 141246)
        self.assertEqual(sum(self.oracle["XID_Continue"]), 144522)
        self.assertEqual(sum(self.oracle["Default_Ignorable_Code_Point"]), 4174)

    def test_all_codepoints_against_independent_property_oracle(self):
        start, cont, ign = (self.oracle[p] for p in ("XID_Start", "XID_Continue", "Default_Ignorable_Code_Point"))
        for cp in range(0x110000):
            expected_start = (cp == 0x5F or bool(start[cp])) and not ign[cp]
            expected_cont = bool(cont[cp]) and not ign[cp]
            if is_start(cp) != expected_start or is_continue(cp) != expected_cont:
                self.fail(f"Unicode profile differs at U+{cp:04X}")

    def test_roundtrip_every_admitted_start_and_continuation_scalar(self):
        start, cont, ign = (self.oracle[p] for p in ("XID_Start", "XID_Continue", "Default_Ignorable_Code_Point"))
        for cp in range(0x110000):
            if (cp == 0x5F or start[cp]) and not ign[cp]:
                name = chr(cp)
                self.assertEqual(read(emit(name).encode()), name)
            if cont[cp] and not ign[cp]:
                name = "_" + chr(cp)
                self.assertEqual(read(emit(name).encode()), name)


if __name__ == "__main__":
    unittest.main()
