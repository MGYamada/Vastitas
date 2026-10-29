from __future__ import annotations

from dataclasses import dataclass, replace
import unittest

from identifier_reference import ESCAPE_PREFIX, IdentifierError
from identifier_syntax_reference import (
    IdentifierToken, IdentifierUse, OpaqueToken, Source, Span,
    print_syntax, read_use, reload_in_process, through_host_checks,
)


def token(spelling: str, context: object) -> IdentifierToken:
    source = Source("fixture.vast", spelling.encode())
    return IdentifierToken(source.data, Span(source, 0, len(source.data)), context)


@dataclass(frozen=True)
class Declaration:
    owner: str
    nominal_id: str


class HostChecksFixture:
    """Deliberately small TEST FIXTURE; not Vastitas resolution/ownership code."""
    def __init__(self):
        self.declarations: dict[tuple[str, object], Declaration] = {}
        self.calls: list[tuple[str, str]] = []

    def bind(self, use: IdentifierUse, module: str) -> Declaration:
        self.calls.append(("reserve", use.name))
        if use.name in {"fn", "let", "Int", "compose", "mod"} or use.name.startswith("__vastitas_"):
            raise ValueError("reserved binding")
        key = (use.name, use.syntax_context)
        self.calls.append(("duplicate", use.name))
        if key in self.declarations:
            raise ValueError("duplicate binding")
        # Identity and owner come from the host's declaration, never spelling.
        declaration = Declaration(module, f"declaration-{len(self.declarations)}")
        self.declarations[key] = declaration
        return declaration

    def resolve(self, use: IdentifierUse) -> Declaration:
        self.calls.append(("resolve", use.name))
        try:
            return self.declarations[(use.name, use.syntax_context)]
        except KeyError as exc:
            raise ValueError("unresolved name") from exc

    def edit(self, use: IdentifierUse, module: str) -> Declaration:
        declaration = self.resolve(use)
        self.calls.append(("owner", use.name))
        if declaration.owner != module:
            raise ValueError("edit authority denied")
        return declaration


class HostPathTests(unittest.TestCase):
    def setUp(self):
        self.context = object()
        self.host = HostChecksFixture()

    def test_same_gate_and_identity_from_both_spellings(self):
        original = through_host_checks(token("λ", self.context), lambda use: self.host.bind(use, "owner"))
        for spelling in ("λ", "__vastitas_id_cebb"):
            self.host.calls.clear()
            result = through_host_checks(token(spelling, self.context), self.host.resolve)
            self.assertIs(result, original)
            self.assertEqual(self.host.calls, [("resolve", "λ")])

    def test_alias_cannot_create_second_binding(self):
        through_host_checks(token("λ", self.context), lambda use: self.host.bind(use, "owner"))
        with self.assertRaisesRegex(ValueError, "duplicate"):
            through_host_checks(token("__vastitas_id_cebb", self.context), lambda use: self.host.bind(use, "owner"))

    def test_contextual_reservations_are_still_checked(self):
        for name in ("fn", "let", "Int", "compose", "mod"):
            with self.assertRaisesRegex(ValueError, "reserved"):
                through_host_checks(token(name, self.context), lambda use: self.host.bind(use, "owner"))

    def test_encoded_name_does_not_authorize_external_edit(self):
        through_host_checks(token("λ", self.context), lambda use: self.host.bind(use, "owner"))
        for spelling in ("λ", "__vastitas_id_cebb"):
            self.host.calls.clear()
            with self.assertRaisesRegex(ValueError, "authority denied"):
                through_host_checks(token(spelling, self.context), lambda use: self.host.edit(use, "external"))
            self.assertEqual(self.host.calls, [("resolve", "λ"), ("owner", "λ")])

    def test_encoded_internal_name_never_reaches_gate(self):
        spelling = ESCAPE_PREFIX + "__vastitas_λ".encode().hex()
        with self.assertRaises(IdentifierError):
            through_host_checks(token(spelling, self.context), lambda use: self.host.bind(use, "owner"))
        self.assertEqual(self.host.calls, [])

    def test_unknown_name_does_not_become_builtin(self):
        through_host_checks(token("tensor", self.context), lambda use: self.host.bind(use, "std::monoidal"))
        for name in ("ｔｅｎｓｏｒ", "λ"):
            printed = print_syntax((token(name, self.context),)).data.decode("ascii")
            for spelling in (name, printed):
                with self.assertRaisesRegex(ValueError, "unresolved"):
                    through_host_checks(token(spelling, self.context), self.host.resolve)

    def test_context_is_not_reconstructed_from_spelling(self):
        through_host_checks(token("λ", self.context), lambda use: self.host.bind(use, "owner"))
        other_context = object()
        with self.assertRaisesRegex(ValueError, "unresolved"):
            through_host_checks(token("__vastitas_id_cebb", other_context), self.host.resolve)


class SyntaxBridgeTests(unittest.TestCase):
    def test_comments_literals_and_u2028_are_opaque(self):
        before = '// λ __vastitas_id_cebb\u2028 still a comment\nlet '.encode()
        after = ' = "λ __vastitas_id_cebb"; // µ\n'.encode()
        source = Source("unicode.vast", before + "λ".encode() + after)
        origin = Span(source, len(before), len(before) + 2)
        context = object()
        tape = (OpaqueToken(before), IdentifierToken(origin.data, origin, context), OpaqueToken(after))
        printed = print_syntax(tape)
        self.assertEqual(printed.data, before + b"__vastitas_id_cebb" + after)
        self.assertFalse(printed.data.isascii())  # Whole-file ASCII is out of scope.
        reprinted = print_syntax(reload_in_process(printed))
        self.assertEqual(reprinted, printed)
        self.assertEqual(origin.line_column(), (2, 5))

    def test_original_utf8_position_and_expansion_trace_survive(self):
        source = Source("macro.vast", "// α\n日本 λ".encode())
        start = source.data.index("λ".encode())
        origin = Span(source, start, start + 2)
        callsite = Span(source, 0, 2)
        context = object()
        original = IdentifierToken(origin.data, origin, context, (callsite,))
        printed = print_syntax((OpaqueToken(source.data[:start]), original))
        reloaded = [part for part in reload_in_process(printed) if isinstance(part, IdentifierToken)][0]
        use = read_use(reloaded)
        self.assertEqual(use.name, "λ")
        self.assertIs(use.origin, origin)
        self.assertIs(use.syntax_context, context)
        self.assertEqual(use.expansion_trace, (callsite,))
        self.assertEqual(use.origin.line_column(), (2, 4))
        self.assertEqual(use.origin.data, "λ".encode())
        self.assertEqual((start, start + 2), (13, 15))

    def test_same_spelling_in_distinct_contexts_stays_distinct(self):
        first, second = object(), object()
        printed = print_syntax((token("λ", first), OpaqueToken(b" "), token("λ", second)))
        uses = [read_use(part) for part in reload_in_process(printed) if isinstance(part, IdentifierToken)]
        self.assertEqual(uses[0].name, uses[1].name)
        self.assertIs(uses[0].syntax_context, first)
        self.assertIs(uses[1].syntax_context, second)

    def test_plain_external_text_has_new_origin_and_host_context(self):
        printed = print_syntax((token("λ", object()),))
        external_source = Source("saved.vast", printed.data)
        fresh = object()
        external = IdentifierToken(printed.data, Span(external_source, 0, len(printed.data)), fresh)
        use = read_use(external)
        self.assertEqual(use.name, "λ")
        self.assertEqual(use.origin.source.file_id, "saved.vast")
        self.assertIs(use.syntax_context, fresh)
        self.assertIsNot(use.syntax_context, printed.identifiers[0].syntax_context)

    def test_invalid_byte_spans_fail(self):
        source = Source("a.vast", "aλ".encode())
        for start, end in ((-1, 1), (0, 4), (3, 2), (2, 3), (1, 2)):
            with self.assertRaises(ValueError):
                Span(source, start, end)
        with self.assertRaises(UnicodeDecodeError):
            Source("bad.vast", b"\xff")

    def test_in_process_reload_revalidates_spelling(self):
        printed = print_syntax((token("λ", object()),))
        with self.assertRaises(IdentifierError):
            reload_in_process(replace(printed, data=b"__vastitas_id_CEBB"))

    def test_invalid_origin_map_ranges_rejected(self):
        printed = print_syntax((token("λ", object()),))
        entry = printed.identifiers[0]
        for entries in ((entry, entry), (replace(entry, start=-1),), (replace(entry, end=len(printed.data) + 1),)):
            with self.assertRaises(ValueError):
                reload_in_process(replace(printed, identifiers=entries))


if __name__ == "__main__":
    unittest.main()
