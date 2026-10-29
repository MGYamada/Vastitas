"""Small in-process syntax-object adapter, NOT a Vastitas lexer or macro system.

Only host-designated identifier tokens are reprinted. All other token/trivia
bytes are opaque. Contexts and origin records are supplied by the host and stay
out of the spelling. The resulting document is NOT promised to be ASCII-only.
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Callable, Iterable

from identifier_reference import read_identifier, print_identifier


@dataclass(frozen=True)
class Source:
    file_id: str
    data: bytes

    def __post_init__(self) -> None:
        self.data.decode("utf-8", errors="strict")


@dataclass(frozen=True)
class Span:
    source: Source
    start: int
    end: int

    def __post_init__(self) -> None:
        data = self.source.data
        if not 0 <= self.start <= self.end <= len(data):
            raise ValueError("invalid UTF-8 byte span")
        for offset in (self.start, self.end):
            if offset < len(data) and data[offset] & 0xC0 == 0x80:
                raise ValueError("span splits a UTF-8 scalar")

    @property
    def data(self) -> bytes:
        return self.source.data[self.start:self.end]

    def line_column(self) -> tuple[int, int]:
        """1-based line and Unicode-scalar column; LF alone changes line."""
        before = self.source.data[:self.start]
        return before.count(b"\n") + 1, len(before.rsplit(b"\n", 1)[-1].decode("utf-8")) + 1


@dataclass(frozen=True)
class IdentifierToken:
    spelling: bytes
    origin: Span
    syntax_context: object  # Opaque host handle, NOT an owner or permission.
    expansion_trace: tuple[Span, ...] = ()


@dataclass(frozen=True)
class OpaqueToken:
    data: bytes


@dataclass(frozen=True)
class IdentifierUse:
    name: str
    origin: Span
    syntax_context: object
    expansion_trace: tuple[Span, ...]


def read_use(token: IdentifierToken, *, max_name_bytes: int | None = None) -> IdentifierUse:
    return IdentifierUse(
        read_identifier(token.spelling, max_name_bytes=max_name_bytes),
        token.origin, token.syntax_context, token.expansion_trace,
    )


def through_host_checks(token: IdentifierToken, checks: Callable[[IdentifierUse], object]):
    """Always call the same host gate after reading either spelling.

    `checks` must do real contextual reservation/resolution/ownership checking.
    This adapter cannot establish that the callback implements those checks.
    """
    return checks(read_use(token))


@dataclass(frozen=True)
class PrintedIdentifier:
    start: int
    end: int
    origin: Span
    syntax_context: object
    expansion_trace: tuple[Span, ...]


@dataclass(frozen=True)
class PrintedDocument:
    data: bytes
    identifiers: tuple[PrintedIdentifier, ...]


def print_syntax(parts: Iterable[IdentifierToken | OpaqueToken]) -> PrintedDocument:
    """Serialize a host syntax tape; no scanning or substitution inside trivia."""
    chunks: list[bytes] = []
    entries: list[PrintedIdentifier] = []
    offset = 0
    for part in parts:
        if isinstance(part, OpaqueToken):
            raw = part.data
        elif isinstance(part, IdentifierToken):
            use = read_use(part)
            raw = print_identifier(use.name).encode("ascii")
            entries.append(PrintedIdentifier(
                offset, offset + len(raw), use.origin, use.syntax_context, use.expansion_trace,
            ))
        else:
            raise TypeError("only identifier and opaque syntax tokens are supported")
        chunks.append(raw)
        offset += len(raw)
    return PrintedDocument(b"".join(chunks), tuple(entries))


def reload_in_process(document: PrintedDocument) -> tuple[IdentifierToken | OpaqueToken, ...]:
    """Use only with a document retained by the same host compilation session.

    This is NOT a sidecar importer. For external text, the real lexer/macro
    expander must reconstruct contexts; never deserialize these context handles.
    """
    parts: list[IdentifierToken | OpaqueToken] = []
    cursor = 0
    for entry in document.identifiers:
        if not cursor <= entry.start < entry.end <= len(document.data):
            raise ValueError("overlapping or invalid identifier mapping")
        parts.append(OpaqueToken(document.data[cursor:entry.start]))
        token = IdentifierToken(
            document.data[entry.start:entry.end], entry.origin,
            entry.syntax_context, entry.expansion_trace,
        )
        read_use(token)  # Revalidate, with the SAME decoder and no trust flag.
        parts.append(token)
        cursor = entry.end
    parts.append(OpaqueToken(document.data[cursor:]))
    return tuple(parts)
