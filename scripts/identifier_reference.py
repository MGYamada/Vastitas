"""Identifier-only reference for Vastitas #219/#220; NOT a compiler frontend.

Names are exact Unicode scalar sequences. No Unicode normalization, case
folding, Python identifier parser, operator aliases, or privilege is involved.
"""
from __future__ import annotations

from bisect import bisect_right
import json
from pathlib import Path
import re

PROFILE = "vastitas-ident-exact-ucd16-v1-draft"
INTERNAL_PREFIX = "__vastitas_"
ESCAPE_PREFIX = "__vastitas_id_"
_LOWER_HEX = re.compile(r"[0-9a-f]+", re.ASCII)
_DATA = json.loads((Path(__file__).with_name("identifier_data") / "unicode16_ranges.json").read_text("utf-8"))
if _DATA["unicode_version"] != "16.0.0":
    raise RuntimeError("wrong Unicode profile")
_RANGES = {key: tuple(map(tuple, value)) for key, value in _DATA["properties"].items()}
_STARTS = {key: tuple(lo for lo, _ in value) for key, value in _RANGES.items()}


class IdentifierError(ValueError):
    def __init__(self, code: str, message: str):
        self.code = code
        super().__init__(message)


def _has_property(cp: int, prop: str) -> bool:
    index = bisect_right(_STARTS[prop], cp) - 1
    return index >= 0 and cp <= _RANGES[prop][index][1]


def is_start(cp: int) -> bool:
    return (cp == 0x5F or _has_property(cp, "XID_Start")) and not _has_property(
        cp, "Default_Ignorable_Code_Point"
    )


def is_continue(cp: int) -> bool:
    return _has_property(cp, "XID_Continue") and not _has_property(
        cp, "Default_Ignorable_Code_Point"
    )


def _check_budget(size: int, max_name_bytes: int | None) -> None:
    if max_name_bytes is not None:
        if type(max_name_bytes) is not int or max_name_bytes < 0:
            raise ValueError("max_name_bytes must be a nonnegative integer or None")
        if size > max_name_bytes:
            raise IdentifierError("E_LIMIT", "decoded identifier exceeds byte budget")


def _strict_utf8(raw: bytes) -> str:
    try:
        return raw.decode("utf-8", errors="strict")
    except UnicodeDecodeError as exc:
        raise IdentifierError("E_UTF8", "identifier is not strict UTF-8") from exc


def validate_name(name: str, *, max_name_bytes: int | None = None) -> str:
    """Check a decoded *user* name, not a binding/type/owner acceptance proof.

    Keywords and ordinary reserved builtin names remain lexically representable;
    their contextual rejection belongs to the unchanged host parser/checkers.
    Internal compiler names are never admitted by this user-name codec.
    """
    if not isinstance(name, str):
        raise TypeError("name must be str")
    try:
        raw = name.encode("utf-8", errors="strict")
    except UnicodeEncodeError as exc:
        raise IdentifierError("E_UTF8", "surrogate is not a Unicode scalar") from exc
    _check_budget(len(raw), max_name_bytes)
    if not name or not is_start(ord(name[0])) or any(
        not is_continue(ord(ch)) for ch in name[1:]
    ):
        raise IdentifierError("E_IDENTIFIER", "name is outside the fixed identifier profile")
    if name.startswith(INTERNAL_PREFIX):
        raise IdentifierError("E_RESERVED", "decoded user name has a compiler-reserved prefix")
    return name


def print_identifier(name: str, *, max_name_bytes: int | None = None) -> str:
    """E: decoded name -> unique ASCII spelling. Never consumes an escape."""
    validate_name(name, max_name_bytes=max_name_bytes)
    return name if name.isascii() else ESCAPE_PREFIX + name.encode("utf-8").hex()


def read_identifier(spelling: bytes, *, max_name_bytes: int | None = None) -> str:
    """R: one complete identifier token -> decoded name, on EVERY input path.

    The caller's lexer provides token boundaries. Malformed escape tokens fail
    as a whole; no prefix decoding, fallback, recursive decoding, or source mode.
    """
    if not isinstance(spelling, bytes):
        raise TypeError("spelling must be bytes from the source token")
    # Prefix is ASCII, so recognize it on bytes before allocating decoded text.
    prefix = ESCAPE_PREFIX.encode("ascii")
    if spelling.startswith(prefix):
        payload = spelling[len(prefix):]
        if not payload or len(payload) % 2:
            raise IdentifierError("E_ESCAPE", "escape needs a nonempty even-length payload")
        _check_budget(len(payload) // 2, max_name_bytes)
        try:
            hex_text = payload.decode("ascii")
        except UnicodeDecodeError as exc:
            raise IdentifierError("E_ESCAPE", "escape payload must be lowercase ASCII hex") from exc
        if _LOWER_HEX.fullmatch(hex_text) is None:
            raise IdentifierError("E_ESCAPE", "escape payload must be lowercase ASCII hex")
        name = _strict_utf8(bytes.fromhex(hex_text))
        # Check the actual decoded name even when it spells a reserved prefix.
        validate_name(name, max_name_bytes=max_name_bytes)
        if name.isascii():
            raise IdentifierError("E_NONCANONICAL", "ASCII names must use their original spelling")
        if print_identifier(name, max_name_bytes=max_name_bytes).encode("ascii") != spelling:
            raise IdentifierError("E_NONCANONICAL", "escape is not canonical")
        return name
    _check_budget(len(spelling), max_name_bytes)
    return validate_name(_strict_utf8(spelling), max_name_bytes=max_name_bytes)


def canonicalize_identifier(spelling: bytes, *, max_name_bytes: int | None = None) -> bytes:
    """C = E after R. Idempotent on accepted complete identifier tokens."""
    return print_identifier(
        read_identifier(spelling, max_name_bytes=max_name_bytes),
        max_name_bytes=max_name_bytes,
    ).encode("ascii")
