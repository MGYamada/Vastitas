"""Name-only demonstration; this does not accept or transform .vast programs."""
from identifier_reference import canonicalize_identifier, read_identifier


if __name__ == "__main__":
    for name in ("λ", "_u03bb", "μ", "µ", "K", "K", "é", "e\u0301"):
        canonical = canonicalize_identifier(name.encode("utf-8"))
        recovered = read_identifier(canonical)
        assert recovered == name
        assert canonicalize_identifier(canonical) == canonical
        print(f"{name!r} -> {canonical.decode('ascii')} -> {recovered!r}")
