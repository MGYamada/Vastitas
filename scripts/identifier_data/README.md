# Fixed Unicode data for the identifier reference

This directory is development-test data, not a compiler/runtime dependency.

- `DerivedCoreProperties-16.0.0.txt` is the complete, unchanged Unicode 16.0.0
  [UCD source](https://www.unicode.org/Public/16.0.0/ucd/DerivedCoreProperties.txt).
  SHA-256: `39d35161f2954497f69e08bdb9e701493f476a3d30222de20028feda36c1dabd`.
- `unicode16_ranges.json` is generated from that file's `XID_Start`,
  `XID_Continue`, and `Default_Ignorable_Code_Point` properties. Keep its version
  and source digest fixed; the host Python Unicode database is not consulted.
- `Unicode-LICENSE.txt` contains the Unicode License V3 for the source data and
  derived ranges. Their license is preserved separately from the repository's
  Apache-2.0 license.

From the repository root, reproduce and check the ranges without network access:

```sh
python3 scripts/generate_identifier_unicode.py
python3 scripts/generate_identifier_unicode.py --check
```

The generator verifies the complete source SHA-256 before extracting properties.
Regression tests independently construct per-code-point bitmaps from the source
and compare the codec over the full code-point range. See the
[identifier contract](../../docs/identifier-ascii-reference.md) for the exclusions
and exact-identity policy; the tables themselves do not normalize names.
