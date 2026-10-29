# Identifier reference — validation report

Run date: 2026-10-29 (JST). Interpreter: Python 3.12.14.
Repository base: `e01fe1d51fa5faf089e52a7b5a07223031db1b7c`.
Dependencies: Python standard library and the bundled Unicode 16.0.0 tables.
The host Python Unicode database is not used for identifier membership.

## Commands and results

| Command | Actual result |
| --- | --- |
| `python3 -m unittest discover -s scripts -p 'test_identifier*.py' -v` | **34 tests passed**, 3.811 seconds, exit 0 |
| `python3 -m unittest discover -s scripts -p 'test_*.py'` | **175 tests passed**, 8.287 seconds, exit 0 |
| `python3 scripts/generate_identifier_unicode.py --check` | Generated ranges exactly match the pinned UCD source; exit 0 |
| `python3 scripts/demo_identifier_reference.py` | Eight examples recovered their exact names and satisfied idempotence; exit 0 |
| `python3 scripts/check_boundaries.py` | Compiler/oracle dependency boundaries verified; exit 0 |

Run these commands from the repository root. Existing CI's Python discovery
includes all 34 new tests. No compiler, Rust, or Lean sources were changed, and
no local Vastitas `check`/`build`, Cargo suite, or Lean proof build was run.

The lexical and reserved-prefix rules cited at the original `7d6515a` baseline
were rechecked against this repository base. Local Markdown file links and
`git diff --cached --check` were also checked. No rendered book/HTML check was
run; the repository's mdBook migration remains planned separately.

## Coverage

* Classification compared with an independently constructed bitmap oracle for
  all **1,114,112** code-point positions, including the 2,048 surrogate positions.
  That is all 1,112,064 Unicode scalar values plus the excluded surrogates.
  The oracle and implementation share the official UCD as the normative input;
  this checks table extraction/membership, not the correctness of the UCD itself.
* Round-trips for all **141,243** admitted start code points as one-character
  names and all **144,253** continuation code points after `_`: **285,496** cases.
* All **3,392** ASCII lexical names of lengths one and two; one valid ASCII name
  longer than 100,000 bytes verifies absence of an introduced default length cap.
  Contextual keyword restrictions are exercised separately in a synthetic gate.
* 20,000 deterministic name-generation attempts, deduplicated, with seed 219220:
  ASCII output, precise output-size formula, recovery, idempotence, and no
  observed collisions. The general laws are argued in [the specification](identifier-ascii-reference.md), not inferred
  from this finite sampling.
* Golden vectors distinguish `λ`/`_u03bb`, `μ`/`µ`, `K`/`K`, composed/decomposed
  accents, mathematical letters, fullwidth letters, and non-Latin names.
* Negative cases cover malformed/uppercase/odd hex, incomplete token suffixes,
  invalid UTF-8 and surrogates, encoded ASCII, encoded reserved names, nested
  encodings, invalid starts, invisible formatting, operators, and byte budgets.
* Syntax-adapter cases preserve original UTF-8 spans, scalar columns, opaque
  context handles, expansion traces, comment/literal bytes, and U+2028. They
  reject malformed span maps and revalidate identifier spelling on rereading.
* A **synthetic host fixture** verifies the same callback path and resolved
  declaration object for raw/encoded forms, duplicate alias rejection, contextual
  reservations, unknown-name rejection, and denial of an external owner's edit.
  It is not Vastitas's actual resolver, ownership checker, or macro system.

## What this establishes

The delivered implementation passes the stated identifier-level regressions
under the fixed profile. The common reader, exact-identity policy, disjoint
ASCII/escape representation, and in-process metadata retention work within
the tested reference interfaces.

It does **not** establish adoption of the prefix, acceptance by the current
Vastitas compiler, full-source ASCII canonicalization, actual hygienic expansion,
whole-program semantic equivalence, namespace/owner proof preservation, or a
Lean theorem. In particular, external ASCII text alone does not reconstruct
original locations or macro contexts. The remaining integration obligations
are listed in [the specification](identifier-ascii-reference.md) sections 5–7.
