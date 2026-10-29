# Vastitas identifier ASCII round-trip — minimal reference specification

Status: **draft contract and development reference**, 2026-10-29 (JST).
No release target. No compiler change, adopted prefix, Lean proof, or whole-program
meaning-preservation claim is implied.

## 1. Scope and baseline

This fragment specifies the ASCII printing, common-path rereading, and exact
name recovery of **user identifier tokens**. It is a component of
[#219](https://github.com/MGYamada/Vastitas/issues/219) and respects
[#220](https://github.com/MGYamada/Vastitas/issues/220)'s requirement that spelling
does not confer semantic authority. Operator aliases, Julia syntax, strings,
comments, complete source formatting, and compiler-generated symbols are outside
the codec's domain.

Baseline: [`src/frontend.rs` at `7d6515a54e9a6b27b5a50dedffd7931c14e40726`](https://github.com/MGYamada/Vastitas/blob/7d6515a54e9a6b27b5a50dedffd7931c14e40726/src/frontend.rs).
The lexer at lines 226–235 admits ASCII letters/underscore followed by ASCII
letters/digits/underscore. `reserved` at lines 63–69 rejects `__vastitas_` and
contextual reserved names; `binding_name` at lines 414–430 adds package keywords.
Index/reference checks also reject the internal prefix. Thus simply printing
an encoded name into the current parser is insufficient. This reference is
not connected to that parser, any wire protocol, or Lean acceptance.

## 2. Fixed identifier profile and identity

Draft profile ID: `vastitas-ident-exact-ucd16-v1-draft`.
Use **Unicode 16.0.0**, not the host runtime's evolving Unicode tables:

```
Start    = (XID_Start ∪ { U+005F LOW LINE }) − Default_Ignorable_Code_Point
Continue = XID_Continue − Default_Ignorable_Code_Point
Name     = Start Continue*
```

The properties are taken from the versioned
[UCD file](https://www.unicode.org/Public/16.0.0/ucd/DerivedCoreProperties.txt).
Its SHA-256 is
`39d35161f2954497f69e08bdb9e701493f476a3d30222de20028feda36c1dabd`.
The file, its license, compact generated ranges, and offline generator are bundled.
The resulting sets contain 141,243 start and 144,253 continuation code points.
This uses the property-based profiling approach of
[UAX #31 revision 41](https://www.unicode.org/reports/tr31/tr31-41.html);
it does **not** adopt normalized-equivalence or case-insensitive identity rules.

Input must be strict UTF-8 encoding Unicode scalar values. Reject invalid,
truncated, overlong, surrogate, and out-of-range encodings; do not replace errors
with U+FFFD. The profile rejects pictographs such as `🙂`, operator glyphs such as
`⊗` and `≤`, separators, private-use/unassigned characters, and noncharacters.
Membership is determined by the sets above, not by a general "emoji" or "math"
label; some mathematical letters and symbols are admitted. Default-ignorable removal
also excludes join controls, bidi controls, variation selectors, and U+034F.
Ordinary RTL letters and mixed scripts are allowed. Noninitial combining marks
are allowed when in `Continue`; a leading U+0301 is rejected because it is not
in `Start`. No additional general-category filter is imposed on the XID sets.

**Name-text equality is exact scalar-sequence equality, equivalently strict UTF-8
byte equality.** No NFC, NFKC, case folding, transliteration, or confusable folding
is applied. XID membership does not itself instruct the implementation to
normalize text. Therefore `μ ≠ µ`, `K ≠ K`, `é ≠ e + U+0301`, and `A ≠ Ａ`.
Potential visual-confusability diagnostics must not silently merge these names.
All accepted original scalar sequences, including decomposed ones, are recoverable.

Let `U` be this lexical name set excluding every name beginning with
`__vastitas_`, including non-ASCII suffixes. This exclusion is about the **decoded
user name**. Keywords, builtin names, and package-reserved words are still
lexically representable, but the host parser must apply its unchanged contextual
rules; codec success is not permission to bind `fn`, `Int`, `compose`, or `mod`.

This defines name text, not declaration identity. Resolution still combines the
name with lexical/module context and hygiene to obtain the actual nominal
declaration. Neither printed name nor origin metadata is a declaration ID,
owner, grant, or proof.

## 3. ASCII printing and common reader

Candidate escape prefix `P = __vastitas_id_` (14 ASCII bytes), deliberately inside
the existing reserved `__vastitas_` namespace. **This is not an adopted spelling.**
Integration must reserve this subnamespace against generated-name allocation as
well; user names and internal generated symbols must remain distinct categories.

For decoded name `n ∈ U`, define:

```
E(n) = n                                  if n is ASCII
E(n) = P ++ lowercase_hex(strict_UTF8(n))   otherwise
```

The entire non-ASCII name is encoded, including any ASCII prefix/suffix. There is
no per-character transliteration and no Unicode normalization. The printer's
input is a decoded name, never an already encoded spelling.

The same reader `R` is used for both human-written and printer-produced tokens:

1. Obtain one complete identifier token from the host lexer with its metadata.
2. If its spelling begins with `P`, require a nonempty even-length sequence of
   lowercase ASCII hex digits; decode hex once and then strict UTF-8.
3. Check the decoded name against the profile **and reserved internal-prefix
   rule**. Require at least one non-ASCII scalar and require `E(decoded)` to equal
   the complete input spelling byte for byte.
4. Otherwise, read strict UTF-8 and apply the same profile and reserved-prefix
   check directly.
5. Return a decoded name occurrence to the ordinary host parser/checkers.

Malformed escape tokens fail completely. There is no longest-valid-hex-prefix
fallback, recursive decoding, trusted-input flag, or acceptance of uppercase hex.
An encoded ASCII name is rejected because its normal ASCII spelling is canonical.
For example, `P ++ 666e` cannot hide `fn`; encoded `__vastitas_λ` is also rejected.

The token-boundary contract matters: the host must lex the full token, not stop
after a decodable prefix. The codec does not parse source text or namespace paths.
Path components are ordinary identifier tokens separated by ordinary punctuation.

| Decoded name | Canonical ASCII spelling | Result |
| --- | --- | --- |
| `λ` | `__vastitas_id_cebb` | admitted name text |
| `_u03bb` | `_u03bb` | different name; legacy spelling preserved |
| `μ` | `__vastitas_id_cebc` | distinct from micro sign |
| `µ` | `__vastitas_id_c2b5` | distinct from Greek mu |
| `K` | `K` | distinct from Kelvin sign |
| `K` | `__vastitas_id_e284aa` | distinct from ASCII K |
| `é` | `__vastitas_id_c3a9` | distinct from decomposed form |
| `e` followed by U+0301 | `__vastitas_id_65cc81` | exact sequence retained |
| `__vastitas_λ` | none | reserved decoded name |
| `⊗` | none in this codec | separate operator syntax proposal |

A human may write `__vastitas_id_cebb` directly: it means `λ`, with no additional
authority. It is not a second user name whose spelling happens to collide.
These reserved ASCII strings were not valid old user names. Conversely, trying
to print the literal decoded name `__vastitas_id_cebb` is rejected as reserved.

## 4. General laws and resource bounds

Let `A = U ∩ ASCII`. Let `S` contain raw UTF-8 spellings of names in `U` and their
canonical escaped spellings. Define `C(s) = E(R(s))` on accepted tokens in `S`.
These are general arguments about the specified algorithms, **not Lean proofs**:

* **Recovery:** `R(E(n)) = n` for every `n ∈ U`. The ASCII branch is unchanged;
  the other branch uses inverse lowercase hex and strict UTF-8 decoding.
* **Injective printer:** if `E(a) = E(b)`, applying `R` yields `a = b`. Equivalently,
  ASCII and escaped images are disjoint because the latter start with the
  reserved prefix; within the escaped image, hex and UTF-8 are injective.
* **Idempotence:** `C(C(s)) = E(R(E(R(s)))) = E(R(s)) = C(s)`.
* **ASCII compatibility:** `E(a) = a` for every `a ∈ A`, including every formerly
  valid ASCII user name. Contextual reserved-name/ownership rules remain in force.

`C` is intentionally **not injective on source spellings**: raw `λ` and its
escaped spelling denote the same name. The injectivity requirement is on `E`
over name identities, not on those synonymous spellings or on whole syntax.

For `n` occupying `b` UTF-8 bytes, output length is `b` for ASCII and exactly
`14 + 2b` otherwise. Time and storage are linear in token size with fixed Unicode
tables (membership uses binary searches of fixed ranges). Python integers avoid
size arithmetic overflow; a Rust port must use checked size arithmetic.

There is no new unconditional name-length cap in the reference, preserving old
ASCII names. Optional `max_name_bytes = B` applies to the **decoded** name on both
input paths. Check escaped payload length before unhex allocation; its accepted
wire spelling may require `14 + 2B` bytes. A host must budget this expansion in
its source/token/output limits. Applying the same smaller raw-byte cap to both
files can break reread closure and is not permitted as an unnoticed codec rule.
Aggregate file/macro/token-count budgets remain a host integration obligation.

## 5. Concrete integration with the existing frontend

Make decoding a normal lexical operation, before any parser or resolver treats
a user identifier as a name. Conceptually replace the current ASCII-only
`TokenKind::Name(name.into())` construction with:

```rust
// Pseudocode: not a patch or current Vastitas API.
let spelling = lex_one_complete_identifier_token(source)?;
let name = read_user_identifier(spelling.utf8_bytes)?; // always, for every input
TokenKind::Name(name) // decoded semantic name; spelling/span/context retained separately
```

Keep syntax token spans in the original byte coordinate system. Preserve decoded
name text through parsing and hygienic expansion, then print identifier spellings
when exposing canonical syntax. Reread printed tokens through the same decoder.
`binding_name`, `name`, index/reference handling, duplicate/shadowing checks,
package resolution, ownership/edit/orphan checks, and downstream checks must see
decoded names. Do **not** add `if encoded { skip_reserved_check() }` or remove
`reserved` from the ordinary binding path.

In particular, `__vastitas_id_cebb` reaches `binding_name` as `λ`; an encoding of
`__vastitas_λ` never becomes a valid user name. Contextual checks can still reject
otherwise valid names. All references and declarations must decode identically
before interning or lookup, including imports, types, endpoints, and macro names.
Audit all ASCII-only validators beyond `frontend.rs` during actual integration.

Both forms must then use the same ordinary parser, resolver, type/ownership/domain
checks, versioned checked IR, and independent Lean-kernel gate. There is no
`--trusted-canonical` mode. Unicode tables, prefix recognition, origin maps, and
hex well-formedness are syntax machinery, not authority evidence.

Compiler-generated names must be represented through internal symbol identities
that user text cannot construct; this user-name decoder is not a backdoor for
reloading them. A display name must never reconstruct a generated symbol, owner,
edit loan, nominal std identity, or privileged monoidal profile. `⊗` remains
outside this codec, and a similar-looking ordinary Unicode name is an ordinary
name. Operator-alias resolution under #220 needs its own semantics and tests.

## 6. Origins, hygiene, and the limit of plain text

The identifier syntax object carries at least `(decoded name, syntax-context
handle, original UTF-8 span, expansion trace)`. Namespace and ownership facts
remain the host resolver/checker's responsibility. Printing changes only spelling.

[`identifier_syntax_reference.py`](../scripts/identifier_syntax_reference.py) demonstrates a host-provided syntax tape with identifier
objects and opaque nonidentifier fragments. It retains a mapping from each
printed identifier's byte interval to its original source span, opaque context
handle, and expansion trace. In-process rereading revalidates spelling and keeps
those same objects. A hex token's expanded byte positions are never mistaken for
original source positions. The fixture uses half-open UTF-8 byte spans and
1-based Unicode-scalar columns, not grapheme-cluster or UTF-16 columns.

The reference maps diagnostics at identifier-token granularity. A production
implementation needing an offending scalar's exact subspan must add a finer
map. Synthesized identifiers and multi-origin macro output require host-owned
origin/expansion records; do not invent contiguous source bytes that never existed.

**Plain ASCII text recovers the name, not the original file position or hygiene.**
On an external reimport, use the new source file's locations and ordinary host
lexical contexts. An origin map may help display diagnostics but cannot grant
owner rights. Do not deserialize caller-supplied hygiene marks as trusted context.
Meaning preservation for post-expansion canonical source requires either retained
in-process syntax contexts or a separately specified, checked reconstruction
format. That format is outside this work. The Python in-process bridge is a
demonstration, not a secure interchange format or independent hygiene validator.

Only host-designated identifier tokens are visited. Strings, paths in literals,
raw/prefixed literals, comments, whitespace, and operators are untouched opaque
data. The fixture retains literal/comment `λ`, the escape-like ASCII text, and
U+2028 byte for byte. It is not a lexer test: supplying correct boundaries is a
host obligation. **The identifier output is ASCII; a document retaining Unicode
comments/literals is not necessarily ASCII-only.** A complete #219 ASCII source
printer must separately define semantics-preserving literal/comment handling.

## 7. Reference evidence versus remaining obligations

| Item | Status |
| --- | --- |
| Fixed lexical profile, exact name identity, E/R/C functions | Implemented in this Python reference |
| Every accepted scalar's basic round-trip; complete code-point profile comparison | Tested against the bundled UCD data |
| ASCII compatibility, malformed escapes, strict UTF-8, reservations, budgets | Regression-tested within this codec |
| Original spans/context/trace retained in a syntax tape | Tested in an in-process adapter |
| Same gate used by raw and encoded names; duplicate/owner denial examples | Tested with an explicitly synthetic host fixture |
| Injectivity, recovery, idempotence for arbitrary finite accepted names | Mathematical arguments above; not mechanized |
| Actual Vastitas parser, resolver, ownership checker, or Lean acceptance | Not implemented or executed by this reference |
| Full lexer token boundaries, all name positions, macro hygiene and capture avoidance | Integration and proof obligations remain |
| Source/checked-IR equivalence, compiler-generated names, canonical std identities | Integration and meaning-preservation obligations remain |
| Whole-program ASCII printing, operator precedence/evaluation, literal/comment semantics | Outside this identifier fragment |

For integration, establish equality of decoded occurrences under the same scope
and syntax contexts; preservation of resolved declaration IDs, owners, shadowing,
and error behavior; and a commuting source-to-canonical semantic correspondence
connected to actual checked IR and the existing Lean gate. Replacing a glyph by
its ASCII escape alone does not establish any of these broader theorems.

The prefix/profile require an explicit language decision. Future Unicode-table
changes require a new profile/edition rule rather than silently following the
runtime. See [the validation report](identifier-ascii-validation.md) for actual commands, results, and bounded evidence.

## 8. Reproduction and follow-up integration acceptance

Python 3.10 or later, standard library only. From the repository root:

```sh
python3 scripts/generate_identifier_unicode.py --check
python3 -m unittest discover -s scripts -p 'test_identifier*.py' -v
python3 scripts/demo_identifier_reference.py
```

The [codec](../scripts/identifier_reference.py),
[syntax adapter](../scripts/identifier_syntax_reference.py), and their
[codec](../scripts/test_identifier_reference.py) and
[adapter](../scripts/test_identifier_syntax_reference.py) tests are development
infrastructure. Existing CI discovers them with `scripts/test_*.py`; neither
ordinary compilation nor generated executables invoke Python or this reference.
[Pinned Unicode data and licensing](../scripts/identifier_data/README.md) are
available offline. No compiler protocol, checker gate, or runtime dependency is
added by this increment.

The subsequent production-integration PR must establish the following with
actual Vastitas source and checked IR, using the reference only as a test oracle:

- [ ] Decode through one path in every supported user-name position, including
  declarations, calls, imports, types, endpoint indices, and exposed macro names.
  Preserve existing valid ASCII source and the supported wire protocols.
- [ ] Under the same dependency snapshot and lexical contexts, raw Unicode and
  its canonical ASCII spelling resolve to the same nominal declarations and
  produce the same semantic checked-IR payload. Compare source-location metadata
  through an explicit origin correspondence; do not erase ownership provenance
  or hygiene to make two outputs appear equal.
- [ ] Both spellings encounter the real duplicate/shadowing, reserved-name,
  visibility, ownership/edit-authority, and domain checks. Test rejection of a
  raw-plus-encoded duplicate declaration and an unauthorized external edit.
- [ ] Malformed escapes, invalid UTF-8, encoded ASCII/internal names, and forged
  generated-symbol or std-profile identities fail through the ordinary path.
- [ ] Original UTF-8 diagnostics and macro expansion contexts survive printing
  and rereading under the supported metadata contract; external text/sidecars
  cannot supply unchecked contexts or authority. Preserve literal/comment bytes
  within this fragment, including U+2028 regression fixtures.
- [ ] Exercise `vastitas check` and `vastitas build`, the actual returned-Core
  connection to independent Lean validation, and valid/invalid integration cases.
  Record remaining source-to-canonical meaning-preservation obligations rather
  than presenting matching examples as a universal proof.

These are follow-up acceptance conditions, not completed tasks. #219 remains
open for whole-source canonicalization and #220 for the admitted operator/sugar
semantics. This reference does not complete either issue.
