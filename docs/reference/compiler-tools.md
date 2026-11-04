# Development references for diagnostics and identifiers

These independent reference tools exercise diagnostic reports, expected rejection and identifier conversion. Each section states its relationship to the public compiler.

<a id="diagnostic-reference"></a>

## Non-punitive diagnostic reference

This small Python reference exercises [#230](https://github.com/MGYamada/Vastitas/issues/230),
[#231](https://github.com/MGYamada/Vastitas/issues/231), and
[#233](https://github.com/MGYamada/Vastitas/issues/233). It creates readable and
machine-readable projections of **one record**, preserving a rejected result.
It adds no compiler acceptance path, Domain Checker, constitutional theorem,
package lookup, issue publication, or maintainer obligation. The Rust/Lean
compiler and its existing refusal conditions are unchanged.

### Run

```sh
python3 scripts/demo_diagnostic_reference.py
python3 scripts/demo_diagnostic_reference.py --json
python3 -m unittest discover -s scripts -p 'test_diagnostic_reference.py' -v
```

Only Python's standard library is required. The live integration test also needs
`target/debug/vastitas` and `lean-kernel/.lake/build/bin/vastitas-kernel`:

```sh
lake -d lean-kernel build vastitas-kernel
cargo build --locked
python3 -m unittest discover -s scripts -p 'test_diagnostic_reference.py' -v
```

Without those binaries, that test is explicitly skipped. The existing native
compiler CI job runs it after the Rust/Lean builds, on Linux and macOS; the
ordinary Python discovery job also runs the standalone reference regressions.

`--json` always emits one JSON array of reports, including for a single diagnostic
or the synthetic example. A captured failure retains exit status 1, and every
diagnostic and its notes remain in the corresponding array element.

### Record and trust boundary

`scripts/diagnostic_reference.py` separates the unresolved obligation, semantic
participants, conflict set, selected assembly, and current obligation holder.
The reference example lists both crossing methods; it never selects one as the
cause. It distinguishes the original function authority (`base`) from the
method contributions (`addon::A`, `addon::B`) and the reference root assembly
location (`app`). These package IDs, revisions and holder location are
**synthetic reference data, not independently reconstructed checker facts**.

| Information | Current reference behavior |
| --- | --- |
| Mathematical obligation | `dispatch_unique`, unresolved in the join fixture |
| Contributions and authority | Separate roles; synthetic IDs, status `unresolved` |
| Current obligation location | Separate role; reference assembly only, status `unresolved` |
| Verified semantic role | Reserved for #229's actual checked ledger; assertions of `verified` are rejected here |
| External context | `candidate` / `external_heuristic`, retained only as optional context, never trusted |
| Current kernel diagnostic | Original code, message, span and every note preserved; all missing semantic facts remain unresolved |

The default human presentation leads with the obligation, preserves the failure
and next verification action, and explicitly labels the synthetic scope. External
hint details stay in JSON instead of displaying guessed people as semantic
participants. There is no `cause`, guilty package, contact or issue-target field.
Hashing a record does not validate it, authenticate files, prove a ledger, or
validate a borrow history.

### Exact identity and advisory grouping

The schema is `vastitas.diagnostic-reference/1`. Only the closed
`finite-scalar-join-reference/1` identity profile is supported. A complete
synthetic record yields `reference_occurrence_id` with the domain-separated
prefix `vastitas-reference-occurrence-v1:` and SHA-256 of `canonical_occurrence`.
The production `diagnostic_occurrence_id` remains **null**, including for this
fixture. Unsupported origins/profiles cannot produce an ID.

Canonical bytes contain the schema/origin and semantic record: unchanged error
code/outcome/phase, obligation, function, assembly, participants, holder,
conflicts, ordered witness arguments, history, input revision, environment
revision, compiler/toolchain identity, profile and dependency closure/edges.
Encoding v1 is compact ASCII JSON with lexicographically sorted object keys,
ASCII semantic identifiers and no numeric floating-point fields. Normalization
sorts and deduplicates **only** these declared sets:

- participants and complete conflicting contribution references;
- ambiguity witness keys (each key's argument order is retained);
- pinned dependency references and dependency edges.

Borrow/apply/return/seal/reborrow/transfer histories keep **both order and
multiplicity**. A reversed trace produces a different exact reference ID; this
serializer does not claim the reversed trace is a valid program. Presentation
paths, spans, messages, suggested actions and external hints are outside identity.
No timestamps, machine identities or maintenance policies are identity inputs.
Unknown semantic fields and duplicate JSON object keys are rejected instead of
being silently discarded. This is a deliberately restricted encoding, not an
implementation of a general JSON canonicalization standard.

`semantic_issue_key` uses a separate `vastitas-reference-issue-v1:` namespace.
It retains profile, diagnostic code, obligation kind, nominal function and
conflicting declarations, while dropping revisions, environment, custody and
history. It is **advisory**: equal keys can group different occurrences and do
not establish the same bug, unique cause or reusable evidence. Changes to the
grouping policy require a new grouping version independently of exact encoding.

### Join, return and repair

`scripts/demo_diagnostic_reference.py` adapts
`tests/edit_borrowing.rs::open_return_can_be_repaired_by_owner_before_seal`:

| Assembly | Result over all 16 scalar pairs |
| --- | --- |
| `Any x Any` plus A = `Number x Any` | Unique selection |
| `Any x Any` plus B = `Any x Number` | Unique selection |
| Both A and B | Four ambiguous pairs: `{Nat, Int} x {Nat, Int}` |
| Both, then return, then owner's `Number x Number` repair | Unique selection |

The Python experiment uses only these four signatures and all four scalar keys;
it does not implement Vastitas nominal subtyping, capabilities, authorization,
body checking, or borrow acceptance. `package_sources` generates real `.vast`
packages with A/B as separate contributions in the same addon module. The live
regression passes all four assemblies through the existing compiler and records
its exact kernel response with a transparent test tap. The unrepaired join must
still fail with `E_DISPATCH_AMBIGUOUS`, and the repair occurs after `return` and
before `seal`. The tap preserves request/response bytes, mode and exit status.

### Existing connection and missing ledger

The inspected base is main `e01fe1d51fa5faf089e52a7b5a07223031db1b7c`.
`src/ir.rs::Diagnostic` still has code/message/span. The current Lean
`Protocol.diagnosticJson` also emits notes; the adapter preserves them.

`from_kernel_response(response, expected_version)` accepts the actual failure
envelope shape, checks the matching wire version, preserves all diagnostics,
and refuses an accepted response. It checks the shape of the response's
`kernel` build identity but imports nothing from it. It does **not** parse provenance out of message
text, import aliases, local paths or supplied hashes. Saved JSON itself is not an
authenticated checker receipt. With no ledger, phase/obligation ID/participants/
holder/environment remain unresolved and both identity keys are null. The CLI
adapter exits 1 when presenting a captured failure:

```sh
python3 scripts/demo_diagnostic_reference.py --kernel-response response.json --expected-version 5 --json
```

Future #229 integration must export independently reconstructed **partial failure
facts**, tied to the same input/environment and actual returned diagnostic:

- `Edit.prepare`, `Edit.runTrace` and `Edit.assemble` already reconstruct declaration
  origins, grants, applied contributions and ordered transitions. The
  `completeFamilies (finalSurface prepared state)` rejection branch is a concrete
  attachment point for the join failure; it currently throws a plain diagnostic
  and does not return the valid prefix state as a diagnostic ledger.
- `Authority.assemble` extends that path for protocol 6; protocol 7 uses the
  `Indexed.AuthoritySource` composition via `Indexed.Wire.check`. Each needs the
  corresponding checked facts, never a successful-assembly certificate invented
  for a failed assembly.
- The pinned package/input/environment identities, complete conflict set, current
  linear obligation custody and rejected-event position need independent
  reconstruction before verified roles or production exact IDs can be emitted.
  `Main.process` / `Protocol.failureJson` and `src/driver.rs::invoke_kernel` are
  the wire/display connection points. The current reference only imports the
  existing response; it does not modify those boundaries or close #229–#233.

Regression coverage includes the 24 order/relocation variants, set duplicates,
ordered history reversal/repetition, argument order, changed revisions and
environments, advisory grouping, candidate isolation, forged verified roles,
unknown profiles, missing pins, duplicate JSON fields, original notes and failure
status, plus the conditional live join/repair integration described above.

<a id="doctest-result-reference"></a>

## Expected-rejection doctest result contract (reference only)

This is a small result-judgment contract and Python standard-library reference for
[#236](https://github.com/MGYamada/Vastitas/issues/236). It consumes observations
from an ordinary `.vast` check; it does not parse, type-check, interpret, or prove
the example. **The current implementation consumes synthetic result records,
not authenticated driver receipts.** Production doctest extraction/execution,
structured driver result export, and official package admission remain unimplemented.
There is no new Domain Checker, compiler acceptance rule, constitutional theorem,
registry implementation, or Vastitas release/version requirement.

Inspected base: `e01fe1d51fa5faf089e52a7b5a07223031db1b7c` (29 October 2026).
Neither Rust/Lean behavior nor the existing human diagnostic rendering is changed.

### Run and scope of the result

```sh
python3 scripts/demo_doctest_result_reference.py
python3 scripts/demo_doctest_result_reference.py --json
python3 -m unittest discover -s scripts -p 'test_doctest_result_reference.py' -v
python3 scripts/doctest_result_reference.py expectation.json result.json
```

The demo constructs ten **synthetic** observation records. It does not run Vastitas
or Lean. Its hashes are explicitly fixture identities, not measured executable
or source hashes. The last command consumes two JSON files and emits one JSON
report; exit 0 means only that the *reference predicate* returned `passed`.
Every report has `scope: "reference_only"` and `registry_eligible: false`, including
passing reports. This executable must not be installed as an admission gate.

### Why an ordinary compiler failure is insufficient

`tests/driver_issues.rs::mismatched_failure_version_preserves_diagnostics_but_success_is_rejected`
sends a version-3 failure to a version-2 request:

```json
{"version":3,"ok":false,"diagnostics":[{"code":"E_SENTINEL","message":"original diagnostic"}]}
```

The exact payload is retained in
`tests/fixtures/doctest/mismatched-failure-v3.json`. A regression checks that it
still occurs in the existing Rust test. `invoke_kernel` intentionally retains
`E_SENTINEL: original diagnostic` and adds a protocol-mismatch note. The CLI fails;
this is **not** erroneous compiler acceptance. A future doctest using only a
nonzero exit and occurrence of `E_SENTINEL` would wrongly pass this case.

The reference returns `failed / protocol_mismatch` while retaining the original
response and diagnostics without modifying them. Diagnostics remain useful to
humans even when the execution cannot establish a legitimate expected rejection.

### Minimal observation envelope

There are three independently versioned reference schemas:

- `vastitas.doctest-expectation-reference/1`: `schema`, `binding`,
  `match: "exact_code_multiset"`, and nonempty `codes`.
- `vastitas.doctest-result-reference/1`: `schema`, `binding`, `path`, `outcome`,
  `integrity`, `driver_exit_code`, `backend`, and `diagnostics`.
- `vastitas.doctest-report-reference/1`: the reference judgment, its reason,
  missing/unexpected codes, and unchanged copies of the expectation and result.

These are observation/consumer schemas, **not changes to the compiler IR protocol**.
Unknown fields/schema versions, missing required fields, ambiguous duplicate JSON
keys, noninteger JSON numbers, and wrong field types fail closed. In particular,
JSON `true` cannot stand in for version 1 or exit code 1.

| Result field | Required meaning from a future producer |
| --- | --- |
| `path` | `ordinary_vast_check`: normal source loading, frontend, and applicable Lean checks for this exact invocation; a direct kernel subprocess or independent evaluator is insufficient |
| `outcome` | Exactly one of `frontend_rejected`, `kernel_rejected`, `accepted`, `infrastructure_failure`, `interrupted`, `not_run`, `unsupported`, `unknown` |
| `integrity` | `complete` only when observations and the complete diagnostic list belong to this invocation and no capture/transport/truncation/cleanup failure is unresolved; otherwise `unknown` |
| `driver_exit_code` | The normal driver termination code, or null when unavailable; rejection under this pinned contract requires 1, never arbitrary nonzero status |
| `backend.state` | `not_reached`, `completed`, `failed`, or `unknown` |
| `backend.request_version` | The actual serialized request's version, or null when no request was made |
| `backend.exit_code` | The actual process exit code, or null; normal failure in the inspected `Main.main` is 1 |
| `backend.response` | The original decoded response object, or null; preserved even if incompatible |
| `diagnostics` | The complete original structured top-level diagnostic list; never extracted from stderr, messages, notes, or occurrence/grouping keys |

`frontend_rejected` includes ordinary language validation such as a supported
syntax/name error. It does not claim Lean ran or that Rust alone can accept a
program. File I/O, bad CLI arguments, missing dependencies, process failures,
protocol decoding, compiler internal errors, and unsupported checking coverage
must not be labeled language rejections. The future producer must classify the
actual control-flow cause **before rendering**, not infer it from a string prefix.

The reference additionally refuses contradictions containing the existing
non-language codes `E_INPUT`, `E_OUTPUT`, `E_USAGE`, `E_ARGUMENT`, `E_BACKEND`,
`E_BUILD`, `E_PROTOCOL`, `E_INTERRUPTED`, `E_CODEGEN`, `E_LIMIT`,
`E_DISPATCH_LIMIT`, `E_UNSUPPORTED`, or the `E_INTERNAL...` family even if mislabeled
as a rejection. This defensive exclusion is **not a complete code classifier**.
Unknown future failures cannot be promoted to language rejections by their code.
Limit/unsupported examples may remain compiler regression tests, but they cannot
satisfy this supported expected-language-rejection admission criterion.

### Same input, toolchain, profile, and invocation

Both the independently prepared expectation and the observed result carry exactly
the following binding fields. All must agree; absent/unknown pins do not match.

| Binding field | Content to pin |
| --- | --- |
| `invocation_id` | Fresh runner-issued attempt ID; prevents cross-attempt receipt reuse |
| `case_id` | Stable example identity including its package/document/block context |
| `package_revision` | Canonical package/source identity at the submitted immutable revision |
| `input_sha256` | SHA-256 of the complete materialized input snapshot, including the exact generated `.vast` wrapper, snippets, explicit libraries, manifests, and module bytes |
| `dependencies_sha256` | SHA-256 of the complete pinned dependency/lock/assembly/model-resolution environment description |
| `toolchain_sha256` | SHA-256 of a descriptor pinning compiler and configured kernel executable content, toolchain revision, edition, and relevant adapter/diagnostic schema versions |
| `profile_sha256` | SHA-256 of a descriptor pinning `check` mode, target/capabilities, supported protocol/checker profile, relevant flags, environment settings, and resource limits |
| `policy` | `expected-rejection/1`; changes to comparison/classification rules require a new policy |

The runner must freeze these inputs and derive the observation from the actual
invocation, not copy an expectation's hashes into an unrelated response. Hashes
are identity bindings, **not authenticity proofs**. The reference compares pins;
it does not construct or attest source snapshots, resolve dependencies, hash real
executables, verify descriptors, or authenticate JSON. Their canonical production
encoding/collection is a remaining integration obligation under #231/#236.

For a legitimate frontend rejection, no backend process or wire version exists:
all backend values except `state: "not_reached"` must be null. The *configured*
toolchain/profile can still be pinned without executing the kernel. If the
producer cannot establish the required input/environment binding, it must leave
the result nonpassing instead of fabricating completeness or a kernel receipt.

### Judgment and exact diagnostic matching

The algorithm validates the contract, compares the bindings, and handles execution
status **before** matching diagnostics:

1. `not_run` returns `skipped`; `unsupported` returns `unsupported`. Neither is a pass.
2. All candidate passes require the ordinary driver path, complete observations,
   and normal driver failure termination (1).
3. A frontend rejection requires the exact not-reached backend record above.
4. A kernel rejection requires completed capture, normal backend failure
   termination (1), a request version supported by the inspected driver (2–7),
   exactly matching response version, `ok: false`, and the same complete diagnostic
   payload in the response and result. Unknown versions/statuses, malformed
   responses, differing payloads, and protocol mismatches cannot pass.
5. Require at least one diagnostic and exclude operational/unsupported/internal
   failures. Compare the full diagnostic code multisets exactly.

**Matching rule:** compare `Counter(actual_top_level_codes)` with
`Counter(declared_codes)`. Order is irrelevant; **multiplicity matters**. Extra
occurrences of the same code are extra diagnostics unless explicitly declared.
Missing codes, different codes, and additional codes all fail. No substring,
regex, wildcard, subset matching, implicit deduplication, or ignored extra errors
are permitted. Empty expectations are invalid. `missing_codes` and
`unexpected_codes` are sorted lists retaining multiplicity.

Messages, source spans, and notes are preserved but do not participate in code
matching. Notes are not independent top-level errors. There is no severity filter:
the current wire failure list consists of diagnostics with notes. A future schema
with warning/error severity requires an explicit versioned policy; it is not
silently discarded by this reference. This policy tests code occurrences, not
exact failed-obligation identities; it does not claim otherwise.

| Observation with the expected code present | Reference status |
| --- | --- |
| Complete supported frontend rejection, backend not reached | passed |
| Complete supported kernel rejection, compatible protocol and normal termination | passed |
| Version-2 request / version-3 `E_SENTINEL` response | failed |
| Unknown integrity, raw-kernel-only evidence, stale input/toolchain/profile/attempt | failed |
| Backend crash, signal, timeout, transport/capture/cleanup error, compiler internal error | failed |
| Interruption, actual acceptance, different/extra diagnostic, missing observation | failed |
| Not run (including scheduling/hardware skip) | skipped |
| Unsupported required profile/check | unsupported |

### Reuse and concrete driver attachment points

Reuse `src/ir.rs::Diagnostic` and
`lean-kernel/VastitasKernel/Protocol.lean::diagnosticJson`: code, message, span,
and Lean's existing notes. The historical sentinel omits span; the reference
preserves that omission instead of inventing a location. No new diagnostic ID,
participant/owner ledger, or semantic attribution scheme is introduced.

[PR #238](https://github.com/MGYamada/Vastitas/pull/238) already wraps this same
payload as `record.presentation.diagnostic`. A future adapter can use that
unchanged payload and retain the richer record as presentation/provenance context;
it must never use advisory grouping keys or candidate roles to satisfy an
expectation. Its `from_kernel_response` checks the failure envelope/version but
does **not** establish ordinary-driver execution, process completion, or input
binding. Calling that adapter alone cannot produce the observation required here.
This reference uses the existing payload directly and does not fork #238's record
or fingerprint implementation; it has no dependency on that attribution module.

| Existing boundary | Required future connection (not implemented here) |
| --- | --- |
| `frontend::parse_sources` / `src/ir.rs::Diagnostic` | Retain the actual diagnostic vector and typed rejection cause before `Sources::parse` turns it into a String; do not rerun another parser or recover codes from rendered text |
| `src/packages.rs::load` and `src/sources.rs` loading/validation | Preserve language rejection versus file/manifest/environment failure while pinning the source/dependency snapshot; never classify every early return as a frontend rejection |
| `driver::run`, before request serialization/invocation | Carry the same invocation/binding through the ordinary `check` path and record a frontend rejection without a fabricated backend version |
| `process::capture` / `driver::invoke_kernel` | Carry spawn/wait/I/O/interruption/cleanup state and process exit status alongside the decoded response; retain version mismatch as machine data as well as the current human note |
| `Main.process` / `Protocol.failureJson` | Expose structured cause/coverage of failure where needed; `ok: false` currently also covers decode/internal/unsupported failures and is insufficient alone |
| Driver error renderer / `src/main.rs` | Render the original diagnostics from the same result; retain the current human message/note behavior and exit semantics |

`driver::run` and `invoke_kernel` currently return `Result<..., String>`. There is
no production structured end-to-end result emission in this change. A tap of
kernel stdout misses frontend failures and cannot establish full driver integrity.
Do not fill this gap with stderr searching, a second semantic checker, or a JSON
`verified: true` assertion. The unit tests exercise the consumer contract and the
copied existing fixture, not the future producer or Rust/Lean execution.

### Handoff to #236

The reference report identifies `check: "doctest"`, a per-example status/reason,
the declared expectation, original result/binding, and missing/unexpected codes.
The immutable input, toolchain, profile, and policy pins travel with each result.
Human diagnostics remain available even for a failed operational check.

A future #236 orchestrator must enumerate every required example and reconcile
one complete trusted observation per attempt. Missing, duplicated, stale, skipped,
unsupported, malformed, or operationally failed checks must never be omitted from
the aggregate or treated as an expected rejection. Required skipped/unsupported
checks are unresolved admission criteria unless a separately documented compatible
runner/attestation route supplies valid evidence for that same binding.

The orchestrator must **reject this report's `reference_only` scope and
`registry_eligible: false` for admission**, independently of `status`. Production
provenance/receipt collection, full suite inventory/aggregation, non-rejection
doctests, example execution, and the other four checks (`fmt/lint/doc/test`) remain
outside this change. A passing reference predicate is neither compiler acceptance
nor completion of #236. Keep #236 open.

<a id="identifier-ascii-reference"></a>

## Vastitas identifier ASCII round-trip — minimal reference specification

Status: **draft contract and development reference**, 2026-10-29 (JST).
No release target. No compiler change, adopted prefix, Lean proof, or whole-program
meaning-preservation claim is implied.

### 1. Scope and baseline

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

### 2. Fixed identifier profile and identity

Draft profile ID: `vastitas-ident-exact-ucd16-v1-draft`.
Use **Unicode 16.0.0**, not the host runtime's evolving Unicode tables:

```text
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

### 3. ASCII printing and common reader

Candidate escape prefix `P = __vastitas_id_` (14 ASCII bytes), deliberately inside
the existing reserved `__vastitas_` namespace. **This is not an adopted spelling.**
Integration must reserve this subnamespace against generated-name allocation as
well; user names and internal generated symbols must remain distinct categories.

For decoded name `n ∈ U`, define:

```text
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

### 4. General laws and resource bounds

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

### 5. Concrete integration with the existing frontend

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

### 6. Origins, hygiene, and the limit of plain text

The identifier syntax object carries at least `(decoded name, syntax-context
handle, original UTF-8 span, expansion trace)`. Namespace and ownership facts
remain the host resolver/checker's responsibility. Printing changes only spelling.

[`identifier_syntax_reference.py`](https://github.com/MGYamada/Vastitas/blob/main/scripts/identifier_syntax_reference.py) demonstrates a host-provided syntax tape with identifier
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

### 7. Reference evidence versus remaining obligations

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
runtime. See [the validation report](#identifier-ascii-validation) for actual commands, results, and bounded evidence.

### 8. Reproduction and follow-up integration acceptance

Python 3.10 or later, standard library only. From the repository root:

```sh
python3 scripts/generate_identifier_unicode.py --check
python3 -m unittest discover -s scripts -p 'test_identifier*.py' -v
python3 scripts/demo_identifier_reference.py
```

The [codec](https://github.com/MGYamada/Vastitas/blob/main/scripts/identifier_reference.py),
[syntax adapter](https://github.com/MGYamada/Vastitas/blob/main/scripts/identifier_syntax_reference.py), and their
[codec](https://github.com/MGYamada/Vastitas/blob/main/scripts/test_identifier_reference.py) and
[adapter](https://github.com/MGYamada/Vastitas/blob/main/scripts/test_identifier_syntax_reference.py) tests are development
infrastructure. Existing CI discovers them with `scripts/test_*.py`; neither
ordinary compilation nor generated executables invoke Python or this reference.
[Pinned Unicode data and licensing](https://github.com/MGYamada/Vastitas/blob/main/scripts/identifier_data/README.md) are
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

<a id="identifier-ascii-validation"></a>

## Identifier reference — validation report

Run date: 2026-10-29 (JST). Interpreter: Python 3.12.14.
Repository base: `e01fe1d51fa5faf089e52a7b5a07223031db1b7c`.
Dependencies: Python standard library and the bundled Unicode 16.0.0 tables.
The host Python Unicode database is not used for identifier membership.

### Commands and results

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

### Coverage

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
  observed collisions. The general laws are argued in [the specification](#identifier-ascii-reference), not inferred
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

### What this establishes

The delivered implementation passes the stated identifier-level regressions
under the fixed profile. The common reader, exact-identity policy, disjoint
ASCII/escape representation, and in-process metadata retention work within
the tested reference interfaces.

It does **not** establish adoption of the prefix, acceptance by the current
Vastitas compiler, full-source ASCII canonicalization, actual hygienic expansion,
whole-program semantic equivalence, namespace/owner proof preservation, or a
Lean theorem. In particular, external ASCII text alone does not reconstruct
original locations or macro contexts. The remaining integration obligations
are listed in [the specification](#identifier-ascii-reference) sections 5–7.
