# Expected-rejection doctest result contract (reference only)

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

## Run and scope of the result

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

## Why an ordinary compiler failure is insufficient

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

## Minimal observation envelope

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

## Same input, toolchain, profile, and invocation

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

## Judgment and exact diagnostic matching

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

## Reuse and concrete driver attachment points

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

## Handoff to #236

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
