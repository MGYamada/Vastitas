# Non-punitive diagnostic reference

This small Python reference exercises [#230](https://github.com/MGYamada/Vastitas/issues/230),
[#231](https://github.com/MGYamada/Vastitas/issues/231), and
[#233](https://github.com/MGYamada/Vastitas/issues/233). It creates readable and
machine-readable projections of **one record**, preserving a rejected result.
It adds no compiler acceptance path, Domain Checker, constitutional theorem,
package lookup, issue publication, or maintainer obligation. The Rust/Lean
compiler and its existing refusal conditions are unchanged.

## Run

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

## Record and trust boundary

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

## Exact identity and advisory grouping

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

## Join, return and repair

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

## Existing connection and missing ledger

The inspected base is main `e01fe1d51fa5faf089e52a7b5a07223031db1b7c`.
`src/ir.rs::Diagnostic` still has code/message/span. The current Lean
`Protocol.diagnosticJson` also emits notes; the adapter preserves them.

`from_kernel_response(response, expected_version)` accepts the actual failure
envelope shape, checks the matching wire version, preserves all diagnostics,
and refuses an accepted response. It does **not** parse provenance out of message
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
