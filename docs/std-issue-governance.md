# std/monad/nature issue and PR review guide

**Status:** Informational review checklist, 2026-11-01. The accepted [ADR 0001](adr/0001-mathematics-first-stdlib.md), its §8 amendment process, and the existing CS/MS/CF, Universe Charter and Lean-kernel proof gates are authoritative. This guide creates no ninth checker, new release deadline or exception. See [integration tracker #386](https://github.com/MGYamada/Vastitas/issues/386).

## One concise issue/PR contract

For an affected mathematical or execution feature, record the applicable entries below. Mark unsupported entries explicitly rather than filling them with guessed implementations.

1. **Decision and responsibility.** Core mechanism, mathematical `std` denotation, optional `monad` execution policy, selected `nature` physical interpretation, or ecosystem algorithm/protocol; name the model-owning function/module and intended dependency direction.
2. **Mathematical meaning.** Definition, objects and basepoints, domains/regularity, hypotheses, equality/equivalence, dimensional or scalar profiles, positive cases, and negative cases. State which laws belong to a structure and which require separate evidence.
3. **Execution and authority.** Abstract/specification-only versus available exact/reference implementation versus selected numerical/native execution. Declare ordering/rounding/failure/cancellation policies and authority to bind a method or rule; imports alone cannot grant it.
4. **Proof and provenance.** The relevant Core form, source-version/evidence binding, admitted Lean/Mathlib/VastitasMath counterpart or reviewed exception, allowed axiom boundary, and unproved gaps. A manifest item or a Python test is not a kernel proof.
5. **Validation.** Distinguish proposed tests from tests actually executed, and distinguish mathematical proof from finite examples, numeric residuals, backend measurements and benchmarks. Include malformed-domain, wrong-basepoint, forged-evidence and unauthorized-owner negatives where relevant.
6. **Status and links.** Link the owning issue, governing ADR, implementation PR and proof/conformance tasks. Keep **design agreed**, **implemented**, **tested**, **kernel-checked** and **released** as separate states.

Do not copy the entire governance charter into each issue or PR. A short link to the relevant ADR section and this checklist is sufficient. Preserve older design drafts, archived test results and review records as *historical*, while labeling or correcting present-tense assertions that conflict with the accepted decisions.

## Important standing distinctions

- Mathematical `std` does not silently select approximation schedules; opt-in execution policies and ecosystem realization must be identified.
- Abstract `std::set::Set` is not the executable `std::structure::FinSet` profile. A proposed internal fast path does not establish law proofs or waive constitutional gates.
- A generic tensor identity does not authorize an imported module to edit another owner's implementation; model-owned bindings and checked delegation are required.
- Nature's selected quantity, error and physical-action semantics do not prove a numerical simulation or physical interpretation merely by importing a type.
- ADR alignment, issue/PR description edits and reference-program regression tests do not establish an implemented compiler/runtime or completed Lean conformance. No publication or merge is implied by editorial completion.

For concrete owners and pending proof work, use [#386](https://github.com/MGYamada/Vastitas/issues/386) and its linked issues. 
