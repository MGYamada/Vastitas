# std/monad/nature issue and PR review guide

**Status:** Informational review checklist, 2026-11-01. The accepted [ADR 0001](adr/0001-mathematics-first-stdlib.md), its §8 amendment process, and the existing CS/MS/CF, Universe Charter and Lean-kernel proof gates are authoritative. This guide creates no ninth checker, new release deadline or exception. See [integration tracker #386](https://github.com/MGYamada/Vastitas/issues/386).

## One concise issue/PR contract

For an affected mathematical or execution feature, record the applicable entries below. Mark unsupported entries explicitly rather than filling them with guessed implementations.

1. **Decision and responsibility.** Core mechanism, mathematical `std` denotation, named `std::structure` computation (§2A′), optional `monad` execution policy, selected `nature` physical interpretation, bundled realization backend, or ecosystem algorithm/protocol; name the unique model/operation owner and dependency direction.
2. **Mathematical meaning.** Definition, objects and basepoints, domains/regularity, hypotheses, equality/equivalence, dimensional or scalar profiles, positive cases, and negative cases. State which laws belong to a structure and which require separate evidence.
3. **Execution and authority.** Abstract/specification-only versus available exact/reference implementation versus selected numerical/native execution. Declare ordering/rounding/failure/cancellation policies and authority to bind a method or rule; imports alone cannot grant it.
4. **Proof and provenance.** The relevant accepted Core and source/assembly revision; Lean core/Std, pinned mathlib, VastitasMath, or reviewed-none counterpart. For `std::structure` add the accepted-Core **operational body, mandatory correctness claim and independently reported status**; extensional claims also require an appropriate mathematical counterpart. A manifest entry or Python test is not a Lean kernel proof.
5. **Validation.** Distinguish proposed tests from tests actually executed, and distinguish mathematical proof from finite examples, numeric residuals, backend measurements and benchmarks. Include malformed-domain, wrong-basepoint, forged-evidence and unauthorized-owner negatives where relevant.
6. **Status and links.** Link the owning issue, governing ADR, implementation PR and proof/conformance tasks. Keep **design agreed**, **implemented**, **tested**, **kernel-checked** and **released** as separate states.

Do not copy the entire governance charter into each issue or PR. **When changing a normative decision, replace conflicting issue-body language instead of appending a later contradictory note.** The timeline and archived PR evidence already preserve history. Keep current bodies coherent, with any genuinely historical section clearly non-normative; track `specified`, `tested`, `kernel proved` and `native refined` separately. Lean-first semantic definitions are the target for new mathematical families; Python may be an independent test, never proof authority.

## Important standing distinctions

- Mathematical `std` does not silently select approximation schedules; opt-in execution policies and ecosystem realization must be identified.
- Abstract `std::set::Set` is not the executable `std::structure::FinSet` profile. Finite group/ring tables yield checked models of #311/#312, not duplicate types. A fast `.vast` path does not waive #184's applicable Domain obligations or the constitutional gates.
- A generic tensor identity does not authorize an imported module to edit another owner's implementation; model-owned bindings and checked delegation are required.
- Nature's selected quantity, error and physical-action semantics do not prove a numerical simulation or physical interpretation merely by importing a type.
- ADR alignment, issue/PR description edits and reference-program regression tests do not establish an implemented compiler/runtime or completed Lean conformance. No publication or merge is implied by editorial completion.

For concrete owners and pending proof work, use [#386](https://github.com/MGYamada/Vastitas/issues/386) and its linked issues. 
