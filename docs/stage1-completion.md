# Historical Stage 1 completion gate

The delivery tracker is [#179](https://github.com/MGYamada/Vastitas/issues/179).
This document records the accepted implementation scope; unchecked rows are
not implemented or proved merely because they appear here. Stage 1b and the
protocol-5 increment do not complete the historical Stage 1 proposal.

| Step | Implementation / issue | Acceptance evidence and status |
| --- | --- | --- |
| Indexed static-call audit | PR #175, merge `e0866c8` | Complete: 205 local tests, kernel regressions, oracle, 6,386-declaration axiom audit, macOS/Linux CI |
| Stabilization | #123–125, #147–149, #169–174, #176–177; PR #185, merge `92091a9` | Complete: 216 local tests, kernel/oracle, 6,391-declaration axiom audit, both OS CI and automatic review passed |
| Finite edit acceptance composition | PR #187, merge `d2f81fd` | Complete for protocol 5 only: same-input/assembly/Core composition, index regressions, oracle, 6,417-declaration audit and both OS CI; #184 remains open |
| Nested edit loans | #181, PR #186, merge `a779a67`; part of #52/#64 | Complete: 222 Rust tests, nine kernel regressions, oracle, integrated 6,780-declaration audit and both OS CI. Protocol 6: explicit delegation, region inclusion, suspended parent authority, inner-first return, complete provenance and final winning-footprint checks; see `edit_authority.rs` and `AuthorityRegression` |
| Permanent authority transfer | #182, PR #186, merge `a779a67`; part of #52/#64 | Complete with the same validation. Protocol 6: immutable definition identity, current owner, explicit transfer, no active loans, retained grants/methods/obligations and revoked former-owner editing; actual-checker proofs in `VastitasOracle.Authority` |
| Indexed declarations and existing geometry | needed #48 foundation; #58–63 and #49 | Complete finite migration in [PR #255](https://github.com/MGYamada/Vastitas/pull/255), with the [acceptance map](geometry-migration.md) and its linked validation record. Canonical scheme/smooth stdlib declarations, one common public source checker (#240, `f2876ef`), typed total evaluation of exact audit/executable Core (#250, `6d1d752`), finite primitive result compatibility and the public source/raw-IR/forged-Core/native regression matrix are in place. Full source operational equivalence and native toolchain equivalence remain unproved and are not claimed by this migration |
| Storage ownership | #183, Core Safety boundary in #180 | In progress: [internal resource IR](storage-ir.md) checks provenance, moves, loans, initialization, views and branch joins, with byte-region and active-loan proofs. Exact lowering now generates optional native real/complex buffers, fill/store/copy and transpose views; sanitizer and generated-executable tests cover output preservation and failure cleanup, with allocation/copy counters. The [internal resource-function component](storage-functions.md) now checks owned arguments/results, scoped borrowed arguments, real caller aliases/layouts, exact call-slice replay and destination reuse. [Protocol 8](resource-source.md) now composes static named package resource functions and their pure return blocks with the actual full authority/Fn/dispatch checker and native execution. Dynamic shapes/value flow, public nominal numerical types, general scratch/dependency handling, native refinement and end-to-end performance comparisons remain pending; the full contract is in [revised Chapter 7](storage-ownership.md) |
| Linear algebra and networks | #66/#67/#69/#91/#92 | In progress: [PR #289](https://github.com/MGYamada/Vastitas/pull/289), merge `ed217b3`, connects the [optional internal GEMM adapter](numerical-adapter.md) to actual resource access/initialization/separation checks, actual-transition proofs and exact generated native execution. [Validation](https://github.com/MGYamada/Vastitas/pull/289#issuecomment-6520375010): 263 local Rust tests, 32 kernel regression targets, 16,974-declaration axiom audit, seven generated GEMM cases, and all 11 hosted checks including both OS numerical jobs and Linux Valgrind. The [internal numerical-value compiler](numerical-values.md) adds nominal local spaces/bases and typed products connected to actual resource/native lowering. Public real/complex GEMM and nominal object/basis interfaces, dual/conjugation/metric, finite occurrence/port/edge/boundary checks and deterministic contraction schedule remain pending |
| Fast like C | Cross-cutting architecture/performance goal; #183/#222 and numerical consumers | In progress: [PR #283](https://github.com/MGYamada/Vastitas/pull/283), merge `e026b89`, records two matched-work C-copy runs with raw samples, full lifecycle versus reused/loop scopes and costs. Shared-VM variation and slower cases do not establish the provisional budget or C parity. End-to-end generated runtime/memory comparisons, explicit packing/retention costs, destination/scratch reuse and recorded budgets remain required; see [performance acceptance](storage-ownership.md#713-performance-evidence-and-acceptance) |
| Integrated completion | #179 | Pending: complete acceptance mapping, merged commit, exact proof boundaries, examples and CI results |

Wire extension 6 supplies edit authority and 7 supplies indexed declarations.
Version 8 implements the initial static resource source profile and
[numerical declaration profiles](numerical-declarations.md) for ideal real/complex
coefficients and nominal scalar bases. The [internal numerical-value compiler](numerical-values.md)
now constructs local nominal spaces and bases, attaches maps to actual loans,
and checks typed bilinear GEMM through the real resource/native schedule.
Its certificate and generated real/complex fixtures are separate from public
source acceptance. Public constructors and typed GEMM, dependent numerical
interfaces, dual/conjugate/metric operations and public network composition
remain pending. Both frontend and independent kernel must
change together. Protocols 2–5 and explicit `--lib` stay supported; new fields
must not be silently ignored in an old envelope.

Storage ownership is Core Safety, separate from the eight domain checkers in
#180. Mutable resource transitions do not inherit pure-Core semantic theorems.
Mathematical linearity, graph wiring, coherence, and ownership are distinct
obligations. All acceptance proofs must refer to the actual returned IR.

GEMM's initial profile is `F64` and `Complex<F64>`, column-major LP64,
synchronous CPU, explicit `NativeFast`, with OpenBLAS 0.3.34 behind a thin C
adapter. Overwrite must not read old output; accumulate requires initialized
output. Preflight failure must preserve output. Non-numerical compilation and
execution must work without OpenBLAS. Numerical CI uses one thread. Floating
point results and the native implementation remain explicit trust boundaries.

Fast like C is the primary performance and architecture goal. Measure the same
algorithm, scalar semantics, layout, backend and numerical policy against C,
including full-operation and prepared-kernel costs. Record allocation/copy counts
and peak live memory as well as runtime. Performance gaps cannot be silently
deferred while claiming the corresponding Stage 1 acceptance condition complete.
Residual retention is specified now to constrain storage design; AD implementation
and its performance gates remain in the later AD stage.

For each implementation PR, run applicable Rust formatting, strict Clippy and
locked all-target tests; kernel build and direct regressions; oracle build and
transitive axiom audit; source check/build/native execution and malformed or
forged IR rejection. Hosted macOS/Linux no-mathlib checks are a merge gate.
Record merged implementation and validation before closing an issue. Parent
#48/#52/#64 and #159/#160/#165 retain any wider unimplemented scope; #49 and
#58–63 close only after all migration acceptance conditions hold.

The initial 67-issue triage is recorded in #179. Later work includes full Lean
frontend migration (#152), recursion, partial application, Union, macros, new
geometry/gluing, AD, SU(2), solvers, snapshot-reading integrators, independent
compilation caches and convenience warnings. mdBook follows the recorded
Stage 1 completion, in a separate change.
