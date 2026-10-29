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
| Indexed declarations and existing geometry | needed #48 foundation; #58–63 and #49 | In progress: declaration/annotation contracts (#188/#189), audited Core/native generation (#194), compatibility lowering (#195), primitive/package semantics (#196/#198), unresolved declaration/type/body adapters (#200/#202/#205), independent Fn specialization (#212, merge `c3d1abf`), finite scalar dispatch (#213, merge `dd21dd6`), internal edit-authority composition (#215, merge `5e98abc`) with all applied/unapplied bodies, and public protocol 7 (#221, merge `f56edd4`); see `indexed-declarations.md`. Public protocol 7 now connects Rust declarations/bodies to the combined checker; the geometry stdlib now declares the finite affine profile in `std::geometry::scheme` / `std::geometry::smooth` via the single `stdlib` entrypoint. Its explicit checked `geometry_compat` export connects unchanged legacy syntax and new syntax to the same declarations/primitive checker, with 20 source integration tests, 12 direct profile regressions and actual-checker structural proofs. The temporary `stdlib/indexed` facade is removed. Whole-term typed evaluation, legacy semantic correspondence and the separate protocols-2–6 frontend path remain pending |
| Storage ownership | #183, Core Safety boundary in #180 | Pending: allocation provenance, affine moves, read/write loans, initialization, views, branch-state joins and final independent resource audit; required layout/alias/cost contracts are specified in [revised Chapter 7](storage-ownership.md) |
| Linear algebra and networks | #66/#67/#69/#91/#92 | Pending: real/complex GEMM, nominal objects/bases/dual/conjugation/metric, finite occurrence/port/edge/boundary checks and deterministic contraction schedule |
| Fast like C | Cross-cutting architecture/performance goal; #183 and numerical consumers | Pending: equivalent-C runtime and memory comparisons, explicit packing/retention costs, destination/scratch reuse and recorded budgets; see [performance acceptance](storage-ownership.md#713-performance-evidence-and-acceptance). Native compilation and BLAS use alone do not satisfy this gate |
| Integrated completion | #179 | Pending: complete acceptance mapping, merged commit, exact proof boundaries, examples and CI results |

Wire extension 6 supplies edit authority and 7 supplies indexed declarations.
Version 8 (resources/numerics/networks) remains planned. Both frontend and independent kernel must
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
