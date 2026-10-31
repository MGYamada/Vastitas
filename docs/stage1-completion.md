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
| Storage ownership | #183, Core Safety boundary in #180 | In progress: [internal resource IR](storage-ir.md) checks provenance, moves, loans, initialization, views and branch joins, with byte-region and active-loan proofs. Exact lowering now generates optional native real/complex buffers, fill/store/copy and transpose views; sanitizer and generated-executable tests cover output preservation and failure cleanup, with allocation/copy counters. The [internal resource-function component](storage-functions.md) now checks owned arguments/results, scoped borrowed arguments, real caller aliases/layouts, exact call-slice replay and destination reuse. [Protocol 8](resource-source.md) now composes static named package resource functions and their pure return blocks with the actual full authority/Fn/dispatch checker and native execution. Dynamic shape/scalar flow, general generative numerical result packages, general scratch/dependency handling, native refinement and end-to-end performance comparisons remain pending; the full contract is in [revised Chapter 7](storage-ownership.md) |
| Linear algebra and networks | #66/#67/#69/#91/#92 | In progress: [PR #289](https://github.com/MGYamada/Vastitas/pull/289), merge `ed217b3`, connects the [optional internal GEMM adapter](numerical-adapter.md) to actual resource access/initialization/separation checks, actual-transition proofs and exact generated native execution. [Validation](https://github.com/MGYamada/Vastitas/pull/289#issuecomment-6520375010): 263 local Rust tests, 32 kernel regression targets, 16,974-declaration axiom audit, seven generated GEMM cases, and all 11 hosted checks including both OS numerical jobs and Linux Valgrind. The [numerical-value compiler](numerical-values.md) now connects public local spaces/bases and typed real/complex products to actual resource/native lowering. [Typed transforms](linear-transforms.md) add explicit dual/conjugate origins, corresponding bases, declared metrics and orthonormal adjoints through actual nested loans/calls. [Vector evaluation](vector-evaluation.md) adds bilinear dual evaluation and explicit orthonormal Hermitian pairing through real borrowed vector arguments and initialized scalar destinations. General generative numerical result packages, dynamic shape/scalar interfaces and general metric realization remain pending. The [two-map network profile](finite-networks.md) now checks occurrence ports, a bilinear edge and explicit boundaries and deterministically emits the existing GEMM. The [finite rank-three contraction](tensor-packing.md) adds actual ordered axes, corresponding-dual contraction and explicit caller-owned packing into one checked GEMM, with coordinate-reference and exact-transition proofs. The [bounded contraction-tree profile](contraction-trees.md) adds explicit finite multi-edge plans, rank-two/three regrouping, reconstructed connectivity and exact producer/resource receipts. General-rank networks, structural nodes and categorical/native-refinement proofs remain pending |
| Fast like C | Cross-cutting architecture/performance goal; #183/#222 and numerical consumers | In progress: [PR #283](https://github.com/MGYamada/Vastitas/pull/283), merge `e026b89`, records two matched-work C-copy runs with raw samples, full lifecycle versus reused/loop scopes and costs. Shared-VM variation and slower cases do not establish the provisional budget or C parity. Bounded initialization coverage now removes redundant whole-input fills from public numerical examples and the shared generated GEMM fixture (768 → 480 written bytes, unchanged allocations/copies/peak data bytes); this is cost evidence, not C parity. End-to-end generated runtime/memory comparisons, explicit packing/retention costs, destination/scratch reuse, and recorded budgets remain required; see [performance acceptance](storage-ownership.md#713-performance-evidence-and-acceptance) |
| Integrated completion | #179 | Pending: complete acceptance mapping, merged commit, exact proof boundaries, examples and CI results |

The latest numerical increments have separate acceptance records:

| Increment | Merged commit and validation | Remaining boundary |
| --- | --- | --- |
| Bilinear vector evaluation and explicit orthonormal Hermitian pairing, PR #332 | `881270df5413b86063d9dab508c074b89222bddc`; [validation](https://github.com/MGYamada/Vastitas/pull/332#issuecomment-6542785520): 301 Rust tests, six optional numerical tests, 36 kernel regression targets, 19,450-declaration axiom audit and all 17 final-head hosted checks | General metric realization and ideal identities remain open; no floating-point field-law or native refinement claim |
| Executable finite two-map networks, PR #331 | `604d0310c997f7b35dd0e83968865116f7322d89`; [integrated validation](https://github.com/MGYamada/Vastitas/pull/331#issuecomment-6542885966): 306 Rust tests, seven optional numerical tests, 37 kernel regression targets, 19,757-declaration axiom audit and all 17 final-head hosted checks | Exactly two rank-two occurrences and one bilinear edge; higher-rank/multi-edge networks, explicit packing/scratch and categorical laws remain open |
| Optional public GEMM experiment, PR #333 | `5664639143d50288d72bfd35c7ab8a15b33b14e3`; [validation](https://github.com/MGYamada/Vastitas/pull/333#issuecomment-6543004832): all 19 final-head hosted checks, including both Linux smoke jobs; [preserved run](../experiments/public_gemm/results/2026-10-31-linux-smoke/RESULTS.md) covers 16 public check/build/executions, 32 native/sanitizer validations and 454 generated/C output/cost pairs | Smoke validates execution and arena costs, not speed or controlled-host acceptance; full-size workloads, total allocation/packing measurements and declared budgets remain open |
| Generative affine owned-map packages, PR #336 | `5681610745d11af6e376924e64e0a70dfe595a16`; [validation](https://github.com/MGYamada/Vastitas/pull/336#issuecomment-6543326912): 309 Rust tests, eight optional numerical tests, 38 kernel regression targets, 20,066-declaration axiom audit and all 18 final-head hosted checks | `OwnedMapTo` closes one primal target and direct basis with static dimensions; general existential resources, dynamic shapes and native refinement remain open |

All four final heads passed review without findings. The network integration also
checks and executes combined network/vector operations across both branch arms.
These merged increments do not close #67/#69/#91/#183/#179 or #201's wider scope.

Wire extension 6 supplies edit authority and 7 supplies indexed declarations.
Version 8 implements the initial static resource source profile and
[numerical declaration profiles](numerical-declarations.md) for ideal real/complex
coefficients and nominal scalar bases. The [numerical-value compiler](numerical-values.md)
now constructs local nominal spaces and bases, attaches maps to actual loans,
and checks typed bilinear GEMM through the real resource/native schedule.
Numerical inputs now retain caller space/basis identities and create scoped child
map loans, including nested calls and destination reuse under explicit static
dimension contracts. Their actual input/binding certificates share the public
checker’s accepted declaration environment. This does not finish the broader
dynamic numerical interface gate.
GEMM coefficients now include explicit real/complex values and initialized 1x1
read loans. Generated source regressions pass earlier GEMM results through calls
as coefficients and execute the rectangular beta=0.5 examples. Actual coefficient
read/init/separation certificates reach the exact native instruction; this is a
specific numerical data-flow path, not general floating Core values or dynamic
shape completion.
Initialized `OwnedMap` inputs and results now retain input-dependent endpoints,
bases, allocation and layout across moves and nested calls. Actual post-body
result checks, initialized-byte theorems, accepted move receipts and public
declaration-origin checks are connected to source/native regressions. Borrowing
the stored layout handles padded results without extra allocations or copies.
General generative numerical packages and dynamic interfaces remain unfinished.

[Owned-map packages](owned-map-packages.md) now add the bounded
`OwnedMapTo<source_basis,target_dimension>` profile: one hidden primal target and
direct basis, initialized affine storage, fresh consuming unpack and explicit
repack. The source basis remains an actual caller dependency. Pack/open/transfer
preserve the exact allocation/layout and emit no additional native instructions.
Dynamic dimensions, general resource packages/closures, borrowed results and
full source/native refinement remain pending.

Public source now independently resolves profile paths and composes those
certificates through the actual checker and native generation. General generative numerical result packages and dynamic shape/scalar
interfaces and general metric realization remain pending.
The [finite two-map network profile](finite-networks.md) now connects public
occurrences, exact port coverage, bilinear edge typing and ordered boundaries to
independent Lean acceptance and one existing overwrite GEMM. Same immutable map
reuse uses distinct ports without new storage ownership. General rank, explicit
trace/copy/pairing nodes, rewrites and order search remain outside this increment;
#69 and #179 stay open. Both frontend and independent kernel must
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

The internal GEMM path supports independent transpose and conjugation flags
(N/T/R/C) without an adapter-created packing buffer. Checker, exact-lowering and
generated-native regressions cover all operand pairs, physical layout and access
obligations, complex coefficients and destination reuse. The public typed
transform composition now supplies actual dual/conjugate-space, basis and metric
evidence, read-child provenance and exact flags through dependent calls. Direct
adjoints require declared identity Gram data in the exact used bases. Raw flags
still do not supply this authority. Actual bilinear evaluation and explicit Hermitian pairing now reach checked scalar destinations; general evaluation/metric laws and realization
remain pending, so #67/#91 remain open.

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
