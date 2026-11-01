# Historical Stage 1 completion gate

**Historical Stage 1 is not complete.** The initial finite numerical/storage
functionality and bounded runtime-shape interface are implemented and integrated;
the agreed Fast like C acceptance and completion record remain unfinished. The delivery
tracker is [#179](https://github.com/MGYamada/Vastitas/issues/179).

The [acceptance map](stage1-acceptance.md) matches all 48 original/amended conditions
from #66/#67/#69/#91/#92/#183 to source, positive/negative regressions,
actual-checker theorems and native evidence. It distinguishes the initial finite
profile from broader parent-issue objectives. Stage 1b or successful native/BLAS
execution alone does not complete this gate.

| Step | Implementation / issue | Acceptance evidence and status |
| --- | --- | --- |
| Indexed static-call audit | PR #175, merge `e0866c8` | Complete: 205 local tests, kernel regressions, oracle, 6,386-declaration axiom audit, macOS/Linux CI |
| Stabilization | #123–125, #147–149, #169–174, #176–177; PR #185, merge `92091a9` | Complete: 216 local tests, kernel/oracle, 6,391-declaration axiom audit, both OS CI and automatic review passed |
| Finite edit acceptance composition | PR #187, merge `d2f81fd` | Complete for protocol 5 only: same-input/assembly/Core composition, index regressions, oracle, 6,417-declaration audit and both OS CI; #184 remains open |
| Nested edit loans | #181, PR #186, merge `a779a67`; part of #52/#64 | Complete: 222 Rust tests, nine kernel regressions, oracle, integrated 6,780-declaration audit and both OS CI. Protocol 6: explicit delegation, region inclusion, suspended parent authority, inner-first return, complete provenance and final winning-footprint checks; see `edit_authority.rs` and `AuthorityRegression` |
| Permanent authority transfer | #182, PR #186, merge `a779a67`; part of #52/#64 | Complete with the same validation. Protocol 6: immutable definition identity, current owner, explicit transfer, no active loans, retained grants/methods/obligations and revoked former-owner editing; actual-checker proofs in `VastitasOracle.Authority` |
| Indexed declarations and existing geometry | needed #48 foundation; #58–63 and #49 | Complete finite migration in [PR #255](https://github.com/MGYamada/Vastitas/pull/255), with the [acceptance map](geometry-migration.md) and its linked validation record. Canonical scheme/smooth stdlib declarations, one common public source checker (#240, `f2876ef`), typed total evaluation of exact audit/executable Core (#250, `6d1d752`), finite primitive result compatibility and the public source/raw-IR/forged-Core/native regression matrix are in place. Full source operational equivalence and native toolchain equivalence remain unproved and are not claimed by this migration |
| Storage ownership | #183, Core Safety boundary in #180 | The initial affine ownership, initialization, views, caller destinations/scratch, `OwnedMapTo`, versioned packing dependencies and mixed scalar-flow contracts are implemented. [Bounded runtime extents](runtime-shapes.md) add guarded whole-map calls and typed GEMM. [Acceptance map](stage1-acceptance.md#183--affine-storage-and-its-performance-amendment): source/forged-IR tests and actual-checker proofs cover the finite profile; the performance amendment and final completion record remain open |
| Linear algebra and networks | #66/#67/#69/#91/#92 | The initial finite real/complex GEMM, explicit dual/conjugate/evaluation, diagonal adjoint/pairing and connected rank-two/three tree profiles are implemented and [mapped to actual tests/proofs/native evidence](stage1-acceptance.md). Exact source identities, ordered ports, caller packing and written multiplication order are retained. This is not completion of general-rank/structural-node parent scope or controlled-host performance |
| Fast like C | #183/#222 and numerical consumers | **Not passed.** Matched-C output, explicit packing/data costs, shared-host timings and selected Lean-object allocation records exist. Controlled-host measurements, a predeclared tiny-call absolute budget, total allocation/backend-workspace attribution and unresolved slow paths remain acceptance gates; see [the required contract](storage-ownership.md#713-performance-evidence-and-acceptance) |
| Integrated completion | #179 | **Not passed.** The [initial-condition evidence map](stage1-acceptance.md) records integrated runtime shapes and Unit-result optimization at merged `95b848b`. A Stage 1 completion commit still requires the performance gate |

The following records retain their merge-time scope. Later rows and the acceptance map supersede earlier statements that a now-delivered feature was still pending; these historical limits do not create new Stage 1 prerequisites.

| Increment | Merged commit and validation | Scope/limits at that merge |
| --- | --- | --- |
| Bilinear vector evaluation and explicit orthonormal Hermitian pairing, PR #332 | `881270df5413b86063d9dab508c074b89222bddc`; [validation](https://github.com/MGYamada/Vastitas/pull/332#issuecomment-6542785520): 301 Rust tests, six optional numerical tests, 36 kernel regression targets, 19,450-declaration axiom audit and all 17 final-head hosted checks | General metric realization and ideal identities remain open; no floating-point field-law or native refinement claim |
| Executable finite two-map networks, PR #331 | `604d0310c997f7b35dd0e83968865116f7322d89`; [integrated validation](https://github.com/MGYamada/Vastitas/pull/331#issuecomment-6542885966): 306 Rust tests, seven optional numerical tests, 37 kernel regression targets, 19,757-declaration axiom audit and all 17 final-head hosted checks | Exactly two rank-two occurrences and one bilinear edge; higher-rank/multi-edge networks, explicit packing/scratch and categorical laws remain open |
| Optional public GEMM experiment, PR #333 | `5664639143d50288d72bfd35c7ab8a15b33b14e3`; [validation](https://github.com/MGYamada/Vastitas/pull/333#issuecomment-6543004832): all 19 final-head hosted checks, including both Linux smoke jobs; [preserved run](../experiments/public_gemm/results/2026-10-31-linux-smoke/RESULTS.md) covers 16 public check/build/executions, 32 native/sanitizer validations and 454 generated/C output/cost pairs | Smoke validates execution and arena costs, not speed or controlled-host acceptance. Subsequent full-size measurements are recorded below; controlled-host, total allocation/packing and budget acceptance remain open |
| Generative affine owned-map packages, PR #336 | `5681610745d11af6e376924e64e0a70dfe595a16`; [validation](https://github.com/MGYamada/Vastitas/pull/336#issuecomment-6543326912): 309 Rust tests, eight optional numerical tests, 38 kernel regression targets, 20,066-declaration axiom audit and all 18 final-head hosted checks | `OwnedMapTo` closes one primal target and direct basis with static dimensions; general existential resources, dynamic shapes and native refinement remain open |
| Explicit rank-three packing and contraction, PR #340 | `c105811d12034c347f905f94a4a916e40c597631`; [validation](https://github.com/MGYamada/Vastitas/pull/340#issuecomment-6543541549): 313 Rust tests, nine optional numerical tests, 39 kernel regression targets, 20,489-declaration axiom audit and all 18 final-head hosted checks | One explicit rank-three permutation and rank-three/rank-two contraction; general networks, native refinement and equivalent-C performance acceptance remain open |
| Explicit versioned packing caches, PR #342 | `0a1062845dc58f030bc946cf52598db81a5bc9f2`; [validation](https://github.com/MGYamada/Vastitas/pull/342#issuecomment-6544701678): 317 Rust tests, ten optional numerical tests, 40 kernel regression targets, 20,832-declaration axiom audit and all 18 final-head hosted checks | Explicit source/scratch dependency stamps and invalidation; general value retention, AD residuals and implicit reuse remain open |
| Bounded contraction trees, PR #343 | `52bf744d9f73b757cef48d074deff74ca7c5e9c6`; [validation](https://github.com/MGYamada/Vastitas/pull/343#issuecomment-6545469463): all 19 final-head hosted checks and review of `54bdeefd146fde38ab6c2ff27f03ce0196eef7fb` passed | Explicit connected finite trees with rank-two/three intermediates, exact producer/version checks and caller regrouping; general ranks, cycles, structural nodes and controlled-host performance remain open |
| Explicit diagonal metrics, PR #348 | `c394716a08f82b7f320c642fd14c5b55a6a3a8e9`; [validation](https://github.com/MGYamada/Vastitas/pull/348#issuecomment-6545720881): 330 Rust tests, twelve optional numerical tests, 42 kernel regression targets, 22,193-declaration axiom audit and all 21 final-head hosted checks | Exact bounded-Int diagonal realization, caller-destination adjoints, scratch-backed weighted pairing and conditional ideal laws tied to actual certificates; dense forms, dynamic interfaces, native refinement and controlled-host performance remain open |
| Runtime scalar flow through resource calls, PR #349 | `ebf9b5b9deba161a43f2a3865a9e1847cf8e4438`; [validation](https://github.com/MGYamada/Vastitas/pull/349#issuecomment-6551239234): 336 Rust tests, twelve optional numerical tests, 43 kernel regression targets, 23,194-declaration axiom audit and all 21 integrated final-head hosted checks | Immutable Nat/Int/Bool/Unit arguments, intermediate values, completed-call scalar results and runtime Bool branches with both-arm resource auditing; dynamic shapes, branch-result scalar joins, general mutable-heap semantics and native refinement remain open |
| Bounded runtime extents and caller-owned maps, PR #352 | `f0768ae9a8c03bfb74fb9aaeb700a01075a85c51`; [validation](https://github.com/MGYamada/Vastitas/pull/352#issuecomment-6551709456): 342 Rust tests, thirteen optional numerical tests, 44 kernel regression targets, 25,287-declaration axiom audit and all 21 final-head hosted checks | Immutable integral extents, explicit arithmetic guards, whole-map call restoration and typed real/complex GEMM through actual symbolic-to-concrete checker realization; runtime-shaped branches and owned/borrowed results, general transformed interfaces, native refinement and controlled-host performance remain separate |

All listed final heads passed review without findings. The network integration also
checks and executes combined network/vector operations across both branch arms.
These merged increments do not close #67/#69/#91/#183/#179 or #201's wider scope.

## Validated integrated record

[PR #353](https://github.com/MGYamada/Vastitas/pull/353) merged as
`95b848b072712eeee3e2027e0dee275678a3baee` after validation of integrated head
`1ccd60eb81c8ada0266390639862851f7a8719d9`, based on merged #352.
[Exact-head review](https://github.com/MGYamada/Vastitas/pull/353#issuecomment-6551767381)
completed without findings and [combined local validation](https://github.com/MGYamada/Vastitas/pull/353#issuecomment-6551818496)
passed: all 13 optional numerical/source tests, all 13 resource/value-flow tests,
updated native storage/guard matrices and checked GEMM, four fresh-process
shared-result regressions, 25 experiment tests and three retained-record verifiers.
[Final validation](https://github.com/MGYamada/Vastitas/pull/353#issuecomment-6551876034)
records all 21 successful checks on both push and pull_request and no remaining
review findings before the merge. This integration is not performance acceptance.

The production change shares only immutable Unit-success IO results through
pinned Lean's once/persistence APIs. Errors, non-Unit results and arena wrappers
remain fresh; status checks and cleanup remain. The observed generated `finally`
fallback and one retained singleton remain charged. The [production record](../experiments/allocation_audit/results/2026-11-01-macos-production/RESULTS.md)
measures its explicitly retained dirty snapshot, not a later merge.

## Remaining acceptance gates

The integrated implementation and initial-condition mapping are recorded above.
The remaining gates are:

1. Measure competent equivalent C with the same algorithm, scalars, layouts,
   backend/thread count, numerical policy and output contract on a controlled
   host. Include full lifecycle and prepared/reuse scopes with their own complete
   costs. The provisional bulk budget is at most 10% median slowdown for
   representative workloads taking at least 1 ms/sample; uncertainty crossing
   the budget is inconclusive. A dedicated controlled Linux host is currently
   unavailable. That does not waive the gate.
2. Set an absolute tiny-call overhead budget before acceptance, retain raw
   alternating pairs/distributions, and resolve or explicitly review material
   slow paths. Do not choose the threshold after seeing a favorable run or infer
   timing improvement from fewer allocations.
3. Complete the outstanding allocation/peak-memory/backend-workspace attribution
   and representative workload coverage. Arena counters and selected FFI/emitted
   object sites exclude general Lean/allocator/BLAS-private costs. Include visible
   packing/copy/metadata/retained bytes and both cache-resident and memory-bound
   work; state any unmeasured path rather than marking it accepted.
4. Record the completion commit only after these gates pass. Update child issue
   status from concrete evidence while retaining broader parent scope; this
   document does not close issues automatically.

## Existing performance evidence and unresolved gaps

Each record keeps its own exact measured revision and environment. Later compiler
merges do not reattribute those measurements. Raw samples and independent
output/cost verification remain available through the linked reports.

| Record | What it establishes and what remains |
| --- | --- |
| [Explicit storage copy](../experiments/storage_copy/README.md), PR #283 | Matched full-lifecycle/reuse copy work and visible arena costs; shared-VM variance and slower paths do not establish the budget |
| [Full public GEMM](../experiments/public_gemm/results/2026-10-31-linux-full/RESULTS.md), PR #335 | Clean `38b96ae5a6b0610ec71babf199e7635867cca023`, 24 cases/1,256 matched pairs. Tiny lifecycle +329–400 ns, small lifecycle ratios 1.19–1.31; some bulk intervals cross the provisional budget. Shared-host evidence, not controlled acceptance |
| [Full tensor packing](../experiments/tensor_packing/results/2026-10-31-linux-full/RESULTS.md), PR #341 | Earlier `3c1664c698be93041012b5768a76f4fc0d975b31`, 877 matched pairs and native LSan checks. Explicit packing costs are included; tiny lifecycle +408–721 ns and some bulk intervals remain outside acceptance |
| [Full contraction tree with block-copy C](../experiments/contraction_trees/results/2026-10-31-linux-block-copy/RESULTS.md), PR #347 | Clean `82e00e97a6f93ef0b078bdc086f142c5703c6bc4`, 1,325 pairs/24 native records. Tiny lifecycle ratios 2.0860–2.2248, small 1.2584–1.5559; bulk 0.9879–1.0320 with an interval reaching 1.1282. Preserve the older weaker comparison; different CPUs prevent cross-run attribution |
| [Contraction tree with production Unit result](../experiments/contraction_trees/results/2026-11-01-linux-unit-result/RESULTS.md) | Clean `3e3157a19ad3dfcae8c265fa4de68dd097138c38`, 1,313 pairs/24 native records. Tiny lifecycle 1.4233–1.5096 (+566–795 ns), reuse 1.4006–1.4646; bulk lifecycle 1.0017–1.0164 within this shared-host run. 52 measurement batches fell below the calibration target. Different CPUs prevent attributing the change from the older record to Unit sharing; timing and full-cost gates remain open |
| [Diagonal metrics](../experiments/diagonal_metrics/README.md) | Matched prepared and matched-preflight C evidence retains tiny-call/coefficient-pass gaps. Public-source lifecycle, total/backend allocation and controlled-host acceptance remain unmeasured |
| [Runtime shapes](../experiments/runtime_shapes/results/2026-11-01-macos/RESULTS.md) | Dirty base `117a6e972308f25b8ddccd9db536af161d6a322a`, 144 pairs/eight native records/12 failure-cleanup cases, multiple extents and caller destination reuse. Correctness/explicit-cost audit only, no operation timings |
| [Original allocation experiment](../experiments/allocation_audit/results/2026-11-01-macos/RESULTS.md), PR #351 | Selected FFI/emitted-object observation with an experiment-only pthread prototype; preserved unchanged, not production optimization or total-heap evidence |
| [Actual production Unit result](../experiments/allocation_audit/results/2026-11-01-macos-production/RESULTS.md), PR #353 | Actual once/persistent helper, dirty base `24b5f3166c020a38d941e6140338a6ec08e1f3a8`, 96 records/48 pairs. Tracked warm bytes `56N+64` per lifecycle batch and 64 per reuse batch include the `finally` fallback; 16 bytes remain persistent and tracked peak is 88 versus 72 for the private fresh comparator. Arena costs unchanged. No timing, total-heap or controlled-host claim |
| [Stock runtime observation calibration](../experiments/stock_allocation_capabilities/README.md), PR #355 | Merged `6185085` after [17 successful checks and review](https://github.com/MGYamada/Vastitas/pull/355#issuecomment-6552305294). Separate clean macOS `8e516d5` and Linux `8e548d3` records calibrate known main-heap retention/release. Small-object churn has no stock-counter signal; huge `current` remains cumulative after release. This identifies unsupported cost channels, not zero allocation, a leak, total heap accounting or timing acceptance |

Unexpected allocation, hidden copies or asymptotically greater data movement fail
the cost contract even if a timing sample is favorable. Native correctness and
cleanup CI are mandatory evidence, separate from performance acceptance.

The optional [OpenBLAS workspace diagnostic](../experiments/openblas_workspace/README.md)
adds independently replayed pool checkout/return and `memory.c` backing events,
including constructor warmup, partial unmaps and explicit shutdown. Its paired
stock/diagnostic adapter fixtures retain identical calculation objects and output
checks. The diagnostic backend is rebuilt, observes no operation timings, and
does not count actual packing bytes, other backend files, Lean objects, RSS or
generated-source lifecycle totals. These additional attribution channels do not
complete the total-cost or controlled-host gate.

## Implemented proof boundary and broader future scope

The [geometry migration](geometry-migration.md) retains exact returned-Core typed
total evaluation and finite primitive result equations. The resource/numerical
map adds actual source authority, call replay, loan/initialization/byte-region,
nominal basis/port, exact lowering and dependency-history certificates. Runtime
shape realization uses the actual concrete resource/numerical checkers under
explicit valuation/guard premises. Conditional exact-field diagonal adjoint and
pairing laws are tied to actual certificates. Native heap behavior, binary64
arithmetic, FFI/backend correctness and full source/native refinement remain
separately tested or unproved; none is inferred from checker acceptance.

The initial profile does not implement arbitrary resource packages/closures,
floating-point pure Core/Fn/dispatch, dense metric solves, arbitrary-rank/cyclic
networks, structural copy/trace nodes, order-search equivalence or #201's general
categorical laws. These broader extensions remain open parent scope; they are
not extra historical Stage 1 implementation gates. The same separation applies
to general runtime results/transformed interfaces and AD retain/snapshot/recompute
execution. Versions and a checked packing-cache consumer do not implement AD.

The initial 67-issue triage remains in #179. Later work includes full Lean frontend
migration (#152), recursion, partial application, Union, macros, new geometry/gluing,
AD, SU(2), solvers, snapshot-reading integrators and independent compilation caches.
mdBook follows recorded Stage 1 completion in a separate change.

For implementation PRs, run the applicable Rust, kernel, oracle/axiom,
source/native, forged-IR and macOS/Linux boundary checks described in [AGENTS.md](../AGENTS.md).
Documentation-only updates verify links, exact evidence and proof claims without
pretending to rerun unchanged implementation suites. Record actual merged
validation before closing a child; broader parent objectives remain visible.
