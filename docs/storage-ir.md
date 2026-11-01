# Internal storage resource IR

This is an internal foundation for [#183](https://github.com/MGYamada/Vastitas/issues/183),
implementing part of the [Chapter 7 contract](storage-ownership.md). Its raw component envelope is not
a public protocol. [Protocol 8](resource-source.md) composes it with independently
checked package resource source. The exact checked component can now
produce standalone native buffer executables through the optional runtime below.
General dynamic source composition, numerical consumers and measured C performance remain in the
[Stage 1 completion gate](stage1-completion.md).

## Input and acceptance

`src/storage.rs` defines an untrusted component schema. The independent decoder
in `VastitasKernel.StorageProtocol` rejects unknown fields, unsupported operations
and integer narrowing: symbols fit unsigned 32 bits, sizes and literal payloads
fit unsigned 64 bits. The checker derives allocation identities and state; callers
cannot supply an allocation identity, initialization flag or checked certificate.
The shared `tests/fixtures/storage.json` exercises every action, both scalar
representations, all access modes, nested borrowing and both branch arms through
Rust serialization and Lean decoding/checking. This is a component fixture, not
an actual-source lowering fixture.

`Storage.checkPlan` starts from an empty environment, checks both branch arms
even for a literal condition, and requires every owner and loan to be closed at
exit. Its certificate records the exact input, `run` result, final audit and
closed-resource equations. `Wire.CheckedInput` additionally records the decoder
and checker equations. Neither certificate is a public wire input. Protocols
2–7 do not execute this component; protocol 2 explicitly rejects the reserved
top-level `resources` field while retaining unrelated legacy hint compatibility.
Protocol 8 reconstructs named resource source through the combined package checker.

There is a 4096-node global plan budget as well as a 4096 traversal-depth bound.
Both arms consume the node budget. Every allocation's initialization metadata
has a 4096-node audit budget, checked before traversing its full history.
Repeated writes of an already initialized region reuse its guarantee; identical
branch guarantees share their history, and an empty guarantee annihilates a
branch intersection. These are metadata bounds, not limits on buffer elements.

## Resources and operations

| Operation | Checked transition |
| --- | --- |
| `allocate` | Fresh logical allocation and owner, byte-size bound, initially unwritten storage |
| `move` | No live loans; preserve identity, initialization and version; revoke old owner |
| `drop` | Live owner without loans; remove the logical allocation |
| `borrow` | Derive allocation from owner or parent loan; check layout, read initialization and pairwise compatibility |
| Reborrow | Child bytes contained in parent; neither read nor write permissions may increase; suspend parent access |
| `release` | Live loan with no children; return loans inside out |
| `transpose` | Swap logical axes, preserving physical allocation and byte footprint; reject suspended parent changes |
| `fill`, `store` | Writable active loan, exact scalar representation; record the whole view or the one addressed cell |
| `expect` | Readable active loan, valid index and initialized cell; native execution asserts the supplied bit pattern |
| `copy` | Active readable source and writable destination with equal scalar representation and logical shape; initialized source. The same loan is an explicit no-op after all access checks; distinct loans require byte separation through the state audit |
| Internal `pack3` | Explicit `[i | k,j]` to `[i,j | k]` permutation into an existing writable rectangle; initialized readable input, matching scalar, bounded dimensions and byte separation; no allocation |
| Internal `gemm` | Initialized readable inputs, exclusive compatible output, explicit NativeFast policy/mode/orientation, independent input/output byte separation; accumulate also requires initialized readable output |
| GEMM coefficients | Matching explicit scalar bits or live initialized readable 1x1 loans disjoint from output; overwrite rejects beta operands, and beta zero does not relax accumulate initialization |
| Branch join | Same owners, allocations and loan structure; intersect initialization guarantees and merge logical versions |

Symbols cannot be reused or shadowed, including after move or release. Fresh
allocations in different branches get different identities and must be dropped
within the branch under this initial closed-plan profile. The
[internal function component](storage-functions.md) additionally checks owned
arguments/results and call-scoped borrowed arguments with caller-owned output
reuse. The public static function profile is described in [resource source](resource-source.md);
dynamic value flow and escaping-loan lifetime contracts remain pending.

Write-only access never reads, and cannot gain read authority by creating a
child loan. An initialized region can instead be reborrowed through an owner
after returning its write-only loan. Read/read sharing is allowed. Active access
with a writer requires distinct allocations or proven disjoint envelopes.
Ancestors may overlap their children only because their access is suspended;
siblings still undergo compatibility checks. Mathematical tensor factors confer
no allocation or alias rights.

`copy(loan, loan)` requires a live, active, initialized `read_write` loan even
though it changes no bytes. It preserves the entire checked state, including
allocation versions and cached dependencies. The exact native lowering emits
no instruction for this case; generated code does not depend on the C adapter's
identical-mapping fast path. Write-only, read-only, suspended and returned loans
remain invalid. This rule is about the same loan identity, not equal dimensions
or a guessed correspondence between different views.

Logical versions advance on writes; a branch join creates a version after both
branches. The bounded [packing cache](cached-packing.md) reconstructs post-pack
source/scratch stamps and rejects stale reuse in actual contraction. Its erased
capture/require/forget operations participate in schedule replay and final audits.
This does not implement residual retention, snapshots, recomputation or AD.

## Layout and initialization

The admitted layout is a column-major physical rectangle with an explicit
logical transpose. Offset and capacity are bytes; leading dimension is elements.
`f64` uses 8 bytes and `complex_f64` uses 16 bytes, with 8-byte relative alignment.
Scalar literals are raw IEEE payloads, not a new public floating-point type or a
claim about floating-point arithmetic. The native adapter checks its matching
representation, base alignment and allocator contract separately.

Rows, columns and leading dimension fit nonnegative LP64 dimensions. Leading
dimension is at least `max(1, rows)`, including empty layouts. Capacities and
computed byte offsets fit the signed 64-bit offset bound. Empty layouts validate
metadata but have no element access and may have an unaligned offset. Arithmetic
uses mathematical `Nat` before checking narrowing.

Containment of a contiguous view uses its interval. Containment of a padded
rectangle additionally checks the row/column shift and compatible column grid;
it never treats padding as initialized. A write records its actual rectangle,
and a scalar store records only its single cell. Branch initialization is the
intersection of both exits. Entailment first tries exact rectangular containment.
Its bounded fallback combines contiguous write intervals in any order, takes the
common covered interval at branch joins, and checks padded requests column by
column without reading their gaps. A padded write is never flattened into its
bounding interval. Every successful query implies coverage of the requested
actual bytes through the same `StorageRegions.initialization_bytes` theorem.

The query checks at most 4096 history nodes before any full traversal. Fallback
interval advancement has a 65,536-node-visit budget, divided among requested
columns; their count must fit that metadata-derived budget before constructing
a range. Large dimensions and allocation capacity do not set the traversal
budget. Exhaustion rejects conservatively. Combinations of padded write profiles
that need stronger symbolic partition reasoning can still be rejected; this is
not a complete geometric union solver. The existing rectangular path continues
to handle large padded rectangles directly.

Interleaved views with overlapping envelopes are rejected
when either writes, even if a stronger partition proof could separate them.
Arbitrary strides, read-only broadcast, general partitions and general packing remain
pending. The finite [rank-three packing profile](tensor-packing.md) preserves these
rectangular footprints while explicitly permuting the coordinate grouping.

## Native lowering and execution

`Storage.Native.compile` reconstructs every native instruction from the actual
checked schedule. `Storage.Native.audit` rechecks that original schedule and
compares the complete lowering, including allocation IDs, layouts, scalar
payloads and both branch arms. `generate` repeats this audit before returning
code. Moves, loans, releases and view transposes are resolved at compilation;
they do not introduce runtime loan objects or per-element reference counts.
The generated program uses structured `IO` with cleanup on success and failure. This mutable
execution remains separate from pure indexed Core and its totality proofs.

The complete generated body returns `IO Unit`. Its success path returns the
cleanup result directly; its error handler runs cleanup once and rethrows the
body error. A cleanup error takes precedence over that body error, as with the
previous `finally` envelope. Nested static/runtime-shape arenas close inside out,
including failure to construct the inner arena. This is a Unit-only codegen
choice, not an implementation of cleanup for arbitrary result types. The actual
public source/build and 23 fault-injection executions in
[`check_resource_cleanup.py`](../scripts/check_resource_cleanup.py) check all three
arena envelopes, original error propagation, cleanup-error precedence, single
close/finalization and zero remaining arena data. The injected runtime is a
test-only copy; the returned source is unchanged.

`lean-kernel/native/` is an optional, separately locked Lake package with no
compiler, oracle, mathlib or BLAS dependency. Its C adapter uses binary64 doubles
and interleaved pairs of doubles for complex storage. Build-time assertions
check the 64-bit platform profile. Each synchronous operation validates live
allocation handles, scalar representations, full bounds, alignment, LP64
narrowing and signed offset arithmetic before element access. Copy also checks
logical shapes and separation before writing; an identical source/destination
mapping is a no-op. `restrict` is confined to the copy kernel after these checks.
Empty views form no data pointer, while still validating metadata. No implicit
packing occurs. A view's transpose swaps axes and does not conjugate values.

Each arena is used synchronously by one caller. Class registration is synchronized
once per arena construction, outside element operations. Data allocation failures
and assertion failures unwind through generated cleanup; the external object's
finalizer provides additional cleanup. Close is idempotent. A live-byte budget
makes allocation failure deterministic in regressions. The raw C/Lean runtime
API does **not** independently establish initialization, source ownership or loan
authority: those obligations come from the exact checked schedule. The C adapter,
FFI ABI, allocator and native compiler remain trusted implementations.

Successful Unit-returning storage and numerical FFI operations share one immutable
`IO.ok ()` result through `vastitas_io_unit_success`. The pinned Lean 4.35
`lean_obj_once` API synchronizes initialization and publication; the result is
marked persistent with `lean_mark_persistent`. The first successful Unit return
constructs it, while later returns use the initialized once cell without creating
another FFI result object. The singleton lives for the process lifetime and
contains only Unit: it retains no arena, array or error. New-arena results,
statistics arrays and errors retain their ordinary fresh result objects.

The [bounded allocation record](../experiments/allocation_audit/results/2026-11-01-macos/RESULTS.md)
motivated this change and reports 16 object bytes for this result in the recorded
64-bit ABI, not a portable size or total heap cost. That historical experiment
published its private alternative through `pthread_once`; production uses Lean's
supported once API instead. A persistent constructor is nonexclusive, so generated
continuations and `finally` may allocate their own replacement result rather than
resetting the shared one. First-touch initialization, repeated FFI returns and
these caller allocations are separate costs. Neither the historical counts nor
this implementation establishes zero total allocation, a speedup, C parity or
native refinement.

The separate [production allocation record](../experiments/allocation_audit/results/2026-11-01-macos-production/RESULTS.md)
observes the actual Lean-once helper and records its measured source snapshots.
In that fixture, reuse allocates 64 observed constructor bytes per batch;
complete lifecycles allocate `56N + 64` fresh object bytes for `N` iterations.
The latter includes each fresh arena result, external wrapper and generated
`finally` fallback. These counts exclude the separately retained 16-byte singleton,
arena data/metadata and unobserved Lean/backend allocations. The private fresh-result
comparator uses the same measured callers and is labeled as an experiment.
Those retained results predate Unit-only cleanup and are not relabeled as current
counts. The allocation and source-cost verifiers reconstruct each complete
wrapper from its actual returned source before selecting the cleanup cost model.

The separate [stock Lean allocation capability experiment](../experiments/stock_allocation_capabilities/README.md)
calibrates observations from the unchanged installed runtime. It detects known
retained/released main-heap objects, but the observed small-allocation counter
has no signal and the huge-byte `current` field remains cumulative after release.
These are measurement limits, not zero-allocation or memory-leak results. Keep
selected FFI events, sampled live blocks, allocator/process backing and backend
workspace channels separate; neither this calibration nor the result-object
optimization completes total-cost or controlled-host performance acceptance.

The adapter reports data allocation/free counts, live and peak data bytes,
written/copied bytes, successful metadata allocations, and the retained
metadata size. Explicit copy reuses its existing destination and allocates no
scratch. These counters exclude Lean objects, allocator overhead and process RSS;
they are not a complete performance or residual-retention measurement.
The shared fixture reports three data allocations, three frees, zero live bytes,
128 peak data bytes, 176 written bytes and 64 copied bytes. Failure fixtures also
finish with zero live data bytes. These observations are regression evidence,
not proofs about native memory or an equivalent-C speed result.

Run `bash scripts/check_storage_native.sh` for strict C compilation with
AddressSanitizer/UndefinedBehaviorSanitizer, all four real/complex transpose-copy
combinations, padding preservation, malformed preflight rejection, alias checks,
destination reuse and standalone generated success/failure executables. Both
no-mathlib CI OS jobs run this gate. `VastitasStorageTest.Emit` is only a test
harness; it does not expose a public wire version or a user-facing interpreter.

## Proofs and regression evidence

The oracle imports the actual kernel definitions:

| Module | Proved boundary |
| --- | --- |
| `VastitasOracle.StorageLayout` | Every admitted logical cell is in bounds and relatively aligned; distinct cells occupy disjoint byte intervals; transpose preserves the footprint; native stride/offset intermediates fit the checked range |
| `VastitasOracle.StorageRegions` | Containment entails inclusion of actual bytes; disjoint envelopes imply disjoint actual bytes; initialization entailment covers requested bytes; normalized writes/joins preserve the logical initialized-byte meaning; bounded interval unions and per-column checks cover actual bytes, with arithmetic work-budget lemmas tied to the actual history traversal |
| `VastitasOracle.StorageSafety` | An audited pair of distinct active loans with a writer cannot share a byte; audited read permissions entail logical initialization; successful action checks audit their input/output; accepted self-copy preserves the exact state; decoder certificates retain the exact checked plan |
| `VastitasOracle.StorageCodegen` | Successful lowering follows the actual checker transitions for both branch arms; self-copy emits no native instruction; checked native instructions are unique for the same input; returned code requires the exact rechecked plan and closed logical exit |
| `VastitasOracle.StorageGemm` | Actual GEMM subject and accepted transition, input/accumulate initialization, output byte separation, and initialized destination bytes in the reconstructed post-state; no nominal or native numerical guarantee |
| `VastitasOracle.StorageFunctions` | Exact call-slice replay, caller-loan restoration, unique owned results with declared initialized bytes, all-body probe coverage and exact decoder/executable/closed-plan connection |

`StorageRegression` compares bounds, injectivity, containment and separation with
an independent enumeration of bytes for small real/complex, padded, shifted,
transposed and empty layouts. It also checks moves, access modes, nested loans,
branch joins, initialization, forged states, metadata budgets and a billion-by-
billion layout and two-half initialization without expanding their elements.
Small independent cell-set tests check real/complex write unions and branch
intersections. Public source tests cover caller-owned padded output initialization
from individual stores, transposed reads and rejection of an incomplete untaken
branch. `VastitasStorageTest.Regression`
checks the Rust fixture and malformed component inputs. Its `NativeRegression`
sibling rejects forged native allocation IDs, sizes, scalars, layouts, payloads,
copy aliases, operation sequences and branch structure before generation.

These theorems do not prove that actual native memory has been allocated or
written, native pointer addition is valid, cleanup occurs on failure, copies or
numerical results are correct, or a complete source program has resource safety.
`expect` acceptance does not prove that memory equals its supplied payload.
The internal state audit validates initialization metadata; only a plan checked
from the empty state reconstructs its history. Arbitrary externally supplied
audited states are not trusted execution histories.

Public/source integration must preserve all existing function, dispatch,
authority and all-body checks, then compose with this exact resource schedule
and its pre-codegen audit. Public owned arguments/results, caller-owned buffers,
dynamic shapes, broader pooling/retained-evidence contracts and controlled-host
performance acceptance remain open. Explicit packing/regrouping and bounded
source/scratch dependency reuse are implemented by the linked numerical checkers. Native liveness, writes and cleanup have the tests
above but no native refinement theorem. Pure indexed Core theorems do not imply
these mutable-resource guarantees, and this increment does not close #183.


The [diagonal metric path](diagonal-metrics.md) adds independently checked raw
`diagonal_adjoint`, `diagonal_scale` and compound `diagonal_pair` transitions.
Raw coefficient metadata establishes only representation/resource safety, not
nominal metric authority. The public path additionally reconstructs coefficients
from actual selected `Metric` values. The compound action checks the exact
scratch write/release/read/GEMM/release execution and invalidates both written
allocation versions. Native preflight covers both destinations before any write.
The internal `regroup3` action carries three physical extents and explicit
input/output axis groupings. It checks complete nontransposed rectangles,
initialization, scalar agreement and byte separation, then performs exactly one
`markWritten` transition on the destination, including cache invalidation.
Public nominal axes and connected producer authority come from the separate
[contraction-tree checker](contraction-trees.md). Rank-two regrouping uses a
proved neutral physical extent and creates no nominal third axis.
