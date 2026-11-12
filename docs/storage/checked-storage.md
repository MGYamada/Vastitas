# Checked storage and resource calls

This chapter describes the internal resource IR that the kernel checks behind
every resource program. It follows an allocation from the layout and
initialization checks through the resource plan, the native lowering and the
replay of function calls, and it ends with a reference model of layout
preflight. The rules of the language are in
[Storage and ownership](../storage-ownership.md) and
[Resource programs](resource-programs.md).
[Resource checking](../internals/resource-checking.md) describes how the
public checker composes this IR with the package checker, and
[Verification boundaries](../verification.md) states what is proved.

<a id="storage-ir"></a>

## Internal storage resource IR

This is an internal foundation that implements part of the
[Storage and ownership](../storage-ownership.md) contract ([History](#history)). Its raw component envelope is not
a public protocol. [Protocols 8 and 9](resource-programs.md#resource-functions) compose it with independently
checked package resource source. The exact checked component can
produce standalone native buffer executables through the optional runtime below.
The [delivery record](../stage1-completion.md) distinguishes the implemented bounded runtime and numerical consumers from broader interfaces and the Stage 2 performance requirements.

### Input and acceptance

`src/storage.rs` defines an untrusted component schema. The independent decoder
in `VastitasKernel.StorageProtocol` rejects unknown fields, unsupported operations
and integer narrowing: symbols fit unsigned 32 bits, sizes and literal payloads
fit unsigned 64 bits. The checker derives allocation identities and state; callers
cannot supply an allocation identity, initialization flag or checked certificate.
The shared `tests/fixtures/storage.json` exercises the ten buffer actions
(`allocate`, `move`, `drop`, `borrow`, `release`, `transpose`, `fill`, `store`,
`expect` and `copy`), both scalar
representations, all access modes, nested borrowing and both branch arms through
Rust serialization and Lean decoding/checking. `tests/fixtures/storage-gemm.json`
adds `gemm`. This is a component fixture, not
an actual-source lowering fixture.

`Storage.checkPlan` starts from an empty environment, checks both branch arms
even for a literal condition, and requires every owner and loan to be closed at
exit. Its certificate records the exact input, `run` result, final audit and
closed-resource equations. `Wire.CheckedInput` additionally records the decoder
and checker equations. Neither certificate is a public wire input. Protocols
2–7 do not execute this component; protocol 2 explicitly rejects the reserved
top-level `resources` field while retaining unrelated legacy hint compatibility.
Protocols 8 and 9 reconstruct named resource source through the combined package checker.

There is a 4096-node global plan budget as well as a 4096 traversal-depth bound.
Both arms consume the node budget. Every allocation's initialization metadata
has a 4096-node audit budget, checked before traversing its full history.
Repeated writes of an already initialized region reuse its guarantee; identical
branch guarantees share their history, and an empty guarantee annihilates a
branch intersection. A write in only one arm leaves the other arm's unchanged
history; two disjoint writes over the same history retain exactly that common
history. These rules prevent repeated single-cell branch writes from doubling
the history at each join. Overlapping or more complex histories still use an
explicit intersection under the same bound; a join that exceeds it reports
`E_RESOURCE_LIMIT: branch join initialization metadata budget exceeded`.
These are metadata bounds, not limits on buffer elements. This normalization
bounds initialization metadata only. The reconstructed indexes below are
another computation of the whole-state audit. Their theorems are equations
with the original predicates and state no bound. The bound on the work of
resource checking is the budget of
[Resource checking work](#storage-functions--resource-checking-work).

#### Reconstructed audit indexes

The checker reconstructs lookup tables and exact name counts from each state.
For a stack of reborrows it checks that names are distinct, each parent is the
next loan in the list, and the final loan has no parent. Under those conditions,
every pair is related by ancestry and a parent cannot reach its own child.
This takes expected linear work in the number of live loans.
Each loan still needs the correct allocation, a contained layout, compatible
permissions and established initialization. When checking a borrow that adds
a loan, the same shortcut also requires the supplied loan and comparison list
to equal the actual state's complete loan list.

For other loan tables, including valid tables in a different order, the
checker builds bounded ancestor sets. It skips read/read pairs and checks
physical disjointness before ancestry for writer pairs. With expected
constant-time hash lookups, these fallback stages take O(L × depth) and
O(W × L), respectively, for L live loans and W writers. The two compiled
equations `auditState_eq_indexed` and `compatibleWith_eq_indexed` agree with
the original predicates on every input, including duplicate names, cycles
and dangling parents. The [shared chain lemmas](https://github.com/MGYamada/Vastitas/blob/main/lean-kernel/VastitasKernel/LoanChain.lean)
prove the first-match ancestry facts.

Both sides of transitions, joins and the native generation boundary retain
their independent audits. The closed-plan checker meters the actual run and
returns both its original replay equation and its measured work. The compiled
`Native.compile` reuses that exact checked schedule and lowering. Its
`compile_eq_once` theorem covers the full success or diagnostic result.
Public generation still audits a supplied native plan before rendering it.
The weighted limit also covers growing and shrinking loan tables.
[Resource work policy](#storage-functions--resource-checking-work)
Use `python3 scripts/check_storage_scaling.py` with `--sizes`, `--shapes`
and `--kernel-root` to compare identical public inputs under its per-case
deadline. The [earlier measurements](https://github.com/MGYamada/Vastitas/blob/main/experiments/compiler_scaling/results/2026-11-02-macos-storage/RESULTS.md)
record the previous 512-deep timeout. The
[chain comparison](https://github.com/MGYamada/Vastitas/blob/main/experiments/compiler_scaling/results/2026-11-03-macos-reborrow-chains/RESULTS.md)
records the later outcomes and controls.

### Resources and operations

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

The component has seven more actions, which the text below describes:
`regroup3`, `diagonal_adjoint`, `diagonal_scale` and `diagonal_pair` at the
end of [Proofs and regression evidence](#proofs-and-regression-evidence), and
the dependency actions `capture_dependency`, `require_dependency` and
`forget_dependency` of the packing cache.

Symbols cannot be reused or shadowed, including after move or release. Fresh
allocations in different branches get different identities and must be dropped
within the branch under this initial closed-plan profile. The
[internal function component](#storage-functions) additionally checks owned
arguments/results and call-scoped borrowed arguments with caller-owned output
reuse. The public static function profile is described in [resource source](resource-programs.md#resource-functions);
escaping-loan lifetime contracts remain pending.

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
branches. The bounded [packing cache](../linalg/networks-and-packing.md#caches) reconstructs post-pack
source/scratch stamps and rejects stale reuse in actual contraction. Its erased
capture/require/forget operations participate in schedule replay and final audits.
This does not implement residual retention, snapshots, recomputation or AD.

<a id="storage-ir--layout-and-initialization"></a>

### Layout and initialization

The admitted layout is a column-major physical rectangle with an explicit
logical transpose. Offset and capacity are bytes; leading dimension is elements.
`f64` uses 8 bytes and `complex_f64` uses 16 bytes. A nonempty view's offset
must be a multiple of its element width relative to the allocation origin:
8 for real and 16 for complex storage. An offset of 8 into complex storage is
rejected; it cannot pair one element's imaginary component with the next real
component. This typed-element rule is separate from the native ABI's 8-byte
binary64 component alignment.
Scalar literals are raw IEEE payloads, not a public floating-point type or a
claim about floating-point arithmetic. The native adapter checks its matching
representation, base alignment and allocator contract separately.

Rows, columns and leading dimension fit nonnegative LP64 dimensions. Leading
dimension is at least `max(1, rows)`, including empty layouts. Capacities and
computed byte offsets fit the signed 64-bit offset bound. Empty layouts validate
metadata but have no element access and may have an unaligned offset. Arithmetic
uses mathematical `Nat` before checking narrowing.

Containment requires a whole-element offset difference even for contiguous
views, then checks the interval. Containment of a padded
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

A rejected read borrow explains itself after the query has decided. The
explanation is presentation only: it runs on no accepted borrow and changes no
decision. It walks the stored cells of the request in physical order through
the runs of the query, which are the whole interval of a contiguous view and
otherwise one run for each stored column. A step asks the rectangular path
whether one recorded write on every path contains the next cells of the run.
If so, the walk passes these cells and the interval that the fallback
justifies after them, and asks for twice as many cells; otherwise it asks for
half as many. The walk stops at the first cell that no recorded write
contains. The diagnostic names that cell only if the query rejects the cell
alone, as `expect` asks for it, so the explanation has no second definition of
coverage. For a history of n nodes the walk takes at most 65,536 / n steps,
and a step traverses the history at most twice. The dimensions of the view do
not set this work. When the walk ends by its bound or passes every cell, the
diagnostic states that the bounded check did not establish coverage, and names
no cell. [Diagnostics](resource-programs.md#diagnostics) gives the
coordinates of a named cell.

Interleaved views with overlapping envelopes are rejected
when either writes, even if a stronger partition proof could separate them.
Arbitrary strides, read-only broadcast, general partitions and general packing remain
pending. The finite [rank-three packing profile](../linalg/networks-and-packing.md#packing-and-contraction) preserves these
rectangular footprints while explicitly permuting the coordinate grouping.

<a id="storage-ir--native-lowering-and-execution"></a>

### Native lowering and execution

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
[`check_resource_cleanup.py`](https://github.com/MGYamada/Vastitas/blob/main/scripts/check_resource_cleanup.py) check all three
arena envelopes, original error propagation, cleanup-error precedence, single
close/finalization and zero remaining arena data. The injected runtime is a
test-only copy; the returned source is unchanged. An entry without an operation
on an arena has no arena and therefore no envelope: its body is its value flow
([Resource checking](../internals/resource-checking.md#all-body-checking-and-generation)).

`lean-kernel/native/` is an optional, separately locked Lake package with no
compiler, oracle, mathlib or BLAS dependency. Its C adapter uses binary64 doubles
and interleaved pairs of doubles for complex storage. Build-time assertions
check the 64-bit platform profile. Each synchronous operation validates live
allocation handles, scalar representations, full bounds, alignment, LP64
narrowing and signed offset arithmetic before element access. Copy also checks
logical shapes and separation before writing; an identical source/destination
mapping is a no-op. `restrict` appears only in the copy, rank-three packing
(`pack3_kernel`) and block-regrouping (`regroup3_blocks`) kernels, each called
after these checks.
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
contains only Unit: it retains no arena, array or error. Results that hold a
fresh arena, statistics arrays and errors retain their ordinary fresh result objects.

The [bounded allocation record](https://github.com/MGYamada/Vastitas/blob/main/experiments/allocation_audit/results/2026-11-01-macos/RESULTS.md)
motivated this change and reports 16 object bytes for this result in the recorded
64-bit ABI, not a portable size or total heap cost. That historical experiment
published its private alternative through `pthread_once`; production uses Lean's
supported once API instead. A persistent constructor is nonexclusive, so a
generated continuation may allocate its own replacement result rather than
resetting the shared one. The `finally` envelope of the retained records did
so; generated code has no `finally` envelope, as the Unit-only cleanup above
describes. First-touch initialization, repeated FFI returns and
these caller allocations are separate costs. Neither the historical counts nor
this implementation establishes zero total allocation, a speedup, C parity or
native refinement.

The separate [production allocation record](https://github.com/MGYamada/Vastitas/blob/main/experiments/allocation_audit/results/2026-11-01-macos-production/RESULTS.md)
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

The separate [stock Lean allocation capability experiment](https://github.com/MGYamada/Vastitas/blob/main/experiments/stock_allocation_capabilities/README.md)
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

### Proofs and regression evidence

The oracle imports the actual kernel definitions:

| Module | Proved boundary |
| --- | --- |
| `VastitasOracle.StorageLayout` | Every admitted logical cell is in bounds, relatively ABI-aligned and on a whole scalar element boundary (`all_accesses_at_element_boundary`); distinct cells occupy disjoint byte intervals; transpose preserves the footprint; native stride/offset intermediates fit the checked range |
| `VastitasOracle.StorageRegions` | Containment entails inclusion of actual bytes; disjoint envelopes imply disjoint actual bytes; initialization entailment covers requested bytes; normalized writes/joins preserve the logical initialized-byte meaning; bounded interval unions and per-column checks cover actual bytes, with arithmetic work-budget lemmas tied to the actual history traversal; the cell that the explanation of a rejected read names is a cell of the view whose first byte no recorded write initializes on every path (`uncoveredCell_uninitialized`) |
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
intersections. For small layouts and histories, the explanation of a rejected
read names a cell if and only if a cell of the view has an unwritten byte in
that enumeration, and the named cell is the first such cell in physical order.
Public source tests cover caller-owned padded output initialization
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

The public resource source preserves all function, dispatch,
authority and all-body checks, and composes them with this exact resource schedule
and its pre-codegen audit. Owned arguments and results, call-scoped caller-owned
buffers and guarded runtime extents are public
([resource source](resource-programs.md#resource-functions)). Broader
pooling/retained-evidence contracts and controlled-host
performance acceptance remain open. Explicit packing/regrouping and bounded
source/scratch dependency reuse are implemented by the linked numerical checkers. Native liveness, writes and cleanup have the tests
above but no native refinement theorem. Pure indexed Core theorems do not imply
these mutable-resource guarantees.


The [diagonal metric path](../linalg/transforms-and-metrics.md#adjoints-for-diagonal-metrics) adds independently checked raw
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
[contraction-tree checker](../linalg/networks-and-packing.md#contraction-trees). Rank-two regrouping uses a
proved neutral physical extent and creates no nominal third axis.

<a id="storage-functions"></a>

## Internal affine resource functions

This is the function component of [storage ownership](#storage-ir)
([History](#history)). Its raw component schema is not `.vast` syntax or a replacement for package/Fn/dispatch/edit
checks. [The resource source of protocols 8 and 9](resource-programs.md#resource-functions) composes this component
with the complete package checker, including bounded Nat/Int/Bool/Unit value
flow and a separate [guarded runtime-shape frame](resource-programs.md#runtime-extents). Broader numerical interfaces remain open beyond the delivered finite profile. [Stage 1 scope](../stage1-completion.md)

### Contracts and calls

`src/storage.rs::functions` and `StorageFunctionProtocol` share an untrusted
component schema. A program has finite definitions and a closed entry. Function
IDs and local symbols are 32-bit component identifiers; they confer no package
visibility or edit authority. Unknown fields, unsupported parameter kinds and
integer narrowing are independently rejected. The shared component schema
carries owned and borrowed parameters. The rows of the table on scalar
values and on numerical spaces, bases and maps apply to the kernel component
as the resource source of protocols 8 and 9 reaches it.

| Contract | Actual-call behavior |
| --- | --- |
| Scalar value parameter | Preserve its actual typed scalar slot; no resource instruction or buffer copy is introduced. |
| Owned parameter | Check scalar, capacity and required initialized regions; move into a fresh callee binding and revoke the caller binding. |
| Borrowed parameter | Check scalar and logical shape; create a child of the actual caller loan with the declared rights, preserving its real offset, padding, transpose and allocation. |
| Numerical space/basis parameter | Preserve the exact caller identity; check explicit static profile/dimension and preceding parameter dependencies. |
| Numerical map parameter | Check both caller bases and the original live snapshot, create an actual child loan, and audit that its map retains both endpoints and the exact borrow transition. |
| Initialized borrowed output | On successful return, require the whole original argument footprint initialized. A single-cell store does not initialize a larger output. |
| Owned result | Check scalar, capacity and initialized regions; reject duplicates and outstanding loans; move into a fresh caller binding in declared result order. |

Borrowed parameters return inside out at the call boundary. A callee-local
transpose does not change the caller's view or lifetime. Two read arguments may
share a region; a writer still needs actual separation. Parameter names confer
no alias evidence. This initial contract rejects borrowed results and local loan
escape. Every owned input/local allocation must be dropped or explicitly returned.

Contracts specify minimum initialization requirements, not trusted summaries.
Each actual call rechecks the body against its caller's real state and derives
writes from the operations. Argument/result transfer adds no buffer allocation
or alias-repair copy. Callers can lend reusable destinations and scratch; any
additional workspace allocation must appear explicitly in the body.

<a id="storage-functions--all-body-checking-and-exact-expansion"></a>

### All-body checking and exact expansion

The public package checker runs the library's batch of synthetic probes once per
source check. For a selected entry, `checkWithLibrary` takes the certificate for
that exact function list, declaration environment and scalar signatures. It
checks the entry contract, expands the real closed call and audits the resulting
scalar flow, symbolic events and static storage schedule. Its result, including
any diagnostic, equals the standalone function check by
`checkWithLibrary_eq_check`. The oracle theorem
`VastitasOracle.ResourceSource.entry_uses_checked_library`
identifies both the shared probe list and that separate executable expansion.
Nested callees each retain their own replay equation and caller exit audit. The
[public compiler observations](https://github.com/MGYamada/Vastitas/blob/main/experiments/compiler_scaling/results/2026-11-03-macos-resource-probes/RESULTS.md)
compare 200 shared loans at three call depths.

Every function receives a separate synthetic probe, including unused definitions
and both branch arms. Owned probes start with declared initialization; borrowed
probes use a contiguous view with declared rights. These detect invalid bodies,
captures, recursion and missing output initialization. They do **not** prove
acceptance for every layout/alias configuration: a hardcoded subview may fit the
probe yet fail for a shifted/padded caller. Actual calls must pass again. Probe
buffers and zero payloads never enter the executable schedule.

Local symbols are renamed freshly per activation. The mixed `StorageValueFlow`
schedule interleaves checked Core calls with the same resource operations,
including explicit moves, loans and returns. Its projection preserves both branch
bodies for the static resource audit; erasing the decision is not a proof of
source or native equivalence. Independent slot typing and the actual Core target
table justify the runtime Bool expression. Scalar probes use typed input slots,
not fabricated literal values.
Branch-local bindings cannot escape; both arms receive distinct fresh allocation
and symbol identities. Definition order is irrelevant. Disconnected recursive
cycles and invalid unused bodies are rejected.

Each call records the exact schedule that it appends and preserves the preceding
operations. A forwarding call can reuse the last nested call's independent
replay when the complete starting resource state and complete action list
compare equal. On a mismatch or in the absence of a nested receipt it runs the
slice from its own caller state. The call path uses `replayMeteredWithEvidence`.
Its result carries the equation with the original replay for a reused receipt
and for a fresh replay that succeeds. A fresh replay that fails returns its
diagnostic without the equation, and so does an exhausted work budget
(`E_LIMIT`). `replayWithEvidence_eq` proves the same identity, including
failures, for the unmetered `replayWithEvidence` and all inputs.
The [matched public checks](https://github.com/MGYamada/Vastitas/blob/main/experiments/compiler_scaling/results/2026-11-03-macos-nested-replay/RESULTS.md)
measure identical forwarding slices at depths 0, 10 and 30.
The receipt checks the same resulting state, restored caller loans, distinct
live/unborrowed owned results, their initialization contracts and absence of
unreturned local owners. The final entry schedule is checked again from empty
state and must close every resource. Existing native-plan auditing then precedes
generation. No function probe, loan interpreter or per-element ownership/refcount
operation enters the generated program.

Limits are 4096 definitions, 64 parameters/results each, 64 initialized regions
per owned type and 4096 source statements across all definitions. Each probe and
the executable have separate 4096-unit expansion-work budgets, counting calls,
source statements and emitted actions, plus a depth bound. This bounds even
exponential acyclic call expansion. The resulting primitive schedule retains the
storage checker's bounds. These are compiler limits, not buffer-size limits.

<a id="storage-functions--resource-checking-work"></a>

### Resource checking work

The public resource checker admits at most 32,000,000 weighted units across
all definition probes and the executable entry. This policy applies to both
static storage and runtime-shape frames. An over-budget request reports
`E_LIMIT` under both `check` and `build`. The existing 4,096-step limit
still applies independently to each expansion. A straight-line body whose
source statements and direct primitive transitions already exceed it fails
before constructing any loans.

For a frame with `U` used names, `A` live allocations, `R` initialization
nodes, `D` dependencies and `L` loans, the base price is
`1 + U + A + R × (1 + L) + D + L`. General loan tables add
`L × (2 × writers + loans_with_a_parent)` for pair comparisons and bounded
parent walks. The verified child-to-root chain takes the base price. The
symbolic frame has zero storage dependencies. Static initialization traversal
uses the existing bounded history check.

Expansion charges its actual frames and shared branch counter. Replaying a
different call charges each visited frame. An already certified identical
slice pays for the call boundary and comparison. The static and symbolic
projections checked at the end of each probe and entry also contribute.
A library checks probes in declaration order and stops on the first failed
debit. A rejected request can finish one individually bounded probe or entry
before its aggregate debit. Each expansion and each of its two projections
has its own ceiling, so a failing root cannot start an unbounded tail of probes.
The price measures compiler metadata exposure. Native operand sizes and wall
time are separate quantities.

The oracle theorems `VastitasOracle.ResourceSource.library_work_bound` and
`entry_work_bound`
connect both admissions to the actual checked public program and original
body list. `Storage.runMetered` and `Shapes.runMetered` return equations for
the original unmetered schedules and the runtime guard sequence. The two
branch arms share the running total.
The [matched public sources and recorded outcomes](https://github.com/MGYamada/Vastitas/blob/main/experiments/compiler_scaling/results/2026-11-03-macos-resource-work-budget/RESULTS.md)
cover forwarding, long reborrows, disjoint writers and the expansion limit.

### Evidence and remaining boundaries

`VastitasOracle.StorageFunctions` imports the actual component. It extracts exact
call-slice replay and caller-loan restoration, distinct owned results with declared
scalar/capacity and initialized bytes, and exclusion of local owner escape. Every
original body has a checked probe retaining its source ID. Decoder, executable
expansion and final closed-plan equations refer to the same input; generation
requires that certificate. These facts do not prove arbitrary parametric function
contracts, full source correspondence or native refinement.

`tests/fixtures/storage-functions.json` crosses Rust serialization, independent
Lean acceptance and native generation. It covers moved/returned owners,
shifted/padded views, callee-local transpose, shared read aliases, repeated
destination reuse, unused functions and both branch arms. Its success executable
records three allocations/frees, zero live bytes, 128 peak bytes, 128 written bytes
and 64 copied bytes. Two copies reuse one destination; probes add no allocation.
Assertion/allocation failures also close all buffers.
`VastitasStorageTest.FunctionRegression` covers
tampering, a nested forwarding call with separate receipts, actual alias
conflicts, probe/caller layout disagreement, incomplete
initialization, escape, capture, recursion and expansion limits.

Calls expand synchronously at static call sites. Ordinary resource forms retain
static shapes; explicit runtime forms have universally guarded symbolic frames. Public
dependent numerical inputs compose through [protocols 8 and 9](../linalg/maps-and-gemm.md#map-parameters);
the older resource-only internal wire schema remains unchanged. Numerical
input receipts supplement the existing exact call replay and loan-return checks.
Initialized owned-map inputs/results additionally preserve input-dependent bases,
allocation identity and the actual coordinate layout. Their transfer emits only
the existing checked move; temporary loans cannot escape. Result contracts are
checked in the post-body state, and actual-layout loans permit padded/subregion
results to be used inside a generic helper without guessing its physical layout.
See [owned numerical results](../linalg/maps-and-gemm.md#owned-maps).
General tensor types, general pure-Core/resource interoperation, general runtime
shape results, floating scalar expression interfaces, general owned-result branch joins and escaping-loan
lifetime contracts are not supplied by this component. General dynamic source
composition, general generative numerical result packages and general
scratch/dependency handling remain open. The
[delivery record](../stage1-completion.md) assigns the remaining equivalent-C
verdict to Stage 2 or later. Independent compilation caching and broader
lifetime extensions retain their separate scope.

Function bodies are not transactions. Initialization postconditions describe
successful return; native failure after earlier writes does not roll those writes
back, and publishes no initialized success value. Mathematical meaning, physical
writes and native failure behavior remain distinct from logical resource proofs.

[Owned-map packages](../linalg/maps-and-gemm.md#owned-map-packages) add the bounded
`OwnedMapTo<source_basis,target_dimension>` profile: one hidden primal target and
direct basis, initialized affine storage, fresh consuming unpack and explicit
repack. The source basis remains an actual caller dependency. Pack/open/transfer
preserve the exact allocation/layout and emit no additional native instructions.
Dynamic package-result dimensions, general resource packages/closures, borrowed results and
full source/native refinement remain pending.


The [bounded packing cache](../linalg/networks-and-packing.md#caches) adds lexical dependency witnesses
for actual rank-three packing and repeated contraction. Capture/require/forget
remain in the exact replayed call schedule; local witnesses are forgotten before
function and branch exits. Mutations through real dependent calls invalidate the
caller witness, and returned owners do not carry a cache lifetime contract.

Demanded scalar returns retain a `ValueReturnReceipt`: the exact source function
return fragment, final lexical argument resolution, accepted scalar signature,
completed actual resource call replay, and the appended pure call. Its
`RuntimeReturn` additionally retains the exact runtime event/action slice and
restored symbolic caller frame before that scalar return. Public
acceptance independently checks the source function and signature-table origins.
The older internal resource-only JSON decoder does not acquire these public
source forms and still rejects extra fields.

<a id="storage-layout-preflight"></a>

## Dense layout/preflight reference for Ownership/Borrow

Status: executable Python reference and finite regression evidence
([History](#history)). It follows the sections
[Allocation and layout records](../storage-ownership.md#allocation-and-layout-records)
to
[Views, transpose, conjugation and packing](../storage-ownership.md#views-transpose-conjugation-and-packing)
of Storage and ownership, and
[Independent checking and proof boundary](../internals/resource-checking.md#independent-checking-and-proof-boundary).
The Lean statements
below are **proposed proof obligations**, not implemented or proved theorems.
This is a component specification for the existing Ownership/Borrow Checker
(Core Safety), not a ninth Domain Checker or a second public acceptance path.
The public resource checker composes the kernel's own dense layout check,
`Storage.checkLayout` with column-major layouts and an explicit transpose. It
does not compose this Python reference.

### Run and inspect

```sh
python3 scripts/storage_layout_reference.py
python3 -m unittest discover -s scripts -p 'test_storage_layout_reference.py' -v
```

The [reference](https://github.com/MGYamada/Vastitas/blob/main/scripts/storage_layout_reference.py) uses only the Python
standard library and arbitrary-precision integers. The existing CI discovery
of `test_*.py` includes the [regressions](https://github.com/MGYamada/Vastitas/blob/main/scripts/test_storage_layout_reference.py).
The demo prints decisions, never dereferences storage. No buffers, native
pointers, BLAS calls, output writes, or code generation enter its API.

### Closed initial profile

Each live allocation has an identity **and generation**, capacity in bytes,
integer base address and element width/alignment. `World` is an authoritative
fixture snapshot, with a resource epoch and all active loans. It rejects two
live generations of one identity and overlapping nonempty physical allocation
ranges with distinct identities. Actual allocator provenance and liveness must
come from the production resource environment; external metadata cannot assert
them. The integer address is only a model of a pointer, not proof that memory
exists. Initialization and allocator/device/ABI validity remain separate.

A rank-two layout has exact extents, byte strides, byte offset, element
representation, kind and a dense-source descriptor. Supported kinds are:

| Kind | Reconstruction and restrictions |
| --- | --- |
| Column-major dense | Source `(m,n,ld)`, shape `(m,n)`, strides `(w,ld*w)`; `ld >= max(1,m)` |
| Explicit transpose | That same source, shape `(n,m)`, strides `(ld*w,w)`; no conjugation and no allocation |
| Read-only broadcast | A dense source with singleton axes explicitly expanded; expanded strides are zero. Both axes may broadcast. Writes are rejected, including empty broadcasts |
| Other strided descriptors | Diagnostic input only; require additional evidence, even when their envelope is in bounds |

The leading-dimension rule also applies to empty metadata in this initial
profile. Negative strides, packed bits, rank other than two, arbitrary
permutations/partitions, foreign device storage, reshape and adjoint are not
admitted. Malformed rank/element metadata is invalid; a well-shaped negative
stride descriptor needs a separately specified extension. This profile is
incomplete by design, not a decision procedure for arbitrary strided layouts.

`Mode.READ`, `WRITE` and `READ_WRITE` denote requested access. WRITE does not
grant initialized-read rights. READ_WRITE still needs the separate initialization
audit before execution. The reference does not model moves, partial writes,
branch joins, reborrows, suspension, escape, asynchronous completion or retention.

### Separate decisions and closed-form arithmetic

`LayoutReport` separates metadata, provenance, profile reconstruction, bounds,
alignment, write injectivity and native conversion. A failed prerequisite
short-circuits dependent checks; a missing check is not a successful check.
The aggregate priority is INVALID, then NEEDS_EVIDENCE, then SAFE. SAFE means
only that all checks of this limited reference succeeded.

Let `w > 0` be the element byte width and `a > 0` its power-of-two alignment,
with `a | w`. For nonnegative byte strides `s0,s1`, define over integers:

```text
D(L)       = {(i,j) | 0 <= i < rows and 0 <= j < columns}
start(L,i,j) = offset + i*s0 + j*s1
bytes(L,i,j) = [start(L,i,j), start(L,i,j) + w)
region(L) = union of bytes(L,i,j) over D(L)       -- specification only
end(L)    = offset + (rows-1)*s0 + (columns-1)*s1 + w
```

For a nonempty view the range check is `0 <= offset` and `end(L) <= capacity`.
Alignment checks `(base + offset) % a = 0`, and `sk % a = 0` on each axis
whose extent exceeds one. Singleton axes impose no access-stride alignment
obligation. The actual absolute address is checked; an assumed aligned base
does not replace this calculation.

These byte/ABI conditions alone do not preserve a typed allocation's element
origin. The implemented dense resource profile additionally requires nonempty
offsets to be multiples of the scalar width (8 for `F64`, 16 for `Complex<F64>`).
Its strides are whole-element multiples by construction, and containment checks
the relative element boundary as well. This rules out half-complex-element views
even though their component addresses satisfy 8-byte ABI alignment. The broader
strided reference model below is an address/injectivity contract; admitting it as
a typed resource view also requires this element-origin contract.

When **either extent is zero**, `D(L)` and `region(L)` are empty. The code
branches before computing either `extent-1`; validates `0 <= offset <= capacity`
and the descriptor/native fields; and produces no accessible envelope. Access
alignment/injectivity are vacuous, and an unaligned empty offset is permitted.
No element or one-past pointer is formed or dereferenced. Empty metadata can
still fail generation, shape, leading-dimension or native narrowing checks.

For dense writes, different columns are separated by `ld*w >= rows*w` and
different rows by `w`. Thus **whole element byte intervals**, not merely their
start addresses, are pairwise disjoint. Transpose transports that argument by
the explicit index swap. Broadcast is read-only. For unsupported strides the
reference detects only constant-size counterexamples: an active axis with
stride less than width, or `(1,0)`/`(0,1)` whose starts differ by less than width.
Absence of these witnesses does not certify write injectivity.

In particular, `(2,2)`, width 8, strides `(8,8)`, capacity 24 passes bounds and
alignment but fails write injectivity. The dense `(8,16)` counterpart requires
capacity 32 and succeeds. Width 16 with stride 8 also fails, despite distinct
starts. These are byte-safety distinctions, not numerical semantics.

#### Native representability is a separate obligation

The default `NativeLimits` contract uses unsigned 64-bit addresses, nonnegative
signed-64 byte offsets/capacities, and nonnegative signed-32 dimensions/leading
dimensions (LP64). Tests also instantiate smaller limits. The checker validates
`index_bits <= offset_bits <= pointer_bits`; indices are widened to the offset
type before multiplication. It validates
every dimension, stored stride, width, alignment, capacity, offset and final
exclusive end, plus `base + capacity` fitting the address type. This
conservative contract excludes a one-past address equal to `2^pointer_bits`.

For the exact access expression `((offset + i*s0) + j*s1)` and the final byte
end, all intermediate products/sums are nonnegative and bounded by `end(L)`.
Loop increments reach at most the checked extent. Thus the arithmetic fits
without first narrowing or wrapping. The reference computes integers first
and checks conversion second. It does not silently replace overflow by wrap,
saturation or modulo arithmetic. Mathematical bounds can pass while narrowing
fails, including an oversized `ld`, an offset exceeding signed range, or an
absolute address overflow.

This argument covers only those expressions. A flattened `rows*columns` loop,
rounded vector load, pointer pre-increment beyond the last cell, alternative
pointer arithmetic or backend ABI operation needs its own intermediate bounds.
No BLAS or complex-number ABI is certified by this reference.

### Loan compatibility without general partition solving

Preflight checks all active loans together with all requested accesses; the
reference IR gives them simultaneous lifetimes. It also checks old/old pairs,
so an inconsistent input environment cannot mint a successful receipt.

| Condition after layout checks | Decision |
| --- | --- |
| Read/read, including shared broadcast | SAFE |
| Either accessed region empty | SAFE |
| Different allocations in the validated live snapshot | SAFE |
| Same allocation, disjoint enclosing half-open intervals | SAFE |
| Same allocation, an actual common byte is reconstructed | INVALID |
| Same allocation, overlapping envelopes without a supported witness/partition | NEEDS_EVIDENCE |

The actual-overlap witness tests either first accessible byte against the other
dense source using one quotient/remainder by `ld*w`. Transpose has the same
byte set; nonempty broadcasts repeat their source cells. This can prove an
overlap, but is not a complete overlap solver. All other overlapping-envelope
cases require evidence; they never become SAFE by failing to find a witness.
Some NEEDS_EVIDENCE cases really overlap in later columns; the tests include
one. The classification means undecided by this bounded checker, not disjoint.

For width 8, views `(rows=1,columns=3,ld=2)` with offsets 0 and 8 have disjoint
actual bytes and overlapping envelopes. Read/read succeeds. If either writes,
the result is NEEDS_EVIDENCE, not a claim of actual collision. Offsets 0 and 16
have a reconstructible common byte and incompatible loans are INVALID.
No hidden copy repairs either rejection. A later explicit partition checker
may prove more cases; it must bind both exact layouts and the same generation.

For `A` allocations and `L` live/requested accesses, this reference uses
`O(A^2 + A*L + L^2)` metadata operations, with arbitrary-precision arithmetic
cost depending on integer bit length. No preflight loop or storage allocation
depends on `rows*columns`. Full enumeration occurs **only in the small tests**.

### Successful-branch evidence and exact returned IR

The reference flow is `Prepared(ir)` → `PreflightSession.preflight` → either
`(report,None)` or `(report,Success)`. A prepared plan and a successful diagnostic
report are not receipts. Only completed SAFE preflight issues a receipt in that
session; neither INVALID nor NEEDS_EVIDENCE issues one.

`Success.ir` is the **same immutable LayoutIR that this path returns**,
with every access, mode, layout kind/source, allocation generation, operation
identity and revision. The receipt also binds the exact allocation/active-loan
snapshot, epoch and native target. `audit_for_bounds_elision` checks issuance,
full equality against the supplied actual returned IR/current environment,
and independently recomputes preflight. It rejects changed layouts even if
their byte sets happen to agree, including a square transpose. It rejects
other generations at the same address, changed capacities, modes, targets,
operations, loans or epochs. `end_scope` expires the receipt; a different
session or copied/forged receipt cannot consume it.

This demonstrates dependencies in an executable API. Python object identity
is not a production proof, cryptographic capability or defense against arbitrary
Python memory mutation. `LayoutIR` is a **reference IR**, not the compiler's
`Indexed.Core`. Production must reconstruct these facts from actual checked
resource IR, audit the actual returned compiler IR and preserve the successful
branch's control dependency. It must not deserialize a `passed=true` flag or
accept this receipt as a Lean certificate.

No preflight function has a buffer/write callback. Failure preserves output
by construction in this model. The production before-first-write property,
including scratch allocation and external calls, still requires its own proof
and native regression. Snapshot equality does not establish physical liveness;
the resource transition checker must establish stability through the last use.

### Lean soundness targets

These are specification signatures for a checker of the wider profile of this
reference. The theorem names below are proposed, not Lean declarations. The
kernel's `Storage.checkLayout` and `Layout.InDomain` exist with other
signatures, and `VastitasOracle.StorageLayout` and `VastitasOracle.StorageSafety`
prove the corresponding facts for the kernel's dense profile
([Proofs and regression evidence](#proofs-and-regression-evidence)). A checker
of the wider profile must be
implemented in `lean-kernel/` and proved by importing those exact definitions
into `lean/`; copying the Python model into an unrelated proof is insufficient.
No unproved axiom, assumed `AllAccessesSafe`, or enumeration-based acceptance
may substitute for the closed-form proof.

1. `checkLayout`, with the proposed signature below, returns finite
   reconstruction and integer inequalities. Prove
   the universal address/alignment and injectivity lemmas from those facts.
2. `checkNative` proves the specified native address expression equals its
   integer denotation and every intermediate/conversion fits.
3. `checkLoanPair = safe` proves actual region compatibility. Prove soundness,
   not completeness; NEEDS_EVIDENCE need not imply actual overlap.
4. Compose those lemmas with the actual preflight return equation, scope,
   initialization and resource-environment preservation obligations.

For clarity, use `Int` for descriptor arithmetic; `InDomain L i j` abbreviates
the four integer inequalities defining `D(L)` above. `ByteSafe A L i j` means
`0 <= start` and `start+w <= A.capacity` and alignment of `A.base+start`.
`ByteInjective L` means distinct domain indices have disjoint byte intervals.
`NativeExact T A L i j` includes equality of the computed address to the integer
denotation **and** representability of each intermediate in its declared type.
`Compatible A B` permits read/read or actual disjoint regions; different
allocations require validated live provenance, not pointer inequality alone.

```lean
-- Proposed signatures, not compiled code or claims of completed proofs.
theorem checkLayout_all_accesses
    (h : checkLayout env allocKey layout mode = .ok cert) :
    cert.allocKey = allocKey ∧ cert.layout = layout ∧ cert.mode = mode ∧
    LiveGeneration env allocKey ∧
    (∀ i j, InDomain layout i j → ByteSafe (env.lookup allocKey) layout i j) ∧
    (mode.writes → ByteInjective layout)

theorem checkNative_all_accesses
    (hL : checkLayout env key layout mode = .ok lc)
    (hN : checkNative target env lc = .ok nc) :
    ∀ i j, InDomain layout i j →
      NativeExact target (env.lookup key) layout i j

theorem checkLoanPair_sound
    (h : checkLoanPair env left right = .safe proof) :
    Compatible env left right

theorem preflight_returned_ir_safe
    (h : runPreflight env target request = .ok result) :
    result.ir = reconstructActualResourceIR env target request ∧
    EvidenceBoundTo result.evidence env.epoch target result.ir ∧
    (∀ access ∈ result.ir.accesses,
      LiveGeneration env access.allocKey ∧
      (∀ i j, InDomain access.layout i j →
        ByteSafe (env.lookup access.allocKey) access.layout i j ∧
        NativeExact target (env.lookup access.allocKey) access.layout i j) ∧
      (access.mode.writes → ByteInjective access.layout)) ∧
    AllSimultaneousLoansCompatible env result.ir
```

The proof of dense injectivity should order the physical column/row indices:
within a column, distinct starts differ by at least `w`; across columns,
`(j2-j1)*ld + i2-i1 >= ld-(rows-1) >= 1`. Multiply by positive `w` to separate
whole byte intervals. Transpose reduces by the bijection `(i,j) ↦ (j,i)`.
For range/alignment, use nonnegative-stride monotonicity and divisibility.
For empty domains, eliminate the impossible index hypotheses before any
subtraction or pointer construction. Broadcast repeats already safe source
addresses and supplies no write certificate.

#### Conditions for eliminating inner bounds checks

Only a use dominated by the successful preflight event may consume its facts.
The proposed subsequent theorem must quantify the **actual emitted access**:

```lean
theorem dominated_access_safe
    (accepted : runPreflight env target request = .ok result)
    (actual : finalResourceAudit result.ir = .ok auditedIR)
    (same : auditedIR = result.ir)
    (dominates : SuccessfulBranchDominates result.event useSite)
    (stable : ResourcesStableThrough env result.event useSite)
    (emitted : EmittedAccessOf target auditedIR useSite access i j)
    (index : InDomain access.layout i j) :
    ByteSafeAtUse env access i j ∧ NativeExactAtUse target env access i j
```

`EmittedAccessOf` must establish membership in that IR and the exact address
expression/element width; it is not a caller-supplied name match. Range evidence
must come from validated loop bounds or refined indices. `ResourcesStableThrough`
must establish the same live generation, layout, capacity, loans, representation
and target, with no drop/reuse/move or incompatible transition until the last
use. A dynamic preflight event is unavailable before its success branch, on a
failure branch or at a join reachable without success. Static evidence must
provide the same facts without a runtime event. The empty branch emits no
access, even if a backend accepts a null pointer.

Once these facts hold, the particular inner bounds/alignment/overflow tests
they imply can be omitted. Initialization, permissions, nominal/numerical
contracts and lifetime safety remain separate resource/Core obligations;
omitting borrow checks also requires the verified whole loan schedule. The
reference's bounds-elision audit returns only a layout eligibility decision.
It does not implement the above compiler theorem or remove any check.
Optimization changing an address, layout, packing, fusion, loop range or alias
scope must re-audit the actual resulting IR and rebind its evidence. Pairwise
loan compatibility alone never authorizes function-wide `restrict`/`noalias`.

### Evidence ledger

Implemented here: mathematical-integer reference checks, tri-state diagnostics,
explicit transpose/broadcast reconstruction, native-field checks, conservative
loan checks, successful-session receipts and independent reference-IR re-audit.
Regression coverage includes 18,900 small dense/transpose cases against literal
enumeration, 5,184 loan pairs against actual byte sets, small native-boundary
cases, malformed/forged/stale evidence, empty layouts, and a `10^9 × 10^9`
matrix that must finish preflight without enumerating its `10^18` elements.
The subprocess deadline tests the absence of element enumeration; it is not
a native performance benchmark.

Implemented in the kernel, and proved as
[Proofs and regression evidence](#proofs-and-regression-evidence) lists: the
dense layout check, loan compatibility, initialized reads and resource
transitions. Their composition with the resource source of protocols 8 and 9
is implemented as well. Two theorems of the oracle module
`VastitasOracle.ResourceSource` are about it. `entry_uses_checked_library`
states that the certificate of an accepted entry holds the result of
`Functions.checkWithLibrary` on the lowered functions and the checked
library, with the probes of that library. `actual_entry_closed` states that
this result is the result of `Functions.check`, and that the schedule of the
entry runs from the empty state and ends with no allocation and no loan.
[Storage and resource programs](../verification.md#storage-and-resource-programs)
describes the theorems of the module. The tests of the native runtime cover
rejection before the first write.

Pending: Lean counterparts of the parts that only this reference has. These
are read-only broadcast, the alignment of absolute base addresses, the
NEEDS_EVIDENCE verdict, preflight receipts, and the obligations
`preflight_returned_ir_safe` and `dominated_access_safe`. Also pending are
refinement from source to native code, regressions for generated code that
omits a check, and controlled-host acceptance against equivalent C/C++
([History](#history)). These reference tests establish none of those claims.

## History

- [#183](https://github.com/MGYamada/Vastitas/issues/183) delivered the
  internal storage IR, its function component and the layout reference, and
  is closed. The remaining performance acceptance, the controlled-host
  verdict against equivalent C/C++, is Planned under
  [#222](https://github.com/MGYamada/Vastitas/issues/222), which is open. The
  [performance handoff](../stage1-completion.md#stage-2-or-later-performance-acceptance)
  lists its measurements.
- [#422](https://github.com/MGYamada/Vastitas/issues/422) reported the cost of
  the whole-state audit. It is closed.
  [Reconstructed audit indexes](#reconstructed-audit-indexes) and
  [Resource checking work](#storage-functions--resource-checking-work)
  describe the indexed audit and the work budget.
