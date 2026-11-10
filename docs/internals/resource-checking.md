# Resource checking

This chapter describes how the compiler checks and generates
[resource programs](../storage/resource-programs.md): the composition of the
pure and resource checkers, the reconstruction of diagnostics, the symbolic
frames of runtime extents, and the evidence for each. The rules of the
language are in the Reference chapter.
[Checked storage](../storage/checked-storage.md) describes the internal
resource IR that these checks produce.

## Independent checking and proof boundary

Public protocol 8 must carry enough untrusted layout, region, transition and
dependency information for Lean to reconstruct the resource schedule independently.
Rust annotations, serialized proof flags, claimed alias facts and alleged
initialization are not evidence. Older protocols must reject unsupported fields.

The actual returned IR must be checked at acceptance and again before native generation.
If optimization changes allocation, fusion, packing, alias scope or retention,
the resulting plan must be reconstructed and checked. Proofs must refer to that same plan
and native lowering contract, not a separately hand-constructed resource model.

Required proof obligations are preservation of live ownership, loan compatibility,
initialized reads, region bounds, scope and dependency validity across admitted
transitions and joins. Runtime checks establish facts that depend on runtime sizes;
their evidence cannot be assumed earlier than the successful branch.
Native ABI, allocator, BLAS, floating-point and hardware behavior remain explicit
trusted boundaries. None of these resource proofs alone proves C-level speed,
whole-program mathematical meaning or higher-order differentiation correctness.

## Implementation status

The [dense layout/preflight reference](../storage/checked-storage.md#storage-layout-preflight) supplies an
executable integer model, regression cases and proposed Lean obligations for
the first dense/transpose fragment. It is not production resource acceptance,
completed Lean soundness, native check elimination or performance evidence.

The [internal resource IR](../storage/checked-storage.md#storage-ir) supplies independently checked
logical transitions, canonical layouts, initialization and branch joins, with
actual-checker byte-region and active-loan theorems. Its component schema is not
public protocol 8. Its optional native runtime and
[internal resource functions](../storage/checked-storage.md#storage-functions) exercise allocation, calls,
destination reuse and failure cleanup. [Protocol 8](#composition-with-the-package-checker) connects the static resource profile
to package source and pure return blocks, including local nominal real/complex
GEMM. Bounded partial-write coverage removes redundant input fills in the worked
numerical examples; its actual-byte theorems and native operation counters are
recorded in [the resource IR](../storage/checked-storage.md#storage-ir). Checked scalar value flow and the
[whole-map runtime-extent profile](../storage/resource-programs.md#runtime-extents) connect immutable
integral dimensions to caller-owned GEMM. [Explicit caches](../linalg/networks-and-packing.md#caches)
and [contraction trees](../linalg/networks-and-packing.md#contraction-trees) cover bounded scratch/dependency
consumers. General shape results, retention/pooling and equivalent-C acceptance
remain pending.

## Composition with the package checker

Protocol 8 connects explicit resource functions to the ordinary `.vast` package
compiler. Names, imports, visibility, canonical module owners, indexed declarations,
finite dispatch and edit assemblies share the same namespace. The existing
`Indexed.AuthoritySource` checks every ordinary, applicable, nonwinning and
unapplied pure body. Resource bodies then pass independent ownership, layout,
initialization and actual-call checks. Static shapes retain their original contracts. The separate
[runtime-extent profile](../storage/resource-programs.md#runtime-extents) supports whole-map caller interfaces;
scalar values flow between checked pure computations, resource calls and runtime branches.
This bounded profile does not complete [Stage 1](../stage1-completion.md).

### Payload spellings

The payloads `f64(…)` and `complex(…)` are source sugar for the unsigned-bit payloads, with no wire/schema
change or runtime conversion. The frontend checks hex precision/range with
integer arithmetic; for decimals it compares the candidate's exact integer
decimal expansion with the original value before accepting its bits. Lean
continues to check the same literal scalar tags and resource authority. This
frontend conversion is tested, not a Lean source-literal refinement theorem
or an IEEE field-law claim. It does not introduce pure floating scalar values or
arithmetic into the existing Nat/Int dispatcher.
Allocation sizes and layout arguments are static metadata. An explicit
`coefficient(loan)` operand instead reads an initialized scalar at GEMM execution;
it does not introduce general scalar expression flow between resource statements.

### All-body checking and generation

Every resource definition is checked, including unused dependencies. Check-only
libraries use actual all-body probes without a fabricated main. A package with
a resource entry reuses that checked probe list and independently expands its
actual entry schedule as described in [resource functions](../storage/checked-storage.md#storage-functions--all-body-checking-and-exact-expansion).
Source owners,
local symbols and call IDs are reconstructed; the public input cannot provide
allocation IDs, checked Core, alias assertions or trusted initialization flags.
Versions 2–7 reject resource declarations rather than discarding them.

Generation rechecks the original mixed schedule, its resource projection and
every native instruction, plus the actual pure Core module, exact fragment
targets and dependency order. A fragment is keyed by its canonical resource
owner and structural source position. Its ordered scalar argument slots must
match the actual checked Core signature. A program has at most 4096
fragments, one for each `value` statement and one for the `value` block that
ends each resource function. The kernel's decoder reads the body of one
resource function with 4096 units of fuel, which the arms of an `if` share
with the statements up to that `if`. The frontend measures both bounds and
reports a program beyond one at a function (`E_RESOURCE_LIMIT`). The kernel
keeps both for a request that the frontend did not write: it refuses such a
body as a malformed request (`E_PROTOCOL`) and such a table of fragments as
invalid (`E_CAPTURE`). Runtime conditions are emitted from
those checked Bool slots; neither arm is selected during resource checking. The same
resource main supplies both the schedule and its pure return block. Native IO uses
structured cleanup, including failure paths; a failed resource operation does not
publish the pure return value. Earlier completed writes are not rolled back.
The Unit-returning main closes its arenas on success and closes/rethrows on
failure; a cleanup error overrides the body error. When both static and dynamic
arenas exist, the inner arena closes first. See the
[native cleanup contract and fault-injection checks](../storage/checked-storage.md#storage-ir).

The generated `main` creates an arena for a checked operation that uses one,
and for nothing else. It creates the static arena when the audited native plan
of the entry holds an instruction on an allocation. These instructions are
allocation, drop, fill, store, `expect`, copy, packing, regrouping, GEMM and
the diagonal operations. The markers of a branch are not among them. It
creates the runtime-shape arena when the checked schedule holds a
runtime-shape event: an operation of a `runtime_` statement or a guard on
runtime extents. An entry with neither holds `value` statements, scalar
branches and calls that expand to these. Its `main` holds the value calls and
the branches and then prints the result. It creates no arena and has no
cleanup. The kernel states the requirement with the source, as
`storage_runtime` in the [emit response](../protocol.md). The source imports
the storage runtime when the requirement holds. The driver compares and links
the storage package under that requirement. It refuses a source that imports
the storage runtime without it ([CLI reference](../guide/cli.md)).

A failing `expect` raises `E_NATIVE_EXPECT` with its view-relative cell and
both payloads, for example
`E_NATIVE_EXPECT: stored bit pattern differs at cell (0, 0): holds f64(0x1.4p1) [bits 4612811918334230528]; expected f64(0x1.cp1) [bits 4615063718147915776]`.
Finite nonzero components use the exact `f64(hex)` spelling followed by their
decimal bits; zeros, infinities and NaNs use `f64_bits(bits)`, so signed zeros
and NaN payloads stay visible. A `Complex<F64>` cell shows both components as
`complex(real, imaginary)`. The ASCII message is formatted without host `printf`
float conversion, so it is identical across hosts, and has at most 361 bytes.
It is built only after the bit comparison fails. Handle, scalar, layout and bounds
errors keep their precedence and fixed messages, and cleanup is unchanged.

The optional `lean-kernel/native` package is linked only for a resource entry
with an operation that uses an arena. A protocol-8 program with only an
ordinary pure entry still builds without that runtime, and so does one whose
resource entry computes scalars alone. No route needs mathlib.
A checked GEMM schedule additionally links
the optional numerical package with explicit pinned OpenBLAS configuration;
other entries remain BLAS-free. See [numerical source and build](../linalg/maps-and-gemm.md#maps).
Native code performs no runtime
loan interpretation or implicit alias-repair copy; operation costs remain visible
in the checked schedule.

## Diagnostic reconstruction

Resource expansion retains the current function and structural statement path
when a check fails. The primary diagnostic points to the failing operation,
including an unselected branch arm. A failed branch join points to its `if`;
an input-contract failure points to the caller; a callee-body failure points to
that body statement and includes the caller as a note. Result/cleanup failures
use the result block when no caller statement is available. Unused bodies keep
their own locations. Header and envelope failures still use the relevant header.

Notes recover names and introduction sites from the original source paired with
its actual lowering. Borrow/drop failures identify the allocation and, when
available, the conflicting or outstanding loan. GEMM endpoint mismatches name
the actual unequal spaces/bases; vector evaluation identifies its actual bases
and explicit metric. Equal dimensions do not suppress these nominal checks.
Other operations include their local operands. Compiler-created temporary loans
without a lexical binding are omitted rather than presented as source names.
Notes are deduplicated and capped at 32, with call context before operand notes.
The internal trace retains at most 32 innermost sites so unwinding a deep
rejected call chain does not repeatedly copy an unbounded diagnostic stack.

This context is internal error data: the public wire format and successful
checked schedules are unchanged. Names and source mappings are recovered only
on rejection, without rerunning all body probes or retaining a resource-state
snapshot for diagnostics. The location wrappers have exact successful-result
equations; source positions and diagnostic prose are covered by regression
tests, not a source-provenance theorem.

## Evidence and remaining work

`ResourceSource.Checked` retains the original decoder/source mapping, canonical
owners, independently re-resolved calls, actual authority acceptance, complete
resource probes, pure fragment compilation and the exact mixed executable plan. The oracle
imports those definitions: source identity and call provenance, all resource-body
coverage, the original authority trace, typed total evaluation of the returned
pure Core, and closed logical resources at successful entry exit are connected to
actual acceptance. These facts do not prove native heap behavior, full source
operational correspondence, numerical results or compiler refinement.

Regression coverage includes actual source check/build/run, runtime assertion
failure, re-exports/private access, moved owners, uninitialized storage, captures,
nonwinning and unapplied pure bodies, legacy-version rejection and forged wire
metadata. The existing forged native-plan, sanitizer, failure-cleanup and allocation
counter regressions remain required.

Numerical inputs accept explicit static `Space`, dependent `Basis`, and
`ReadMap`/`WriteMap`/`ReadWriteMap` contracts; see [the input contract](../linalg/maps-and-gemm.md#map-parameters).
`OwnedMap<source_basis,target_basis>` inputs/results additionally transfer initialized
storage and input-dependent mathematical identities; see [owned results](../linalg/maps-and-gemm.md#owned-maps).
Bounded generative owned-map packages, explicit rank-three packing/regrouping,
versioned scratch reuse and connected rank-two/three contraction trees are
implemented, as the numerical chapters describe. [Diagonal metrics](../linalg/transforms-and-metrics.md#adjoints-for-diagonal-metrics) add explicit declared
coefficient realization and scratch-backed pairing. Nat/Int/Bool/Unit value flow and runtime Bool branches compose with these
operations. The separate [runtime-shape profile](../storage/resource-programs.md#runtime-extents) adds straight-line
whole-map GEMM. Broader dynamic interfaces, floating scalar expression interfaces, general resource packages, dense
metric realization, general owned-result joins and retained-evidence interfaces
remain open. Equivalent-C measurements exist for bounded paths; controlled-host
performance and total allocation acceptance remain unfinished. Escaping borrowed lifetimes and
broader lifetime interfaces retain their separate scope. Protocol 8's static
profile and native compilation alone do not establish **Fast like C**.

[Typed transforms](../linalg/transforms-and-metrics.md#dual-and-conjugate-spaces) add explicit dual/conjugate spaces,
corresponding bases, canonical involutions, declared coordinate metrics and
read-only dual/conjugate/orthonormal-adjoint operations. Dependent parameter
contracts and actual reborrows preserve their evidence and conjugation through
nested calls. The public checker also audits the exact transform receipt origins.

[Vector evaluation](../linalg/transforms-and-metrics.md#pairings) adds bilinear dual evaluation and explicit
orthonormal Hermitian pairing with scoped vector loans. [Finite two-map networks](../linalg/networks-and-packing.md#two-map-networks)
check occurrence identity, exact port usage, the bilinear edge and ordered boundaries.
Both features reach the same resource/native path and retain their public origin
audits through both branch arms; their broader metric and network contracts remain open.

[Owned-map packages](../linalg/maps-and-gemm.md#owned-map-packages) add the bounded
`OwnedMapTo<source_basis,target_dimension>` profile: one hidden primal target and
direct basis, initialized affine storage, fresh consuming unpack and explicit
repack. The source basis remains an actual caller dependency. Pack/open/transfer
preserve the exact allocation/layout and emit no additional native instructions.
Dynamic package-result dimensions, general resource packages/closures, borrowed results and
full source/native refinement remain pending.

`cache saved = pack3(source, scratch);` and
`contract3_cached(saved, packed, right, output, NativeFast);` expose the bounded
[packing dependency contract](../linalg/networks-and-packing.md#caches). Cache names are lexical metadata
with no parameter/result or escaping package form. All-body and both-branch checks
include their capture, consumer and cleanup schedules.

[Bounded contraction trees](../linalg/networks-and-packing.md#contraction-trees) add explicit unresolved finite
graphs, ordered ports and caller-supplied regroup/GEMM plans. The full public
checker independently resolves their nominal axes and resource names, retains
actual producer/event receipts from both branches and audits their declaration
environment alongside package and packing-cache receipts.

## Runtime-extent frames and guards

The independent Lean checker reconstructs a symbolic frame containing static
allocation identities, owner/loan names, access rights, parent links, canonical
whole-map layouts, write histories and versions. A write history is interpreted
with the existing `Initialization.record`, including its empty/redundant-write
normalization. It is not a guessed concrete state at a representative size.
Whole-map child loans retain their caller snapshots, suspend parent access and
return inside out. Calls preserve all caller owners/layouts and restore every
caller loan; only justified initialization/version changes survive.

Only arithmetic facts become emitted guards: integral narrowing, byte capacity,
LP64 dimensions/leading bounds, physical layout validity, dependent dimension
equality and constant cell bounds. Extents never authorize ownership, borrowing,
nominal identity or profile paths. `StorageShapeFlow` independently projects the
actual mixed scalar schedule; `StorageValueFlow` checks that every referenced
slot is live and integral at its actual use, not merely present in a final table.
Both static and symbolic projections are independently audited before codegen.

Guards containing only literals are decided by the Lean checker. False physical
layout/capacity, dimension, bound or cell conditions produce `E_RUNTIME_GUARD`
during `check`, including conditions from nominal maps and call contracts.
The audits of the whole flow, `Shapes.check` and `Shapes.Flow.check`, decide
these guards after the last statement and are the acceptance. The expansion
decides a false one as well, where its operation or its event enters the
flow, so that the diagnostic has the statement.
True closed guards emit no native condition. Guards referring to scalar slots
remain runtime checks; this does not constant-fold an earlier `value` block or
guess its value. The certificate retains both physical and explicit guard
decisions, and the oracle proves that admitted closed guards hold under every
valuation for the actual checked public entry. The helper arithmetic agreement
below does not establish full source/native refinement. Resource diagnostics
retain the failing statement, available binding locations and call-site context;
see [Diagnostic reconstruction](#diagnostic-reconstruction).

Runtime shape operations or calls are rejected under resource branch nodes,
including transitively and in unselected arms. Ordinary scalar/resource branches
retain both-arm checks. A scalar-returning helper may compute an extent before a
straight-line runtime-shape region. General shape results, branch phi values,
borrowed/owned runtime results and resource closures remain future work.

Guards precede the operation that needs them. The native adapter independently
checks physical handles, layout, aliases and GEMM ABI before writes; logical
initialization remains an independent checker obligation. A failing GEMM preflight preserves its output. The whole
multi-operation function is not a transaction: earlier successful writes need
not roll back if a later guard fails. Entry failure cleans up both arenas.

## Runtime-extent proof boundary

`VastitasOracle.StorageShapes` proves, for every guard-satisfying valuation,
exact interpretation of frame audits, each accepted `Storage.checkAction`, and
the complete instantiated `Storage.run`. Its call theorem uses the actual
accepted call slice and proves exact caller-loan restoration and preserved
allocation identity/owner/scalar/capacity fields. Guard premises include the
initial frame's guards and the complete emitted step guards.

`StorageShapeNumerical` proves actual numerical environment validity, full live
loan snapshots and acceptance by the existing `Storage.Numerical.checkProduct`
with the same endpoints, bases, coefficients and GEMM request. The public
`ResourceRuntimeShapes` corollaries use actual source origins, entry projections
and scalar-return receipts. Synthetic probes do not prove universal extents.

The test-only [runtime guard proof](https://github.com/MGYamada/Vastitas/blob/main/scripts/prove_runtime_shape_guards.lean)
connects the actual `runtimeLayoutValid` helper to `Storage.checkLayout` for all
Lean `UInt64` inputs and both scalar tags, including empty extents and either transpose
flag. LP64 bounds prove the nonempty span multiplication/addition cannot wrap;
invalid scalar tags are rejected. The `layout_guard` corollary connects this
result to actual `Shapes.Guard.eval` under explicit extent-representation
premises. Bound, equality and cell expressions have matching Nat judgments
when emitted constants fit Lean `UInt64`. Actual Nat/Int narrowing helpers return the
exact admitted value without wrapping or clamping, and produce their prescribed
IO errors on checker rejection. All 13 theorems have a transitive axiom audit.
`UInt64` here names the backend Lean type. Source extents still come from `Nat`
or `Int`; this work does not add the planned Vastitas `U64` source type.

This script imports kernel and runtime only for validation; neither gains a
further dependency and the optional native/FFI package stays outside the oracle.
These results do not prove that source scalar execution supplies the stated
valuation, interpret generated source strings, or establish native memory safety
of the full C/Lean toolchain, floating-point field laws or numerical error bounds.
Native boundary tests, sanitizers and equivalent-work experiments remain separate
implementation evidence.

## Execution costs and limits

The compiler reconstructs lookup tables and exact name counts from the symbolic
frame. When distinct loan names form one child-to-root stack, it verifies all
parent links in one pass. Every loan still needs its original allocation,
layout, access and initialization checks. Other loan tables use bounded
ancestor sets and all writer pairs. `Shapes.auditFrame_eq_indexed` and
`Shapes.compatibleWith_eq_indexed` prove equality with the reference checks
for every frame and every compatibility input. The proof depends only on the
loan graph and applies at any runtime extent.

Every call checks the actual caller and exit frame. An identical starting
frame and action slice can reuse a completed nested replay, including its
ordered guards. `Shapes.Functions.checkCall_eq_uncached` equates that call
check with a fresh replay. Different frames or actions take the ordinary path.
The public entry also reuses the checked library's all-body probe batch.
[Forwarding-call measurements](https://github.com/MGYamada/Vastitas/blob/main/experiments/compiler_scaling/results/2026-11-03-macos-nested-replay/RESULTS.md)

General nested expansion, writer comparisons and frame audits consume the
shared resource-work budget. The metered replay checks every symbolic step
and returns the original frame and ordered guards. Unused probes and the
actual entry contribute to one accepted total.
[Resource checking work](../storage/checked-storage.md#storage-functions--resource-checking-work)

The public harness `scripts/check_storage_scaling.py --profile runtime`
measures allocation/drop, shared reads, distinct-allocation writers, reborrow
chains and forwarding calls. It records compiler checking times. The earlier
record includes the 512-deep timeout and the later chain record measures the
same workload after the ancestry check changed.
[Earlier comparison](https://github.com/MGYamada/Vastitas/blob/main/experiments/compiler_scaling/results/2026-11-03-macos-runtime/RESULTS.md) · [Chain comparison](https://github.com/MGYamada/Vastitas/blob/main/experiments/compiler_scaling/results/2026-11-03-macos-reborrow-chains/RESULTS.md)

A generated entry with a runtime-shape event creates one runtime-shape arena and
cleans it up once; an entry that also has an operation on a static allocation
has a second, disjoint arena
([All-body checking and generation](#all-body-checking-and-generation)). A call does not create
an arena or silently allocate/copy a matrix. Only explicit `runtime_allocate`,
fill and GEMM actions cause corresponding data effects. Loan/move/nominal
metadata erase; scalar narrowing and arithmetic guards remain visible generated
work. There is no runtime compiler, symbolic frame or loan interpreter.

Resource calls still expand statically at their call sites. Their generated GEMM
calls use the same compiled generic runtime ABI with runtime extent operands;
this is not compiled resource-function code sharing. Storage-only runtime
programs need no OpenBLAS. Actual GEMM uses the existing optional pinned
sequential LP64 OpenBLAS package.

The [runtime-shape experiment](https://github.com/MGYamada/Vastitas/blob/main/experiments/runtime_shapes/README.md) separates
canonical public programs from instrumented callable wrappers, explicit lifecycle
costs from destination reuse, and arena data counters from Lean/FFI/backend
allocations. Counting, poison and correctness hooks are not timing evidence.
Controlled-host equivalent-C budgets, total allocation attribution and general
runtime numerical interfaces remain open. The runtime-extent profile does not close Stage 1.

## Validation

The kernel regression target `VastitasStorageTest.ShapeRegression` checks 80
exact real/complex, transpose, mode and zero-axis valuations against the actual
concrete schedule, plus forged frame/snapshot, alias, initialization, slot and
caller-restoration failures. `tests/runtime_shape_source.rs` checks public/raw
wire rejection and executes 17 positive and five failing source programs in its
optional native suite. The numerical CI runs that suite on both supported OSes.
The [storage-native guard regression](https://github.com/MGYamada/Vastitas/blob/main/scripts/check_runtime_shape_guards.lean)
compares 5,488 physical-layout boundary tuples and 13 integral narrowing cases
against the actual runtime and checker helpers.
These finite checks supplement both the universal mathematical guard theorems
and the 13 actual helper/expression theorems above. The storage-native harness
checks both scripts against its freshly built standalone runtime.

`tests/resource_entry_runtime.rs` checks the emitted source and the storage
runtime requirement of entries with and without an operation on an arena. It
builds and runs both kinds. The entries that compute scalars alone are built
in a kernel root that holds no storage package. The test also gives the driver
responses that import the storage runtime without the requirement, and the
driver refuses them. `VastitasStorageTest.ValueFlowRegression` checks the same
requirement in the kernel and the classification of native instructions.

When the runtime-extent profile was delivered, its full validation included 342 Rust tests and all 13 optional public
numerical native tests, 44 kernel regression targets,
full kernel/oracle builds, and a 25,287-declaration transitive axiom audit allowing
only `propext`, `Classical.choice` and `Quot.sound`. Native storage/GEMM checks and
the [retained output/cost record](https://github.com/MGYamada/Vastitas/blob/main/experiments/runtime_shapes/results/2026-11-01-macos/RESULTS.md)
remain separate from those proofs. The retained experiment identifies its actual
dirty source snapshots and binaries; it is not attributed to a later commit.

## Delivery and regression obligations

1. Finalize allocation/layout/region IR and explicit cost contracts before public
   storage APIs. Implement protocol-8 Rust and Lean changes in the same increment.
2. Reject move-after-use, loan escape, stale generations, overlapping views,
   noninjective writes, uninitialized reads and incompatible branch resources.
3. Check native bounds/alignment/narrowing, failure-before-write, partial-write
   states and scratch release. Include forged raw and checked IR regressions.
4. Implement destination-passing GEMM and finite network schedules; execute actual
   source `check`/`build` outputs and compare equivalent C baselines.
5. Connect actual-checker resource theorems and the final code-generation audit;
   record every remaining native/semantic assumption in `verification.md`.
6. Keep residual metadata extensible. AD retention and replay and their proofs
   remain open; the [Stage 3 roadmap entry](../guide/historical-roadmap.md#stage-3-smooth-affine-geometry-and-reverse-ad)
   tracks them.

The completion record must distinguish implemented checks, regression evidence,
formal theorems, trusted native behavior and measured performance. This list
defines the required work; it is not evidence that any unchecked item has passed.

## History

The finite Stage 1 compiler implements the ownership profiles mapped in the
[acceptance record](../stage1-acceptance.md). The remaining performance
acceptance is tracked in [#183](https://github.com/MGYamada/Vastitas/issues/183)
and the [performance handoff](../stage1-completion.md#stage-2-or-later-performance-acceptance).
The unmeasured cost of residual encodings in compiled reverse Core is tracked
in [#222](https://github.com/MGYamada/Vastitas/issues/222).
