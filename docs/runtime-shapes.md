# Runtime extents and caller-owned maps

Protocol 8 supports a bounded runtime-extent resource profile. Immutable `Nat`
or nonnegative `Int` values from actual checked pure computations can determine
rank-two allocation capacities, column-major layouts and nominal space dimensions.
Real and complex GEMM can reuse a caller's destination through nested calls at
multiple extents. Dimension values never become dispatch keys or evidence that
two nominal spaces or bases are equal.

The [worked package](../examples/packages/runtime-shapes/src/main.vast) uses two
extents in one executable and calls the same helper twice into each destination.
Run `cargo run -- check --manifest-path examples/packages/runtime-shapes/Vastitas.toml`;
native build additionally requires `--openblas-prefix <pinned-prefix>`.

## Public interface

```vast
resource fn multiply(
    m: Nat, k: Nat, n: Nat,
    u: RuntimeSpace<profiles::RealSmooth, m>,
    v: RuntimeSpace<profiles::RealSmooth, k>,
    w: RuntimeSpace<profiles::RealSmooth, n>,
    bu: RuntimeBasis<u>, bv: RuntimeBasis<v>, bw: RuntimeBasis<w>,
    a: RuntimeMap<bv, bu, read>,
    b: RuntimeMap<bw, bv, read>,
    out: RuntimeMap<bw, bu, write> initializes
) -> Unit {
    runtime_gemm(a, b, out, overwrite, NativeFast);
    value { () }
}
```

The caller declares `runtime_space u = linear(profiles::RealSmooth, m);` and
`runtime_basis bu = basis(u);`. It explicitly allocates storage:

```vast
let capacity: Nat = value { leading * columns };
runtime_allocate data: F64[capacity] runtime_layout(rows, columns, leading, false);
runtime_borrow output = write(data);
runtime_map map = view(output, source_basis, target_basis);
```

Each extent is a literal or an earlier `Nat`/`Int` binding. Compute arithmetic in
`value` blocks; extents contain no separate expression language. Parameters may
refer only to preceding scalar, space and basis parameters. The caller's actual
space and basis identities survive calls; a same-dimensional independently
created basis is not interchangeable. `RuntimeMap` access is `read`, `write` or
`read_write`; `initializes` promises full logical output initialization on return.
An `Int` extent rejects negative values before conversion.

`runtime_fill`, `runtime_expect`, `runtime_release`, `runtime_move` and
`runtime_drop` mirror the corresponding explicit storage operations.
`runtime_borrow` uses the allocation's entire declared map; it has no layout or
offset override. Layouts have exactly rows, columns, leading dimension and a
fixed transpose flag. Padding is retained and does not become initialized merely
because every logical cell is written. Zero extents are supported, with the
existing requirement `leading >= max(1, rows)`. Empty extents do not authorize
an otherwise conflicting loan or an unwritten read in the symbolic contract.

`runtime_gemm` supports `F64`/`Complex<F64>`, overwrite or accumulate and explicit
`NativeFast`. Optional alpha/beta are matching machine literals. Overwrite has
no beta; accumulate requires an initialized readable/writable output even for
beta zero. Runtime coefficient loans, transformed/metric/vector/tensor interfaces
and cross-component storage conversion are outside this initial profile.

## Exact frame and guard contract

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
True closed guards emit no native condition. Guards referring to scalar slots
remain runtime checks; this does not constant-fold an earlier `value` block or
guess its value. The certificate retains both physical and explicit guard
decisions, and the oracle proves that admitted closed guards hold under every
valuation for the actual checked public entry. The helper arithmetic agreement
below does not establish full source/native refinement. Resource diagnostics
retain the failing statement, available binding locations and call-site context;
see [resource source](resource-source.md).

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

## Proof boundary

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

The test-only [runtime guard proof](../scripts/prove_runtime_shape_guards.lean)
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
new dependency and the optional native/FFI package stays outside the oracle.
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
[Forwarding-call measurements](../experiments/compiler_scaling/results/2026-11-03-macos-nested-replay/RESULTS.md)

General nested expansion, writer-pair checks and full frame audits still
contribute to checking cost. A request-wide resource-work limit remains open.
[#423](https://github.com/MGYamada/Vastitas/issues/423) · [Static storage #422](https://github.com/MGYamada/Vastitas/issues/422)

The public harness `scripts/check_storage_scaling.py --profile runtime`
measures allocation/drop, shared reads, distinct-allocation writers, reborrow
chains and forwarding calls. It records compiler checking times. The earlier
record includes the 512-deep timeout and the later chain record measures the
same workload after the ancestry check changed.
[Earlier comparison](../experiments/compiler_scaling/results/2026-11-03-macos-runtime/RESULTS.md) · [Chain comparison](../experiments/compiler_scaling/results/2026-11-03-macos-reborrow-chains/RESULTS.md)

A generated entry creates one runtime-shape arena and cleans it up once; entries
also using static resources have a second, disjoint arena. A call does not create
an arena or silently allocate/copy a matrix. Only explicit `runtime_allocate`,
fill and GEMM actions cause corresponding data effects. Loan/move/nominal
metadata erase; scalar narrowing and arithmetic guards remain visible generated
work. There is no runtime compiler, symbolic frame or loan interpreter.

Resource calls still expand statically at their call sites. Their generated GEMM
calls use the same compiled generic runtime ABI with runtime extent operands;
this is not new compiled resource-function code sharing. Storage-only runtime
programs need no OpenBLAS. Actual GEMM uses the existing optional pinned
sequential LP64 OpenBLAS package.

The [runtime-shape experiment](../experiments/runtime_shapes/README.md) separates
canonical public programs from instrumented callable wrappers, explicit lifecycle
costs from destination reuse, and arena data counters from Lean/FFI/backend
allocations. Counting, poison and correctness hooks are not timing evidence.
Controlled-host equivalent-C budgets, total allocation attribution and general
runtime numerical interfaces remain open. This increment does not close Stage 1.

## Validation

The kernel regression target `VastitasStorageTest.ShapeRegression` checks 80
exact real/complex, transpose, mode and zero-axis valuations against the actual
concrete schedule, plus forged frame/snapshot, alias, initialization, slot and
caller-restoration failures. `tests/runtime_shape_source.rs` checks public/raw
wire rejection and executes 17 positive and five failing source programs in its
optional native suite. The numerical CI runs that suite on both supported OSes.
The [storage-native guard regression](../scripts/check_runtime_shape_guards.lean)
compares 5,488 physical-layout boundary tuples and 13 integral narrowing cases
against the actual runtime and checker helpers.
These finite checks supplement both the universal mathematical guard theorems
and the 13 actual helper/expression theorems above. The storage-native harness
checks both scripts against its freshly built standalone runtime.

The full feature validation includes 342 Rust tests and all 13 optional public
numerical native tests, 44 kernel regression targets,
full kernel/oracle builds, and a 25,287-declaration transitive axiom audit allowing
only `propext`, `Classical.choice` and `Quot.sound`. Native storage/GEMM checks and
the [retained output/cost record](../experiments/runtime_shapes/results/2026-11-01-macos/RESULTS.md)
remain separate from those proofs. The retained experiment identifies its actual
dirty source snapshots and binaries; it is not attributed to a later commit.
