# Resource programs and runtime shapes

Package resource functions combine checked scalar computation with explicit storage transitions. The runtime-shape profile adds bounded whole-map extents and caller-frame replay.

<a id="resource-source"></a>

## Package resource functions (protocol 8)

Protocol 8 connects explicit resource functions to the ordinary `.vast` package
compiler. Names, imports, visibility, canonical module owners, indexed declarations,
finite dispatch and edit assemblies share the same namespace. The existing
`Indexed.AuthoritySource` checks every ordinary, applicable, nonwinning and
unapplied pure body. Resource bodies then pass independent ownership, layout,
initialization and actual-call checks. Static shapes retain their original contracts. The separate
[runtime-extent profile](#runtime-shapes) supports whole-map caller interfaces;
scalar values flow between checked pure computations, resource calls and runtime branches.
This bounded profile does not complete [Stage 1](../stage1-completion.md).

The [complete example](https://github.com/MGYamada/Vastitas/blob/main/examples/packages/storage/app/src/main.vast) imports
resource functions from a separate directory-aligned package, receives an owned
buffer, borrows it for inspection, moves it through another function, drops it,
and computes `42` using ordinary finite dispatch and an independent lambda:

```sh
vastitas check --manifest-path examples/packages/storage/app/Vastitas.toml
vastitas build --manifest-path examples/packages/storage/app/Vastitas.toml -o /tmp/storage-example
/tmp/storage-example
```

<a id="resource-source--explicit-source-contracts"></a>

### Explicit source contracts

Resource declarations use `resource fn`. The operations are statements; the final
`value { ... }` block uses ordinary pure expression syntax. A root resource `main`
has no resource inputs or owned outputs and returns `Int`. A package may instead
have an ordinary pure `main`, or no main when checking a library. Pure and resource
functions cannot declare the same name in one module.

```vast
pub resource fn make()
    returns (data: Owned<F64, 8> initialized [layout(8, 2, 2, 4, false)]) -> Unit {
    allocate data: F64[8];
    borrow output = write(data, layout(8, 2, 2, 4, false));
    fill(output, f64(0x1.8p1)); // 3.0
    release(output);
    value { () }
}
```

`Owned<S, elements>` consumes an owner. An optional `initialized [layout(...), ...]`
contract requires those exact regions; capacity and padding alone imply no
initialization. `returns (name: Owned<...>, ...)` transfers the named body owners
in order. For example, `call buffers::make() -> (data);` receives its owner into a
fresh caller binding. A consumed binding remains unusable and cannot be shadowed.

Borrowed parameters use `Read<S, rows, columns>`, `Write<S, rows, columns>` or
`ReadWrite<S, rows, columns>`, optionally followed by `initializes`. They receive
scoped child loans of the actual caller view. Their scalar and logical shape must
match, but their real offset, padding and transpose are preserved. The caller's
loan resumes only after all children are returned. Two read arguments may alias;
parameter names never prove separation for a writer. Individual cell stores can
establish an entire initialized output, including a padded caller view, through
the bounded write-union check. Both branches must independently cover each
requested cell. No preliminary fill is required when the stores suffice; missing
cells, padding holes and exhausted coverage budgets remain unreadable.

| Statement | Meaning |
| --- | --- |
| `allocate data: F64[8];` | Allocate one initially uninitialized owner; `Complex<F64>` is also supported. |
| `move data -> next;` | Transfer an unborrowed owner; revoke `data`. |
| `borrow view = read(data, layout(...));` | Borrow from an owner or reborrow a loan; also `write` and `read_write`. |
| `release(view);` | Return a childless loan. |
| `drop(data);` | Free an unborrowed owned allocation. |
| `transpose(view);` | Swap the logical axes without copying or conjugating. |
| `fill(view, f64(0x1.8p0));` | Fill the writable logical rectangle with 1.5. |
| `store(view, row, column, payload);` | Initialize one checked cell. |
| `expect(view, row, column, payload);` | Assert the exact bits of an initialized readable cell at runtime. |
| `copy(input, output);` | Copy between compatible checked views; reuse the destination. |
| `space v = linear(Profile, 3);` | Construct a fresh nominal linear space from an independently resolved profile. |
| `basis bv = basis(v);` | Introduce a distinct basis tied to that space. |
| `map a = view(input, bv, bw);` | Interpret a live loan as a map from `v` to `w` in those bases. |
| `map a = owned(buffer, layout(...), bv, bw);` | Move initialized coordinate storage into an owned map with exact bases and layout. |
| `borrow coordinates = read(a);` | Borrow an owned map using its actual stored layout; also `write` and `read_write`. |
| `map view = view(coordinates, a);` | Recover the owned map's exact interpretation for a matching live loan. |
| `gemm(a, b, c, overwrite, NativeFast);` | Check exact endpoints/bases and resources, then multiply into `c`; also `accumulate`. |
| `gemm(a, b, c, accumulate, NativeFast, alpha=coefficient(s), beta=f64(0x1p-1));` | Read alpha from the checked 1x1 scalar loan at execution and use beta = 0.5. Complex maps require complex coefficients. |
| `call path(arguments) -> (owners);` | Invoke a resource function, transferring its ordered owned results. |
| `let n: Nat = value { expression };` | Compute a checked pure scalar at this point in the resource body. |
| `let answer: Int = call helper(n) -> (owners);` | Receive a pure result after the callee completes its resource operations and returns its loans. |
| `if flag { ... } else { ... }` | Execute the arm selected by a checked Bool binding; independently check and join both resource states. Literal conditions remain supported. |

Public `gemm` is a numerical statement over typed map views. Lean resolves its
nominal endpoints/bases before composing the actual resource checks and exact
native lowering. Protocol 8 rejects a raw resource `action` containing `gemm`;
the internal action cannot bypass nominal checking. See
[numerical source and wire compatibility](../linalg/maps-and-gemm.md#numerical-values--source-and-wire-compatibility)
and [adapter responsibilities](../linalg/maps-and-gemm.md#numerical-adapter--responsibilities-along-the-implemented-path).

`layout(offset, rows, columns, leading, transposed)` uses a byte offset and an
element leading dimension. Bounds, LP64 dimensions, capacity, alignment and
initialization are checked independently in Lean. Native preflight checks physical
handles and arithmetic again. See [the layout contract](checked-storage.md#storage-ir).

Use `f64(value)` or `complex(real, imaginary)` for **exact finite** resource
payloads. Hexadecimal notation makes the binary exponent explicit.

```vast
fill(output, f64(0x1.8p1));                      // 3.0
store(output, 0, 0, f64(-0x1p-2));               // -0.25
fill(complex_output, complex(0x1.8p0, -0x1p1));  // 1.5 - 2i
```

`f64(value)` and `complex(real, imaginary)` work in fill/store/expect and literal
GEMM coefficients, including the runtime-extent profile. In a hexadecimal
literal, `p` introduces a required decimal exponent `e`. The value is the
hexadecimal significand multiplied by `2^e`. For example, `0x1.8p0` is
`(1 + 8/16) * 2^0`, exactly `1.5`.
`0x1p-1074` is the least positive subnormal and `0x1.fffffffffffffp1023` the
greatest finite binary64 value. Exact decimal forms such as `f64(1.5)` or
`f64(125e-3)` (0.125) are also accepted. Exponents must fit a signed 64-bit
integer. Literals use plain digits without separators or type suffixes.

There is **no rounding on acceptance**. For example `f64(0.1)` and
`f64(9007199254740993)` are rejected; the diagnostic shows their adjacent binary64
values in exact hex form. Inexact hex values, overflow and underflow below
subnormal precision are rejected too. Positive zero is accepted; negative zero,
infinities and NaN payloads use `f64_bits(bits)` or
`complex_bits(real_bits, imaginary_bits)`, whose arguments are unsigned 64-bit
IEEE binary64 payloads. For example
`f64_bits(9223372036854775808)` preserves negative zero.

This is source sugar for the existing unsigned-bit payloads, with no wire/schema
change or runtime conversion. The frontend checks hex precision/range with
integer arithmetic; for decimals it compares the candidate's exact integer
decimal expansion with the original value before accepting its bits. Lean
continues to check the same literal scalar tags and resource authority. This
frontend conversion is tested, not a new Lean source-literal refinement theorem
or an IEEE field-law claim. It does not introduce pure floating scalar values or
arithmetic into the existing Nat/Int dispatcher.
Allocation sizes and layout arguments are static metadata. An explicit
`coefficient(loan)` operand instead reads an initialized scalar at GEMM execution;
it does not introduce general scalar expression flow between resource statements.

### Pure values and executable boundaries

Resource parameters, typed `let` bindings and captured call results support
`Nat`, `Int`, `Bool` and `Unit`. A `value { ... }` block can use earlier scalar
bindings, ordinary functions, finite generic families, independent lambdas and
indexed geometry under the existing declaration contracts. For example:

```vast
resource fn finish(data: Owned<F64, 1>, seed: Int) -> Int {
    drop(data);
    let answer: Int = value { seed + 1 };
    value { answer }
}
```

The [scalar-flow example](https://github.com/MGYamada/Vastitas/blob/main/examples/packages/resource-values/src/main.vast)
passes a computed Bool through a resource helper, chooses different fills at
runtime, returns the Bool together with an initialized owner, and inspects the
selected output before computing `42`. Nat remains arbitrary precision with
saturating subtraction; Nat-to-Int conversion remains explicit.

Each pure block receives only its earlier scalar bindings. Resource handles,
loans, numerical metadata and packing caches cannot enter pure Core. Pure locals
cannot shadow enclosing bindings, and lambdas retain the independent capture
audit. Resource functions remain unavailable as `Fn` values, pure callees,
dispatch keys or editable generic families. Every branch is checked even when a
condition originates from a literal. Branch-local scalar bindings are unavailable
in the sibling or after the join; there are no scalar phi values or branch result
bindings in this increment.

An ordinary `call` still transfers owners and discards the pure result. Discarded
results, including previously supported terminal Pair results, remain fully
checked without native evaluation. A `let ... = call` computes its result only
after the callee's resource schedule succeeds and its borrowed inputs have been
restored. The entry's final Int is printed after successful resource completion.
No scalar result is published after a resource failure; previous writes are not
rolled back. Ordinary storage forms keep static capacities and layouts; explicit
`runtime_*` forms use integral scalar slots for bounded whole-map dimensions,
capacities and layouts. Profile and nominal identities remain static. This does
not add floating Core arithmetic, resource reads in pure expressions or escaping
resource closures. Runtime-shape calls are rejected under resource branches.

Every resource definition is checked, including unused dependencies. Check-only
libraries use actual all-body probes without a fabricated main. A package with
a resource entry reuses that checked probe list and independently expands its
actual entry schedule as described in [resource functions](checked-storage.md#storage-functions--all-body-checking-and-exact-expansion).
Source owners,
local symbols and call IDs are reconstructed; the public input cannot provide
allocation IDs, checked Core, alias assertions or trusted initialization flags.
Versions 2–7 reject resource declarations rather than discarding them.

Generation rechecks the original mixed schedule, its resource projection and
every native instruction, plus the actual pure Core module, exact fragment
targets and dependency order. A fragment is keyed by its canonical resource
owner and structural source position. Its ordered scalar argument slots must
match the actual checked Core signature. Runtime conditions are emitted from
those checked Bool slots; neither arm is selected during resource checking. The same
resource main supplies both the schedule and its pure return block. Native IO uses
structured cleanup, including failure paths; a failed resource operation does not
publish the pure return value. Earlier completed writes are not rolled back.
The Unit-returning main closes its arenas on success and closes/rethrows on
failure; a cleanup error overrides the body error. When both static and dynamic
arenas exist, the inner arena closes first. See the
[native cleanup contract and fault-injection checks](checked-storage.md#storage-ir).

The optional `lean-kernel/native` package is linked only for a resource entry.
A protocol-8 program with only an ordinary pure entry still builds without that
runtime. Neither route needs mathlib. A checked GEMM schedule additionally links
the optional numerical package with explicit pinned OpenBLAS configuration;
other entries remain BLAS-free. See [numerical source and build](../linalg/maps-and-gemm.md#numerical-values).
Native code performs no runtime
loan interpretation or implicit alias-repair copy; operation costs remain visible
in the checked schedule.

### Resource diagnostics

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

### Evidence and remaining work

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

Numerical inputs now accept explicit static `Space`, dependent `Basis`, and
`ReadMap`/`WriteMap`/`ReadWriteMap` contracts; see [the input contract](../linalg/maps-and-gemm.md#numerical-values--dependent-numerical-inputs).
`OwnedMap<source_basis,target_basis>` inputs/results additionally transfer initialized
storage and input-dependent mathematical identities; see [owned results](../linalg/maps-and-gemm.md#numerical-values--owned-numerical-results).
Bounded generative owned-map packages, explicit rank-three packing/regrouping,
versioned scratch reuse and connected rank-two/three contraction trees are
implemented below. [Diagonal metrics](../linalg/transforms-and-metrics.md#diagonal-metrics) add explicit declared
coefficient realization and scratch-backed pairing. Nat/Int/Bool/Unit value flow and runtime Bool branches compose with these
operations. The separate [runtime-shape profile](#runtime-shapes) adds straight-line
whole-map GEMM. Broader dynamic interfaces, floating scalar expression interfaces, general resource packages, dense
metric realization, general owned-result joins and retained-evidence interfaces
remain open. Equivalent-C measurements exist for bounded paths; controlled-host
performance and total allocation acceptance remain unfinished. Escaping borrowed lifetimes and
broader lifetime interfaces retain their separate scope. Protocol 8's static
profile and native compilation alone do not establish **Fast like C**.

[Typed transforms](../linalg/transforms-and-metrics.md#linear-transforms) now add explicit dual/conjugate spaces,
corresponding bases, canonical involutions, declared coordinate metrics and
read-only dual/conjugate/orthonormal-adjoint operations. Dependent parameter
contracts and actual reborrows preserve their evidence and conjugation through
nested calls. The public checker also audits the exact transform receipt origins.

[Vector evaluation](../linalg/transforms-and-metrics.md#vector-evaluation) adds bilinear dual evaluation and explicit
orthonormal Hermitian pairing with scoped vector loans. [Finite two-map networks](../linalg/networks-and-packing.md#finite-networks)
check occurrence identity, exact port usage, the bilinear edge and ordered boundaries.
Both features reach the same resource/native path and retain their public origin
audits through both branch arms; their broader metric and network contracts remain open.

[Owned-map packages](../linalg/maps-and-gemm.md#owned-map-packages) now add the bounded
`OwnedMapTo<source_basis,target_dimension>` profile: one hidden primal target and
direct basis, initialized affine storage, fresh consuming unpack and explicit
repack. The source basis remains an actual caller dependency. Pack/open/transfer
preserve the exact allocation/layout and emit no additional native instructions.
Dynamic package-result dimensions, general resource packages/closures, borrowed results and
full source/native refinement remain pending.

`cache saved = pack3(source, scratch);` and
`contract3_cached(saved, packed, right, output, NativeFast);` expose the bounded
[packing dependency contract](../linalg/networks-and-packing.md#cached-packing). Cache names are lexical metadata
with no parameter/result or escaping package form. All-body and both-branch checks
include their capture, consumer and cleanup schedules.

[Bounded contraction trees](../linalg/networks-and-packing.md#contraction-trees) add explicit unresolved finite
graphs, ordered ports and caller-supplied regroup/GEMM plans. The full public
checker independently resolves their nominal axes and resource names, retains
actual producer/event receipts from both branches and audits their declaration
environment alongside package and packing-cache receipts.

<a id="runtime-shapes"></a>

## Runtime extents and caller-owned maps

Protocol 8 supports a bounded runtime-extent resource profile. Immutable `Nat`
or nonnegative `Int` values from actual checked pure computations can determine
rank-two allocation capacities, column-major layouts and nominal space dimensions.
Real and complex GEMM can reuse a caller's destination through nested calls at
multiple extents. Dimension values never become dispatch keys or evidence that
two nominal spaces or bases are equal.

The [worked package](https://github.com/MGYamada/Vastitas/blob/main/examples/packages/runtime-shapes/src/main.vast) uses two
extents in one executable and calls the same helper twice into each destination.
Run `cargo run -- check --manifest-path examples/packages/runtime-shapes/Vastitas.toml`;
native build additionally requires `--openblas-prefix <pinned-prefix>`.

### Public interface

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

### Exact frame and guard contract

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
see [resource source](#resource-source).

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

### Proof boundary

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
new dependency and the optional native/FFI package stays outside the oracle.
These results do not prove that source scalar execution supplies the stated
valuation, interpret generated source strings, or establish native memory safety
of the full C/Lean toolchain, floating-point field laws or numerical error bounds.
Native boundary tests, sanitizers and equivalent-work experiments remain separate
implementation evidence.

### Execution costs and limits

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
[Resource checking work](checked-storage.md#storage-functions--resource-checking-work)

The public harness `scripts/check_storage_scaling.py --profile runtime`
measures allocation/drop, shared reads, distinct-allocation writers, reborrow
chains and forwarding calls. It records compiler checking times. The earlier
record includes the 512-deep timeout and the later chain record measures the
same workload after the ancestry check changed.
[Earlier comparison](https://github.com/MGYamada/Vastitas/blob/main/experiments/compiler_scaling/results/2026-11-03-macos-runtime/RESULTS.md) · [Chain comparison](https://github.com/MGYamada/Vastitas/blob/main/experiments/compiler_scaling/results/2026-11-03-macos-reborrow-chains/RESULTS.md)

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

The [runtime-shape experiment](https://github.com/MGYamada/Vastitas/blob/main/experiments/runtime_shapes/README.md) separates
canonical public programs from instrumented callable wrappers, explicit lifecycle
costs from destination reuse, and arena data counters from Lean/FFI/backend
allocations. Counting, poison and correctness hooks are not timing evidence.
Controlled-host equivalent-C budgets, total allocation attribution and general
runtime numerical interfaces remain open. This increment does not close Stage 1.

### Validation

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

The full feature validation includes 342 Rust tests and all 13 optional public
numerical native tests, 44 kernel regression targets,
full kernel/oracle builds, and a 25,287-declaration transitive axiom audit allowing
only `propext`, `Classical.choice` and `Quot.sound`. Native storage/GEMM checks and
the [retained output/cost record](https://github.com/MGYamada/Vastitas/blob/main/experiments/runtime_shapes/results/2026-11-01-macos/RESULTS.md)
remain separate from those proofs. The retained experiment identifies its actual
dirty source snapshots and binaries; it is not attributed to a later commit.
