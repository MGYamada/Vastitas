# Nominal numerical values and typed GEMM (protocol 8)

`StorageNumerical` connects the common indexed declaration environment to the
actual resource-function compiler and its GEMM schedule. Public protocol 8
exposes local space/basis/map constructors and bilinear GEMM inside resource
functions. Rust sends unresolved profile paths and local names; Lean independently
resolves them in the same namespace as the complete authority/Fn/dispatch checker.
No checked declaration ID, allocation ID or numerical certificate is accepted.

## Public source and build

Inside a resource function, with three live loans of the corresponding shapes:

```vast
space u = linear(profiles::RealSmooth, 2);
space v = linear(profiles::RealSmooth, 3);
space w = linear(profiles::RealSmooth, 2);
basis bu = basis(u);
basis bv = basis(v);
basis bw = basis(w);
map left = view(input_a, bv, bw);
map right = view(input_b, bu, bv);
map destination = view(output, bu, bw);
gemm(left, right, destination, overwrite, NativeFast);
```

The [complete example](../examples/packages/numerical/src/main.vast) calls sibling
`real` and `complex` modules, checks rectangular products and then accumulates
into the same destination. Each module lives in its own directory with `mod.vast`.
The real product is `[[1,2,3],[4,5,6]] * [[7,8],[9,10],[11,12]]`, giving
`[[58,64],[139,154]]`. The complex example from [#91](https://github.com/MGYamada/Vastitas/issues/91)
uses `[[1,i,2],[0,1,-i]] * [[1,0],[2,1],[0,i]]`, giving
`[[1+2i,3i],[2,2]]`. These are general matrices, not rank-one factor pairs.
Both examples check every output cell and then double the result by accumulating
another product. No conjugation is implicit. Omitted coefficients retain
alpha one and beta zero (`overwrite`) or one (`accumulate`). Explicit machine
coefficients and synchronous scalar-loan reads are supported below; the source
regressions also execute the worked examples with beta=0.5.
The inputs are initialized by their individual stores, with no preliminary
zero-fill. The actual bounded initialization checker combines those write
regions before admitting a read or GEMM input. In the shared generated real and
complex GEMM fixture, removing the four redundant fills reduces recorded written
bytes from 768 to 480, preserving six allocations, zero copied bytes and 256 peak
live data bytes. These are operation counters, not elapsed-time measurements or
evidence of C parity; see [initialization coverage](storage-ir.md#layout-and-initialization).

```sh
cargo run --locked -- check --manifest-path examples/packages/numerical/Vastitas.toml
cargo run --locked -- build --manifest-path examples/packages/numerical/Vastitas.toml \
  --openblas-prefix /path/to/openblas-0.3.34 -o /tmp/numerical-example
/tmp/numerical-example
```

On Linux, add `--native-cc cc` for the host libc used by the pinned OpenBLAS
build. This explicit option selects the numerical consumer compiler/linker and
retains the pinned Lean support libraries; it does not alter ordinary builds.
The prefix must supply the sequential LP64 OpenBLAS 0.3.34 headers and static
archive described in [the adapter contract](numerical-adapter.md).

`check` and kernel emission do not need OpenBLAS. The driver requires an explicit
prefix only when the actual checked entry emits GEMM. An ordinary or storage-only
entry, including one with unused numerical definitions, does not link OpenBLAS.
Unused numerical definitions still undergo all-body checks. Numerical build
options are rejected for `check` and for entries without numerical operations.
Failed checking, prefix resolution or native compilation preserves an existing
output artifact.

## Source and wire compatibility

These forms extend the static body of a package `resource fn`; their prefixes
are parsed in that context. Existing pure functions and resource statements
retain their syntax. Dimensions are unsigned static literals, map endpoints are
explicit local bases, and both the GEMM mode and `NativeFast` policy are required.
Dependent input contracts are described below. Numerical return types and an
implicit product syntax remain separate work.

| Source form | Protocol-8 `operation` fields (besides `op`) |
| --- | --- |
| `space x = linear(path, n);` | `name`, `implementation: {path, span}`, `dimension` |
| `basis b = basis(x);` | `name`, `space` |
| `map m = view(loan, source_basis, target_basis);` | `name`, `loan`, `source`, `target` |
| `gemm(a, b, c, overwrite\|accumulate, NativeFast);` | `left`, `right`, `output`, `mode`, `policy: "native_fast"` |

Every operation is wrapped in `{kind: "numerical", operation, span}`. Profile
paths remain unresolved path segments, and local operands remain names. The
independent Lean decoder validates the schema; `ResourceSource.lowerNumerical`
resolves each profile in its original module and lowers to
`Storage.Functions.Statement.numerical`. The actual full declaration checker
supplies `numericalEnvironment` for both all-body probes and executable expansion.
The kernel rechecks profile visibility, kind and base against those declarations
even if the frontend previously accepted the input. Checked IDs, proof tags,
native conjugation flags and product receipts are not input authority.

This is an additive extension within protocol 8, with no change to the existing
protocol-2–7 schemas. Versions 2–7 reject numerical/resource payloads; a kernel
predating the numerical extension of version 8 rejects the unknown statement
tag. A matching version number alone is therefore not feature negotiation.
Use the matching frontend/kernel revision for these forms. No downgrade to raw
resource GEMM or fallback after rejection is permitted. Unknown semantic fields
remain errors, including fields nested in the profile path. Future incompatible
changes must use a new protocol version rather than reinterpret these forms;
additional optional operations must continue to fail closed on older kernels.

## Explicit and computed coefficients

GEMM accepts optional named coefficients after `NativeFast`:

```vast
// Real beta = 0.5. Accumulate still requires initialized output.
gemm(left, right, accumulated, accumulate, NativeFast,
    beta=f64_bits(4602678819172646912));
// alpha is read at execution time from an initialized 1x1 scalar loan.
gemm(left, right, destination, overwrite, NativeFast,
    alpha=coefficient(scale));
```

Complex coefficients use `complex_bits(real_bits, imaginary_bits)`, with two
binary64 components. Their representation must match the maps; real-to-complex
coercion is not implicit. `alpha` and `beta` may each appear once, in either
order. Overwrite rejects any beta operand and fixes beta to zero. Accumulate
computes `alpha*A*B + beta*C_old` and requires initialized readable output even
for an explicit zero beta. The numerical policy remains `NativeFast`.

`coefficient(loan)` requires a live, unsuspended, readable and initialized 1x1
loan with the matching scalar representation, physically disjoint from output.
It can share read storage with inputs or the other coefficient. The compiler
retains its allocation/byte offset; it does not read or predict the payload.
The native adapter reads its current value synchronously before output writes.
A previous GEMM can produce this scalar, and a later checked update changes the
value read by the next call. The source regression exercises both across actual
resource-function calls for real and complex scalars. No scalar-buffer allocation,
packing or tensor copy is inserted for a coefficient read.

Optional wire fields `alpha` and `beta` contain either
`{kind: "literal", value: <resource literal>}` or
`{kind: "loan", loan: <local name>}`. Omitted fields retain previous behavior;
explicit null and unknown fields are rejected by the kernel. Older kernels
reject these additional fields. Scope resolution and actual read/init/alias
checks remain mandatory; no frontend certificate can substitute for them.

For an empty output there is no matrix element access or BLAS call; explicit
coefficient loans are still validated and read. For zero inner dimension and
nonempty output, the defined degenerate operation is `beta*C`, independent of
alpha (including NaN/Inf alpha). Zero beta fills zero without reading old C;
one beta leaves C untouched; other beta values scale C in place. This is an
explicit numerical execution convention, not an exact-field theorem. Bounds,
representation and alias failures occur before any output write. The existing
native trust boundary and no-rollback behavior of earlier completed calls remain.

`CheckedCoefficient` records the actual scalar/read/init/separation check;
`CheckedProduct.coefficients` retains the requested operands and the exact
emitted GEMM carries them through the independent native-plan audit. The Oracle
proves the coefficient loan contract, initialized bytes, absence of a beta read
in overwrite, and coefficient emission. General scalar expressions, pure-Core
floating values and dynamic shape interfaces remain separate work.

## Dependent numerical inputs

Resource functions can receive caller-created spaces, bases and borrowed maps:

```vast
resource fn multiply_into(
    u: Space<profiles::RealSmooth, 2>,
    v: Space<profiles::RealSmooth, 3>,
    w: Space<profiles::RealSmooth, 2>,
    bu: Basis<u>, bv: Basis<v>, bw: Basis<w>,
    left: ReadMap<bv, bw>, right: ReadMap<bu, bv>,
    destination: WriteMap<bu, bw> initializes
) -> Unit {
    gemm(left, right, destination, overwrite, NativeFast);
    value { () }
}
// In the caller, using the values constructed above:
call multiply_into(u, v, w, bu, bv, bw, left, right, destination) -> ();
```

`Space<profile, n>` requires that exact independently resolved implementation
and static dimension. `Basis<u>` requires the actual space passed as `u`;
it does not construct a new space or basis from a descriptor. Map contracts
refer to two preceding basis parameters. Forward/self references, wrong-kind
dependencies, a different basis of the same space, and equal-size distinct
objects are rejected. Passing one space or basis more than once preserves its
identity. Object identities and dimensions do not become dispatch keys.

`ReadMap`, `WriteMap` and `ReadWriteMap` create call-scoped child loans of the
actual views. They retain the caller's physical offset, padding, transpose,
allocation and endpoints. All input snapshots are checked against the original
caller state before reborrowing; the actual resource transitions then check
each new child against existing siblings. Reusing one immutable map for two
read parameters is allowed; two symbolic parameter names never prove physical
separation for a writer. A map binding remains distinct from its underlying
resource handle. The callee cannot use it as a raw storage handle.

`initializes` checks the whole borrowed region on successful return, allowing
an uninitialized overwrite destination. `ReadWriteMap` requires initialized
input and is suitable for accumulation. Children return inside out, caller
loans and numerical bindings are restored, and nested calls keep the same
nominal endpoints. Borrowed map values and temporary child loans cannot escape as owned results.
Initialized owned-map results use the separate transfer contract below.

The wire parameter tags are `space` (`name`, unresolved `implementation`,
`dimension`, `span`), `basis` (`name`, `space`, `span`) and `map` (`name`,
`source`, `target`, `access`, `initializes`, `span`). Rust and Lean reject
unknown fields. Header profile references undergo the same lexical resolution
and provenance audit as body constructors, including unused definitions.
Older protocol-8 kernels reject these new parameter tags; there is no fallback.
The older internal resource-only component wire format remains unchanged.

Separate probes check every body with its declared static contracts. Every
actual call is independently rechecked with its caller's identities, layout,
initialization and aliases; probes do not prove universal shape or alias
polymorphism. `NumericalInputReceipt` retains the actual input check and an
independent binding audit. Immutable bindings preserve the original identity;
map bindings preserve both bases and the exact successful borrow transition.
The public checker also audits each receipt's declaration environment.

The nested real/complex source regressions execute overwrite and accumulation
through these inputs. Their generated schedule retains six allocations and
four GEMMs with no copy, matching the direct-call fixture. These are structural
cost checks, not timings or a claim of C parity. Runtime shape/scalar flow,
generative numerical packages and escaping-lifetime contracts remain open.

## Owned numerical results

`OwnedMap<source_basis, target_basis>` consumes and returns initialized coordinate
storage while preserving the exact input-dependent endpoints and bases:

```vast
resource fn create(u: Space<profiles::RealSmooth, 1>, bu: Basis<u>,
                   w: Space<profiles::RealSmooth, 1>, bw: Basis<w>)
    returns (result: OwnedMap<bu, bw>) -> Unit {
    allocate buffer: F64[5];
    borrow write = write(buffer, layout(8, 1, 1, 3, false));
    fill(write, f64_bits(4611686018427387904));
    release(write);
    map result = owned(buffer, layout(8, 1, 1, 3, false), bu, bw);
    value { () }
}
// In a caller with these spaces/bases:
call create(u, bu, w, bw) -> (result);
borrow coordinates = read(result);
map a = view(coordinates, result);
release(coordinates);
drop(result);
```

The `owned` constructor is an explicit interpretation of initialized raw storage.
It checks scalar/profile compatibility, bounds, logical dimensions and complete
initialization of the specified view, then moves the original owner into the
new name. Padding outside the view need not be initialized. The old owner is
unusable, and an outstanding loan prevents the move. The owned map retains
allocation identity and the exact offset/leading dimension/transpose layout;
its metadata does not allocate or copy a buffer.

`borrow coordinates = read(result)` (also `write` and `read_write`) uses that
actual stored layout. It is supported only for owned maps. The explicit-layout
borrow form remains available. `view(coordinates, result)` requires the same live
allocation and exact layout and retains the stored bases; a changed transpose,
offset or stale owner cannot silently reuse the interpretation. `move result ->
next` preserves this metadata while revoking the previous owner.

An owned-map parameter requires initialized coordinates and consumes the actual
owner. A result type refers only to basis parameters, whose space dependencies
are also explicit inputs. Returning a different nominal endpoint or basis is an
error even with identical dimensions. On exit, the actual post-body state must
have initialized coordinates, no outstanding loans and no duplicated returned
owner. Call-scoped child loans must have been returned. The caller receives the
same allocation and coordinate metadata under a fresh owner name; later updates
and nested ownership transfers use that exact state.

Raw owned results keep their existing `type: {scalar,elements,initialized}` wire
form. A numerical result uses `type: {kind:"owned_map",source,target}`; the
parameter tag is also `owned_map`. New operation tags are `owned_map`,
`borrow_owned` and `owned_view`. The independent decoder rejects additional
allocation IDs, checked flags and unknown fields. Old kernels reject these forms.
Result dependencies cannot refer to callee-local objects or bases. General
generative numerical packages and borrowed escaping results remain separate work;
the existing all-body probes do not prove universal shape/layout polymorphism.

`NumericalResultReceipt` retains the actual accepted dependent result contract
and returned interpretation. `OwnedMapTransfer` records the exact accepted move
and unchanged allocation/layout/endpoints. The public checker ties result
receipts to its same accepted declaration environment. Oracle results derive
initialized bytes and input/result/transfer identity facts. They do not prove
floating arithmetic, native heap execution or full source correspondence.
Source/native regressions exercise real/complex padded results through nested
calls, update them and use them in later GEMM; six allocations and no copies are
emitted for the two three-buffer programs. This is a structural cost check,
not equivalent-C performance evidence.

## Objects, bases and views

A space constructor requires a concrete `linearDescriptor` implementation from
the independently audited indexed environment. It retains the implementation,
coefficient marker and kind, nominal geometric base, setting, dimension and a
fresh local `Indexed.ObjectRef`. A complex smooth space has complex dimension
`n` and underlying real dimension `2*n`. An affine descriptor, a classification,
a marker or a dimension alone cannot provide linear structure.

Each basis constructor introduces a fresh identity tied to an existing space.
Two bases of the same space are distinct. Two separately constructed spaces of
the same implementation and dimension are also distinct, including across
successive function activations. Numerical values share the compiler's monotone
fresh-name supply with resource bindings. Spaces and bases remain local to their
function or branch unless explicitly passed as numerical inputs, and cannot be
returned as raw owners. Initialized owned maps retain input-dependent bases under
the [owned-result contract](#owned-numerical-results); locally generated object/basis
packages remain pending.

A map view explicitly interprets a buffer in a source and target basis. Its
logical row count is the target dimension and its column count is the source
dimension. Both spaces must have the same implementation, coefficient and
geometric base. The actual allocation's scalar must implement that coefficient
kind. This construction does not assert that existing floating-point data
satisfy additional algebraic laws.

The view retains the complete actual loan: allocation identity, layout, access
and parent. Every use rechecks that snapshot against the current resource state.
Released, suspended or transposed loans cannot reuse stale views, even when a
square transpose preserves dimensions. Payload writes do not change endpoint
typing; no retained payload-dependent mathematical evidence is introduced.

## Checked product and native schedule

For `A : V → W` and `B : U → V`, the destination must represent `U → W`.
The common middle object **and basis**, and both destination endpoints, must
match exactly. The initial product is bilinear: no conjugation or metric is
inserted. Dual, conjugate, adjoint and general metric operations are separate
remaining work.

`checkProduct` reconstructs the three actual views and validates their complete
value provenance, declaration environment and live resource state. It then
calls the existing `Storage.checkGemm` on those exact loans. Readability,
initialization, output exclusivity and physical input/output separation remain
mandatory. `overwrite` does not require initialized output; `accumulate` does.

`StorageFunctions` runs that check during each actual call, separately from
all-body signature probes. A `NumericalReceipt` records the returned product
certificate, exact emitted GEMM, and exact resource transition. Generation
rechecks the function program and then the existing storage/native plan. The
public resource checker supplies its exact accepted declaration environment
to this compiler, audits each independently resolved profile reference and
checks that all returned product receipts retain that same environment.

The nominal values erase before native execution. The closed real and complex
fixtures generate three destination/input allocations, no tensor copies or
extra numerical metadata allocations, and preserve caller-selected output
storage. These counters and successful BLAS calls are not evidence that **Fast
like C** has been achieved; equivalent-C measurements remain a completion gate.

## Evidence and remaining boundaries

`VastitasStorageTest.NumericalRegression` tests actual declaration checking,
real/complex products, distinct nominal objects/bases, fresh call identities,
both branches, unused bodies, scalar/base mismatch, scope escape, stale loans
and forged metadata. `scripts/check_gemm_checked.py` also executes generated
rectangular real and complex fixtures with exact expected bit patterns and
allocation/copy counters, using pinned OpenBLAS 0.3.34.
`tests/numerical_source.rs` tests the actual public source and wire boundaries,
visibility and aliases, wrong bases/objects, scope/capture, old versions and
forged fields. Direct wire mutations exercise both real and complex bodies,
including unused definitions, equal-dimension distinct spaces, distinct bases,
released/suspended loans and a square transpose whose dimensions do not change.
The raw resource-GEMM rejection in `tests/resource_source.rs` preserves a valid
statement span and checks the action-decoder diagnostic, so rejection cannot be
satisfied by missing metadata before the GEMM boundary is reached.
Both OS numerical CI jobs explicitly run the OpenBLAS-dependent
tests for generated real/complex execution, nested numerical inputs, runtime assertion failure and output
protection. Normal compiler CI runs the remaining tests without OpenBLAS.

`VastitasOracle.StorageNumerical` proves profile validity, nominal endpoint and
basis equality, actual loan/layout identity, composition with the resource
checker, and the relation to the emitted request. Existing resource and native
audit theorems still apply to that same schedule. These facts do not prove
ideal field/module laws, floating-point accuracy, source operational
correspondence or native refinement.
`ResourceSource.numerical_provenance` and `public_product_origin` connect profile
resolution and the actual returned product receipts to the same accepted public
source and declaration environment.

`actual_input`, `input_space_identity`, `input_basis_identity` and
`input_map_reborrow` describe the certificates produced by actual argument
binding. `ResourceSource.public_numerical_input_origin` connects those receipts
to the exact environment of the same accepted public request. They do not claim
universal correctness from synthetic probes or native refinement.

Generative numerical result packages, dynamic shape/scalar interfaces, dual/conjugate/metric
evidence, finite tensor networks, dynamic dimensions, packing and end-to-end C
performance comparisons remain open in the [Stage 1 gate](stage1-completion.md).
