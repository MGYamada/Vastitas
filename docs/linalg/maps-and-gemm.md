# Numerical maps, ownership and GEMM

This chapter follows a map from its declaration and nominal spaces through owned packages to the real and complex CPU adapter.

<a id="numerical-declarations"></a>

## Numerical declaration profiles (protocol 8)

**Implemented boundary:** package source can declare and independently check
ideal real/complex coefficient kinds, nominal geometric scalar bases and finite
linear representation profiles. These use the existing indexed declaration
namespace and the complete authority/Fn/dispatch checker. Declaration acceptance
alone does not authorize numerical operations; the separate
[numerical-value path](#numerical-values) checks local spaces, bases, actual
map loans and typed GEMM in public resource functions.

The [mathematics-first charter](../adr/0001-mathematics-first-stdlib.md) distinguishes
an ideal mathematical coefficient domain from its numerical realization. The
existing resource scalars `F64` and `ComplexF64` describe binary64 storage; neither
is an exact `Field` or a `C∞`-ring. `ComplexF64` is still a closed representation,
not a general public `Complex<T>` type constructor. No new scalar dispatch key,
pure floating arithmetic or recursive `Fn` scalar type is introduced here.

### Source contract

```vast
pub indexed marker RealCoefficients;
pub indexed marker ComplexCoefficients;
pub indexed implementation SmoothScalar(RealCoefficients, scalar_base(smooth, real)) capabilities();
pub indexed global SmoothBase(SmoothScalar);
pub indexed implementation RealSmooth(RealCoefficients, linear_descriptor(SmoothBase, real)) capabilities();
pub indexed implementation ComplexSmooth(ComplexCoefficients, linear_descriptor(SmoothBase, complex)) capabilities();
```

The marker is a nominal coefficient declaration. `SmoothBase` is a distinct
global geometric object, resolved through its package/module and visibility.
Passing the marker or the implementation declaration as the base is rejected.
Two globals of the same base implementation remain different base IDs. An alias
resolves to the original ID; identical spelling in another package does not.

`scalar_base(setting, coefficient)` admits `scheme` and `smooth` settings and
`real` and `complex` ideal coefficient kinds. A smooth scalar base must be real.
An ordinary scheme base may use either kind. `linear_descriptor(Base, kind)`
requires that exact global base to refer to a scalar-base implementation:

| Linear profile | Required base and coefficient relationship |
| --- | --- |
| Ordinary scheme, real or complex | Same ideal kind and exact coefficient marker as the base |
| Smooth, real | Real geometric base and the same coefficient marker |
| Smooth, complex | Real geometric base and a distinct complex coefficient marker |

Every numerical use of one nominal marker must agree on its ideal coefficient
kind throughout the complete environment, including unused declarations. Profile
validation is declaration-order independent. The complex smooth profile retains
complex coefficients over a real geometric base; the later object constructor
must retain the distinction between complex dimension `n` and real dimension
`2*n`. No dimensions are constructed by these declarations alone.

Both new representations require `capabilities()`. They cannot claim the old
affine `origin` or `dimension` capabilities. Old `descriptor` and `global`
primitive bindings and point/morphism representation families remain limited to
the affine descriptor backend. Numerical metadata therefore cannot turn an
existing geometry primitive into a numerical realization. Generic token families
retain their existing index mechanism. A declared linear profile does not attest
algebraic laws or convert arbitrary `Scheme`/`CInfScheme` values into linear maps.

### Wire and checker boundary

Rust selects protocol 8 when any package contains a numerical representation,
even without resource functions. Existing `"affine_descriptor"` JSON is unchanged.
New representations are single-key objects:

```json
{"scalar_base": {"setting": "smooth", "coefficient": "real"}}
{"linear_descriptor": {"base": {"path": ["SmoothBase"], "span": {"start": 0, "end": 0, "line": 1, "column": 1}}, "coefficient": "complex"}}
```

Unknown fields, multiple representation keys, machine scalar names in the ideal
coefficient field, and old wire versions are rejected. Lean resolves base paths
through the same namespace resolver and records their provenance. The actual
`Indexed.Source.checkDeclarations` certificate checks all new contracts;
`ResourceSource` still checks every ordinary and resource body. The exact returned
Core independently audits its complete declaration environment again before
generation. No frontend-selected checked IDs or profile certificates are accepted.

The example under `examples/packages/numerical/numerical-declarations` checks these
declarations while compiling an ordinary program that returns `42`. It requires
neither OpenBLAS nor the storage native runtime. Declaration acceptance is not
evidence of numerical execution or C-level performance.

### Validation and remaining connection

`tests/numerical_declarations.rs` exercises source check/build/execution, version
downgrades, unused invalid bodies/profiles, wrong coefficient/base relationships,
namespace visibility, old primitive rejection and forged wire metadata.
`IndexedNumericalRegression` additionally checks nominal base preservation,
declaration permutations, cycles and tampered returned-Core rejection.

The actual-checker theorems in `VastitasOracle.IndexedSource` establish the
implementation contract, required linear base profile, real base/distinct
coefficient for smooth complex profiles, coefficient-kind coherence and the old
constructor boundary. `ResourceSource.public_numerical_declaration` connects
that contract to the actual protocol-8 decoded and accepted input. These prove
structural declaration facts, not mathematical field/module laws, native
refinement or floating-point accuracy.

The [numerical-value compiler](#numerical-values) now constructs
local nominal spaces/bases and loan-backed maps, checks their bilinear GEMM
composition and emits the exact independently rechecked storage schedule.
The public decoder and source grammar expose these operations inside resource
functions, with independently resolved profile paths and exact receipt provenance.

Dependent map interfaces, explicit dual/conjugate/metric evidence and finite networks are part of the [delivered profile](../stage1-completion.md). The declaration metadata alone grants no authority to execute a numerical operation.

<a id="numerical-values"></a>

## Nominal numerical values and typed GEMM (protocol 8)

`StorageNumerical` connects the common indexed declaration environment to the
actual resource-function compiler and its GEMM schedule. Public protocol 8
exposes local space/basis/map constructors and bilinear GEMM inside resource
functions. Rust sends unresolved profile paths and local names; Lean independently
resolves them in the same namespace as the complete authority/Fn/dispatch checker.
No checked declaration ID, allocation ID or numerical certificate is accepted.
The [adapter responsibility map](#numerical-adapter--responsibilities-along-the-implemented-path)
distinguishes this public entry, actual Lean checks, checked native lowering and
physical OpenBLAS execution.

<a id="numerical-values--public-source-and-build"></a>

### Public source and build

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

The [complete example](https://github.com/MGYamada/Vastitas/blob/main/examples/packages/numerical/numerical/src/main.vast) calls sibling
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
evidence of C parity; see [initialization coverage](../storage/checked-storage.md#storage-ir--layout-and-initialization).

```sh
cargo run --locked -- check --manifest-path examples/packages/numerical/numerical/Vastitas.toml
cargo run --locked -- build --manifest-path examples/packages/numerical/numerical/Vastitas.toml \
  --openblas-prefix /path/to/openblas-0.3.34 -o /tmp/numerical-example
/tmp/numerical-example
```

On Linux, add `--native-cc cc` for the host libc used by the pinned OpenBLAS
build. This explicit option selects the numerical consumer compiler/linker and
retains the pinned Lean support libraries; it does not alter ordinary builds.
The prefix must supply the sequential LP64 OpenBLAS 0.3.34 headers and static
archive described in [the adapter contract](#numerical-adapter).

`check` and kernel emission do not need OpenBLAS. The driver requires an explicit
prefix only when the actual checked entry emits GEMM. An ordinary or storage-only
entry, including one with unused numerical definitions, does not link OpenBLAS.
Unused numerical definitions still undergo all-body checks. Numerical build
options are rejected for `check` and for entries without numerical operations.
Failed checking, prefix resolution or native compilation preserves an existing
output artifact.

<a id="numerical-values--source-and-wire-compatibility"></a>

### Source and wire compatibility

These forms extend the static body of a package `resource fn`; their prefixes
are parsed in that context. Existing pure functions and resource statements
retain their syntax. Dimensions are unsigned static literals, map endpoints are
explicit local bases, and both the GEMM mode and `NativeFast` policy are required.
Dependent input contracts and initialized owned results are described below.
General generative numerical result packages and implicit product syntax remain separate
work. [Typed dual/conjugate/adjoint operations](transforms-and-metrics.md#linear-transforms) add explicit
derived-space, basis, involution and metric contracts.
[Vector evaluation](transforms-and-metrics.md#vector-evaluation) additionally uses single-basis
coordinate vectors, explicit conjugation, dual evaluation and declared-form
pairing with actual scalar output loans.

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

<a id="numerical-values--explicit-and-computed-coefficients"></a>

### Explicit and computed coefficients

GEMM accepts optional named coefficients after `NativeFast`:

```vast
// Real beta = 0.5. Accumulate still requires initialized output.
gemm(left, right, accumulated, accumulate, NativeFast,
    beta=f64(0x1p-1));
// alpha is read at execution time from an initialized 1x1 scalar loan.
gemm(left, right, destination, overwrite, NativeFast,
    alpha=coefficient(scale));
```

For complex maps, `alpha=complex(0x1.8p0, -0x1p1)` specifies `1.5 - 2i`.
Both components must be exactly representable in binary64. Use
`complex_bits(real_bits, imaginary_bits)` when the bit patterns themselves
matter, for example a NaN payload or negative zero. Each coefficient must use
the same scalar representation as the maps. See the
[literal syntax](../storage/resource-programs.md#resource-source--explicit-source-contracts).

`alpha` and `beta` may each appear once, in either
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
floating values remain separate work; whole-map integral extents use the
separate [runtime-shape interface](../storage/resource-programs.md#runtime-shapes).

<a id="numerical-values--dependent-numerical-inputs"></a>

### Dependent numerical inputs

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
cost checks, not timings or a claim of C parity. Broader runtime numerical flow,
general generative numerical packages and escaping-lifetime contracts remain open.

<a id="numerical-values--owned-numerical-results"></a>

### Owned numerical results

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

### Objects, bases and views

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
the [owned-result contract](#numerical-values--owned-numerical-results). [Owned-map packages](#owned-map-packages)
can hide one generated primal target and direct basis; general closures remain pending.

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

### Checked product and native schedule

For `A : V → W` and `B : U → V`, the destination must represent `U → W`.
The common middle object **and basis**, and both destination endpoints, must
match exactly. GEMM inserts no implicit conjugation or metric.
[Explicit typed transforms](transforms-and-metrics.md#linear-transforms) can supply dual or conjugate
maps, or adjoints for declared orthonormal metrics. Their checked views retain
the resulting endpoints, bases and flags through GEMM. General metric realization
remains separate work. The [two-map network profile](networks-and-packing.md#finite-networks) adds
independent occurrence/port/edge/boundary checks before this same product path.

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

### Evidence and remaining boundaries

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
tests for generated real/complex execution, computed coefficients, nested numerical
inputs, owned results, typed transforms, runtime assertion failure and output
protection. Normal compiler CI runs the remaining tests without OpenBLAS.

`VastitasOracle.StorageNumerical` proves profile validity, nominal endpoint and
basis equality, actual loan/layout identity, composition with the resource
checker, and the relation to the emitted request. Existing resource and native
audit theorems still apply to that same schedule. These facts do not prove
ideal field/module laws, floating-point accuracy, source operational
correspondence or native refinement.
`ResourceSource.numerical_provenance` and `public_product_origin` connect profile
resolution and the actual returned product receipts to the same accepted public
source and declaration environment. In the reverse direction,
`NumericalCoverage.public_action` finds the typed receipt for each static GEMM
or diagonal metric instruction at its exact position in that entry's schedule.
The audit distinguishes both branch arms and repeated calls to the same function.
See the [positional coverage theorems](https://github.com/MGYamada/Vastitas/blob/main/lean/VastitasOracle/NumericalCoverage.lean).

`actual_input`, `input_space_identity`, `input_basis_identity` and
`input_map_reborrow` describe the certificates produced by actual argument
binding. `ResourceSource.public_numerical_input_origin` connects those receipts
to the exact environment of the same accepted public request. They do not claim
universal correctness from synthetic probes or native refinement.

The [typed transform compiler](transforms-and-metrics.md#linear-transforms) now retains dual/conjugate
origins, corresponding bases and declared metric evidence through actual
read reborrows and nested calls. [Vector evaluation](transforms-and-metrics.md#vector-evaluation) now
connects bilinear dual and explicit orthonormal Hermitian pairing to scalar
destinations through the same checked GEMM. [Finite two-map networks](networks-and-packing.md#finite-networks)
add checked occurrences and ports, an explicit bilinear edge and ordered boundaries.
[Explicit diagonal metrics](transforms-and-metrics.md#diagonal-metrics) add materialized adjoints and
weighted pairing with caller-owned scratch and exact declared Int coefficients.
Dense metric realization, general generative numerical result packages, broader runtime
shape/scalar interfaces, general-rank/cyclic networks and controlled-host C
performance acceptance remain with the broader trackers. See the [performance handoff](../stage1-completion.md#stage-2-or-later-performance-acceptance).

[Owned-map packages](#owned-map-packages) now add the bounded
`OwnedMapTo<source_basis,target_dimension>` profile: one hidden primal target and
direct basis, initialized affine storage, fresh consuming unpack and explicit
repack. The source basis remains an actual caller dependency. Pack/open/transfer
preserve the exact allocation/layout and emit no additional native instructions.
Dynamic package-result dimensions, general resource packages/closures, borrowed results and
full source/native refinement remain pending.


[Bounded contraction trees](networks-and-packing.md#contraction-trees) now extend the two-map network
path with explicit finite multi-edge plans and rank-two/three intermediates.
Caller-owned regrouping and versioned producer rebinds preserve axes, resource
provenance and cache invalidation. [Packing caches](networks-and-packing.md#cached-packing) separately
permit checked reuse of unchanged packed scratch. These finite paths do not add
general dynamic tensor-valued interfaces or complete native refinement.

<a id="owned-map-packages"></a>

## Generative owned-map packages

Protocol 8 supports `OwnedMapTo<source_basis, target_dimension>`, an affine
package containing one initialized owned map, one hidden primal target space and
its direct basis. The source basis is an explicit dependency on an earlier
parameter. Dimensions remain static. This bounded profile does not implement
runtime dimensions, arbitrary existential resource tuples or borrowed results.

The [real and complex example](https://github.com/MGYamada/Vastitas/tree/main/examples/packages/numerical/generative-owned-map)
returns locally generated targets, passes packages through nested calls, opens
and repacks them, and uses their exact padded allocation through dependent
owned-map and read-map parameters. It builds and runs without OpenBLAS because
its checked schedule contains no GEMM.

```vast
resource fn create(u: Space<profiles::RealSmooth, 2>, bu: Basis<u>)
    returns (boxed: OwnedMapTo<bu, 3>) -> Unit {
    space w = linear(profiles::RealSmooth, 3);
    basis bw = basis(w);
    allocate buffer: F64[10];
    borrow initialize = write(buffer, layout(8, 3, 2, 4, false));
    fill(initialize, f64_bits(0));
    release(initialize);
    map result = owned(buffer, layout(8, 3, 2, 4, false), bu, bw);
    map boxed = pack(result);
    value { () }
}
// In a caller with u and bu:
call create(u, bu) -> (boxed);
unpack boxed as (w, bw, result);
borrow coordinates = read(result);
release(coordinates);
drop(result);
```

`pack` consumes an initialized `OwnedMap`. Its target must be primal and its basis
direct; hiding a dual/conjugate origin, derived basis or metric dependency needs a
richer closure contract and is rejected. The independent check retains the exact
source basis, implementation, geometric base, real/complex coefficient profile,
allocation, offset, stride, transpose and initialization. Equal dimensions do not
establish these identities. Padding outside the view need not be initialized.
Outstanding loans prevent packing, moving, passing or returning the owner.

An opaque package permits only metadata-preserving ownership moves, matching
`OwnedMapTo` arguments/results, consuming unpack and drop. Raw borrowing, raw
`Owned` arguments/results and reconstruction as another owned map are rejected
while it is opaque. These restrictions are checked in the actual resource
compiler, including direct internal function input; frontend binding kinds do
not supply authority. An opaque value's binding name must equal its owner.

`unpack boxed as (w, bw, result);` consumes `boxed` and introduces fresh abstract
space and basis brands plus a fresh owner name. It keeps the source basis and
all physical storage metadata. Two independent same-dimensional packages remain
distinct. Repacking and opening again introduces new abstract identities; an old
opened basis cannot type the newly opened map. No conversion, conjugation,
metric, coordinate copy or equality evidence is inserted.

Opened names belong to the current function or branch scope. Ordinary owned-map
results still refer only to basis parameters; a hidden local target cannot escape
through that result contract. Repack explicitly to return a hidden target. A
function must return or drop every local owner and restore all caller loans.
General result joins between branches and escaping borrowed lifetimes remain
outside this profile. Both branches and every unused resource body are checked;
synthetic argument probes never supply executable payloads.

### Wire and independent certificates

Parameters use `kind:"owned_map_to"` with `name`, `source`, `dimension`, `span`.
Results use `type:{kind:"owned_map_to",source,dimension}`. The source dependency
must name an earlier basis parameter. `pack_map` has `name` and `owner`;
`unpack_map` has `package`, `space`, `basis`, `owner`. All appear inside the usual
numerical operation envelope. Rust and Lean independently decode these forms;
unknown fields, supplied allocation IDs, success flags and old wire envelopes
are rejected. The fields contain unresolved source names, not checked brands.

`StorageOwnedPackages.checkPackage` reconstructs and audits the closed target,
actual live/initialized map, fresh opening and exact `Storage.checkAction` move.
`StorageFunctions` retains the accepted operation and emitted-move receipt, plus
actual post-body result receipts. Returned payloads are tagged as raw, map or
package. Real calls validate their original caller's dependencies; package
results carry their closed target across the ordinary lexical-state reset.
The public source checker audits every package operation/result receipt against
the same declaration environment accepted by the full authority checker.

`VastitasOracle.StorageOwnedPackages` proves actual acceptance and emission,
source/allocation/layout preservation, initialization, opening freshness and
witness bindings, closed target restrictions and actual dependent result
contracts. Public origin theorems refer to the exact protocol-8 returned checker
result. These are structural/resource guarantees, not float field laws, full
source operational equivalence or native heap refinement.

### Execution cost and validation

Pack, unpack and transfer emit only existing resource moves. Native lowering
erases moves, so there is no runtime package allocation, coordinate copy or
extra GEMM. The example emits exactly two data allocations (one per scalar
profile), and no copies; no-mathlib/no-OpenBLAS native tests execute padded,
transposed and zero-dimensional variants. This is cost evidence, not a claim of
C parity.

`OwnedPackageRegression` covers actual dependent calls and results, both branch
receipt sets, initialization, outstanding loans, raw erasure, stale allocation,
forged hidden provenance, reused witnesses and opaque name/owner mismatch.
`tests/generative_packages.rs` checks source and strict raw-wire rejection and
executes generated real/complex programs. The optional numerical suite feeds
opened maps into actual real/complex GEMM with unchanged allocation counts and
no copies. The existing resource replay, forged native-plan, cleanup and
sanitizer checks remain applicable.

<a id="numerical-adapter"></a>

## Optional native GEMM adapter

Public protocol 8 can execute real and complex GEMM from `.vast` package
`resource fn` bodies. The [public numerical path](#numerical-values) connects
unresolved source names to independently checked nominal spaces, bases and live
map views, then to the checked resource/native schedule and OpenBLAS execution.
`lean-kernel/numerical` is its optional **internal C backend and Lean FFI package**;
the internal API is distinct from the already implemented public source entry.

<a id="numerical-adapter--responsibilities-along-the-implemented-path"></a>

### Responsibilities along the implemented path

| Layer | Responsibility | Boundary |
| --- | --- | --- |
| Public syntax and protocol 8 | The Rust frontend parses numerical statements; `ResourceProtocol` independently decodes unresolved paths, local names, modes and coefficients in Lean. | Frontend acceptance is not semantic acceptance. Public input cannot supply checked IDs, product receipts or raw resource GEMM actions. |
| Actual Lean checking | `ResourceSource` supplies the same declaration environment accepted by the full authority/Fn/dispatch checker. `StorageNumerical` checks nominal endpoints, bases and live map views; `StorageFunctions` checks every body and each actual call. `Storage.checkGemm` checks access, initialization, scalar/shape compatibility, coefficients and output separation. | Raw resource access or matching dimensions alone cannot authorize a mathematical map or metric. All-body probes remain separate from executable call checks. |
| Checked native lowering | `ResourceCodegen` and `StorageCodegen` recheck the source components, exact resource schedule and native instructions, retaining actual allocation/layout, mode, coefficients and explicit transform flags. | Only a checked entry whose schedule contains GEMM requests the optional numerical runtime. |
| Native execution | The C adapter reconstructs physical views from the live storage arena, checks layout/alias/ABI conditions before writes, and calls pinned OpenBLAS `dgemm` or `zgemm` for nondegenerate products. | It relies on the checked caller for logical initialization, permissions and nominal authority. Empty and zero-inner operations use the explicit conventions below. |

The separate `lean/` proof oracle imports the actual checker definitions and
proves structural acceptance, provenance and exact-lowering facts. Ordinary
compilation and generated programs do not invoke it. Those facts and native
regression results do not prove floating-point field laws, ideal matrix results,
certified numerical error bounds or source/native refinement; see the
[proof boundary](../verification.md#what-is-outside-these-claims).

### Build and dependency boundary

For public package syntax and `vastitas check`/`build`, use
[the numerical source guide](#numerical-values--public-source-and-build).
Checking and kernel source emission need no OpenBLAS. A native build requires
`--openblas-prefix` only when its checked entry emits GEMM or diagonal Hermitian
pairing; unused numerical
bodies are still checked but do not force a numerical runtime dependency.

Build this optional dependency explicitly with Python 3.12+, Make and a host C
toolchain. The checked executable tests also require the pinned Lean toolchain:

```sh
python3 scripts/build_openblas.py --prefix /tmp/vastitas-openblas --jobs 4
python3 scripts/check_gemm_native.py --prefix /tmp/vastitas-openblas
```

On Linux run
`python3 scripts/check_gemm_checked.py --prefix /tmp/vastitas-openblas --lean-cc cc`.
On macOS run
`python3 scripts/check_gemm_checked.py --prefix /tmp/vastitas-openblas`.

The builder downloads the [OpenBLAS 0.3.34 release](https://github.com/OpenMathLib/OpenBLAS/releases/tag/v0.3.34)
and verifies SHA-256
`cd7e129868320cc2d033afa920e31202dfe0b8066a5b66661900ccc0f197dfed`.
`--archive path` permits an offline build of that exact archive. An existing
nonempty prefix is rejected. The profile is a host-specific static BLAS/CBLAS
archive, LP64 (signed 32-bit BLAS integers), sequential execution with locking,
no LAPACK/Fortran dependency, and no shared library. This is a build-host artifact,
not a portable prebuilt distribution. `vastitas-openblas.json` records the source
pin and build options; the prefix also contains the upstream BSD-3-Clause notice.
Redistributing linked binaries requires retaining that notice.

Linux numerical consumers select the host compiler with Lake's `LEAN_CC=cc`
override, matching the libc used to build OpenBLAS. The regression script's
`--lean-cc cc` applies this override only to generated consumers and adds
`-L <lean-prefix>/lib` to their link arguments. This retains Lean's matching
C++ ABI and support archives instead of substituting an incompatible host
libc++ version; it does **not** add `<lean-prefix>/lib/glibc`. Lean's
[portable toolchain](https://github.com/leanprover/lean4/blob/v4.35.0/script/prepare-llvm-linux.sh)
bundles an older libc for linking and only minimal C headers, not a full C SDK.
A host-built archive can reference newer libc symbols such as `__isoc23_strtol`
that the bundled linker libraries lack.
macOS CI tests the existing bundled Lean linker against its host-built archive.
These are host-specific linked programs; no broader deployment ABI is claimed.

The ordinary compiler, checking kernel, storage-only runtime and nonnumerical
programs do not invoke this builder or link OpenBLAS. The numerical CI job is
separate from both no-mathlib compiler jobs. The adapter includes the installed
CBLAS header and checks the linked library's version, integer ABI and threading
before any GEMM. It rejects ILP64 and unsupported threaded builds; it never changes
process-wide thread settings inside an operation. A sequential build must also
report `USE_LOCKING` in its configuration: OpenBLAS 0.3.34 serializes its shared
buffer pool only in locked or threaded builds, and concurrent operations on
distinct arenas rely on that lock. The builder checks the installed archive's
reported profile and fails closed before recording a prefix. The linked static backend is
validated once with `pthread_once`; both success and failure statuses are cached.
`vgemm_configuration` shares that initialization and returns an immutable copy,
avoiding repeated writes to OpenBLAS's global configuration buffer during
concurrent operations on distinct arenas. This adds a fixed 256-byte static
snapshot plus once/status metadata, with no heap allocation. A missing or
oversized provider string is rejected. The cache covers backend identity only;
each operation still checks its actual shapes, bounds, aliases and coefficients
before writes. Existing measured records retain their original adapter and
costs; the once change alone is not new timing or C-parity evidence.
LP64 and alternate integer ABIs
are distinct interfaces in the [upstream distribution contract](https://www.openmathlib.org/OpenBLAS/docs/distributing/).

Linux numerical CI selects the explicit `HASWELL`/AVX2 target for Valgrind's
[documented instruction support](https://valgrind.org/docs/manual/manual-core.html).
macOS CI uses its build host's target. This does not extend memory-check evidence
to untested CPU kernels. The builder also accepts the conservative `ARMV8` target.

### Initial operation contract

`vgemm_execute` receives arena allocation IDs and physical view descriptors.
`vstorage_prepare_dense` reconstructs each ephemeral descriptor from the actual
live allocation; no supplied pointer or claimed capacity is accepted. The
descriptor must not survive an intervening drop or concurrent arena mutation.
An arena is used synchronously by one resource operation at a time.

`vgemm_execute` preserves the original alpha-one/beta-zero-or-one entry.
`vgemm_execute_scaled` adds explicit binary64 coefficients and actual scalar-view
reads. Default alpha is one; default beta is zero for overwrite and one for
accumulate. Both entries use the same preflight and execution path.

| Mode | Numerical action | Required logical resource authority |
| --- | --- | --- |
| `VGEMM_OVERWRITE` | `C := alpha A B`, beta zero, no old-C dependency; an explicit beta is rejected | Exclusive write; output may be uninitialized |
| `VGEMM_ACCUMULATE` | `C := alpha A B + beta C` | Exclusive read/write; all logical output cells initialized even for beta zero |

`VGemmCoefficient` selects default, explicit scalar bits, or one scalar at a
live allocation/byte offset. Nonempty complex views and live complex coefficient
views must start on a 16-byte element boundary relative to that allocation;
the native binary64 component pointer alignment remains 8 bytes. Half-element
offsets fail preflight before reading coefficients or writing output. Views
undergo bounds/alignment/scalar and output
separation checks, then their values are read before any output mutation. They
may alias input reads and each other. Logical read rights and initialization
come from `Storage.checkCoefficient`; physical preflight does not manufacture
them. Coefficients use stack scalars, with no additional data allocation or
implicit packing/copy. The Lean FFI retains the original `gemm` entry and adds
`gemmScaled`; exact native lowering chooses the latter for explicit coefficients.

The C adapter checks live handles, scalar representation, stored and logical
dimensions, offsets/alignment, leading dimensions, bounds, overflow, LP64
narrowing and conservative accessed-region overlap before writing. Inputs may
alias one another; output must be disjoint from both. Disjoint views in one
allocation are permitted only when their physical bounding byte intervals do not
overlap. Unsupported layouts are rejected; no implicit packing or alias-repair
copy is introduced. CBLAS receives column-major buffers through one direct
`dgemm` or `zgemm` call for nondegenerate compatible operands, except that a
1×1 output uses the [fused scalar path](#numerical-adapter--scalar-outputs).

Transpose and conjugation are independent input operations. Complex inputs use
N (neither), T (transpose), R (conjugation without transpose), or C (both).
The pinned OpenBLAS [CBLAS interface](https://github.com/OpenMathLib/OpenBLAS/blob/v0.3.34/cblas.h)
and [GEMM implementation](https://github.com/OpenMathLib/OpenBLAS/blob/v0.3.34/interface/gemm.c)
provide `CblasConjNoTrans` for R; the adapter passes it directly without adding a
packing buffer or copy. This is a contract with the pinned backend, not a claim
of portability to every BLAS implementation. Real conjugation is the identity,
so its two orientations remain N and T. Transposed output is still rejected.
Conjugation never swaps dimensions, changes physical byte regions, or conjugates
the explicit alpha/beta coefficients.

These raw flags do not confer mathematical dual/adjoint authority: the
[public typed caller](transforms-and-metrics.md#linear-transforms) independently checks derived
endpoints/bases or declared orthonormal metric evidence before selecting flags.
Complex scalars and arrays use two adjacent binary64
components; alpha/beta use the CBLAS pointer convention.

An empty output performs no matrix element access and no kernel call; explicit
coefficient views are still checked and read. For nonempty output and zero inner
dimension, the defined operation is beta*C independently of alpha, including
nonfinite alpha. Zero beta fills zero without reading C, one beta preserves C,
and other beta values scale C in place, without a BLAS call. Any preflight failure leaves output
bytes, write counters and the returned operation report unchanged. The native
BLAS routine has no recoverable partial-write result; crashes and violations of
its contract are outside this guarantee.

<a id="numerical-adapter--scalar-outputs"></a>
A 1×1 output with a nonzero inner dimension, as in vector evaluation and the
diagonal Hermitian pairing, does not enter the BLAS driver. The adapter computes
`beta*C + alpha*sum_p op(A[0,p]) op(B[p,0])` in one native loop over the same
checked views, strides and conjugation flags, with no packing or BLAS workspace.
The sum starts at +0 and adds each product in increasing p. Every product,
difference and sum is separately rounded, with no FMA contraction, so the result
does not depend on the host's BLAS kernel. It can differ in the last bits from
the former `dgemm`/`zgemm` call, whose kernels may use FMA and their own order.
As in the pinned level-3 driver, zero beta reads no old output, one beta
preserves it, and zero alpha reads neither input; an alpha of one is applied
exactly. Preflight, write accounting and the returned report are unchanged; the
loop counts as the operation's one kernel call. When every product and partial
sum is exactly representable, the result equals the former call bit for bit;
the adapter tests check this for every orientation, conjugation and coefficient form.

### Evidence and remaining obligations

Tests cover real and complex 2×3 by 3×2 products for all 16 pairs of independent
transpose/conjugation flags, with compact and padded/shifted views. An independent
small-integer reference loop checks complex results; input values and output
padding guards remain unchanged. Tests also cover T versus C on `[i]`, read
aliases, output reuse, empty shapes,
input/output alias rejection, scalar mismatch, bounds and narrowing failures.
Overwrite is exercised with genuinely uninitialized malloc-backed output and
with old NaNs. NaN/Inf inputs are accepted; no implicit finite scan occurs.
The adapter adds no data allocation or copy. Reports count calls and written
logical bytes; storage counters exclude OpenBLAS's internal workspace/packing
and allocator/Lean overhead, so they are not an end-to-end cost measurement.
The separate [workspace diagnostic](https://github.com/MGYamada/Vastitas/blob/main/experiments/openblas_workspace/README.md)
rebuilds only OpenBLAS's memory-management object and calibrates pool loans versus
retained mmap/malloc requests. Its paired macOS/Linux records preserve identical
calculation objects and adapter results. They measure virtual/requested capacity,
not actual packing bytes, residency, unchanged-backend timing or total allocation.

Successful Unit results from `gemm`, `gemmScaled` and diagonal pairing use the
storage FFI's [shared persistent result](../storage/checked-storage.md#storage-ir--native-lowering-and-execution).
Production uses pinned Lean's `lean_obj_once`, rather than the private
`pthread_once` prototype in the
[original allocation record](https://github.com/MGYamada/Vastitas/blob/main/experiments/allocation_audit/results/2026-11-01-macos/RESULTS.md).
Its one-time result retains no arena or backend data; errors remain fresh, and
nonexclusive caller continuations can still allocate. Removing repeated FFI
success-result construction leaves physical preflight, GEMM execution and cleanup
unchanged; it makes no total-heap, speed or C-parity claim.
The [production allocation record](https://github.com/MGYamada/Vastitas/blob/main/experiments/allocation_audit/results/2026-11-01-macos-production/RESULTS.md)
counts the actual once initializer and returned uses separately from the
remaining generated-caller constructors and physical arena costs.

ASan/UBSan cover the shim and storage runtime. Linux numerical CI additionally
uses Valgrind on the actual linked OpenBLAS machine code to detect observable
uninitialized-value use. Compile-time ILP64 rejection and simulated linked-library
version/ABI/threading mismatches exercise rejection before output mutation.
These are regression evidence, not a proof that arbitrary native implementations
never read uninitialized memory or always compute the ideal mathematical product.

The selected kernel may use FMA, blocking and its own reduction order. It does
not promise cross-backend bitwise equality, finite results, exact field laws or
a certified error bound. Mathematical smoothness concerns the ideal operation,
not the discrete bit-pattern function. General scalar expressions and LAPACK
operations need separate typed contracts.

The C API trusts its caller's logical initialization and read/write rights, as
the existing native storage layer does. The checked internal path below supplies
those rights. The public path separately supplies nominal numerical types and
source integration, including explicit typed dual/conjugate operations and
adjoints for declared orthonormal metrics. The remaining public scope is listed
below.
This increment does not establish **Fast like C**; use the
[storage performance gate](../storage-ownership.md#713-performance-evidence-and-acceptance).

### Checked internal resource execution

`Storage.Action.gemm` names existing loans, explicit `native_fast` policy,
`overwrite`/`accumulate` mode and explicit input conjugation flags. The strict
Rust/Lean component decoders reject missing/unknown policy and mode fields.
This component is not a public wire envelope or a mathematical map constructor.
Public resource source rejects the raw action and uses the independently checked
numerical operation instead. Raw flags cannot provide transformed endpoint,
basis or metric authority.

`Storage.checkGemm` reconstructs each loan and its allocation from the actual
state, rejects suspended parents, requires initialized readable inputs and a
writable output, and checks scalar representations, logical dimensions and the
supported native orientation. Accumulate additionally requires readable,
initialized output. Explicit input/output separation is checked even when the
same read/write handle is reused in multiple operand roles. Read inputs may
alias; disjoint views of the same allocation may use checked byte envelopes.
No allocation, packing, copy or metric selection is inserted.

A successful resource transition records exactly the output rectangle and
advances its logical version. Zero-inner overwrite initializes zeros in native
execution; zero-inner accumulate scales previously initialized output by beta. Empty
regions contain no bytes. These logical guarantees apply to successful completion;
a failed native call throws and the generated Unit-only `try`/`catch` closes the
arena before rethrowing. Cleanup runs once on either path; if cleanup itself
fails, that error takes precedence over the body error. Successful completion
returns the cleanup's Unit result directly, avoiding the old generated
`finally` result-reconstruction allocation. The older allocation records retain
their measured fallback cost; this change does not remove other caller
allocations or the persistent shared result. Earlier completed writes are not
rolled back. Native backend faults remain trusted-boundary
failures, not recoverable checked transitions.

`Storage.Native` retains the exact allocation IDs, physical views, flags, mode and
policy, and repeats original schedule/lowering comparison before generation.
GEMM plans import `VastitasGemmNative`; other plans import only the storage runtime.
The numerical Lake package depends solely on the sibling storage package and an
explicit pinned OpenBLAS prefix. The archive is a transitive native dependency,
including downstream generated executables; no system BLAS fallback is selected.
For a direct package build use
`lake -d lean-kernel/numerical -Kopenblas=/path/to/prefix build`;
on Linux set `LEAN_CC=cc` for that build and each downstream executable build,
and give the downstream package `moreLinkArgs := #["-L", "<lean-prefix>/lib"]`
using its actual `lean --print-prefix` output.
The regression consumer demonstrates a dependency-specific `openblas` Lake option.

`VastitasOracle.StorageGemm` imports the actual checker. It proves the exact
accepted transition, input initialization, accumulate's old-output requirement,
input/output byte separation and initialized output bytes in the actual logical
post-state. `conjugation_preserves_resource_obligations` proves that changing
either explicit conjugation flag preserves the entire physical resource
predicate. `emitted_operation` connects the actual accepted request, reconstructed
views, flags and coefficients to the exact native instruction. Existing
exact-lowering and closed-exit theorems cover these actions.
It does not prove nominal map typing, ideal matrix multiplication, floating-point
results, native no-read behavior or source/native refinement.

The shared Rust/Lean fixture executes real and complex rectangular products,
overwrite into uninitialized output and accumulate in reused output. Native tests
also cover all 16 complex N/T/R/C pairs on rectangular padded views through the
actual checker, generated Lean FFI and native execution, with non-real alpha/beta
and destination reuse. They cover T versus C on `[i]`, empty output, zero inner
dimension, failure cleanup,
and header dependency rebuilding. Forged native IDs/layouts/flags/modes, unavailable
or suspended loans, wrong shapes, input/output aliases, uninitialized reads and
branch-only initialization are rejected. Numerical CI runs the actual generated
consumer on both supported operating systems; it remains separate from no-BLAS
compiler/storage jobs. Runtime counters exclude backend workspace and Lean overhead.

### Public coverage and remaining work

[PR #298](https://github.com/MGYamada/Vastitas/pull/298) connected public numerical
syntax to this checked native path.
[PR #309](https://github.com/MGYamada/Vastitas/pull/309) strengthened direct-wire
rejection regressions, including unused bodies and the raw resource-GEMM bypass.
The public checker rejects forged IDs/flags/receipts, wrong nominal objects or
bases, and stale or suspended map loans before native generation.

The implemented public scope also includes dependent numerical inputs with static
dimension contracts, initialized `OwnedMap` inputs/results preserving allocation
and layout, and explicit real/complex alpha/beta or coefficients read from
initialized scalar loans. See [the numerical contracts](#numerical-values).
[Owned-map packages](#owned-map-packages) additionally transfer one hidden
primal target and its basis, with consuming fresh unpack and no runtime copy.
[Typed transforms](transforms-and-metrics.md#linear-transforms) supply explicit dual/conjugate origins,
corresponding bases and declared orthonormal metric evidence for direct adjoints;
raw component flags do not supply that authority.
[Vector evaluation](transforms-and-metrics.md#vector-evaluation) supplies bilinear dual evaluation and
explicit orthonormal Hermitian pairing through actual vector loans and scalar
destinations. The [two-map network profile](networks-and-packing.md#finite-networks) checks finite
occurrences, ports, the bilinear edge and ordered boundaries before invoking
the same product/resource path.

`tests/numerical_source.rs` covers public source/wire checking and optional
generated execution for real/complex products, coefficients, nested inputs,
owned results, typed transforms, vector evaluation and two-map networks,
including their composition across both branch arms. `tests/resource_source.rs` checks that a
raw resource GEMM with otherwise valid statement metadata is rejected by the
public action decoder. Both OS numerical CI jobs explicitly run the
OpenBLAS-dependent tests; normal compiler checks remain BLAS-free.

General generative numerical result packages, scalar expressions and dynamic
shape interfaces, dense metric realization/transport, general-rank/cyclic networks
and broader retained-evidence handling remain work. Bounded multi-edge
[contraction trees](networks-and-packing.md#contraction-trees), explicit regrouping and versioned
[packing caches](networks-and-packing.md#cached-packing) are implemented separately.
Equivalent-C runtime, allocation/copy and peak-memory
comparisons are still required. The [optional public GEMM experiment](https://github.com/MGYamada/Vastitas/blob/main/experiments/public_gemm/README.md)
has passed generated execution and paired output/arena-cost smoke checks; its
shared-host timings retain their measured scope. The finite GEMM delivery is recorded in the [Stage 1 ledger](../stage1-completion.md); final **Fast like C** acceptance continues under [#222](https://github.com/MGYamada/Vastitas/issues/222).


[Explicit diagonal metrics](transforms-and-metrics.md#diagonal-metrics) add a no-BLAS adjoint pass to the
optional storage runtime and a scratch-weighting/GEMM compound operation to this
adapter. All backend/layout/alias/coefficient/counter checks precede either
scratch or scalar-output writes. Coefficient tables are immutable borrowed Lean
metadata for the complete synchronous call; their bytes and object overhead are
separate from arena data counters. No dense Gram or inverse allocation is made.
