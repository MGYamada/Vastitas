# Numerical backend

This chapter describes how the compiler checks and executes the numerical
statements of [Numerical maps](../linalg/maps-and-gemm.md): the declaration
profiles, the wire forms, the certificates of the kernel, the native GEMM
adapter, and the evidence for each. The rules of the language are in the
Reference chapter. [Resource checking](resource-checking.md) describes the
checker of resource functions that these statements extend.

## Declaration profiles

**Implemented boundary:** package source can declare and independently check
ideal real/complex coefficient kinds, nominal geometric scalar bases and finite
linear representation profiles. These use the existing indexed declaration
namespace and the complete authority/Fn/dispatch checker. Declaration acceptance
alone does not authorize numerical operations; the separate
[numerical-value path](#numerical-values-and-typed-gemm) checks local spaces, bases, actual
map loans and typed GEMM in public resource functions.

The [mathematics-first charter](../adr/0001-mathematics-first-stdlib.md) distinguishes
an ideal mathematical coefficient domain from its numerical realization. The
existing resource scalars `F64` and `ComplexF64` describe binary64 storage; neither
is an exact `Field` or a `C∞`-ring. `ComplexF64` is still a closed representation,
not a general public `Complex<T>` type constructor. No further scalar dispatch key,
pure floating arithmetic or recursive `Fn` scalar type is introduced here.

### Wire and checker boundary

Rust selects protocol 8 when any package contains a numerical representation,
even without resource functions. Existing `"affine_descriptor"` JSON is unchanged.
The two representations are single-key objects:

```json
{"scalar_base": {"setting": "smooth", "coefficient": "real"}}
{"linear_descriptor": {"base": {"path": ["SmoothBase"], "span": {"start": 0, "end": 0, "line": 1, "column": 1}}, "coefficient": "complex"}}
```

Unknown fields, multiple representation keys, machine scalar names in the ideal
coefficient field, and old wire versions are rejected. Lean resolves base paths
through the same namespace resolver and records their provenance. The actual
`Indexed.Source.checkDeclarations` certificate checks all of these contracts;
`ResourceSource` still checks every ordinary and resource body. The exact returned
Core independently audits its complete declaration environment again before
generation. No frontend-selected checked IDs or profile certificates are accepted.

The example under `examples/packages/numerical-declarations` checks these
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

The [numerical-value compiler](#numerical-values-and-typed-gemm) constructs
local nominal spaces/bases and loan-backed maps, checks their bilinear GEMM
composition and emits the exact independently rechecked storage schedule.
The public decoder and source grammar expose these operations inside resource
functions, with independently resolved profile paths and exact receipt provenance.

Dependent map interfaces, explicit dual/conjugate/metric evidence and finite networks are part of the [delivered profile](../stage1-completion.md). The declaration metadata alone grants no authority to execute a numerical operation.

## Numerical values and typed GEMM

`StorageNumerical` connects the common indexed declaration environment to the
actual resource-function compiler and its GEMM schedule. Public protocol 8
exposes local space/basis/map constructors and bilinear GEMM inside resource
functions. Rust sends unresolved profile paths and local names; Lean independently
resolves them in the same namespace as the complete authority/Fn/dispatch checker.
No checked declaration ID, allocation ID or numerical certificate is accepted.
The [adapter responsibility map](#responsibilities-along-the-implemented-path)
distinguishes this public entry, actual Lean checks, checked native lowering and
physical OpenBLAS execution.

The inputs of the worked example are initialized by their individual stores, with no preliminary
zero-fill. The actual bounded initialization checker combines those write
regions before admitting a read or GEMM input. In the shared generated real and
complex GEMM fixture, removing the four redundant fills reduces recorded written
bytes from 768 to 480, preserving six allocations, zero copied bytes and 256 peak
live data bytes. These are operation counters, not elapsed-time measurements or
evidence of C parity; see [initialization coverage](../storage/checked-storage.md#storage-ir--layout-and-initialization).

### Source and wire compatibility

These forms extend the static body of a package `resource fn`; their prefixes
are parsed in that context. Existing pure functions and resource statements
retain their syntax. Dimensions are unsigned static literals, map endpoints are
explicit local bases, and both the GEMM mode and `NativeFast` policy are required.
Dependent input contracts and initialized owned results are described below.
General generative numerical result packages and implicit product syntax remain separate
work. [Typed dual/conjugate/adjoint operations](../linalg/transforms-and-metrics.md#dual-and-conjugate-spaces) add explicit
derived-space, basis, involution and metric contracts.
[Vector evaluation](../linalg/transforms-and-metrics.md#pairings) additionally uses single-basis
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
changes must use another protocol version rather than reinterpret these forms;
additional optional operations must continue to fail closed on older kernels.

### Coefficients

For a `coefficient(loan)` operand the compiler retains its allocation and byte
offset; it does not read or predict the payload. The native adapter reads its
current value synchronously before output writes. The source regression
exercises a coefficient that a previous GEMM produces and one that a later
checked update changes, across actual resource-function calls for real and
complex scalars. No scalar-buffer allocation, packing or tensor copy is
inserted for a coefficient read. The degenerate cases of an empty output and of
a zero inner dimension are an explicit numerical execution convention, not an
exact-field theorem.

Optional wire fields `alpha` and `beta` contain either
`{kind: "literal", value: <resource literal>}` or
`{kind: "loan", loan: <local name>}`. Omitted fields retain previous behavior;
explicit null and unknown fields are rejected by the kernel. Older kernels
reject these additional fields. Scope resolution and actual read/init/alias
checks remain mandatory; no frontend certificate can substitute for them.

`CheckedCoefficient` records the actual scalar/read/init/separation check;
`CheckedProduct.coefficients` retains the requested operands and the exact
emitted GEMM carries them through the independent native-plan audit. The Oracle
proves the coefficient loan contract, initialized bytes, absence of a beta read
in overwrite, and coefficient emission. General scalar expressions, pure-Core
floating values remain separate work; whole-map integral extents use the
separate [runtime-shape interface](../storage/resource-programs.md#runtime-extents).

### Dependent inputs

`ReadMap`, `WriteMap` and `ReadWriteMap` create call-scoped child loans of the
actual views. They retain the caller's physical offset, padding, transpose,
allocation and endpoints. All input snapshots are checked against the original
caller state before reborrowing; the actual resource transitions then check
each child against existing siblings.

The wire parameter tags are `space` (`name`, unresolved `implementation`,
`dimension`, `span`), `basis` (`name`, `space`, `span`) and `map` (`name`,
`source`, `target`, `access`, `initializes`, `span`). Rust and Lean reject
unknown fields. Header profile references undergo the same lexical resolution
and provenance audit as body constructors, including unused definitions.
Older protocol-8 kernels reject these parameter tags; there is no fallback.
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

### Owned results

Raw owned results keep their existing `type: {scalar,elements,initialized}` wire
form. A numerical result uses `type: {kind:"owned_map",source,target}`; the
parameter tag is also `owned_map`. The operation tags are `owned_map`,
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
the [owned-result contract](../linalg/maps-and-gemm.md#owned-maps). [Owned-map packages](#owned-map-packages)
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
[Explicit typed transforms](../linalg/transforms-and-metrics.md#dual-and-conjugate-spaces) can supply dual or conjugate
maps, or adjoints for declared orthonormal metrics. Their checked views retain
the resulting endpoints, bases and flags through GEMM. General metric realization
remains separate work. The [two-map network profile](../linalg/networks-and-packing.md#two-map-networks) adds
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

The [typed transform compiler](../linalg/transforms-and-metrics.md#dual-and-conjugate-spaces) retains dual/conjugate
origins, corresponding bases and declared metric evidence through actual
read reborrows and nested calls. [Vector evaluation](../linalg/transforms-and-metrics.md#pairings)
connects bilinear dual and explicit orthonormal Hermitian pairing to scalar
destinations through the same checked GEMM. [Finite two-map networks](../linalg/networks-and-packing.md#two-map-networks)
add checked occurrences and ports, an explicit bilinear edge and ordered boundaries.
[Explicit diagonal metrics](../linalg/transforms-and-metrics.md#adjoints-for-diagonal-metrics) add materialized adjoints and
weighted pairing with caller-owned scratch and exact declared Int coefficients.
Dense metric realization, general generative numerical result packages, broader runtime
shape/scalar interfaces, general-rank/cyclic networks and controlled-host C
performance acceptance remain with the broader trackers. See the [performance handoff](../stage1-completion.md#stage-2-or-later-performance-acceptance).

[Owned-map packages](#owned-map-packages) add the bounded
`OwnedMapTo<source_basis,target_dimension>` profile: one hidden primal target and
direct basis, initialized affine storage, fresh consuming unpack and explicit
repack. The source basis remains an actual caller dependency. Pack/open/transfer
preserve the exact allocation/layout and emit no additional native instructions.
Dynamic package-result dimensions, general resource packages/closures, borrowed results and
full source/native refinement remain pending.

[Bounded contraction trees](../linalg/networks-and-packing.md#contraction-trees) extend the two-map network
path with explicit finite multi-edge plans and rank-two/three intermediates.
Caller-owned regrouping and versioned producer rebinds preserve axes, resource
provenance and cache invalidation. [Packing caches](../linalg/networks-and-packing.md#caches) separately
permit checked reuse of unchanged packed scratch. These finite paths do not add
general dynamic tensor-valued interfaces or complete native refinement.

## Owned-map packages

The restrictions on an owned-map package are checked in the actual resource
compiler, including direct internal function input; frontend binding kinds do
not supply authority. An opaque value's binding name must equal its owner.
Opening a package inserts no conversion, conjugation, metric, coordinate copy
or equality evidence. Both branches and every unused resource body are
checked; synthetic argument probes never supply executable payloads. Runtime
dimensions, arbitrary existential resource tuples, borrowed results, general
result joins between branches and escaping borrowed lifetimes are outside
this bounded profile.

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

## Native GEMM adapter

Public protocol 8 can execute real and complex GEMM from `.vast` package
`resource fn` bodies. The [public numerical path](#numerical-values-and-typed-gemm) connects
unresolved source names to independently checked nominal spaces, bases and live
map views, then to the checked resource/native schedule and OpenBLAS execution.
`lean-kernel/numerical` is its optional **internal C backend and Lean FFI package**;
the internal API is distinct from the already implemented public source entry.

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
[the numerical source guide](../linalg/maps-and-gemm.md#building-a-numerical-program).
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
costs; the once change alone is not timing or C-parity evidence.
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
[public typed caller](../linalg/transforms-and-metrics.md#dual-and-conjugate-spaces) independently checks derived
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
[storage performance gate](../storage-ownership.md#performance-evidence-and-acceptance).

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

## Transforms, vectors and metrics

This section describes the checking and execution of the statements of
[Transforms, evaluation and metrics](../linalg/transforms-and-metrics.md).

The checker proves the exact declared-data conditions and their connection to
the accepted operation. These conditions are not a theorem about an arbitrary
native matrix or a completed formal model of all Hermitian-module laws.

The operation record retains its original map, exact derived bases or metric
references, conjugation and complete child-loan snapshot. Function argument
reborrowing preserves this interpretation, including conjugation, and actual
calls check the caller's layout, initialization and aliases. A later raw
transpose/release cannot make a stale interpretation valid. The output of GEMM
must be an ordinary writable coordinate view, not a lazy conjugated destination.

Metadata, transforms and reborrows add no native allocation or copy. Only the
checked physical layouts and explicit flags reach the pinned GEMM adapter.
OpenBLAS may use internal packing/workspace; those costs and full-operation
equivalent-C timings remain part of the [Fast like C gate](../storage-ownership.md#performance-evidence-and-acceptance).

### Wire and proof boundary of transforms

Protocol 8 adds `dual_space`, `conjugate_space`, `derived_basis`, `involution`,
`metric` and `transform` numerical operations. The last has an unresolved parent
name and a strict nested operation (`dual`, `conjugate`, or `adjoint`), naming
bases, an involution or metrics. Gram entries are exact decimal strings in a
strict `identity`, `scaled_identity`, or `diagonal` object. The dependent
parameter forms use the corresponding tags; metric headers explicitly record
the orthonormal requirement. These are source names and declared data, never
trusted IDs, raw native flags, prechecked tags or tolerance certificates. Unknown
nested fields and old protocol envelopes are rejected. Older protocol-8 kernels
reject these operations; use a matching frontend/kernel revision.

`StorageNumerical.checkTransform` checks the original live map, exact metric
contract, actual resource borrow, full value provenance and returned live view.
`StorageFunctions` replays the borrow and records its exact emitted schedule.
The public checker audits transform receipt origins against the declaration
environment of the same full authority/Fn/dispatch source check.

The oracle's `actual_transform`, `transform_storage`, `dual_flags`,
`conjugate_flags`, `adjoint_flags`, `adjoint_forms`, `declared_metric` and extended
`input_map_reborrow` refer to these actual certificates.
`public_numerical_transform_origin` connects them to the accepted public request.
These prove structural types, explicit form selection, resource provenance and
the exact lowering connection, not general source/native refinement, float field
laws or all mathematical adjoint identities.

### Example and regression evidence of transforms

```sh
cargo run --locked -- check --manifest-path examples/packages/linear-transforms/Vastitas.toml
cargo run --locked -- build --manifest-path examples/packages/linear-transforms/Vastitas.toml \
  --openblas-prefix /path/to/openblas-0.3.34 -o /tmp/linear-transforms
/tmp/linear-transforms
```

On Linux, add the explicit `--native-cc cc` numerical consumer option as in
[the adapter guide](#native-gemm-adapter). The example uses three original
buffers, padded layouts, two levels of function calls and one reused destination.
It checks every one-dimensional output, then prints `42`.

`TransformRegression` checks rectangular real/complex transformed composition,
origin and metric mutations, actual allocation retention, parent suspension,
nested loan returns and forged native flags. Public source/wire tests cover
wrong nominal objects and bases, missing/degenerate forms, non-orthonormal bases,
incompatible involutions, weak or forged contracts, unused invalid helpers,
old envelopes and output-file preservation. Optional numerical CI executes
real/complex rectangular examples through actual source check/build and native
GEMM. A metadata-only entry with unused valid numerical helpers builds and runs
without OpenBLAS.

[Vector evaluation](#vector-evaluation) executes bilinear dual evaluation
and explicitly conjugated Hermitian pairing for declared orthonormal forms.
[Explicit diagonal metrics](#diagonal-metrics) additionally support materialized
adjoints and scratch-backed Hermitian pairing, with actual declared coefficient
realization and conditional ideal laws. Dense metric realization/transport remains work, as do
general generative numerical packages, dynamic scalar/shape interfaces, general
networks and equivalent-C performance acceptance. Bounded [contraction trees](../linalg/networks-and-packing.md#contraction-trees)
and [packing caches](../linalg/networks-and-packing.md#caches) have their own implemented contracts. This increment does not close Stage 1.

### Vector evaluation

Each evaluation checks the original live vectors, borrows a transposed read
child for the left coordinates and an unchanged read child for the right,
checks/emits GEMM, then releases the children inside out. The certificate
rechecks the whole schedule, restored input snapshots and initialized scalar
output. Shared readable inputs are allowed; output and coefficient aliases
still need the actual byte-region checks.

Evaluation/conjugation introduce no data allocation, copy or packing buffer.
The example reuses one output allocation. Its scalar results use the adapter's
[fused scalar loop](#numerical-adapter--scalar-outputs) rather
than BLAS. Full runtime remains part of the [Fast like C gate](../storage-ownership.md#performance-evidence-and-acceptance).

Rust and Lean share strict unresolved protocol-8 forms: `vector`,
`conjugate_vector`, and `evaluate` with a nested `dual` or `hermitian` operation.
Headers use `kind: "vector"`, a basis name, access and initialization requirement.
Native flags, allocation IDs, checked tags and origin certificates are not
source authority. Old versions reject these payloads; older protocol-8 kernels
reject these operations. Use a matching frontend/kernel revision.

`StorageEvaluation.checkVectorConjugate` validates actual origins, basis,
involution and borrow. `checkEvaluation` connects the exact dual or explicit
Hermitian contract to original live inputs, real child loans, `checkGemm`,
replayed schedule, restored snapshots and initialized output. The function
compiler independently replays that schedule and records exact emitted code.
The public checker audits every receipt against the same full
authority/Fn/dispatch check's accepted declaration environment.

The oracle's `vector_space`, `vector_input_reborrow`,
`actual_vector_conjugation`, `actual_evaluation`, `dual_evaluation_types`,
`hermitian_evaluation_form`, `evaluation_preserves_interpretation` and
`evaluation_returns_inputs_and_scalar` extract those actual-checker facts.
`public_vector_conjugation_origin` and `public_evaluation_origin` connect them
to the public request. These are structural/resource/lowering proofs, not
general ideal-module laws or native numerical refinement.

`EvaluationRegression` covers real/complex dimensions 0/1/3, ordinary and
physically transposed columns, provenance/flag mutations, initialization,
aliases, suspended parents, both branch states and native-plan audits. Public
tests cover nested repeated read inputs, malformed wire, old versions, invalid
unused helpers, artifact preservation and metadata-only execution without
OpenBLAS. Numerical CI executes all shape/orientation cases, mixed complex
components and explicit accumulation.

```sh
cargo run --locked -- check --manifest-path examples/packages/vector-evaluation/Vastitas.toml
cargo run --locked -- build --manifest-path examples/packages/vector-evaluation/Vastitas.toml \
  --openblas-prefix /path/to/openblas-0.3.34 -o /tmp/vector-evaluation
/tmp/vector-evaluation
```

On Linux add `--native-cc cc`, as in [the adapter guide](#native-gemm-adapter).
The program checks both distinct complex results and prints `42`. Empty
evaluation uses the adapter's documented zero-inner convention; it supplies
no separate exact-field theorem.

[Explicit diagonal metrics](#diagonal-metrics) extend Hermitian evaluation to
non-orthonormal declared diagonal forms through caller scratch and a compound
preflight, with conditional ideal pairing/adjoint laws. Dense forms and basis
transport remain outside that increment.

[Bounded contraction trees](../linalg/networks-and-packing.md#contraction-trees) validate rank-two/three
occurrences, ports, edges and boundaries with explicit schedules and regrouping;
[packing caches](../linalg/networks-and-packing.md#caches) check retained scratch dependencies.
General-rank networks, broader generative numerical packages, dynamic interfaces
and equivalent-C acceptance remain open Stage 1 work.

### Cell statements of vectors

A `fill`, `store`, `expect` or `copy` that
[names a vector](../linalg/transforms-and-metrics.md#vectors) reaches the
checker as the resource action of
[Resource statements](../storage/resource-programs.md#resource-statements),
with the name of the vector in the `loan`, `source` or `target` field. The wire
has no other form for it. The action decoder rejects a certificate, a flag or
a resolved loan in such an action as an unknown field.

`Storage.Functions.operation` (in `StorageFunctionOperations.lean`) resolves
the operand of these four actions. For a name that is bound to a vector it requires
`VectorView.Live`: the loan
snapshot of the vector is the live loan, with the same layout and without a
live child. A read also requires a vector without the conjugation flag. The
operand of the primitive action is then the loan of the snapshot. That loan
is the loan of the `vector` statement, the child loan that a call lends to a
vector parameter, or the `read` child of a conjugate vector. `checkAction`
decides access, bounds and element type on that loan. It records a write in
the initialization, the version and the dependency stamps of the allocation,
as it does for a statement that names the loan. Every other binding keeps its
identity, so a map, a tensor or a basis in these statements stays an error.

The schedule holds the `fill`, `store`, `expect` or `copy` of the loan. Native
lowering and the storage runtime see no vector, and the statements add no
allocation, borrow, copy or conjugation flag. An executable that uses vectors
only in these statements builds without OpenBLAS.

The oracle states nothing about the resolution of the operand. Its theorems
about checked plans and call receipts apply to the emitted actions.

`EvaluationRegression` compares the schedule and the final resource state of
a body that names vectors with those of the same body that names their loans.
It does so for real and complex vectors of dimensions 0, 1 and 3, in ordinary
and transposed columns. It also covers the promise of `initializes` through a
vector parameter, both arms of a branch, read and conjugate vectors,
suspended, transposed and released loans, the statements that reject a
vector, and a forged schedule that writes through the suspended loan of the
caller. `tests/numerical_source.rs` checks, builds and runs
[`examples/packages/vector-cells`](https://github.com/MGYamada/Vastitas/tree/main/examples/packages/vector-cells)
for real and complex cells and for padded and transposed layouts of the
caller. A changed write or a changed `expect` stops the executable with
`E_NATIVE_EXPECT`. The tests pin the codes of the Reference rules and reject
wire requests that name a vector where the checker refuses one.
`tests/cached_packing.rs` checks that a write through a vector ends the
validity of a cache.

```sh
cargo run --locked -- check --manifest-path examples/packages/vector-cells/Vastitas.toml
cargo run --locked -- build --manifest-path examples/packages/vector-cells/Vastitas.toml \
  -o /tmp/vector-cells
/tmp/vector-cells
```

The program prints `42`.

### Diagonal metrics

The scratch argument is a caller-owned allocation without outstanding loans.
It cannot be an opaque `OwnedMapTo` package or a borrowed handle. The checker
reconstructs and accepts this exact sequence:

1. Borrow scratch for writing; read and weight the right vector into it.
2. Return that write loan; create a fresh initialized read loan of scratch.
3. Create a read child of the left vector with the required row orientation.
4. Execute the existing overwrite GEMM into the scalar output.
5. Return both children, restoring caller loans and allocation owners.

The public compiler also replays the sequence independently and records its
equality with the single compound resource action. There is no access upgrade
or invented source read loan. Scratch and output are marked written once each,
invalidating cached dependencies on either allocation. Adjoint writes invalidate
dependencies on its destination. Both branch arms, unused bodies, original
caller arguments and the final schedule are independently checked.

### Native costs and failure boundary of diagonal metrics

`adjoint_into` executes one O(mn) pass and writes mn scalar-width bytes.
`hermitian_diagonal` executes one O(n) weighting pass and one existing GEMM,
writing (n+1) scalar-width bytes, or just the zero scalar when n=0. The adapter
runs that 1×1 GEMM as its [fused scalar loop](#numerical-adapter--scalar-outputs)
over the scratch vector, without a BLAS driver call. Both reuse
caller storage and add no data allocation or data copy. They perform explicit
`NativeFast` multiplication/division, with normal floating rounding, overflow
and nonfinite propagation; exact metric coefficients do not imply exact results.

Every returned preflight error preserves destination data, scratch, write
counters and the GEMM report. The compound pairing validates the backend,
all actual layouts/scalars, source/output and scratch separation, all diagonal
entries, bounds and total write-counter overflow before its first write. After
preflight it performs no fallible adapter operation between weighting and GEMM.
This is a synchronous native implementation contract, not a theorem about
backend crashes or arbitrary foreign pointers.

Generated coefficient payloads are immutable Lean `ByteArray` constants borrowed
for the duration of each FFI call. FFI retains no coefficient pointer afterward.
Their payload is 8(n+m) bytes for two explicit adjoint diagonals and 8n bytes for
pairing; identity/scaled identity uses eight bytes per form, plus Lean object
and container overhead. A static hex string holds twice the payload bytes; a
reserved linear decoder constructs each table once, with a temporary UTF-8 copy
of that hex text. Generated C does not retain every array-literal prefix. These
are metadata, not arena data allocations, and are
not counted by arena data counters. Foreign C callers must provide readable
immutable tables of the declared byte length for the complete synchronous call;
concurrent mutation or forged pointer extents are outside the trusted ABI.
The pinned Lean-generated C fixture initializes the two distinct closed tables
once on first use and reuses them across repeated operations; the checked-native
test audits this placement. Initial construction and retained metadata still
cost memory/time, and this inspection is not a general native-refinement proof.

Standalone adjoint uses only the optional storage native runtime, without
OpenBLAS. Pairing links the pinned sequential LP64 OpenBLAS 0.3.34 adapter.
The [prepared adapter/C experiment](https://github.com/MGYamada/Vastitas/blob/main/experiments/diagonal_metrics/README.md)
reports actual costs and performance gaps. It excludes public-source/FFI and
lifecycle costs and does not close the [Fast like C gate](../storage-ownership.md#performance-evidence-and-acceptance).

### Checking, proofs and examples of diagonal metrics

Rust and Lean strictly decode `adjoint_into` and `hermitian_diagonal` numerical
operations in protocol 8. Operands are unresolved names and explicit scratch
layout, never supplied Gram bytes, allocation identities or acceptance receipts.
Protocols 2–7 and unknown fields reject these payloads. `StorageMetric` obtains
metrics from the actual accepted value environment, retains exact realization,
resource transition and replay evidence; `StorageFunctions` retains the precise
emitted action, and `ResourceSource` audits every executable receipt's original
declaration environment. `StorageCodegen` reconstructs and checks the native
instruction against the original schedule before generating code.

`VastitasOracle.StorageMetric` extracts those actual-checker guarantees.
`StorageMetricLaws` interprets the exact certificate metric fields over a lawful
characteristic-zero commutative field with an explicit additive/multiplicative
involution. Nonzero coordinate weights follow from the actual selected metric
validity, not an extra arbitrary nondegeneracy assumption. It proves pairing
linearity/semilinearity and Hermitian symmetry, adjoint additivity/star scaling,
the defining adjoint pairing equation and finite composition contravariance.
Composition requires equality of the full intermediate `Metric`; equal shape
does not suffice. These laws concern ideal coordinate formulas. They do not
prove that an unrelated composite buffer holds a matrix product, source/native
refinement, numerical error bounds, or floating-point field identities.

```sh
cargo run --locked -- check --manifest-path examples/packages/diagonal-metrics/Vastitas.toml
cargo run --locked -- build --manifest-path examples/packages/diagonal-metrics/Vastitas.toml \
  --openblas-prefix /path/to/openblas-0.3.34 -o /tmp/diagonal-metrics
/tmp/diagonal-metrics
```

The example checks real/complex padded rectangular adjoints and repeated
scratch-backed pairings, then prints `42`. `MetricRegression`, source/wire tests,
standalone native sanitizers and exact checked-schedule execution cover stale
dependencies, incorrect metric/basis/loan provenance, malformed coefficients,
zero dimensions, aliasing, forged native flags, resource restoration and costs.
Dense Gram adoption, basis transport, solves, arbitrary runtime coefficients,
dynamic interfaces, AD and complete native refinement remain outside this
increment.

## Networks, packing and contraction trees

This section describes the checking and execution of the statements of
[Networks, packing and contraction trees](../linalg/networks-and-packing.md).

### Two-map networks: graph and independent acceptance

Rust serializes an unresolved resource statement with `kind: "network"`, `graph`,
`output`, `policy: "native_fast"` and `span`. The graph has:

| Field | Entries |
| --- | --- |
| `occurrences` | Two `{name, value}` objects; `value` is a local map name |
| `edges` | One `{dual, primal}` edge |
| `inputs` | One explicit input boundary port |
| `outputs` | One explicit output boundary port |

Each port is `{occurrence, role}`, where `role` is `input` or `output`. Types,
allocations, inferred conversions, certificates and schedules are not accepted
from the frontend. The decoder bounds these lists before traversing them and
rejects unknown fields at every level. Older protocols reject network statements;
older protocol-8 kernels fail closed on the unknown tag.

`ResourceSource.lowerStatements` independently resolves map names in the actual
function scope. `Storage.Functions.networkOperation` resolves the current call's
activation and passes the actual numerical environment, values and resource state
to `TensorNetwork.check`. It validates occurrence identity, exact port coverage,
edge variance, nominal edge type and ordered boundaries. It then calls the
existing `Storage.Numerical.checkProduct` for the actual three maps. Storage and
GEMM checking are shared with direct products, including stale views, initialization,
output aliases and exact scalar/layout checks. All-body probes remain separate from executable expansion. Both branch arms
are checked, and each arm's receipts are retained exactly once together with
receipts before and after the branch, including nested branches. A branch receipt
records its local schedule segment; it does not claim that both arms execute.

The sole edge determines the left and right operands. Declaration order does not
select a different schedule. Lowering emits exactly one overwrite GEMM with
default alpha one, beta zero and explicit `NativeFast`. There is no order search,
packing, intermediate allocation or copy inserted by the graph layer.
`NetworkReceipt` retains the exact accepted graph, pre-state, mathematical product,
emitted operation and actual accepted storage transition. The public checker audits
that every executable network receipt uses its same accepted declaration environment.

### Two-map networks: proof and validation boundaries

`VastitasOracle.TensorNetwork` imports the actual implementation and proves:

| Theorem | Guarantee |
| --- | --- |
| `ports_used_once` | Every declared occurrence port has exactly one use |
| `admitted_bilinear_edge` | Both edge ends have the same exact basis with dual/vector roles |
| `edge_product_basis` | The graph edge basis equals the actual GEMM inner basis |
| `output_boundary` | Ordered boundaries and destination bases agree |
| `no_implicit_conjugation` | Lowering preserves only the checked operand conjugation flags |
| `same_input_plan` | The same accepted input produces the same GEMM request |
| `actual_lowering` | Actual graph acceptance, emitted GEMM and storage acceptance agree |
| `public_network_origin` | Public acceptance ties the receipt to the exact declaration environment |

These are graph acceptance, nominal typing and exact lowering facts. They do not
prove floating-point arithmetic, a general tensor-category denotation theorem,
full source operational equivalence or native heap/toolchain refinement. They
reuse the existing product/storage proofs rather than reimplementing those models.

`NetworkRegression` checks actual internal expansion and mutated graphs/values/native
instructions. `tests/numerical_source.rs` checks public source, strict raw-wire
rejection, unused bodies, branches, declaration-order independence, alias rejection
and immutable reuse. Its optional native test executes real/complex rectangular
products, `(2+3i)^2 = -5+12i` through two occurrences of one map, and nested dependent
calls. Both numerical CI jobs run the optional source tests. The direct pair emits
six data allocations and two GEMMs, without copies; the reuse pair emits four data
allocations and two GEMMs. These are structural costs, not C-parity measurements.

### Tensor packing: independent checking and native execution

The strict protocol-8 `tensor` statement carries an unresolved operation:

- `view`: `name`, `loan`, ordered `axes`, and `grouping` with `order` and `split`.
- `pack`: `source` and `target` tensor names.
- `contract3`: `left`, `right`, `output`, and `native_fast` policy.

The decoder bounds axes and permutations before traversing them and rejects
unknown fields. It accepts no allocation IDs, resolved bases, flags, proof
objects or fabricated schedules. Older envelopes reject these statements.
`TensorNumerical` reconstructs the actual values in the same declaration
environment used by the full authority checker. `StorageFunctions` retains
constructor, packing and contraction receipts with exact accepted states and
emitted code. Both branch arms retain all receipts exactly once; local tensor
bindings are restored at branch and call exits, separately from all-body probes.

Raw `Storage.Action.pack3` records source/destination loans and the three extents.
It checks the two precise rectangles, initialized input and byte separation,
and initializes only the destination rectangle. `StorageCodegen` reconstructs
allocation IDs and both layouts from that original schedule; modified packing
dimensions, layouts or instructions fail regeneration.

The native C operation preflights all descriptors, products, representations,
aliases and accounting limits before writing. It uses bounded stack metadata
and nested loops that copy contiguous first-axis blocks. No data or scratch
allocation occurs inside packing. Nonempty overlapping envelopes are rejected,
even for identical mappings; disjoint regions of one allocation are allowed.
Empty cases still validate all metadata and form no element pointers. Source
bytes and destination padding are preserved. The optional storage runtime
remains independent of BLAS; contraction selects the existing numerical runtime.

### Tensor packing: proof and cost boundaries

`VastitasOracle.TensorNumerical` imports the actual checker and proves mixed-radix
index injectivity, the accepted packing coordinates and their actual rectangular
bounds, initialized destination bytes, actual nominal axes/dual origins, actual
GEMM loans, inner extent and coordinate grouping, exact emitted transitions and public declaration origins.
Its finite coordinate-reference theorem uses the same summation order and
requires no field laws. These are not C/FFI memory refinement, floating-point
arithmetic, general tensor-category laws or source/native operational equivalence.

For extents `u,v,w,x` and scalar width `s`, the explicit pack reads and writes
`u*v*w*s` bytes. It increments the existing copied and written counters by that
amount. The caller's scratch capacity, including any padding, remains live until
explicit release/drop. GEMM writes `u*w*x*s` output bytes. There is one packing
operation and one GEMM per contraction in the example; grouping metadata adds
no data allocation. The two example calls contain eight explicit data allocations,
two packs and two GEMMs. These are structural costs, not C-parity measurements.
Arena counters do not cover Lean allocation, allocator overhead, process RSS or
OpenBLAS internal workspace. Compare the complete generated path and a competent
C implementation using the same packing and pinned sequential BLAS, including
full lifecycle and reused scratch/destination scopes. Packing time/bytes, peak
live memory, raw paired samples and uncertainty remain required before any
performance claim; see [the performance gate](../storage-ownership.md#performance-evidence-and-acceptance).

The optional [tensor packing experiment](https://github.com/MGYamada/Vastitas/blob/main/experiments/tensor_packing/README.md)
checks the canonical public executable, instruments its actual emitted resource
instructions, and compares them with a matched explicit C pack plus direct CBLAS.
It includes lifecycle, reused-buffer, packing-adapter and BLAS diagnostic scopes,
exact arena counters, every-coordinate and padding checks, and raw paired samples.
Instrumented reuse hoists setup/cleanup around repeated emitted pack/GEMM calls;
it does not add source-level dynamic iteration. Local validation or exploratory
timing alone does not close the controlled-host performance gate.

Regression coverage includes public real/complex coordinate expectations, padding,
each zero extent, nested dependent calls, both branch directions, forged raw and
native metadata, wrong bases/dual origins, stale loans and explicit permission
transitions. Source checking and unused-body auditing need no OpenBLAS; numerical
CI executes the optional public tensor tests on both operating systems.

The optional [checked packing cache](../linalg/networks-and-packing.md#caches) binds an actual packing
to source/scratch versions and rejects stale use in `contract3_cached`. Ordinary
`pack3` and `contract3` continue to permit independently stored snapshots.

### Contraction trees: independent graph and producer checks

Rust serializes unresolved graph names, ports, ordered boundaries and the
explicit plan. Lean independently resolves local bindings, actual bases and
loans against the public declaration environment. The strict additive protocol-8
`tree` statement has `graph`, `output`, `policy`, `plan` and `span` fields.
The graph has `occurrences` (`name`,`value`), `edges` (`name`,`dual`,`primal`)
and `boundary`; a port has `occurrence` and `axis`.
Plan `kind` values are `action`, `view`, `regroup`, `rebind` and `join`.
Only borrow/release actions are admitted. Unknown fields, trusted-proof fields,
allocation IDs and fabricated native flags are rejected.

Local counts and single-use ports are insufficient for connectivity: a
boundary component beside a disconnected cycle can satisfy them. The checker
therefore reconstructs active components and a binary producer tree. Every
join connects disjoint leaf sets through its actual declared edge. At every
step it checks the occurrence partition, remaining port frontier, consumed
edges and exact original port-to-basis mapping. Completion requires one
producer tree containing every occurrence and edge exactly once, the precise
ordered boundary and the caller's exact initialized output view. No component
or cycle can be silently discarded. Declaration order does not choose execution
order; the submitted named plan does.

The checker retains each actual `CheckedRegroup` or `CheckedSingle` result,
its accepted event, before/after resource state and exact action suffix.
Each suffix and the whole tree schedule are independently replayed by the
resource checker, then checked again during ordinary resource expansion and
native code generation. Both branch arms preserve all receipts and public
origin audits.

### Contraction trees: physical regrouping and costs

The existing optimized `pack3` handles `[0 | 1,2]` to `[0,2 | 1]` unchanged.
Other explicit regroupings use `Storage.Action.regroup3` and the native bounded
permutation loop. Its descriptor contains three physical extents and two
encoded grouping permutations. For rank two, a trailing physical extent one
and trailing index zero embed the same rectangle; this adds no logical axis,
space or basis. The oracle proves that embedding preserves the actual rank-two
coordinates.

For logical dimensions `d` and a group `p`, flattening is first-axis-fastest:
`index[p0] + d[p0] * (index[p1] + ...)`. Row and column groups determine the
actual rectangle coordinate. Its byte address is
`offset + scalar_width * (row + leading * column)`.
The native code independently checks both permutations, all dimensions and
products, complete rectangles, scalar agreement, nonempty envelope separation
and accounting overflow before pointers or writes. Raw 8/16-byte cells are
copied without conjugation; source bytes and destination padding are preserved.
When the source's first axis occupies 16–64 bytes, has more than one element
and has unit scalar stride in both prepared views, the native loop copies that
entire axis with one `memcpy` per pair of remaining coordinates. The other
groupings use exact 8/16-byte cell copies. Block widths from 16 through 64 bytes select fixed-size
copies outside the loops, allowing the C compiler to inline them; larger blocks
retain the cell loop. This decision uses actual physical strides after all
preflight checks; equal dimensions or nominal factor identities do not justify
coalescing, aliasing or skipping checks. No block includes padding and no
temporary storage is added. Both paths preserve every payload bit, including
signed zeros and signaling NaNs.
Empty volume still validates all metadata and performs no pointer formation,
copy or counter increment. Overlapping nonempty envelopes, including identity
mapping in place, are rejected. Disjoint regions of one allocation are allowed.

Each explicit regroup reads and writes `product(dimensions)*scalar_width`
bytes and increments copied and written counters by that volume. Each GEMM
writes its actual output rectangle. For the example dimensions `(u,v,w,a,b)`,
packing copies `(u*v*w + u*w*a)*scalar_width` bytes, and GEMMs write
`(u*w*a + u*a*b)*scalar_width` bytes. Both terms for the reused scratch remain
visible; its capacity is the maximum required physical envelope, including
padding. Each scalar profile has six caller allocations, two packs and two
GEMMs. Metadata and proofs erase from generated code. Arena counters exclude
Lean allocation, allocator overhead, RSS and BLAS internal workspace.

The separate [matched C experiment](https://github.com/MGYamada/Vastitas/blob/main/experiments/contraction_trees/README.md)
uses the actual emitted schedule and equivalent explicit C packing and GEMMs.
Measurements and sanitizer runs are evidence about those cases, not a native
refinement proof or a claim of C parity. Controlled-host performance acceptance
remains subject to the [performance gate](../storage-ownership.md#performance-evidence-and-acceptance).
The [short-block adapter comparison](https://github.com/MGYamada/Vastitas/blob/main/experiments/contraction_trees/results/2026-11-01-macos-regroup-blocks/RESULTS.md)
retains both rejected variable-copy experiments and the final clean native
comparison. It motivates the bounded 16–64-byte path without claiming a
whole-program speedup or replacing the existing generated/C measurements.
The [subsequent full Linux public-program record](https://github.com/MGYamada/Vastitas/blob/main/experiments/contraction_trees/results/2026-11-01-linux-regroup-blocks/RESULTS.md)
measures clean main `7486d2c` after this optimization. All twelve public programs
and native/output/cost checks passed. It reports adapter, FFI-inclusive reuse and
lifecycle scopes separately, retains tiny overhead and fallback slow observations,
and does not establish a causal speedup between the two versions or controlled-host acceptance.

### Contraction trees: proofs, tests and remaining scope

`VastitasOracle.TensorContraction` imports actual checked views and proves
mixed-radix coordinate bounds/injectivity, initialized destination bytes,
rank-two physical embedding, actual selected-axis coordinates, exact GEMM
operands/inner extent and a finite coordinate-reference equality preserving
summation and multiplication order. `VastitasOracle.TensorTree` proves actual
single-use ports, corresponding dual origins, the reconstructed connected
producer tree's full node/edge coverage, exact ordered boundary bases,
submitted event order, actual numerical/resource transitions and public
checker origins. `regroup_invalidates_dependencies` connects the actual
destination-write certificate to invalidation of every mentioned cache entry. No field laws, custom axioms, categorical equalities or
floating reassociations are used.

Regression coverage includes more than two edges, rank-two chains, repeated
immutable occurrences, every selected-axis/operand orientation of a rank-three
and rank-two pair, padded real/complex execution, zero extents, scratch reuse,
both branches, 64-node acceptance and 65-node rejection, unrelated cache
survival and generic-regroup cache invalidation, unused bodies, stale/foreign producers, invalid ports,
disconnected cycles, opaque packages and forged wire/native metadata. Native
C tests independently cover all 144 rank-three grouping pairs, raw special
bits, padding, same-allocation separation, invalid codes, overflow and failure
preservation.

General ranks, multiple rank-three nodes, arbitrary intermediate ranks,
trace/copy nodes, metrics and Hermitian contractions, automatic planning,
common-subexpression reuse and tensor-category rewrites remain outside this
profile. The separate cached-pack increment supplies explicit version/dependency
reuse receipts; it does not authorize implicit reuse inside this plan. Full
source/native correspondence, C/FFI/BLAS refinement, floating laws and the
historical Stage 1 performance gate remain open.

### Cached packing: dependency stamps

The checker records two stamps after the actual `pack3`: source and scratch
allocation identities, logical versions, scalar representations and physical
layouts. Both stamps use the post-pack state. In particular, disjoint source and
scratch regions may belong to one allocation, whose version advances during packing.
The nominal cache also records the accepted ordered axis bases and grouping.
No source or wire input supplies allocation identities, versions, proof flags or
a trusted packing relation.

`contract3_cached` requires that both allocations are still live with the recorded
versions. The actual packed operand must retain the recorded scratch allocation,
layout, ordered nominal bases and grouping. Its current loan may have another name
and ancestry after explicit release/reborrow or owner transfer. It must be active,
readable and initialized. The ordinary right operand, output, dual-axis contract,
initialization and alias checks still apply.

### Cached packing: snapshot use and retention

Ordinary `pack3` and `contract3` retain their existing snapshot behavior. Changing
the original source does not change coordinates already copied into scratch.
Ordinary contraction of that old snapshot remains valid; cached contraction
additionally requires its relation to the current original source.

A real read loan already retains a region against overlapping writes, owner moves
and drops for its checked scope. A versioned dependency instead detects that a
previous relation became stale after access ended. It preserves no old bytes and
cannot replace a retention loan. Retain/snapshot/recompute residual strategies,
escaping lifetime contracts and AD execution remain later work; see
[Chapter 7.10](../storage-ownership.md#residual-retention).

### Cached packing: schedule and generation boundary

The internal resource schedule includes three metadata operations:

| Operation | Independent requirement | Effect |
| --- | --- | --- |
| `captureDependency` | Fresh symbol; actual live initialized source/scratch loans | Reconstruct both stamps from the current state |
| `requireDependency` | Named live dependency with matching current stamps | Validate use without granting memory access |
| `forgetDependency` | Matching lexical dependency handle, including an invalidated one | End compiler metadata scope |

The audited dependency table rejects duplicate identities, owner/loan collisions,
invalid live stamps and unclosed lexical handles. Writes/drop leave invalidated
entries for explicit cleanup; they cannot be reactivated by reusing a name. A
raw capture asserts no nominal axes or packing equivalence. Only the public
operation's accepted packing certificate can supply a cached contraction.

The source checker records exact pack/capture and require/GEMM schedules, both-arm
receipts, separate all-body probes and declaration origins. Code generation reruns
the complete source checker and the original primitive schedule, including all
dependency operations, before erasing them. Their native lowering is empty.

Regressions cover stale source/scratch versions, disjoint updates, call effects,
move/reborrow, branch invalidation and cleanup, refreshed packing, real/complex
results, malformed wire inputs and forged native plans. The checked-native fixture
executes one packing and two products with three allocations: real counters are
24 peak data bytes, 32 written bytes and 8 copied bytes; complex counters double
those byte counts. All data is freed. The sole copy is the explicit packing.
These arena counters exclude Lean/allocator overhead and BLAS-private memory.
They establish bounded cost evidence, not equivalent-C performance acceptance.

`VastitasOracle.StorageDependencies` derives an earlier capture and an accepted
entry-preserving action suffix from the exact accepted raw schedule prefix. It
proves freshness, no resurrection after invalidation/forgetting, and write/join
invalidation. Checked-cache and consumer-receipt corollaries take an explicit
accepted intervening replay; a right-arm corollary includes the actual left run
and exact allocator reseed. They do not assume branch-local `priorCode` starts
from an empty state. Automatic replay-prefix extraction from arbitrary nested
source receipts remains a source-correspondence obligation.

`VastitasOracle.StorageCachedPacking` connects actual accepted packing/capture,
current allocation versions, nominal packed operands, emitted schedules, public
declaration origins and empty native metadata lowering to those same checker
receipts. The oracle boundary is logical resource history and structural checking. Native byte copying, BLAS arithmetic, full source/native correspondence
and ideal floating-point field laws remain separate trusted/tested or unproved
boundaries. This increment does not complete general scratch pooling, retained
numerical evidence, dynamic shapes, AD or the wider Stage 1 storage issue.

## History

[PR #298](https://github.com/MGYamada/Vastitas/pull/298) connected public numerical
syntax to this checked native path.
[PR #309](https://github.com/MGYamada/Vastitas/pull/309) strengthened direct-wire
rejection regressions, including unused bodies and the raw resource-GEMM bypass.
The public checker rejects forged IDs/flags/receipts, wrong nominal objects or
bases, and stale or suspended map loans before native generation.

The implemented public scope also includes dependent numerical inputs with static
dimension contracts, initialized `OwnedMap` inputs/results preserving allocation
and layout, and explicit real/complex alpha/beta or coefficients read from
initialized scalar loans. See [the numerical contracts](#numerical-values-and-typed-gemm).
[Owned-map packages](#owned-map-packages) additionally transfer one hidden
primal target and its basis, with consuming fresh unpack and no runtime copy.
[Typed transforms](../linalg/transforms-and-metrics.md#dual-and-conjugate-spaces) supply explicit dual/conjugate origins,
corresponding bases and declared orthonormal metric evidence for direct adjoints;
raw component flags do not supply that authority.
[Vector evaluation](../linalg/transforms-and-metrics.md#pairings) supplies bilinear dual evaluation and
explicit orthonormal Hermitian pairing through actual vector loans and scalar
destinations. Since [issue #708](https://github.com/MGYamada/Vastitas/issues/708),
`fill`, `store`, `expect` and `copy` accept a vector
([Cell statements of vectors](#cell-statements-of-vectors)); before it, a body
could keep the promise of a `WriteVector` parameter with `initializes` only for
dimension 0. The [two-map network profile](../linalg/networks-and-packing.md#two-map-networks) checks finite
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
[contraction trees](../linalg/networks-and-packing.md#contraction-trees), explicit regrouping and versioned
[packing caches](../linalg/networks-and-packing.md#caches) are implemented separately.
Equivalent-C runtime, allocation/copy and peak-memory
comparisons are still required. The [optional public GEMM experiment](https://github.com/MGYamada/Vastitas/blob/main/experiments/public_gemm/README.md)
has passed generated execution and paired output/arena-cost smoke checks; its
shared-host timings retain their measured scope. The finite GEMM delivery is recorded in the [Stage 1 ledger](../stage1-completion.md); final **Fast like C** acceptance continues under [#222](https://github.com/MGYamada/Vastitas/issues/222).

[Explicit diagonal metrics](../linalg/transforms-and-metrics.md#adjoints-for-diagonal-metrics) add a no-BLAS adjoint pass to the
optional storage runtime and a scratch-weighting/GEMM compound operation to this
adapter. All backend/layout/alias/coefficient/counter checks precede either
scratch or scalar-output writes. Coefficient tables are immutable borrowed Lean
metadata for the complete synchronous call; their bytes and object overhead are
separate from arena data counters. No dense Gram or inverse allocation is made.

The complex worked example of `examples/packages/numerical` comes from
[#91](https://github.com/MGYamada/Vastitas/issues/91).

Resource functions construct selected dual and conjugate spaces, corresponding
bases, explicit canonical scalar involutions, declared coordinate Hermitian forms,
and read-only transformed maps. These operations compose with actual dependent
function inputs, nested resource loans and checked GEMM. This is an implementation
of finite coordinate operations, not general tensor evaluation or a proof of
floating-point algebraic laws. [#67](https://github.com/MGYamada/Vastitas/issues/67)
and [#91](https://github.com/MGYamada/Vastitas/issues/91) remain open.

Package-only protocol 8 checks coordinate vectors, explicit vector conjugation,
algebraic dual evaluation and an orthonormal Hermitian pairing. The actual
source checker connects nominal bases and derived-space origins to live storage
loans, the exact GEMM schedule and native execution. This advances
[#67](https://github.com/MGYamada/Vastitas/issues/67) and the finite-network
foundation under [#69](https://github.com/MGYamada/Vastitas/issues/69); neither
issue is completed by this increment.

The diagonal-metric increment left #67, #91, #183 and historical Stage 1 open.

Protocol 8 supports a finite profile of [#69](https://github.com/MGYamada/Vastitas/issues/69):
two rank-two map occurrences, one bilinear evaluation edge, one input boundary,
one output boundary and one caller-provided overwrite destination. It is connected
to the independent Lean checker and the existing typed GEMM/storage/native path.
This finite profile is part of the completed [Stage 1 delivery](../stage1-completion.md). Broader network constructions remain with #69.

This profile has exactly two rank-two maps and one contraction, uses a caller-owned
destination, and fixes overwrite with unit alpha. Network accumulation and scalar
coefficients, arbitrary rank or multiple edges, scalar covector/vector evaluation,
explicit Hermitian pairing nodes, trace/copy/diagonal/hyperedge nodes, general metric
realization, rewrites and contraction-order optimization are not implemented here.
The existing crossing-word `Graph` checker and its categorical obligations remain
separate. The broader #69 checklist stays open.

The delivery includes bounded runtime shapes, explicit scratch and packing dependencies. Stage 2 or later owns equivalent-C runtime and outstanding total-memory measurements. [Integrated evidence](../stage1-completion.md)

The separate [rank-three contraction and packing profile](../linalg/networks-and-packing.md#packing-and-contraction)
supplies one fixed higher-rank coordinate contraction with explicit scratch.
It does not extend this two-map graph schema or implement general graph rewriting.
