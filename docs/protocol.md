# Wire protocols 2–9

This chapter describes the wire protocols between the driver and the kernel:
the JSON request, the response, and the forms that each of the versions 2 to
9 admits. It names the decoder and the checker of each version and says what
a decoder refuses. The rules of the language are in the Vastitas Reference.
[Programs](language/programs.md) gives the two modes of a compilation.
[Packages](packages.md) and [Modules](language/modules.md) give manifests and
names. Each construct has its chapter:
[Generics and dispatch](stage1a.md), [Function values](stage1b.md),
[Edit authority](language/edit-authority.md),
[Indexed declarations](indexed-source.md),
[Presented affine declarations](affine-geometry.md),
[Smooth affine declarations](language/smooth-declarations.md),
[Resource programs](storage/resource-programs.md) and
[Numerical maps](linalg/maps-and-gemm.md).
[The driver](internals/driver.md) describes how the Rust side writes a
request and reads a response, and [Verification boundaries](verification.md)
states what is proved about the result of each checker.

## Requests, decoders and checkers

The Rust frontend sends one JSON object on stdin to `vastitas-kernel check`
or `vastitas-kernel emit`. The Lean backend writes one response on stdout;
tool logs belong on stderr. Neither the frontend's annotations nor names are
trusted. The backend allocates nominal identities while checking lexical
bindings; the wire format cannot supply a trusted object identity.

`lean-kernel/Main.lean` reads the `version` of a request and selects the
decoder and the checker:

| Version | Input | Decoder | Checker |
| --- | --- | --- | --- |
| 2 | Flat | `decodeSurfaceModule` in `SurfaceProtocol.lean` | `Indexed.LegacySource.check` |
| 3 | Package | `decodeNamespaceProgram` in `NamespaceProtocol.lean` | `Indexed.LegacySource.check` |
| 4 | Flat or package, by the field `input` | `decodeSurfaceModule` or `decodeNamespaceProgram` | `Indexed.LegacySource.check` |
| 5, 6 | Package | `decodeNamespaceProgram` | `Indexed.LegacySource.check` |
| 7 | Package | `Indexed.Wire.program` in `IndexedProtocol.lean` | `Indexed.Wire.check` |
| 8, 9 | Package | `ResourceSource.Wire.program` in `ResourceProtocol.lean` | `ResourceSource.Wire.check` |

In the mode `emit`, `Main` passes the Core of the check result of protocols
2 to 7 to `Indexed.Core.Codegen.generate`. For protocols 8 and 9 it calls
`ResourceSource.Wire.emit`, which runs the check and passes its result to
`ResourceSource.Codegen.generateChecked`.
[The three checker routes](development/architecture.md#the-three-checker-routes)
describes the routes.

Request: `{ "version": 2, "file": "input.vast", "functions": [...],
"generics": [...], "methods": [...] }`. All three declaration arrays are
present, including when empty. Protocol 3 uses the separate namespace request
below. Protocol 4 adds abstract declarations, protocol 5 adds package edit assemblies,
protocol 6 adds nested loans and permanent authority transfer, and package-only
protocol 7 adds indexed declarations and rich bodies as described below.
Package-only protocols 8 and 9 add resource functions, named recipients and
the algebraic, smooth, metric, frame and physical-dimension forms.
Package requests never fall back to protocol 2. Other versions are rejected.

## Protocol selection

The driver selects the protocol of a request from the declarations that the
source contains. In flat mode it uses protocol 2, or protocol 4 when the
program declares abstract types, subtypes or abstract methods. In manifest
mode it takes the first match of this list:

1. any grant, delegation or transfer, a presented affine declaration of
   [Presented affine geometry](affine-geometry.md), a smooth or metric
   declaration of [Smooth affine declarations](language/smooth-declarations.md),
   or a [frame](#protocol-9-frame-forms) or
   [physical-dimension](#protocol-9-physical-dimension-forms) declaration:
   protocol 9;
2. resource functions, or an indexed implementation other than an affine
   descriptor: protocol 8;
3. other indexed declarations, an indexed type annotation, a typed `pack`,
   an `unpack` with ordered fields, or a `geometry_compat` export of a loaded
   package: protocol 7;
4. `reborrow` or `transfer` events in an assembly: protocol 6;
5. contributions or an assembly: protocol 5;
6. abstract declarations: protocol 4;
7. none of these: protocol 3.

A root package without an assembly selects an empty edit trace; the kernel
still validates every grant and checks every unapplied contribution.
The kernel accepts a `reborrow` event only with a delegation and a `transfer`
event only with a transfer declaration, and each of these declarations
selects protocol 9 by item 1. A request of protocol 6 that the driver writes
therefore holds an event that the kernel rejects.

## Protocols 8 and 9

Package-only [protocol 8](storage/resource-programs.md#resource-functions) adds unresolved `resource_functions`
to modules while preserving the full protocol-7 declaration/Fn/dispatch/authority
checks. Each resource function carries `name`, `parameters`, ordered owned
`results`, resource `body`, pure `value_type`/`value_body`, `public` and `span`.
Calls carry unresolved paths and local names, not checked IDs. The strict schema
is defined by `storage.rs::source` and `ResourceProtocol.lean`. Emit responses
include `storage_runtime: Bool` and `numerical_runtime: Bool` to request optional
native packages only when the actual entry needs them. `storage_runtime` is
true when the checked entry has an operation on an arena or a runtime-shape
event. A resource entry that computes scalars alone reports false, and its
`lean_source` imports no `VastitasStorageNative` and creates no arena
([Resource checking](internals/resource-checking.md#all-body-checking-and-generation)).
A numerical requirement
also requires storage and explicit driver build configuration. The [internal storage component schema](storage/checked-storage.md#storage-ir)
is not an alternative public envelope; top-level `resources` and downgraded
`resource_functions` must not be silently discarded by legacy protocol 2.

Package-only protocol 9 retains that complete protocol-8 envelope and composition,
and replaces `grantee_source` with `grantee_package: String` in `grants`,
`delegations` and `transfers`. `grantee_path` remains an ordered list of module
components. The string is the original manifest package name, never a resolved
source location, dependency alias or claimed PackageId. Lean reconstructs the
root-reachable selected packages, requires one exact name match before examining
the module path, and retains that record's full source/name/version identity.
No match or several matches is `E_OWNER`, even for unused declarations. A name
collision cannot be resolved by version, module availability or list order.

Source recipient declarations select protocol 9 even without resources;
pure-only emits return both optional-runtime flags as false. Protocols 5–8 retain
`grantee_source` and reject `grantee_package`; protocol 9 rejects `grantee_source`
even alongside `grantee_package`. Earlier versions retain their strict schemas.
[Source migrations](appendix/history.md#source-migrations) describes the
source migration, and
[Geometry compatibility exports](packages.md#geometry-compatibility-exports)
the explicit geometry compatibility requirement.

<a id="protocol-9-algebraic-affine-forms"></a>

**Protocol-9 algebraic affine forms (Stage 2).** Presented affine declarations
are validated optional fields of protocol 9; no feature-level version is added
([History](#history)). Any module using one selects
protocol 9, and protocols 7 and 8 reject each form with `E_PROTOCOL`.

- **Representation.** An implementation may use
  `{"presented_affine": {"field": "rational"}}`, with exactly one key and no
  other field.
- **Constraint.** `{"kind": "structural", "object": i, "base": j}`.
- **Declaration.** `kind: "affine"` carries `implementation` (path),
  `generators` (names), `relations` (polynomials), `base` (path or `null`) and
  `bindings` (`[{name, image}]`), besides the common `name`, `public` and `span`.
- **Primitives.** The binding `op` may be `relative_compose` or
  `relative_equal`, each with `family`; `relative_view` with `family`,
  `source` and `target`; `relative_coefficient` with `family`, `source`,
  `target`, `coordinate` (a name) and `monomial` (a polynomial in the form
  below); `relative_int_point` with `family`, `object` and `base`; or
  `relative_pair` with `family` and `fiber`. Every other value is a path.
- **Family representation.** A family may use the string `"relative"`.
- **Morphism.** `kind: "morphism"` carries `family` (path), `indices` (paths)
  and `definition`, besides the common fields. The `definition` is
  `{"kind": "pullback", "images": [{name, image}]}`, `{"kind": "identity"}`,
  `{"kind": "structure"}`, `{"kind": "first"}`, `{"kind": "second"}` or
  `{"kind": "restrict", "morphism": path}`.
- **Fiber product.** `kind: "affine_fiber"` carries `implementation`, `left`
  and `right` (paths) and `via`. The value of `via` is `null` or
  `{"forward": [{name, image}], "inverse": [{name, image}]}`.
- **Principal open.** `kind: "affine_localization"` carries `implementation`
  and `object` (paths), `element` (a polynomial) and `inverse` (a name).
- **Isomorphism.** `kind: "iso"` carries `forward` and `inverse` (paths).
- **Cartesian evidence.** `kind: "cartesian"` carries `first`, `second`,
  `fiber` and `inverse` (paths).

Polynomials are tagged by `op`:

- `natural {value}`
- `fraction {numerator, denominator}`, where the numerator may be signed
- `coordinate {name}`
- `neg {operand}`
- `sum {terms}` and `product {factors}`, each with at least two entries
- `pow {base, exponent}`

Literals are unsigned decimal strings of at most 64 digits, and nesting is at
most 64. Unknown fields and operations are rejected. The wire never carries a
basis, a cofactor, a normal form or an elaborated structure image: Lean
computes and verifies them. See [affine geometry](affine-geometry.md).

<a id="protocol-9-smooth-forms"></a>

**Protocol-9 smooth forms.** Smooth objects, smooth maps, tangent or cotangent
fibers, and tapes are validated optional fields of protocol 9. Any module that
uses one selects protocol 9. Protocols 7 and 8 reject each form with
`E_PROTOCOL`.

- **Representation.** An implementation may use the string `"smooth_affine"`.
- **Family representation.** A family may use the string `"smooth"`,
  `"cotangent"`, `"tangent"` or `"tape"`.
- **Constraint.** `{"kind": "canonical", "object": i}`.
- **Declaration.** `kind: "smooth_affine"` carries `implementation` (path),
  `dimension` (an unsigned decimal string) and `coordinates` (names), besides
  the common `name`, `public` and `span`.
- **Maps.** A declared smooth map is an ordinary `kind: "morphism"` record whose
  family has the `smooth` representation. Its `definition` is
  `{"kind": "pullback", "images": [{name, image}]}` or `{"kind": "identity"}`.
- **Primitives.** The binding `op` may be `smooth_compose`, `smooth_equal` or
  `smooth_composite`, each with `family`, or `smooth_int_point` with `family`,
  `object` and `point`.
- **Primitives on tangent or cotangent fibers and tapes.** Each binding names
  its families as paths:
  - `fiber_vector` with `family`, `map_family` and `object`;
  - `fiber_at` with `family` and `map_family`;
  - `fiber_equal` with `family`;
  - `fiber_component` with `family`, `object` and `coordinate` (a name);
  - `fiber_pairing` with `cotangent` and `tangent`;
  - `cotangent_pullback` with `map_family`, `cotangent` and `mode`, the string
    `"saved"` or `"recomputed"`; another string is an error (`E_PROTOCOL`);
  - `differential` with `map_family`, `cotangent` and `line`;
  - `linearize` with `map_family` and `tape`;
  - `cotangent_backward` with `tape` and `cotangent`.

Tangent or cotangent fibers and tapes have no record of their own. The wire
never carries a covector, a vector, a [tape](appendix/glossary.md#tape) or a
coordinate index. The kernel resolves the coordinate of `fiber_component` to
its index. Generated programs compute every tangent or cotangent fiber and
every tape at run time.

The kernel admits the primitive operations of its family table, which
[protocol 7](#protocol-7-indexed-declarations-and-rich-package-bodies)
describes. A spelling that
only shares a prefix with a listed operation is an error (`E_PROTOCOL`). The
wire carries names, a declared dimension and polynomial expressions. It never
carries a map, a program or an image in normal form. The kernel elaborates
every map, and it checks the declared dimension against the coordinates and
the generator limit.
[Smooth affine objects](language/smooth-declarations.md#smooth-affine-objects)
and [Smooth maps](language/smooth-declarations.md#smooth-maps) give the errors
of the declarations.
[Fiber primitives](language/smooth-declarations.md#fiber-primitives) and
[Reverse-pass primitives](language/smooth-declarations.md#reverse-pass-primitives)
give the errors of the primitives on tangent or cotangent fibers and tapes.
The [`E_SMOOTH` rows](appendix/diagnostics.md#e-smooth) of the diagnostics
reference link these sections. The frontend spelling
`Affine(K, n)[…]` has no record of its own: it produces the `kind: "affine"`
record of `spec[…] over K`.

<a id="protocol-9-metric-forms"></a>

**Protocol-9 metric forms.** Metrics, metric evidence, `flat` and `sharp` are
validated optional fields of protocol 9. Any module that uses one selects
protocol 9. Protocols 7 and 8 reject each form with `E_PROTOCOL`.

- **Family representation.** A family may use the string `"metric_form"`.
- **Metric.** `kind: "metric"` carries `family` (path), `indices` (paths) and
  `gram`, besides the common `name`, `public` and `span`. `gram` is
  `{"kind": "euclidean"}` or `{"kind": "gram", "rows": [[poly, …], …]}`, where
  each entry is a polynomial expression in the form above. Another `kind` is
  an error (`E_PROTOCOL`).
- **Evidence.** `kind: "evidence"` carries `metric` (path) and `evidence`, the
  string `"nondegenerate"` or `"riemannian"`, besides the common `name`,
  `public` and `span`. Another string is an error (`E_PROTOCOL`).
- **Primitives.** The binding `op` may be `flat` with `tangent`, `cotangent`
  and `metric`, or `sharp` with `cotangent`, `tangent`, `metric` and
  `evidence`. Each value is a path.

The wire never carries a Gram matrix in normal form, an inverse, an `L D Lᵀ`
factorization or the object of a binding. A record with any other field is an
error (`E_PROTOCOL`). The kernel evaluates every Gram entry in the
coordinates of the metric's object, within the
[metric limits](appendix/limits.md#smooth-metrics). It computes each
certificate and checks it again before acceptance. It copies the metric's object and matrices
into each `flat` and `sharp`, and the declaration audit checks that each copy
equals its declaration. The list of primitive operations has no `gradient`
operation: a gradient is an ordinary function that applies `sharp` to a
differential. [Metrics](language/smooth-declarations.md#metrics),
[Metric evidence](language/smooth-declarations.md#metric-evidence) and
[Flat and sharp](language/smooth-declarations.md#flat-and-sharp) give the
errors of the declarations, and the
[`E_METRIC` row](appendix/diagnostics.md#e-metric) of the diagnostics
reference links these sections.

<a id="protocol-9-frame-forms"></a>

**Protocol-9 frame forms.** Frame declarations, the families of frames, frame
arrays and frame matrices, the frame parameter and the frame primitives are
validated optional fields of protocol 9. Any module that uses one selects
protocol 9. Protocols 7 and 8 reject each form with `E_PROTOCOL`, with the
message "frame declarations require protocol 9" for a declaration, a family
representation and a parameter.

- **Family representation.** A family may use the string `"frame"` (the
  frames of a smooth object, `Frame<X>`), `"frame_vector"` (the arrays of
  vectors in a frame, `Coords<b>`), `"frame_covector"` (the arrays of
  covectors, `CoCoords<b>`) or `"frame_map"` (the matrices of linear maps
  between two frames, `FrameMap<b, c>`).
- **Parameter.** `{"kind": "frame", "family": TypePath}` is a frame index of
  the family `family`. A family with such a parameter is a protocol-9 form,
  whatever its representation. An annotation passes a frame as an ordinary
  argument `{"kind": "name", "reference": TypePath}`; the parameter's kind
  makes the kernel resolve the name to a frame declaration.
- **Declaration.** `kind: "frame"` carries `family` (path), `indices` (paths),
  `columns` and `inverse`, besides the common `name`, `public` and `span`.
  `columns` is `{"kind": "coordinates"}`, the coordinate frame, or
  `{"kind": "columns", "columns": [[poly, …], …]}`. Each inner list is one
  column, a frame vector in the coordinate frame of the object, and each
  entry is a polynomial expression in the form above. `inverse` is `null` or
  `{"kind": "columns", "columns": …}` of the same form. Another `kind` is an
  error (`E_PROTOCOL`).
- **Primitives.** The binding `op` may be one of the thirteen frame
  operations below. A field of kind `natural` is an unsigned decimal string of
  at most 64 digits; the decoder checks the length before it reads the digits,
  and another value is an error (`E_PROTOCOL`). Every other field is a path.

| Op | Fields |
| --- | --- |
| `frame_encode` | `fiber`, `coords`, `frame` |
| `frame_decode` | `coords`, `fiber`, `frame` |
| `frame_vector` | `coords`, `map_family`, `frame` |
| `frame_matrix` | `map_family`, `frame_map`, `source`, `target` |
| `frame_transition` | `map_family`, `frame_map`, `source`, `target` |
| `frame_apply` | `frame_map`, `coords` |
| `frame_coapply` | `frame_map`, `cocoords` |
| `frame_compose` | `frame_map` |
| `frame_pairing` | `cocoords`, `coords` |
| `frame_component` | `family`, `index` (natural) |
| `frame_entry` | `frame_map`, `row` and `column` (natural) |
| `frame_equal` | `family` |
| `frame_at` | `family`, `map_family` |

`natural` is the sixth field kind of the family table, next to `path`,
`object_type`, `coordinate`, `polynomial` and `pullback_mode`. The decoder
functions are those of `lean-kernel/VastitasKernel/IndexedDeclarationProtocol.lean`:

| Form | Decoder |
| --- | --- |
| Frame declaration | `declarationBody`, with `frameColumns` and `frameInverse` |
| Frame family representations | `familyRepresentation` |
| Frame parameter | `parameter` |
| Natural field of a primitive | `naturalField`, through `wireArgument` |

The wire never carries the rows of a frame matrix, a variance, a frame array,
a frame matrix of a map or a transition. It never carries the inverse of a
constant frame either: the kernel computes it, and a constant frame that
declares an inverse is an error (`E_FRAME`), even when the inverse is
correct. A frame primitive carries the names of its frames only. The kernel
copies the object, the matrix and the inverse of each named frame into the
binding, and the variance of an encoding or a decoding from its fiber family.
The declaration audit checks that each copy equals its declaration. A
binding record with any other field, such as a matrix, an inverse or an
object, is an error (`E_PROTOCOL`). The kernel expands every column in the
coordinates of the frame's object, within the limits of
[smooth metrics](appendix/limits.md#smooth-metrics) for a constant frame and
of [exact affine algebra](appendix/limits.md#exact-affine-algebra) for a
polynomial one. It checks `P·Q = Q·P = I` before acceptance. The
[specification of `std::geometry::frame`](spec/std-geometry-frame.md) states
the laws of the forms, and the
[`E_ENDPOINT` row](appendix/diagnostics.md#geometric-types) of the
diagnostics reference covers frame and object mismatches of a call.

<a id="protocol-9-physical-dimension-forms"></a>

**Protocol-9 physical-dimension forms.** The declarations of
`nature::dimension` and their families are validated optional fields of
protocol 9. Any module that uses one selects protocol 9. Protocols 7 and 8
reject each form with `E_PROTOCOL`, with the message "physical dimension
declarations require protocol 9".

- **Family representation.** A family may use the string `"reading"` or
  `"physical_metric"`.
- **Base dimension.** `kind: "base_dimension"` carries only the common
  `name`, `public` and `span`.
- **Quantity.** `kind: "quantity"` carries `dimension`, a list of factors
  `{"base": TypePath, "exponent": String}`.
- **Reading.** `kind: "reading"` carries `family` (path), `indices` (paths)
  and `quantities`, a list of `{"coordinate": String, "quantity": TypePath}`
  in source order.
- **Scale.** `kind: "scale"` carries `quantity` (path) and `magnitude`, a
  polynomial expression in the form above.
- **Physical metric.** `kind: "physical_metric"` carries `family` (path),
  `indices` (paths), `metric` (path), `reading` (path), `value` and
  `entries`. `value` is `null` or a list of factors as in a quantity.
  `entries` is `{"kind": "euclidean"}`,
  `{"kind": "gram", "rows": [[monomial, …], …]}` or
  `{"kind": "normalized", "scales": [{"coordinate": String, "scale": TypePath}, …]}`.
  A monomial is `{"coefficient": poly, "factors": [{"scale": TypePath, "exponent": String}, …]}`.
  Another `kind` is an error (`E_PROTOCOL`).

An exponent is a decimal string with an optional leading `-` and at most 64
digits. The decoder `exponent` checks the length before it reads the digits;
another value is an error (`E_PROTOCOL`). `declarationBody`, `dimensionFactor`,
`coordinateQuantity`, `scaleMonomial`, `physicalGram` and `dimensionValue` of
`IndexedDeclarationProtocol.lean` decode the forms. The wire never carries a
dimension in canonical form, the value of a magnitude or a coefficient, the
coordinate order of a reading or a normalized metric, or an evaluated Gram
matrix. The kernel computes each, within the
[dimension limits](appendix/limits.md#physical-dimensions), and checks every physical metric
against the Gram matrix of the metric it names. The
[specification of `nature::dimension`](spec/nature-dimension.md) states what
an accepted interpretation guarantees.

### Resource statements and numerical forms

Scalar parameters use `kind: "value"` with `name`, `type` and `span`. Resource
statements add `kind: "value"` (`name`, `type`, pure `body`, `span`),
`kind: "call_value"` (`callee`, named `arguments`, owned `results`, scalar `value`,
`type`, `span`), and `kind: "branch_value"` (named `condition`, `yes`, `no`, `span`).
The existing Bool-valued `kind: "branch"` remains unchanged. These scalar bindings
accept only Nat/Int/Bool/Unit; the kernel independently reconstructs the pure Core
fragments and their exact source positions, owners, types and runtime slots.
No checked target, slot ID, trusted condition or resource handle is accepted in a
pure block. Protocols 2–7 and the internal resource component retain their strict
old schemas.

The [runtime-extent profile](storage/resource-programs.md#runtime-extents) adds parameter kinds
`runtime_space` (`name`, `implementation`, `dimension`, `span`), `runtime_basis`
(`name`, `space`, `span`) and `runtime_map` (`name`, `source`, `target`, `access`,
`initializes`, `span`). An extent is exactly `{kind:"literal",value:<u64>}` or
`{kind:"slot",name:<local name>}`. A runtime layout has exactly `rows`, `columns`,
`leading`, `transposed`; no offset is admitted. Statements `kind:"runtime"`
carry a strict resource `action`; `kind:"runtime_numerical"` carry an unresolved
`operation` (`space`, `basis`, `map`, `gemm`) and `span`. Raw runtime actions do
not admit GEMM. All authority, live slots, frame transitions, origins and guards
are reconstructed; no checked IDs or prevalidated shape metadata is accepted.
The checker rejects a coefficient loan in a runtime GEMM. It rejects runtime
events under resource branches, including through calls (`E_RUNTIME_BRANCH`).
Protocols 2–7 reject these forms.

Protocol 8 also admits [numerical declaration profiles](linalg/maps-and-gemm.md#linear-implementations)
in the existing `indexed_declarations` array: `scalar_base` and
`linear_descriptor` representation objects preserve ideal coefficient kinds and
unresolved nominal base paths. They require version 8 or 9 even without resource
functions. Protocol 7 retains only `"affine_descriptor"`; it rejects these
representations. Declaration acceptance alone does not enable GEMM.

Resource bodies also support `kind: "numerical"` statements carrying `operation`
and `span`. Operations are `space` (name, unresolved implementation path,
dimension), `basis` (name, space), `map` (name, loan, source/target bases), and
`gemm` (left, right, output, mode, policy). Mode is `overwrite` or `accumulate`;
policy is explicitly `native_fast`. See [the source contract](linalg/maps-and-gemm.md#maps).
All names remain unresolved. Numeric IDs, trusted certificates, raw GEMM flags
and extra fields are rejected. The old raw resource `action` schema does not
acquire a public GEMM operation. Version 8 composes independent path resolution,
nominal value checking and actual resource checks before native generation.

Numerical GEMM optionally carries `alpha`/`beta` operands, each either
`{kind:"literal",value:<resource literal>}` or `{kind:"loan",loan:<local name>}`.
Source `f64(...)`/`complex(...)` exact finite literals lower to the same unsigned
64-bit payload fields as `f64_bits`/`complex_bits`; decimal or hex strings are not
wire values. See [literal admission](storage/resource-programs.md#payloads) for exactness and
the explicit-bit treatment of signed zero and nonfinite values.
Absent fields retain alpha one and beta zero/one. Explicit null and unknown
fields reject. Overwrite accepts no beta operand; accumulate requires initialized
output even for beta zero. A coefficient loan must be a matching initialized
readable 1x1 region disjoint from output. The checked allocation/offset reaches
native execution, where the current scalar is read before output writes.
See [coefficient semantics](linalg/maps-and-gemm.md#matrix-products).

Owned numerical inputs use parameter `kind:"owned_map"` with `name`, `source`,
`target` and `span`. Result `type` may be `{kind:"owned_map",source,target}`;
the original `{scalar,elements,initialized}` raw owned-result form is unchanged.
Both refer only to preceding input basis contracts. Numerical operation
`owned_map` supplies `name`, raw `owner`, `layout`, `source` and `target` and moves
initialized storage into the interpretation. `borrow_owned` supplies `name`,
`owner` and `access`, using the actual stored layout; `owned_view` supplies `name`,
`loan` and `owner`, retaining exact allocation/layout/bases. These forms are
independently checked, contain no allocation IDs or trusted metadata, and are
rejected by older decoders. See [owned results](linalg/maps-and-gemm.md#owned-maps).
The bounded generative form uses parameter `kind:"owned_map_to"` with `name`,
`source`, `dimension`, `span`, and result `type:{kind:"owned_map_to",source,dimension}`.
Numerical `pack_map` takes `name,owner`; `unpack_map` takes
`package,space,basis,owner`. These are unresolved names; no allocation/brand or
success metadata is accepted. See [owned-map packages](linalg/maps-and-gemm.md#owned-map-packages).


Resource parameters additionally support `kind: "space"` with unresolved
`implementation` and static `dimension`, `kind: "basis"` naming an earlier
`space` parameter, and `kind: "map"` naming earlier `source`/`target` basis
parameters plus `access` and `initializes`. Every parameter includes `name` and
`span`. [Dependent input checking](linalg/maps-and-gemm.md#map-parameters)
preserves actual caller identities and creates scoped child loans for maps.
Unknown tags/fields fail closed on older kernels; these are additive protocol-8
forms. They do not add a shape-polymorphic signature language.

[Typed transforms](internals/numerical-backend.md#wire-and-proof-boundary-of-transforms) add numerical
operations `involution`, `dual_space`, `conjugate_space`, `derived_basis`, `metric`
and `transform`. Their operands remain unresolved local names; `transform`
contains a strict operation naming derived bases or explicit metrics, never raw
native flags. Exact Gram entries are decimal strings. Corresponding dependent
parameter tags retain earlier space/basis/involution relationships and an explicit
orthonormal requirement for direct adjunction. Rust serializes these forms and
Lean decodes them, each with a strict schema; old envelopes and unknown nested
metadata fail closed.

[Vector evaluation](linalg/transforms-and-metrics.md#pairings) adds `vector` (`name`, `loan`, `basis`),
`conjugate_vector` (`name`, `parent`, `basis`, `involution`) and `evaluate`
(`left`, `right`, `output`, `operation`, `mode`, `policy`, optional `alpha`/`beta`).
The nested operation is strictly `{kind: "dual"}` or
`{kind: "hermitian", metric: <local name>}`. Vector parameters use `kind: "vector"`
with `name`, `basis`, `access`, `initializes`, `span`. Actual vector and form
provenance, child loans, scalar output and emitted flags are reconstructed by
the independent checker; no supplied origin or native flag grants authority.
The resource actions `fill`, `store`, `expect` and `release` may carry the local
name of a vector in `loan`, and `copy` in `source` or `target`. They have no other form
for a vector: the checker resolves the vector to its loan, as
[Vectors](linalg/transforms-and-metrics.md#vectors) describes.

[Diagonal metrics](linalg/transforms-and-metrics.md#adjoints-for-diagonal-metrics) add strict numerical operations
`adjoint_into` (`input`, `output`, `source_metric`, `target_metric`, `policy`) and
`hermitian_diagonal` (`left`, `right`, `output`, `metric`, `scratch`, `layout`,
`policy`), which [Pairings](linalg/transforms-and-metrics.md#pairings) specifies. Source syntax also requires the explicit `overwrite` keyword for the
latter. Metric operands remain unresolved names; no raw realization coefficients,
prechecked Gram tags, inverse matrix or native flags are admitted at this public
boundary. The independent checker reconstructs exact coefficients and the full
scratch write/release/read transition. Protocols 2–7 reject these operations.

The additive protocol-8 `network` resource statement checks a strict finite
graph. [Two-map networks](linalg/networks-and-packing.md#two-map-networks)
gives the source rules, and
[Two-map networks: graph and independent acceptance](internals/numerical-backend.md#two-map-networks-graph-and-independent-acceptance)
the wire schema. It is checked
independently before lowering to the existing numerical/storage path.

The additive protocol-8 `tensor` operations (`view`, `pack`, `contract3`) carry a
bounded ordered-axis/grouping schema.
[Packing and contraction](linalg/networks-and-packing.md#packing-and-contraction)
gives the source rules, and
[Tensor packing: independent checking and native execution](internals/numerical-backend.md#tensor-packing-independent-checking-and-native-execution)
the wire schema.
Packing is explicit and checked independently from nominal contraction authority.

The additive protocol-8 `tree` statement carries a bounded unresolved finite graph
and an explicit plan. A step of the plan has the `kind` `action`, `view`,
`regroup`, `rebind` or `join`, and an `action` step admits `borrow` and
`release`. Lean reconstructs producer
connectivity, nominal ports and actual resource transitions; see
[contraction trees](linalg/networks-and-packing.md#contraction-trees). The raw internal `regroup3` action
contains source/target loans, three physical dimensions and explicit input/output
groupings; it is not a public nominal-authority certificate.
Protocol-8 tensor operations also include strict `cached_pack`
(`name`, `source`, `target`) and `cached_contract3`
(`cache`, `left`, `right`, `output`, `policy`) envelopes. They carry unresolved
local names, never stamps or certificates. See [cached packing](linalg/networks-and-packing.md#caches).

## Protocol 2: flat requests

Every function, generic, method, parameter, block, statement and expression has `span`:
`{ "start": 0, "end": 1, "line": 1, "column": 1 }` (UTF-8 byte offsets,
one-based Unicode-scalar columns). Types and indices have their containing
node's span. All arrays are ordered. With explicit `--lib` inputs, declarations
are merged after separately parsing each file. Byte offsets occupy disjoint
source ranges, while line and column remain local to the original file. The
Rust driver retains the range-to-path map and formats backend diagnostics;
`file` identifies the entry input. The backend does not read library files.

Function: `{ "name": "f", "params": [...], "return_type": Type,
"body": Block, "span": Span }`.
Parameter: `{ "name": "x", "ty": Type, "span": Span }`.
Block: `{ "statements": [Statement...], "result": Expr, "span": Span }`.

Generic: `{ "name": "add", "params": [{ "name": "left", "span": Span },
{ "name": "right", "span": Span }], "domain": [[Type, Type], ...],
"span": Span }`. An empty domain is `[]`; a domain containing the zero-argument
key is `[[]]`. Each tuple contains exactly the declared number of concrete
scalar types.

Method: `{ "name": "add", "params": [Parameter...], "return_type": Type,
"requires": ["HasOrder"], "body": Block, "span": Span }`. Parameter `ty`
fields may use the scalar selectors `Any` and `Number` as well as concrete
scalars; the result must be concrete. An absent source `requires` clause is
encoded as `[]`. Requirement names use their containing method's span.

Types use a `kind` tag:

- `named`: `name` is `Nat`, `Int`, `Bool`, `Unit`, `Scheme`, or `CInfScheme`.
- `pair`: `element` is the string `Nat` or `Int`, for example
  `{"kind":"pair","element":"Nat"}`. Lean independently rejects other elements.
  This is a closed homogeneous value family, not general parametric data.
- `point`: `target: Index`, `source: Index`.
- `morphism`: `source: Index`, `target: Index`.
- `pointed`: `setting` is `Scheme` or `CInfScheme`; `base` is `QQ` or `CInfReal`.
  The base must be the base of the setting: `QQ` for `Scheme` and `CInfReal`
  for `CInfScheme` (`E_BASE`).
- `function`: `params: [Type...]`, `return_type: Type`. The recursive contract
  contains only Nat, Int, Bool, Unit and function types. An empty `params` is
  `Fn<(), R>`; a single Unit element is `Fn<Unit, R>`. `Fn` is a reserved source
  constructor, not a `named` IR type. Type nesting is bounded to 64 levels.

Index: `{ "kind": "name", "name": "X" }` or
`{ "kind": "base", "ring": "QQ" }`.

`Any` and `Number` are allowed only in method parameter selectors. Domain
tuples accept only `Nat`, `Int`, `Bool`, and `Unit`. Method results additionally
accept `Pair<Nat>` and `Pair<Int>`. The selected method's declared result is
preserved in its specialized signature; expected results do not select methods.
Geometric values and nominal object IDs cannot select a method. The backend
constructs the nominal hierarchy and capability facts itself; request metadata
cannot add subtype edges, assert capabilities, or provide a trusted winner.
It checks ambiguity on the complete concrete key space, coverage on the
declared domain, and every applicable monomorphized body, including nonwinners.
Each family's table is compared twice with a 16,000,000-unit dispatch-work
bound, each time before the work that the bound covers: first keys × methods
plus the squared number of methods, then the sum over all keys of the squared
number of applicable methods. An amount above the bound reports `E_LIMIT`.
[Selection](stage1a.md#selection) gives the rules, and
[Dispatch checking](internals/checking-pipeline.md#dispatch-checking) the
specialization order and limits.

Expressions use a `kind` tag and always include `span`:

`pair`, `pair_first`, and `pair_second` use ordinary `call` nodes. Both constructor
operands are inferred independently, with no expected-type conversion. Pair
values can occur in ordinary function contracts and data expressions, but not
in dispatch keys/selectors or recursive Fn contracts. These forms use the
protocol-2 and protocol-3 envelopes.

- `integer`: decimal unsigned `value` string (unary minus is separate).
- `boolean`: boolean `value`.
- `unit`: no payload.
- `variable`: `name`.
- `call`: `callee` string, `args: [Expr...]`.
- `invoke`: `callee: Expr`, `args: [Expr...]`.
- `lambda`: `params: [Parameter...]`, `return_type: Type`, `body: Block`.
- `unary`: `op` (`-`, `!`), `operand: Expr`.
- `binary`: `op` (`+`, `-`, `*`, `==`, `!=`, `<`, `<=`, `>`, `>=`, `&&`, `||`),
  `left: Expr`, `right: Expr`.
- `if`: `condition: Expr`, `then_branch: Block`, `else_branch: Block`.
- `block`: `body: Block`.
- `pack`: `scheme: Expr`, `point: Expr`.

An ordinary function name may occur as `variable`; a generic family may not.
A string `call` may refer to a local Fn binding. The `invoke` form supports
arbitrary callee expressions. Lambda IDs and static targets are assigned by
Lean; spans are diagnostic metadata and cannot establish target identity.
There is no public internal-reference constructor. Unknown expression tags
are rejected. All previously valid protocol-2 requests remain supported.

Statements use a `kind` tag and always include `span`:

- `let`: `name`, `annotation: Type | null`, `value: Expr`.
- `unpack`: `value: Expr`, `scheme` binding name, `point` binding name.

Builtins are `Affine(K, n)`, `Base(K)`, `origin(X)`, `id(X)`,
`compose(g, f)`, `apply(f, p)`, `dimension(X)`, `int(n)` (Nat to Int),
`pair(a, b)`, `pair_first(p)` and `pair_second(p)`.
Only the ring argument of `Affine`/`Base` accepts the reserved variable
`QQ` or `CInfReal`. Their use as ordinary values is invalid.

## Responses

Success: `{ "version": 2, "ok": true, "lean_source": "..." }` (the source
is present for emit and absent for check).
Failure: `{ "version": 2, "ok": false, "diagnostics": [
{ "code": "E_TYPE", "message": "...", "span": Span,
  "notes": [{ "message": "...", "span": Span }] }] }`.
Every response also carries `"kernel": { "sources": String, "lean": String }`:
the digest of the files that the kernel executable is elaborated from
(`VastitasKernel/BuildIdentity.lean`, mirrored by the driver's `build.rs`) and
the Lean version it was built with. The digest covers the bytes of the kernel's
`Main.lean`, of every kernel module it imports and of `compiler-limits.json`,
which `VastitasKernel/Limits.lean` reads while it is elaborated. The kernel's
`lakefile.toml` names each of these files as an input of the executable, so
Lake elaborates `Main` again, with its digest, when one of them changes.
Drivers reject a success response whose
identity is missing or differs from their own build, and add a note to failure
diagnostics. The identity is a build-consistency check, not a semantic proof.
It covers the kernel executable, not the files that a native build compiles.
The driver compares those files of the selected kernel root with its own build
before it runs Lake ([CLI reference](guide/cli.md)). It refuses (`E_PROTOCOL`)
a `lean_source` that imports a module other than
`VastitasKernel.IndexedRuntime`, `VastitasKernel.AlgebraRuntime` and
`VastitasKernel.SmoothRuntime`, with `VastitasStorageNative` when the response
selects the storage runtime and `VastitasGemmNative` when it selects the
numerical runtime. These are the modules whose sources the driver compares.
Notes carry related source locations, including object introduction sites. They
are diagnostic metadata, not trusted identity evidence. Current backends emit
an empty array when there are no notes; drivers also accept omitted notes.
Failure responses preserve any readable natural-number request version, even
when unsupported. Missing or non-natural versions are rejected before decoder
selection. An unreadable version, invalid JSON or non-UTF-8 stdin produces an
`E_PROTOCOL` JSON response using version 2 as the fallback; stdin decoding errors
do not escape as uncaught IO exceptions. Before JSON parsing, the kernel also
answers `E_PROTOCOL` (with the same version-2 fallback) for requests over 1 GiB
(`requestBytes` of the compiler limits, by which the frontend bounds the requests
that it writes), nesting deeper than 16384
arrays/objects, numbers with more than 64 integer and fraction digits or an
exponent of more than two digits, and duplicate object keys (compared after
string decoding). Path lists are structured: each component is nonempty and
contains no `:`. Integer literal and Gram strings are ASCII decimal digits
(Gram entries may start with `-`); `_` separators are rejected.
`supportedProtocolVersions` in the kernel defines the complete wire
version list. Drivers display failure diagnostics before adding a version
mismatch note; a mismatched success response is always rejected.

## Codes, common checks and generated code

Frontend and backend use the same codes for name violations: `E_SHADOW` for a
binding with a name of the namespace of its module, such as a function or a
generic, and for a parameter or a binding of a lambda that repeats a name
bound outside the lambda;
`E_RESERVED` for a reserved name;
`E_NAME` for an invalid or unresolved name (including an undeclared generic);
and `E_DUPLICATE` for repeated declarations and for a binding that repeats a
name of its block or of an enclosing block.
[Scopes of bindings](language/statements.md#scopes-of-bindings) and
[Lambdas and their names](stage1b.md#lambdas-and-their-names) give the rules.
`E_ARITY` and
`E_TYPE` identify argument-count and type violations. `E_LIMIT` reports bounded
implementation resources; the check of source bodies and the function compiler
share the 4096-unit per-function checking-budget diagnostic. Diagnostic wording does
not change the acceptance rule or its proof boundary.
`E_CAPTURE` rejects references to outer lambda bindings; `E_STATIC_CALL`
rejects an `if` whose function-valued branches resolve to different static
targets.
Higher-order specialization has a separate 4096-instance bound.

The checker rejects recursion (including mutual recursion), duplicate function
names, reserved names, unbound references, incompatible annotations, escaping
nominal identities, and a main signature other than `fn main() -> Int`.
Check accepts modules without main; emit requires main.
Source declaration order does not constrain function calls.
The `__vastitas_` prefix is reserved for hygienic specialization names and for
the declarations (`__vastitas_rd…`) and generated functions (`__vastitas_rf…`)
of compiled reverse Core. A source binder, or a declaration or function of a
wire request, under that prefix is an error (`E_RESERVED`). So is a reference
to such a name in a flat source and in a request of protocols 2–6. In
protocols 7–9 the kernel declares the compiled reverse names only after
acceptance, so a call of one in a request is an unbound name (`E_NAME`).

`decodeSurfaceModule` in `SurfaceProtocol.lean` decodes the extended request and
`Indexed.LegacySource` converts its unresolved syntax into the common
`Indexed.AuthoritySource.checkProgram` input. The old `checkSurfaceProgram`
remains an internal API with separate retained proofs. Function syntax remains separate from core
syntax. Every lambda and function body is checked, including unused functions;
signature probes for abstract function parameters are confined to a separate
audit pass. Executable specialization memoizes definition/function-argument
IDs, erases function values and produces only direct calls. The unchanged
finite engine still checks all applicable method bodies. See
[Function values](stage1b.md) and
[Function specialization](internals/checking-pipeline.md#function-specialization).

After the original wire decoder, protocols 2–6 adapt source functions, methods,
contributions and namespace metadata before semantic elaboration. Flat input uses
an adapter-owned package identity independent of the displayed filename. The
adapter supplies a closed, unresolved compatibility declaration package because
these wire versions cannot carry indexed declarations. The original namespace
must validate before injection; a source dependency cannot resolve through the
private profile. The same declaration/profile, authority, Fn/dispatch and Core
checks used by protocol 7 remain mandatory. Old wire versions continue to reject
the declaration fields of later versions. Internal Core formats are not
alternative wire protocols.

Runtime representation: generated Lean code imports
`VastitasKernel.IndexedRuntime`, and `VastitasKernel.AlgebraRuntime` or
`VastitasKernel.SmoothRuntime` only when it uses them. A program of protocol
8 or 9 that selects the storage or the numerical runtime also imports
`VastitasStorageNative` or `VastitasGemmNative`. A program of protocols 2–6
imports `VastitasKernel.IndexedRuntime` alone. Scalar types map to Lean `Nat`, `Int`, `Bool`,
`Unit`; geometric objects, indexed points/morphisms and existential payloads use
the common runtime representations. Nominal typing is established before erasure.
The old runtime remains for retained legacy evaluation proofs.
The [finite migration acceptance map](internals/indexed-checker.md#finite-geometry-migration-acceptance) records checked
primitive result compatibility, source regressions and the limits of the
source/native proof claims. The compatibility adapter is not an additional wire
version or a privileged semantic checker.
User symbols are always renamed to generated identifiers; source text is never
inserted as Lean syntax. Integers are validated decimal literals.


## Protocol 3: package namespaces

The namespace request is `{ "version": 3, "file": "entry manifest",
"root": "/canonical/app/Vastitas.toml", "packages": [Package...] }`.
The response has the same shape as version 2 and echoes version 3.

- Package: `source` (canonical manifest location), `name`, `version` (SemVer),
  `dependencies: [{ "alias": "math", "target": "/canonical/math/Vastitas.toml" }]`,
  `modules: [Module...]`. The three identity fields distinguish owners. A
  manifest location occurs once, regardless of how many dependency aliases use it.
- Module: `path: ["logical", "components"]`, `public: Bool`, `span`,
  `imports`, `functions`, `generics`, `methods`. The root has path `[]`.
  Each non-root path has a declared parent. Its visibility belongs to the
  module declaration in that parent. There is no source-file owner field.
- Import: `path: ["package", "math", "add"]`, `alias`, `public`, `span`.
- Functions and generics retain the v2 fields and add `public: Bool`.
  Methods retain the v2 fields; `name` is an unresolved reference path.
- Expressions retain the v2 shape. Global `variable.name` and `call.callee`
  preserve unresolved `::` paths. Locals and dependent indices remain lexical
  names. There are no frontend-supplied function IDs or edit-authority grants.

Lean validates package/module/declaration uniqueness, acyclic dependencies,
imports and reexports (including unused ones), visibility on every traversed
path, and exact-module generic method authority. Each resolution shares a
4096-member work budget across path components and aliases, as well as a
nesting bound; exhaustion returns `E_LIMIT` at the referring source span or,
inside a chain of aliases, at the import declaration where the bound ran out.
Completed dependency nodes are memoized, so duplicate aliases do not cause
repeated graph traversal. Unknown namespace metadata
fields, including claimed owners, are rejected. Protocols 2–6 also reject unknown
fields in nested type/index, parameter, expression, statement, block, declaration
and span records. Only protocol 2's top-level envelope retains its legacy tolerance
for unrelated untrusted hints; that exception does not apply to nested records or
allow newer declarations to be silently downgraded. Flat declarations cannot carry
the package-only `public` field. Invalid membership scalar names are rejected as
`E_TYPE` before constructing their namespace authority graph.

A public reexport preserves
its original target and requires a public declaration; private intermediates
must be accessible from the reexporting module. Private declarations are
visible from their declaring module and descendants only. Parent names are
not implicitly in scope. Dependency aliases are only initial path components.

Protocols 3–6 are accepted through `Indexed.LegacySource.check`. It validates
the original namespace, adapts functions, methods and contributions to the
source checker of protocol 7 and runs `Indexed.AuthoritySource.checkProgram`.
That checker checks every body in an audit pass and in an executable pass,
and then the Core. `Namespace.lower` assigns symbols from package identity +
logical module path + declaration name. On this path it lowers the headers
that the authority assembler and the dispatch families read. For a rejected
request `describeDiagnostic` lowers the original namespace once more, with
its bodies, only to restore source names in the diagnostic; the result of
that lowering decides nothing about acceptance. Only an ordinary
root-package root-module `main` becomes the core entrypoint. Protocol 2 keeps
its flat namespace. `checkNamespaceProgram` and `checkSurfaceProgram` remain
internal APIs that `Main` does not call.

A request admits at most 1,000,000 member visits across all import
declarations. The kernel also limits the sum of the wire price of the request
and the namespace queries in its independent body passes to 4,000,000 units.
The wire price counts syntax nodes, path components and the largest
reconstructed import cost for each matching spelling. It charges matching
strings as well as references, omits diagnostic spans and prices import
declarations separately. Public resource programs include both additional
pure-fragment passes. Either aggregate limit produces `E_LIMIT`; the per-path
limit and the target, visibility and cycle checks of every import still apply.
A body-checking pass caches successful unqualified import aliases under their
full package, module and spelling; each cache hit pays for the same member
visits as the original lookup. The
[matched compiler measurements](https://github.com/MGYamada/Vastitas/blob/main/experiments/compiler_scaling/results/2026-11-03-macos-namespace-work-budget/RESULTS.md)
cover single-use chains, repeated references and the aggregate limits.

`E_VISIBILITY` identifies private access or a nonpublic reexport; `E_OWNER`
identifies unauthorized method extension, including ordinary functions.
`E_CYCLE` identifies package or import cycles. Existing duplicate, name,
shadowing, capture, static-call and checking-limit codes remain in use.

These checks validate the supplied namespace graph, not the authenticity of
filesystem contents. Changing a graph into a different *valid* program is not
an authentication failure: the wire protocol is not a signed artifact format.
Rust is responsible for canonical file loading and retaining all input files
for output collision protection. [Protocol selection](#protocol-selection) says
when manifest mode selects protocol 3. See [Packages](packages.md) and
[Modules](language/modules.md) for source syntax, commands and file loading.


## Protocol 4: finite abstract declarations

Sources without abstract declarations retain version 2 (flat, including
explicit `--lib`) or version 3 (packages), and abstract declarations select
version 4, when no earlier item of [Protocol selection](#protocol-selection)
applies. A request of version 4 has a required `input` field whose value is
exactly `flat` or `package`. Flat input keeps the version-2
`file`, `functions`, `generics`, and `methods` fields. Package input keeps the
version-3 `file`, `root`, and `packages` graph. Responses echo version 4.

Flat roots and package modules may contain `abstract_types`, `subtypes` and `abstract_methods`
arrays; absent arrays mean empty, and present arrays must be arrays. Each
abstract type has `name`, `parents`, and `span`, with an additional required
`public` boolean in package mode. A parent is an unresolved `{path: [String],
span: Span}`; an empty parent list means the default Any parent. Each subtype
has `scalar`, `target` (an unresolved path plus span), and declaration `span`.
Path components must be nonempty; flat type paths have one component. Existing
method selector `named` types retain their unresolved path spelling until Lean
resolves them in the defining module. No selected IDs or hierarchy matrices are
accepted from the frontend. Version 2/3 reject these extension fields.

The kernel independently validates the maximum 64 nominal types, cycles,
duplicates, scalar memberships and unchanged builtin relations/capability facts.
It resolves abstract selector aliases using the namespace index and records
membership edit authority in the independently checked reference ledger.
`E_HIERARCHY` reports cycles or changes to builtin relations; `E_OWNER` reports
unauthorized membership edits. All existing method/body/core audits remain in
the acceptance path. See [abstract selectors](stage1a.md#abstract-types) for semantics
and theorem boundaries.

An `abstract_methods` entry has `name`, `params`, `return_type`, `requires`,
`domain`, and `span`, with no body or visibility field. Parameters use the
existing named selector encoding; results are scalar or homogeneous numeric
Pair types. `domain` is an array of tuples of unresolved `{path, span}` objects.
An empty array is an explicit empty domain; `[[]]` is the nullary tuple. Every
written tuple must expand to at least one concrete key. Lean resolves each
path, enforces exact generic-owner authority, validates selector/capability
applicability, and checks the selected concrete result for every contract key.
The callable domain is the union of the generic domain and all expanded
contract domains. Contracts never enter the candidate list. `E_CONTRACT_EMPTY`,
`E_CONTRACT_DOMAIN`, and `E_CONTRACT_RESULT` distinguish empty expansion,
inapplicable contract keys, and selected-result conflicts. Missing/ambiguous
concrete winners retain the existing dispatch diagnostics.

## Protocol 5: scoped edits and assembly

Protocol 5 extends the protocol-4 package envelope, requires `input: "package"`,
and retains all package identities, declarations, hierarchy and unresolved paths.
Inputs without edit declarations use versions 2/3/4, or the later version
that [Protocol selection](#protocol-selection) gives them. There is no
cached or pre-approved assembly input. See [Edit authority](language/edit-authority.md)
for the source rules and
[Edit authority acceptance](verification.md#edit-authority-acceptance-protocol-6)
for the proof boundary.

Each module additionally permits `grants: [Grant...]`,
`contributions: [Contribution...]` and `assembly: Assembly` (each optional; an
explicit `null` is rejected).
The decoded module determines each declaration's owner; the wire cannot assert
an issuer, owner, accepted flag or stable identity independently of that module.

```text
Grant = { name, target: [identifier...], grantee_source: manifest-location,
          grantee_path: [identifier...], region: [[scalar...], ...], public, span }
Contribution = { name, target: [identifier...], methods: [Method...], public, span }
Assembly = { events: [Event...], span }
Event = { op: "borrow", grant: [identifier...], loan: identifier, span }
      | { op: "apply", contribution: [identifier...], loan: identifier | null, span }
      | { op: "return", loan: identifier, span }
      | { op: "seal", target: [identifier...], span }
```

This grammar is the decoder contract of protocols 5–8. The driver writes
`grantee_package` and selects protocol 9 for every grant, delegation and
transfer ([Protocol selection](#protocol-selection)). It writes protocol 5
for contributions and an assembly when no earlier item of that list applies.

Grant paths refer only to the selected dependency closure. Grant/contribution
IDs derive from package identity, module path and declaration name; method
ordinals distinguish methods within a contribution. Unknown fields in these
records and events are rejected. Ordinary expressions retain their existing
protocol decoder contract. A maximum of one assembly is permitted, exactly at
the root package's root module. An omitted root assembly is an empty trace;
all declaration, unapplied-body and completion audits still run.

The kernel independently reconstructs grant and contribution lowering from
original scopes, checks exact module authority and unresolved references,
audits every exclusive borrow/apply/return/seal transition and complete replay
provenance, and requires all loans returned and edited generics sealed. It checks
completion in the final immutable environment, including domain-union coverage,
contract results, all-key ambiguity and each installed method's final winning
footprint. All applied bodies and every applicable ground instance of unapplied
contributions are checked; unapplied declarations never become dispatch candidates.
The executable Core comes from the source bodies through the function compiler
and the Core audits of every other protocol.

The shared limits allow 4096 assembly events, 4096 contribution methods in the
whole closure, and 4096 ground functions in the separate unapplied-body audit.
Every per-event state and transition audit runs; the audits of one trace share
a 200,000,000-unit budget, charged before each audit, and exhaustion reports
`E_LIMIT`. An assembly of more than 4096 events is a decoder error
(`E_PROTOCOL`).
Existing per-family key, hierarchy, type-depth and specialization bounds remain.
No digest in this same input proves filesystem or author authenticity.

## Protocol 6: nested loans and current edit authority

Protocol 6 is package-only and keeps the version-5 envelope and declarations.
Grants may additionally carry `delegable: Bool` (default false); presence of
this field is rejected in protocol 5 even when false. Modules may add:

- `delegations: [Grant...]`: the same record shape, with the issuer derived from
  its declaring module. It is usable only through an active explicitly delegable
  parent loan held by that module, with the same target and a contained region.
- `transfers: [{name, target, grantee_source, grantee_path, public, span}]`:
  a named permanent transfer operation, declared by its issuer module. The exact
  recipient must already exist in the selected closure.

The additional assembly events are
`{op: "reborrow", parent: String, delegation: Path, loan: String, span}` and
`{op: "transfer", declaration: Path, span}`. Unknown fields are rejected;
claimed issuer/current-owner IDs, accepted flags and supplied histories are not
wire fields. All old event schemas remain unchanged. Protocol 2 also rejects
semantic package/authority fields while retaining its unrelated hint metadata
compatibility.

`Authority.assemble`, which `Indexed.AuthoritySource.checkProgram` calls,
reconstructs histories and complete delegation chains and audits each
transition against an independent relation. `checkProgram` performs the same
namespace, membership, final dispatch, footprint, all-body and Core audits.
`checkAuthorityProgram` remains an internal API that `Main` does not call.
The original function identity never changes. A returned loan or transfer
preserves contributions and unresolved completion obligations. The final
winning region is contained in every ancestor's grant, and transfer requires
no outstanding loans. See [source semantics](language/edit-authority.md#transfers) and
[the proof boundary](verification.md#edit-authority-acceptance-protocol-6).

## Protocol 7: indexed declarations and rich package bodies

The package-only envelope is `{version:7,input:"package",file,root,packages}`.
Package/module identity, dependencies, imports, abstract selectors/contracts and
all protocol-6 authority metadata retain their existing schemas and checks.
Each module may add `indexed_declarations`, defaulting to an empty array.
Rust selects 7 when no condition of protocol 8 or 9 holds
([Protocol selection](#protocol-selection)) and any loaded module uses an
indexed declaration, annotation, typed pack or ordered-field unpack, or any
package exports `geometry_compat`. Every body in that package closure then uses
the rich source path. Flat input and explicit `--lib` keep protocol 2/4.

A declaration has `{kind,name,public,span,...}` with these additional fields:

| Kind | Fields |
| --- | --- |
| `marker` | None |
| `implementation` | `marker:TypePath`, `representation:"affine_descriptor"`, `capabilities:["origin"\|"dimension"]` |
| `classification` | `parents:[TypePath]`, `domain:[TypePath]` |
| `global` | `implementation:TypePath` |
| `family` | `parameters:[Parameter]`, `constraints:[Constraint]`, `representation:"token"\|"point"\|"morphism"` |
| `package` | `cases:[{witness_type:ObjectType,fields:[BoundApplication]}]` |
| `primitive` | `binding:Primitive` |

`TypePath` is `{path:[String],span}`; the path is unresolved and nonempty.
`ObjectType` is `{domain:TypePath,marker:TypePath}`.
Parameter tags are `{kind:"domain"|"marker"|"natural"}` or
`{kind:"object",domain:TypePath}`. Constraint tags are
`{kind:"same_object"|"same_base",left:Nat,right:Nat}` or
`{kind:"over",object:Nat,marker:Nat}`; positions are zero-based.
The Rust source parser bounds constraint positions to `u32`; Lean additionally
checks them against the actual finite parameter contract.

`BoundApplication` is `{family:TypePath,indices:[BoundIndex]}`.
Bound-index tags are `{kind:"witness"}`, `{kind:"natural",value:String}` or
`{kind:"global"|"domain"|"marker",declaration:TypePath}`.
Natural values use unsigned decimal strings, preserving arbitrary precision.
Every package field is ordered and checked against its exact opened witness.

Primitive bindings use `op`, with these payloads:

| Op | Fields |
| --- | --- |
| `descriptor` | `implementation:TypePath` |
| `global` | `declaration:TypePath` |
| `origin` | `domain:ObjectType`, `point_family:TypePath`, `base_object:TypePath` |
| `identity` | `domain:ObjectType`, `map_family:TypePath` |
| `dimension` | `domain:ObjectType` |
| `compose` | `map_family:TypePath` |
| `apply` | `map_family:TypePath`, `point_family:TypePath` |

The field set of every operation, here and in protocol 9, comes from one
table: the families of `lean-kernel/VastitasKernel/IndexedPrimitiveFamilies.lean`.
Each family names an `op`, its fields with their kinds in wire order, and
whether only protocol 9 admits it. The decoder admits a binding only with its
family's fields. The frontend reads `src/primitive_table.rs`, which
`scripts/check_primitive_table.py` generates from the same families, and
writes the fields in that order.

Data annotations retain concrete scalar `named` and homogeneous `pair` types and add
`{kind:"indexed_object",domain:TypePath,marker:TypePath}` and
`{kind:"indexed_apply",family:TypePath,arguments:[Argument]}`.
Arguments are `{kind:"name",reference:TypePath}` or
`{kind:"natural",value:String}`; expected parameter kinds determine whether a
name refers to a declaration or a preceding local object binding.
Fn types keep the scalar/recursive-Fn-only contract and existing depth bound.

Ordinary expression and statement forms retain their schemas. Explicit packages
use `{kind:"indexed_pack",package:Type,witness:Expr,fields:[Expr],span}` and
`{kind:"unpack_fields",value:Expr,witness:String,fields:[String],span}`.
The existing legacy `pack`/`unpack`, named Scheme/CInfScheme and
`point`/`morphism`/`pointed` annotation schemas are also decoded strictly.
Their meaning requires exactly one validated compatibility export. Inferred
legacy pack types are an internal body-only form, never a signature escape hatch.
The existing protocol-2–6 compatibility path is preserved.

A package may add `geometry_compat` (omission means no export; `null` is invalid):

```text
{
  point: String, morphism: String, pointed: String,
  compose: String, apply: String,
  scheme: GeometrySetting, smooth: GeometrySetting
}
GeometrySetting = {
  domain: String, marker: String, base_object: String,
  affine: String, base: String, origin: String, identity: String, dimension: String
}
```

These are unresolved `::`-separated paths, exactly as in the manifest’s
`[geometry_compat]`, `[geometry_compat.scheme]` and `[geometry_compat.smooth]`
tables. Lean resolves them in the exporting package’s root scope, preserving
canonical owners, and audits all exports against the same accepted declaration
environment. Contracts require distinct markers, compatible classification/base/
affine roles, exact primitive bindings, Point/Morphism representations with
exactly `same_base(0,1)`, and matching Pointed package cases. No serialized
validity flag or trusted ID is accepted. Zero or multiple exports disable only
legacy syntax; qualified indexed syntax remains available. A malformed unused
export still rejects the program. The [source contract](indexed-source.md#core-geometry-syntax)
defines fallback precedence and nominal identity behavior.

Declarations, rich types/bodies and the envelope reject unknown fields. No
serialized owner, winner, lifted lambda ID, certificate or checked Core can enter
acceptance. Older package versions reject `indexed_declarations` and
`geometry_compat`; flat protocol 2 also rejects these semantic fields rather
than ignoring them as unrelated metadata.

`Indexed.Wire.check` retains the exact decode and actual
`Indexed.AuthoritySource.checkProgram` result. The actual authority assembler,
all-key footprints, every applied/unapplied body, independent Fn audits and both
Core checks therefore run before success. `emit` passes `compiled` to
`Indexed.Core.Codegen.generate`: the executable Core with its reverse passes
compiled into Core and checked again by the Core audit. The generator
rechecks it independently.
See [source syntax and limitations](indexed-source.md).

## Expected-rejection doctest consumer (reference only)

The [doctest result contract](reference/compiler-tools.md#doctest-result-reference) separates
ordinary language rejection from protocol, transport, and execution failure.
It reuses the diagnostic payload above without changing this wire protocol or
the driver's preservation of diagnostics on incompatible failure responses.
The Python reference and fixture regressions do not implement production driver
receipts, doctest execution, or official package admission.

## Tests

- `tests/protocol_shape.rs::legacy_decoders_reject_unknown_fields_in_every_nested_record_shape`
  adds a field to every record shape of requests of protocols 2 to 6. It
  requires `E_PROTOCOL` with the version of the request. The envelope of
  protocol 2 is the one exception.
  `public_decoders_reject_unknown_fields_in_every_captured_v7_to_v9_record_shape`
  does the same for the requests of protocols 7 to 9 that the driver writes
  for the example packages, and `frame_and_nature_records_reject_unknown_fields`
  for every frame and physical-dimension record of the fixture package
  `tests/fixtures/frame-dimension-declarations/`.
- `tests/frame_dimension_declarations.rs::frame_and_nature_declarations_select_protocol_nine_only`
  and `tests/frame_primitives.rs::frame_primitives_select_protocol_nine_and_decode_only_there`
  pin the protocol of the frame and physical-dimension forms: protocol 9
  decodes them, and protocols 7 and 8 reject each with `E_PROTOCOL`.
  `raw_wire_rejects_forged_frame_bindings` of the second file rejects a
  natural field that is not an unsigned decimal string of at most 64 digits,
  and a frame binding without one of its fields.
- `legacy_hint_tolerance_is_limited_to_the_v2_envelope`,
  `invalid_membership_scalar_is_rejected_before_authority_analysis` and
  `malformed_versions_and_non_utf8_input_return_protocol_json` of the same
  file pin the envelope of protocol 2, the scalar names of memberships and
  the responses to a request that the kernel cannot read.
- `tests/stabilization.rs::unknown_wire_version_is_echoed_with_the_complete_supported_set`
  pins the response to a version that the kernel does not support.
- `tests/edit_authority.rs::named_recipient_wire_rejects_forged_locations_and_unselected_records`
  and `recipient_source_migration_keeps_legacy_wire_and_optional_runtime_boundaries`
  pin the recipient fields of protocols 6 to 9.
- The kernel regressions `VastitasKernel.IndexedWireRegression`,
  `VastitasKernel.LegacySourceRegression` and
  `VastitasPublicTest.AuthorityRegression` decode and check requests without
  the driver. `VastitasKernel.FrameDeclarationRegression`,
  `VastitasKernel.FrameRegression` and `VastitasKernel.NatureRegression`
  decode every frame and physical-dimension form in protocol 9 and reject it
  in protocols 7 and 8. `VastitasKernel.NamespaceRegression` tests the
  retained `checkNamespaceProgram` on Lean values and decodes no request.
  `bash scripts/check_kernel_regressions.sh` builds them.

## History

- Presented affine declarations, smooth forms, metric forms, frame forms and
  physical-dimension forms are optional fields of protocol 9 and have no
  version of their own, by a decision that
  [#533](https://github.com/MGYamada/Vastitas/issues/533) records. The frame
  and physical-dimension forms belong to the Stage 4 tracker
  [#759](https://github.com/MGYamada/Vastitas/issues/759). That
  issue is open. It records the policy of one wire protocol for the release
  v0.1.0: the driver writes one schema, the kernel accepts that schema
  alone, and the other versions with their decoders are retired in one
  verified change. The change is not made: this chapter describes the
  versions 2 to 9 that the kernel accepts.
- The doctest result contract of
  [Expected-rejection doctest consumer](#expected-rejection-doctest-consumer-reference-only)
  belongs to [#236](https://github.com/MGYamada/Vastitas/issues/236).
- The `pair` type tag and the `pair`, `pair_first` and `pair_second` calls
  were added to the protocol-2 and protocol-3 envelopes without a version of
  their own. A kernel that predates them rejects the tag.
- [Source migrations](appendix/history.md#source-migrations) records the
  change of the recipient syntax that protocol 9 carries.
