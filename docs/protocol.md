# The wire protocol

This chapter describes the wire protocol between the driver and the kernel:
the JSON request, the response, and the forms that a request admits. It names
the decoder and the checker and says what the decoder refuses. The rules of
the language are in the Vastitas Reference.
[Programs](language/programs.md) gives the two modes of a compilation.
[Packages](packages.md) and [Modules](language/modules.md) give manifests and
names. Each construct has its chapter:
[Generics and dispatch](stage1a.md), [Function values](stage1b.md),
[Edit authority](language/edit-authority.md),
[Indexed declarations](indexed-source.md),
[Presented affine declarations](affine-geometry.md),
[Smooth affine declarations](language/smooth-declarations.md),
[Frames](language/frames.md),
[Physical dimensions](language/physical-dimensions.md),
[Spectral observations](language/spectral-observations.md),
[Resource programs](storage/resource-programs.md) and
[Numerical maps](linalg/maps-and-gemm.md).
[The driver](internals/driver.md) describes how the Rust side writes a
request and reads a response, and [Verification boundaries](verification.md)
states what is proved about the result of the checker.

## Requests, decoders and checkers

The Rust frontend sends one JSON object on stdin to `vastitas-kernel check`
or `vastitas-kernel emit`. The Lean backend writes one response on stdout;
tool logs belong on stderr. Neither the frontend's annotations nor names are
trusted. The backend allocates nominal identities while checking lexical
bindings; the wire format cannot supply a trusted object identity.

The wire has one **schema epoch**, protocol 10: the one version that the
driver writes and the kernel accepts. The kernel holds it in
`currentProtocol` of `lean-kernel/VastitasKernel/Protocol.lean`. The driver's
`PROTOCOL` in `src/ir.rs` holds the same number: `build.rs` reads the Lean
definition, and a constant assertion fails the build of the driver when the
two differ. `vastitas --version` prints that number, as in
`vastitas 0.1.0-beta (wire protocol 10)`. The version is a schema epoch, not
a feature level: an optional record of the envelope never selects a version.

`lean-kernel/Main.lean` reads the request up to its byte bound, decodes it
as UTF-8, scans it (`WireScan.scan`) and parses the JSON. Only then does it
read `version`, before any other field. A version other than
`currentProtocol` is an error (`E_PROTOCOL`), whatever the other fields hold;
[Other versions](#other-versions) gives the diagnostic and the steps that
come before it. A request of the epoch goes to one decoder and one checker:

| Version | Decoder | Checker | Emit |
| --- | --- | --- | --- |
| 10 | `ResourceSource.Wire.program` in `ResourceProtocol.lean` | `ResourceSource.Wire.check` | `ResourceSource.Wire.emit` |

`ResourceSource.Wire.program` decodes each module with the decoders of
`IndexedProtocol.lean` (`Indexed.Wire.module` and `Indexed.Wire.package`), its
indexed declarations with those of `IndexedDeclarationProtocol.lean` and its
bodies with those of `IndexedBodyProtocol.lean`. The decoders of the module
envelope and of its types, generics, abstract declarations, imports, grants,
transfers, contributions and assembly are in `EnvelopeProtocol.lean`. In the
mode `emit`, `Main` calls `ResourceSource.Wire.emit`, which runs the check and
passes its result to `ResourceSource.Codegen.generateChecked`.
[The checker route](development/architecture.md#the-checker-route) describes
the route.

## The envelope

A single-file request is `{ "version": 10, "file": "entry.vast", "root":
"vastitas:compat:flat", "root_source": {"offset": 0, "text": "…"},
"packages": [Package...] }`, with the optional
fields `legacy_geometry` and `expected_function_revision`. These are its only fields: another top-level field is
an error (`E_PROTOCOL`), with the message `unknown protocol field '<name>'`.
So a request with the field `input` is an error, and so is a flat module with
top-level `functions`, `generics` and `methods`. Every request is a package
request: [Package namespaces](#package-namespaces) gives the packages and
modules, and the sections below give the records of a module.

Every optional record and field of the envelope is admitted in every request
and validated where it occurs. Optional does not mean unchecked: a record with
a missing, unknown or ill-formed field is an error (`E_PROTOCOL`), and the
checker checks every admitted record as the sections below describe. The
optional records are the observations of `show!`, the field
`legacy_geometry`, resource functions, numerical representations, named
recipients of grants, delegations and transfers, abstract declarations,
contributions and assemblies, indexed declarations, the `geometry_compat`
export of a package, and the algebraic, smooth, metric, frame,
physical-dimension, spectral, transition-average and physical-model forms.

## Function revision replay

The kernel mode `function-revision` checks the request and returns its
`function_revision` object. Its `input` field is the complete protocol 10
request with only `expected_function_revision` removed. Its `families` table
names functions by defining package, module and declaration; each callable
dispatch key records the winning ordinary or contributed method and its
definition number. The `pure` and `resource_values` tables bind those numbers
to the emitted Core symbols, static uses, calls and exact arithmetic sites of
their respective executable passes. The latter table is null when there are
no resource value fragments. Ordinals and Core symbols are local to this
revision, whereas an import alias does not change the defining function.

Each executable `static_uses` record identifies its caller by definition
number and ordered static target arguments. Two specializations of one
function can therefore select different targets at the same source site.
When the executable pass resolves a family reference, `family_refs` records
the caller, source path and span, and defining owner. The checker resolves
the path in the caller's writing scope.
A closed package retains the emitted siblings of a family referenced by a
retained specialization, even if the callee ignores its function argument.

For a function with finite index parameters, the family row's
`finite_binders` gives the defining schema of each model and the model slot
of each object. Each emitted specialization's `finite_indices` gives its
ordered nominal model and object indices. Explicit indices and inferred
indices that resolve to the same substitution share the Core symbol. Two
models with identical tables retain separate identities.

When a finite method forwards a callable operand, `pure.finite_forwards`
records the caller specialization, family, selected indices, represented
definition, forwarding declaration span and call-site span. The target list
has one entry per argument. A data argument has a null entry. A producer
entry carries its selected target and its full nullary Hom signature. The
checker reads the returned Core at the caller's first argument binding and
checks the input bindings, producer calls and final call in order.

A finite functor schema has `kind: "schema"` and `schema_kind: "finite_functor"`.
Its instance has `kind: "instance"`, a schema path, and a `functor` record
with four paths named `source`, `target`, `objects` and `arrows`. Each
path carries its source span. A category instance uses the `graph` record.
The decoder requires exactly one record and checks its fields. Changing a
category reference changes the revision even when both categories share
their carriers and tables. [Finite carriers and tables](indexed-source.md#finite-carriers-and-tables)

A `finite_nat_trans` schema admits a `transformation` record with paths
`source`, `target` and `components`. Both functors must name the same domain
and codomain categories. The component table supplies one arrow per source
object. A `finite_monad` schema admits a `monad` record with paths `category`,
`functor`, `unit` and `multiplication`. Both transformations must target the
selected endofunctor. All four paths and their spans belong to the same
revision. The kernel checks the identity and squared source actions and
the Monad equations on the resolved tables before use.

A schema of kind `finite_kleisli` or `finite_kleisli_triple` carries a
`monad_schema` path to the defining Monad schema. Its instance record is
`kleisli` or `kleisli_triple`, respectively, with one `monad` path to an
instance of that exact schema. Both paths retain their source spans.
An explicit function index through either view specializes on the underlying
Monad ID. The complete function revision also retains the source view
reference, so changing that reference requires a fresh receipt.

Each `operator_sites` row names its Core function, the defining operator
and its ordered operand types. In particular, `(Nat, Int)` and `(Int, Nat)`
are distinct division keys. Glyphs and direct named calls need only these
Core operations. When a program refers to an operator as a function value,
the kernel supplies ordinary finite method bodies for that family. The
bodies appear under the protected package source `vastitas:compat:operators`
and pass the same audits as other methods. The request cannot provide this
package, its bodies or its selected keys. A typed function value refers to
the selected method in the same compilation revision.

A request may carry a saved object in `expected_function_revision`. Both
`check` and `emit` reconstruct the receipt from the independent checks and
compare the complete compact JSON serializations; JSON member order and
formatting do not select a method. A mismatch is `E_FUNCTION_REVISION`.
Success with a supplied receipt adds `function_revision_matched: true` to
the response. Changes to source locations, unapplied bodies or another
package invalidate the compilation revision even when the winner is the
same. Revisions have a 64 MiB compact JSON limit, and the ordinary request
limits still apply during replay. The receipt is evidence about this input
and its checked functions, and carries no native or LLVM proof.

## Flat programs and the legacy geometry

The driver writes protocol 10 for every program. In manifest mode the request
holds the packages of the manifest. A flat program, with or without `--lib`
inputs and with or without
[`show!`](language/programs.md#showing-values-with-show), is one package with
the reserved identity `vastitas:compat:flat`, `legacy_flat` and `1.0.0`
(`packages::flat_request`). Its one module is the public root module, and
every function, generic and abstract type of the program is public in it. The
driver shows the kernel's names of these declarations without the package
prefix `legacy_flat::`.

The request of every flat program has the field `legacy_geometry`
([Compatibility profile](#compatibility-profile)). A package request has it
unless the program has one of these records:

- a grant, delegation or transfer, an observation of `show!`, resource
  functions, an indexed declaration, an indexed type annotation, a typed
  `pack`, an `unpack` with ordered fields, or a `geometry_compat` export of a
  loaded package. The presented affine declarations of
  [Presented affine geometry](affine-geometry.md), the smooth and metric
  declarations of
  [Smooth affine declarations](language/smooth-declarations.md), the
  [frame](#frame-forms), [physical-dimension](#physical-dimension-forms) and
  [spectral](#spectral-forms) forms are indexed declarations.

A package with one of the records has the legacy geometry only from a
`geometry_compat` export.

Every request includes `root_source` with the entry’s `offset` and exact UTF-8 `text`. The driver takes the
original UTF-8 text of the physical entry file and its starting byte offset
from the files it read for compilation. In a flat unit with `--lib`, the
entry file has offset zero. In a package, earlier manifests and modules can
give the entry file a positive offset. The namespace work budget charges
the decoded names. The edit parser scans the source text under the entry
file's 16 MiB limit.

File-backed packages and flat compilations with libraries also include
`root_source.files`. This array lists each physical input in load order,
including manifests, unused dependencies and external module files. Each
record has a path and byte offset. The entry uses the enclosing `text`
field. Every other record contains its own complete text. In a request
from a manifest, `file` and `root` both name its canonical path. A single flat
file with a UTF-8 path uses the envelope’s `file` field. On Unix a
non-UTF-8 path uses the original path bytes in a JSON array.

The checker reconstructs every offset from the preceding UTF-8 byte
lengths and the one-byte separator. For disk-backed packages it checks
that the first input is the root manifest, every package manifest occurs,
and the entry contains the root module’s source location. The function
revision includes the ordered files. Even a comment-only change in a
library or dependency manifest invalidates its replay. Filesystem discovery
and the translation of source declarations into wire records use the Rust
frontend.

Lean reads the edit commands from this text, including original path
spellings, optional loan labels, and the positions of opening and closing
braces. A package with an edit block in the entry file must supply the
matching structured commands and events. A package with no such block
selects an empty edit trace. The kernel still validates every grant and
checks every unapplied contribution. The protected flat unit accepts only
an empty assembly.
The kernel accepts a `reborrow` event only with a delegation and a `transfer`
event only with a transfer declaration, and each of these declarations is a
record of the list above. A request with `legacy_geometry` that holds such an
event therefore holds an event that the kernel rejects.

## Optional records

Package [resource functions](storage/resource-programs.md#resource-functions)
are unresolved `resource_functions` of a module. The kernel checks them with
the full declaration/Fn/dispatch/authority checks of the pure program. Each
resource function carries `name`, `parameters`, ordered owned `results`,
resource `body`, pure `value_type`/`value_body`, `public` and `span`. Calls
carry unresolved paths and local names, not checked IDs. The schema is defined
by `storage.rs::source` and `ResourceProtocol.lean`. Emit responses include
`storage_runtime: Bool` and `numerical_runtime: Bool` to request optional
native packages only when the entry needs them. `storage_runtime` is
true when the checked entry has an operation on an arena or a runtime-shape
event. A resource entry that computes scalars alone reports false, and its
`lean_source` imports no `VastitasStorageNative` and creates no arena
([Resource checking](internals/resource-checking.md#all-body-checking-and-generation)).
A numerical requirement
also requires storage and explicit driver build configuration. The [internal storage component schema](storage/checked-storage.md#storage-ir)
is not an alternative public envelope: a top-level `resources` or
`resource_functions` field is an error (`E_PROTOCOL`), as an unknown field of
the envelope.

<a id="named-recipients"></a>

**Named recipients.** A record of `grants`, `delegations` and `transfers`
names its recipient package with `grantee_package: String` and its module with
`grantee_path`, an ordered list of module components. The string is the original manifest package name, never a resolved
source location, dependency alias or claimed PackageId. Lean reconstructs the
root-reachable selected packages, requires one exact name match before examining
the module path, and retains that record's full source/name/version identity.
No match or several matches is `E_OWNER`, even for unused declarations. A name
collision cannot be resolved by version, module availability or list order.

A recipient record has no other location field: `grantee_source` is an unknown
field (`E_PROTOCOL`), even beside `grantee_package`. A program without
resource functions emits both optional-runtime flags as false.
[Source migrations](appendix/history.md#source-migrations) describes the
source migration, and
[Geometry compatibility exports](packages.md#geometry-compatibility-exports)
the explicit geometry compatibility requirement.

Pure functions with static category or object parameters carry
`finite_binders` in declaration order. A `category` entry carries
`name`, a path in `schema` and `span`. An `object` entry carries `name`,
the earlier category parameter name in `category`, and `span`. A
`finite_call` expression carries a callee path, the ordered `indices`
paths, the value expressions in `args` and the expression `span`. The
callee and index paths retain their own spans. An inferred call uses
`call`, and both forms keep the `finite_hom` parameter types.

<a id="observations-of-show"></a>

**Observations of `show!`.** A pure function of a module may have the
optional field `observations`: a nonempty array of objects with
exactly the fields `statement` (a natural number below 2^64) and `label` (a
string). Each names the `statement`-th top-level statement of the function's
body, whose `let` the request sends without `show!`. The kernel checks the observations after it checks the pure program, before code
generation and in `check` mode too:

- only the entry point `main` of the root module of the root package may have
  observations. An observation on another function is an error
  (`E_UNSUPPORTED`), with the message of the frontend;
- the statements must increase strictly, and each must exist. Another list,
  an empty list or another field is an error (`E_PROTOCOL`). A statement that
  is an `unpack` is an error (`E_UNSUPPORTED`);
- the value of each observed `let`, in the compiled Core of the checked
  program, must have type `Int`, `Nat`, `Bool`, `Unit` or `Pair`. Another type,
  including a function value, which Core erases to `Unit`, is an error
  (`E_TYPE`).

The label is presentation only: the kernel never reads it for acceptance, and
code generation writes it as a quoted Lean string literal. The request of a
flat program ([Flat programs and the legacy geometry](#flat-programs-and-the-legacy-geometry))
carries the observations in the functions of its one module.

<a id="compatibility-profile"></a>

**Compatibility profile.** A request may have the optional top-level field
`legacy_geometry`. Its value must be the JSON boolean `true`; another value,
including `false`, is an error (`E_PROTOCOL`). With the field, the kernel
appends its **compatibility profile** as the last package of the program that
it checks. The profile is the package `vastitas:compat:2-6` (`legacy_geometry`,
`1.0.0`) of `CompatibilityProfile.lean`. It declares `Scheme`, `CInfScheme`,
`Point`, `Morphism`, `Pointed`, `compose`, `apply` and the primitives of the
two settings, and its `geometry_compat` export supplies the legacy geometry.
Its declarations pass the same declaration and role checks as those of a
source library. The profile's `dim` primitives bind `PrimitiveBinding.dimension`,
as a source library's do.

- No package of a request with the field may have a `geometry_compat` export.
  Such a request is an error (`E_PROTOCOL`), and the message names the
  package.
- The profile is no package of the request. The reserved identities below
  are checked on the packages of the request, so a request cannot supply the
  profile, name it as a root or depend on it.
- The profile has no part in the price of the request
  ([`namespaceProgramWork`](appendix/limits.md)): the kernel prices the JSON
  of the request, which does not hold the profile, and the profile has no
  import and is no dependency, so it changes the price of no import.
- The kernel validates the namespace of the request's packages before it
  reports a decoded Fn signature with an inadmissible data component
  ([Indexed declarations](#indexed-declarations-and-rich-package-bodies)).

A package source that begins with `vastitas:compat:` is reserved. A request
may use one only as the package of a flat program: the one package of the
request and its root, with the identity of
[Flat programs and the legacy geometry](#flat-programs-and-the-legacy-geometry), no dependencies, no
`geometry_compat` export and one public root module. Any other package,
dependency target or root with such a source is an error (`E_PROTOCOL`).

<a id="algebraic-affine-forms"></a>

**Algebraic affine forms (Stage 2).** Presented affine declarations are
validated optional records of the envelope.

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

<a id="smooth-forms"></a>

**Smooth forms.** Smooth objects, smooth maps, tangent or cotangent fibers,
and tapes are validated optional records of the envelope.

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
[Indexed declarations](#indexed-declarations-and-rich-package-bodies)
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

<a id="metric-forms"></a>

**Metric forms.** Metrics, metric evidence, `flat` and `sharp` are validated
optional records of the envelope.

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

<a id="frame-forms"></a>

**Frame forms.** Frame declarations, the families of frames, frame arrays and
frame matrices, the frame parameter and the frame primitives are validated
optional records of the envelope.

- **Family representation.** A family may use the string `"frame"` (the
  frames of a smooth object, `Frame<X>`), `"frame_vector"` (the arrays of
  vectors in a frame, `Coords<b>`), `"frame_covector"` (the arrays of
  covectors, `CoCoords<b>`) or `"frame_map"` (the matrices of linear maps
  between two frames, `FrameMap<b, c>`).
- **Parameter.** `{"kind": "frame", "family": TypePath}` is a frame index of
  the family `family`. A family with such a parameter is a frame form,
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

The wire never carries a variance, a frame array, the frame matrix of a map
or a transition. It never carries the inverse of a constant frame either: the
kernel computes it, and a constant frame that declares an inverse is an
error (`E_FRAME`), even when the inverse is correct. A frame primitive
carries the paths of the frames it names, never their data. The kernel
copies the object, the matrix and the inverse of each named frame into the
binding, and the variance of an encoding or a decoding from its fiber family.
The declaration audit checks that each copy equals its declaration. A
binding record with any other field, such as a matrix, an inverse or an
object, is an error (`E_PROTOCOL`). The kernel expands every column in the
coordinates of the frame's object, within the limits of
[smooth metrics](appendix/limits.md#smooth-metrics) for a constant frame and
of [exact affine algebra](appendix/limits.md#exact-affine-algebra) for a
polynomial one. It checks `P·Q = Q·P = I` before acceptance.
[Frame declarations](language/frames.md#frame-declarations),
[Encoding and decoding](language/frames.md#encoding-and-decoding),
[Map arrays and transitions](language/frames.md#map-arrays-and-transitions),
[Contraction in frames](language/frames.md#contraction-in-frames) and
[Operand checks](language/frames.md#operand-checks) give the errors of the
declarations and the primitives. The
[`E_FRAME` row](appendix/diagnostics.md#e-frame) of the diagnostics
reference links these sections, and its
[`E_ENDPOINT` row](appendix/diagnostics.md#geometric-types) covers frame and
object mismatches of a call. The
[specification of `std::geometry::frame`](spec/std-geometry-frame.md) states
the laws of the forms.

<a id="physical-dimension-forms"></a>

**Physical-dimension forms.** The declarations of `nature::dimension` and
their families are validated optional records of the envelope.

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
against the Gram matrix of the metric it names.
[Physical dimensions](language/physical-dimensions.md) gives the errors of
the declarations, and the
[`E_DIMENSION` row](appendix/diagnostics.md#e-dimension) of the diagnostics
reference links its sections. The
[specification of `nature::dimension`](spec/nature-dimension.md) states what
an accepted interpretation guarantees.

<a id="spectral-forms"></a>

**Spectral forms.** The spectral families, the declarations of free modules,
endomorphism fields, spectra and branches, the definitions `trace_power` and
`char_coefficient` of a morphism declaration and the six spectral primitives
are validated optional records of the envelope.

- **Family representation.** A family may use the string `"free_module"`,
  `"endomorphism"`, `"spectrum"` or `"branch"`.
- **Free module.** `kind: "free_module"` carries `family` (path), `indices`
  (paths) and `basis`, the basis names as a list of strings in source order,
  besides the common `name`, `public` and `span`.
- **Endomorphism field.** `kind: "endomorphism"` carries `family`,
  `indices`, `module` (path), `rows` and `symmetric`. `rows` is a list of
  rows, each a list of polynomial expressions in the form above, and
  `symmetric` is a JSON boolean.
- **Spectrum.** `kind: "spectrum"` carries `family`, `indices`,
  `endomorphism` (path) and `fiber`, the name of the fiber coordinate as a
  string. The kernel's audit requires the name to be an identifier of the
  source grammar, so no strict keyword, that is no coordinate of the object
  and no basis name of the module of the field (`E_SPECTRAL`).
- **Branch.** `kind: "branch"` carries `family`, `indices`, `spectrum`
  (path), `localize` and `witness`, two polynomial expressions, and
  `exponent`, an unsigned decimal string of at most 64 digits.
- **Invariants.** The `definition` of a morphism declaration may be
  `{"kind": "trace_power", "endomorphism": TypePath, "power": String}` or
  `{"kind": "char_coefficient", "spectrum": TypePath, "index": String}`, with
  the power and the index as natural fields.
- **Primitives.** The binding `op` may be one of the six spectral
  operations below. A field of kind `coordinate` holds a basis name, and a
  field of kind `polynomial` a polynomial expression in the coordinates of
  the object and the fiber coordinate.

| Op | Fields |
| --- | --- |
| `annihilates` | `map_family`, `spectrum`, `element` (polynomial) |
| `action_entry` | `map_family`, `spectrum`, `element` (polynomial), `row` and `column` (coordinate) |
| `on_branch` | `map_family`, `line`, `branch` |
| `branch_differential` | `map_family`, `cotangent`, `line`, `branch` |
| `branch_projector` | `map_family`, `line`, `branch`, `row` and `column` (coordinate) |
| `average_at` | `map_family`, `line`, `average` |

| Form | Decoder |
| --- | --- |
| Spectral declarations | `declarationBody`, with `polyRows` and `certificateExponent` |
| Spectral family representations | `familyRepresentation` |
| Invariants | `morphismDefinition`, with `naturalField` |
| Spectral primitives | the families of `IndexedPrimitiveFamilies.lean`, through `primitive` and `wireArgument` |

The wire never carries a characteristic polynomial, an adjugate, a quotient,
the image of an invariant or an embedded declaration. The kernel computes
χ and the adjugate of every spectrum, the quotients of its checks and of
every gap witness, and the polynomial of every invariant, and it checks each
before acceptance, within the limits of
[spectral observations](appendix/limits.md#spectral-observations) and of
[exact affine algebra](appendix/limits.md#exact-affine-algebra). A spectral
primitive carries the paths of the spectrum or the branch that it names,
never their data. The kernel resolves the spectrum or the branch first,
copies the field, the spectrum and the branch into the binding, and expands
the element and the basis names. The declaration audit checks that each
copy equals its declaration. A record with any other field, such as
`characteristic`, `adjugate`, `quotient`, `map`, `rows` or `localize` in a
binding, is an error (`E_PROTOCOL`).
[Spectral observations](language/spectral-observations.md) gives the errors
of the declarations and the primitives. The [`E_SPECTRAL` row](appendix/diagnostics.md#e-spectral) of the
diagnostics reference links its sections, and its
[`E_ENDPOINT` row](appendix/diagnostics.md#geometric-types) covers object
mismatches of a call. The
[specification of `std::linalg::spectral`](spec/std-linalg-spectral.md)
states the laws of the forms.

<a id="physical-model-forms"></a>

**Transition-average and physical-model forms.** The declarations of
transition averages, conventions, models, calibrations, datasets and
comparisons, the family representations `"transition_average"`, `"model"`,
`"calibration"`, `"dataset"` and `"comparison"`, and the spectral primitive
`average_at` are validated optional records of the envelope.

Each record carries the common `name`, `public` and `span` and the fields
below. `family` is a path and `indices` a list of paths, as for the other
indexed declarations.

- **Transition average.** `kind: "transition_average"` carries `family`,
  `indices`, `branch` (path), `from` and `to`, two basis names as strings,
  and `numerator` and `denominator`, two polynomial expressions.
- **Convention.** `kind: "convention"` carries `value`, which is
  `"hbar_one"`.
- **Model.** `kind: "model"` carries `family`, `indices`, `hamiltonian`,
  `reading` and `convention` (paths), `prepare` and `observe`, two basis
  names as strings, `predicts` (path) and `regime`, a recorded text.
- **Calibration.** `kind: "calibration"` carries `family`, `indices`,
  `parameters`, a list of records `{"coordinate": String, "value": …,
  "uncertainty": …}`, `method`, which is `"type_a"` or `"type_b"`, and
  `reference` and `revision`, two recorded texts.
- **Dataset.** `kind: "dataset"` carries `family`, `indices`, `model` and
  `calibration` (paths), `coverage` and `points`, a list of records
  `{"coordinates": [{"coordinate": String, "value": …}], "value": …,
  "uncertainty": …}`.
- **Comparison.** `kind: "comparison"` carries `family`, `indices`,
  `dataset` and `calibration` (paths), `fingerprint`, a recorded text, and
  `verdict`, which is `"consistent"` or `"inconsistent"`.
- **Rational literals.** A value, an uncertainty, a coverage factor and the
  value of a coordinate of a point are rational literals: a polynomial
  expression `natural` or `fraction`, under at most one `neg`, the forms that
  the frontend reads. Each literal has at most `algebraCoefficientDigits`
  digits. Any other expression, such as a power, a sum or a coordinate, is an
  error (`E_PROTOCOL`), so that no value is larger than its literal.
- **Recorded texts.** A regime, a reference, a revision and a fingerprint
  hold at most `recordTextBytes` = 256 bytes of printable ASCII, from the
  space to `~`, other than `\` and `"`, the string literals that the
  frontend accepts there. Any other text is an error (`E_PROTOCOL`).
- **Observation.** `average_at` carries the fields of the table of
  [spectral forms](#spectral-forms).

| Form | Decoder |
| --- | --- |
| The six declarations | `declarationBody`, with `rationalLiteral`, `sourceMeasured`, `calibrated`, `sourcePoint`, `pointCoordinate`, `recordText`, `convention`, `calibrationMethod` and `verdict` |
| The five family representations | `familyRepresentation` |
| `average_at` | the family `average_at` of `IndexedPrimitiveFamilies.lean`, through `primitive` |

The wire never carries a certificate of a transition average, its trace
form, its unit quotient or its exponent, the fingerprint that the kernel
computes for a calibration, the verdict that it computes for a comparison,
or the data of the average that `average_at` names. The kernel computes the
trace form and the unit certificate of every average and checks them, within
the limits of [spectral observations](appendix/limits.md#spectral-observations)
and of [exact affine algebra](appendix/limits.md#exact-affine-algebra). It
computes the fingerprint of each calibration and compares it with the one
that a comparison records (`E_STALE`), and it computes each verdict again
and compares it with the recorded one (`E_ERRORBAR`). `average_at` carries
the path of its average, and the kernel copies the average, its branch and
its closed form into the binding; the declaration audit checks the copy. A
record with any other field, such as `certificate` or `trace` on an average
or `numerator` on `average_at`, is an error (`E_PROTOCOL`).
[Physical models](language/physical-models.md) and
[Transition averages](language/spectral-observations.md#transition-averages)
give the errors of the declarations, and the
[`E_MODEL`](appendix/diagnostics.md#e-model),
[`E_ERRORBAR`](appendix/diagnostics.md#e-errorbar) and
[`E_STALE`](appendix/diagnostics.md#e-stale) rows of the diagnostics reference
link their sections. The specifications of
[`nature::model` and `nature::errorbar`](spec/nature-physical-model.md) and
[`spectral.transition-average`](spec/std-linalg-spectral.md#spectral.transition-average)
state the laws of the forms.

<a id="gluing-forms"></a>

**Gluing forms.** The declarations of glued objects, covers, and
separation, manifold and projective claims are validated optional records of
the envelope. A smooth open has no record of its own. It is a
`kind: "affine_localization"` record of a
[principal open](#algebraic-affine-forms) whose `implementation` names a
`smooth_affine` implementation, and the kernel derives its presentation
from the smooth object that `object` names.

Each record carries the common `name`, `public` and `span` and the fields
below. A binding `{name, image}` is the record of the
[algebraic affine forms](#algebraic-affine-forms), with an image in their
polynomial form.

- **Glued object.** `kind: "glued"` carries `implementation` (path), `opens`
  (paths), and `forward` and `inverse` (bindings), the images of `by(…)` and
  of `inverse(…)`.
- **Cover.** `kind: "cover"` carries `object` (path), `opens` (paths) and
  `coefficients` (polynomials).
- **Separation claim.** `kind: "separated"` carries `glued` (path) and
  `witness`, one binding.
- **Manifold claim.** `kind: "manifold"` carries `glued` (path),
  `dimension`, an unsigned decimal string of at most
  `algebraCoefficientDigits` digits, and `witness`, one binding.
- **Projective claim.** `kind: "projective"` carries `glued` (path),
  `homogeneous` (names) and `charts`, a list of records
  `{"chart": path, "dehomogenized": String, "image": polynomial,
  "inverse": [{name, image}]}`.

| Form | Decoder |
| --- | --- |
| The five declarations | `declarationBody` of `IndexedDeclarationProtocol.lean`, with `binding`, `smoothDimension` and `polyExpr` |
| A smooth open | The case `affine_localization` of `declarationBody`; `elaborateSmoothOpens` of `IndexedGluingSource.lean` derives its presentation |

The wire never carries the presentation of a smooth open, a normal form of
an image, the stored chart transition, the order of the chart entries of a
projective claim or the index of their homogeneous coordinates: the kernel
computes them and checks every declaration again in its audit
(`GluingValidity.lean`). A record with any other field, such as
`transition` on a glued object, `certificate` on a separation claim or
`isomorphism` on a projective claim, is an error (`E_PROTOCOL`), and so is a
dimension that is no unsigned decimal string. `opens` of a glued object may
have any length on the wire, and the kernel rejects a length other than two
(`E_GLUE`). [Gluing declarations](language/gluing.md) gives the errors of
the declarations, and the [`E_GLUE` row](appendix/diagnostics.md#e-glue) of
the diagnostics reference links its sections.

### Resource statements and numerical forms

Scalar parameters use `kind: "value"` with `name`, `type` and `span`. Resource
statements add `kind: "value"` (`name`, `type`, pure `body`, `span`),
`kind: "call_value"` (`callee`, named `arguments`, owned `results`, scalar `value`,
`type`, `span`), and `kind: "branch_value"` (named `condition`, `yes`, `no`, `span`).
The existing Bool-valued `kind: "branch"` remains unchanged. These scalar bindings
accept only Nat/Int/Bool/Unit; the kernel independently reconstructs the pure Core
fragments and their exact source positions, owners, types and runtime slots.
No checked target, slot ID, trusted condition or resource handle is accepted in a
pure block. The internal resource component keeps its own schema.

A `realization` resource statement carries the unresolved `callee`, up to
three ordered `arguments` as paths, the local `result` name and the statement
`span`. The paths carry their own spans. The `representation` field holds
`real32`, `real64`, `complex32`, `complex64` or JSON null. The boolean
`into` distinguishes the destination of `run` from a freshly bound result.
The kernel resolves each operation in its source module and checks the
identity of the protected `monad::float` declaration.

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

The `indexed_declarations` array also admits
[numerical declaration profiles](linalg/maps-and-gemm.md#linear-implementations):
`scalar_base` and `linear_descriptor` representation objects preserve ideal
coefficient kinds and unresolved nominal base paths, with or without resource
functions. Declaration acceptance alone does not enable GEMM.

Resource bodies also support `kind: "numerical"` statements carrying `operation`
and `span`. Operations are `space` (name, unresolved implementation path,
dimension), `basis` (name, space), `map` (name, loan, source/target bases), and
`gemm` (left, right, output, mode, policy). Mode is `overwrite` or `accumulate`;
policy is explicitly `native_fast`. See [the source contract](linalg/maps-and-gemm.md#maps).
All names remain unresolved. Numeric IDs, trusted certificates, raw GEMM flags
and extra fields are rejected. The raw resource `action` schema has no public
GEMM operation. The checker composes independent path resolution, nominal
value checking and resource checks before native generation.

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
independently checked and contain no allocation IDs or trusted metadata. See [owned results](linalg/maps-and-gemm.md#owned-maps).
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
Unknown tags and fields fail closed. These forms do not add a
shape-polymorphic signature language.

[Typed transforms](internals/numerical-backend.md#wire-and-proof-boundary-of-transforms) add numerical
operations `involution`, `dual_space`, `conjugate_space`, `derived_basis`, `metric`
and `transform`. Their operands remain unresolved local names; `transform`
contains a strict operation naming derived bases or explicit metrics, never raw
native flags. Exact Gram entries are decimal strings. Corresponding dependent
parameter tags retain earlier space/basis/involution relationships and an explicit
orthonormal requirement for direct adjunction. Rust serializes these forms and
Lean decodes them, each with its own schema; unknown nested metadata fails
closed.

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
scratch write/release/read transition.

The `network` resource statement checks a finite graph. [Two-map networks](linalg/networks-and-packing.md#two-map-networks)
gives the source rules, and
[Two-map networks: graph and independent acceptance](internals/numerical-backend.md#two-map-networks-graph-and-independent-acceptance)
the wire schema. It is checked
independently before lowering to the existing numerical/storage path.

The `tensor` operations (`view`, `pack`, `contract3`) carry a bounded
ordered-axis/grouping schema.
[Packing and contraction](linalg/networks-and-packing.md#packing-and-contraction)
gives the source rules, and
[Tensor packing: independent checking and native execution](internals/numerical-backend.md#tensor-packing-independent-checking-and-native-execution)
the wire schema.
Packing is explicit and checked independently from nominal contraction authority.

The `tree` statement carries a bounded unresolved finite graph
and an explicit plan. A step of the plan has the `kind` `action`, `view`,
`regroup`, `rebind` or `join`, and an `action` step admits `borrow` and
`release`. Lean reconstructs producer
connectivity, nominal ports and actual resource transitions; see
[contraction trees](linalg/networks-and-packing.md#contraction-trees). The raw internal `regroup3` action
contains source/target loans, three physical dimensions and explicit input/output
groupings; it is not a public nominal-authority certificate.
The tensor operations also include `cached_pack`
(`name`, `source`, `target`) and `cached_contract3`
(`cache`, `left`, `right`, `output`, `policy`) envelopes. They carry unresolved
local names, never stamps or certificates. See [cached packing](linalg/networks-and-packing.md#caches).

## Declarations, types and expressions

The functions, generics and methods of a module, and their types, blocks,
statements and expressions, have these records. Every function, generic,
method, parameter, block, statement and expression has `span`:
`{ "start": 0, "end": 1, "line": 1, "column": 1 }` (UTF-8 byte offsets,
one-based Unicode-scalar columns). Types and indices have their containing
node's span. All arrays are ordered. With explicit `--lib` inputs of a flat
program, the driver parses each file separately and merges the declarations
into the one module of the program. Byte offsets occupy disjoint
source ranges, while line and column remain local to the original file. The
Rust driver retains the range-to-path map and formats backend diagnostics;
`file` identifies the entry input. The backend does not read library files.

Function: `{ "name": "f", "params": [...], "return_type": Type,
"body": Block, "public": Bool, "span": Span }`.
Parameter: `{ "name": "x", "ty": Type, "span": Span }`.
Block: `{ "statements": [Statement...], "result": Expr, "span": Span }`.

Generic: `{ "name": "add", "params": [{ "name": "left", "span": Span },
{ "name": "right", "span": Span }], "domain": [[Type, Type], ...],
"public": Bool, "span": Span }`. An empty domain is `[]`; a domain containing
the zero-argument key is `[[]]`. Each tuple contains exactly the declared number of concrete
scalar types.

Method: `{ "name": "add", "params": [Parameter...], "return_type": Type,
"requires": ["HasOrder"], "body": Block, "span": Span }`. The `name` of a
method is an unresolved reference path. Parameter `ty` fields may use the scalar selectors `Any` and `Number` as well as concrete
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
in dispatch keys/selectors or recursive Fn contracts.

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
are rejected.

Statements use a `kind` tag and always include `span`:

- `let`: `name`, `annotation: Type | null`, `value: Expr`.
- `unpack`: `value: Expr`, `scheme` binding name, `point` binding name.

Builtins are `Affine(K, n)`, `Base(K)`, `origin(X)`, `id(X)`,
`compose(g, f)`, `apply(f, p)`, `dim(X)`, `int(n)` (Nat to Int),
`pair(a, b)`, `pair_first(p)` and `pair_second(p)`. A `call` carries the
source spelling of its callee, so the operation `dim` is the callee `"dim"`,
and the callee `"dimension"` is an ordinary name that the checker resolves
like any other. An unresolved `dimension` is `E_NAME` with a
note.
Only the ring argument of `Affine`/`Base` accepts the reserved variable
`QQ` or `CInfReal`. Their use as ordinary values is invalid.

## Responses

Success: `{ "version": 10, "ok": true, "lean_source": "..." }` (the source
is present for emit and absent for check).
Failure: `{ "version": 10, "ok": false, "diagnostics": [
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
A response to a request of the epoch has the version `currentProtocol`. The
failure response to a request of [another version](#other-versions) keeps the
request's natural-number version. A missing or non-natural version is an
error (`E_PROTOCOL`, `IR version must be a natural number`) before the
decoder runs. An unreadable version, invalid JSON or non-UTF-8 stdin produces an
`E_PROTOCOL` JSON response at the version `currentProtocol`; stdin decoding
errors do not escape as uncaught IO exceptions. Before JSON parsing, the kernel
also answers `E_PROTOCOL` (at the same version) for requests over 1 GiB
(`requestBytes` of the compiler limits, by which the frontend bounds the requests
that it writes), nesting deeper than 16384
arrays/objects, numbers with more than 64 integer and fraction digits or an
exponent of more than two digits, and duplicate object keys (compared after
string decoding). Path lists are structured: each component is nonempty and
contains no `:`. Integer literal and Gram strings are ASCII decimal digits
(Gram entries may start with `-`); `_` separators are rejected.
Drivers display failure diagnostics before adding the note
`incompatible backend protocol version in failure response` to a failure
response of another version; a success response of another version is an
error (`E_PROTOCOL: incompatible backend protocol version`).

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
to such a name in the source of a flat program, which the frontend rejects.
The kernel declares the compiled reverse names only after acceptance, so a
reference to one in a request is an unbound name (`E_NAME`).

`ResourceSource.Wire.program` decodes the request, and its pure program is the
input of `Indexed.AuthoritySource.checkProgram`. Function syntax remains
separate from core syntax. Every lambda and function body is checked,
including unused functions; signature probes for abstract function parameters are confined to a separate
audit pass. Executable specialization memoizes definition/function-argument
IDs, erases function values and produces only direct calls. The unchanged
finite engine still checks all applicable method bodies. See
[Function values](stage1b.md) and
[Function specialization](internals/checking-pipeline.md#function-specialization).

A flat program has a reserved package identity independent of the displayed
filename ([Flat programs and the legacy geometry](#flat-programs-and-the-legacy-geometry)).
The compatibility profile of `legacy_geometry` is a closed, unresolved
declaration package; the request's namespace validates before the kernel adds
it, and a source dependency cannot resolve through it. The declaration and
profile, authority, Fn/dispatch and Core checks run on every program.
Internal Core formats are not alternative wire protocols.

Runtime representation: generated Lean code imports
`VastitasKernel.IndexedRuntime`, and `VastitasKernel.AlgebraRuntime` or
`VastitasKernel.SmoothRuntime` only when it uses them. A program that
selects the storage or the numerical runtime also imports
`VastitasStorageNative` or `VastitasGemmNative`. Scalar types map to Lean `Nat`, `Int`, `Bool`,
`Unit`; geometric objects, indexed points/morphisms and existential payloads use
the common runtime representations. Nominal typing is established before erasure.
The old runtime remains for retained legacy evaluation proofs.
The [finite migration acceptance map](internals/indexed-checker.md#finite-geometry-migration-acceptance) records checked
primitive result compatibility, source regressions and the limits of the
source/native proof claims. The compatibility profile is not an additional
wire version or a privileged semantic checker.
User symbols are always renamed to generated identifiers; source text is never
inserted as Lean syntax. Integers are validated decimal literals. The label of
an observation of `show!` is written as a quoted Lean string literal.

The generated `main` has type `IO UInt32`. It returns the exit status of the
`Int` result of the entry point, the result modulo 256 (`Int.emod`), and
writes nothing for the result. A resource entry point sets the status inside
the cleanup of its arenas and returns it after they are closed. With
observations, the entry point binds the top-level statements of the body of
`main` in order, up to the last observed one, writes `label = value` and a
line feed after each observed `let`, and returns the exit status of the rest
of the body.


## Package namespaces

The `packages` of a request ([The envelope](#the-envelope)) hold the
selected dependency closure, and `root` names the root package.

- Package: `source` (canonical manifest location), `name`, `version` (SemVer),
  `edition: "2026"`,
  `dependencies: [{ "alias": "math", "target": "/canonical/math/Vastitas.toml" }]`,
  `modules: [Module...]`, and an optional `geometry_compat` export
  ([Indexed declarations](#indexed-declarations-and-rich-package-bodies)).
  The three identity fields distinguish owners. A manifest location occurs
  once, regardless of how many dependency aliases use it.
  The Lean decoder independently requires the string `"2026"` on every
  package, including the protected synthetic package of a flat program with
  or without `--lib`. A missing edition, any other string or a value of another
  type fails with `E_PROTOCOL`. Edition is admission metadata; it does not
  change package identities or introduce another wire version.
- Module: `path: ["logical", "components"]`, `public: Bool`, `span`,
  `imports`, `functions`, `generics`, `methods`, and the optional records of
  the later sections. The root has path `[]`.
  Each non-root path has a declared parent. Its visibility belongs to the
  module declaration in that parent. There is no source-file owner field.
- Import: `path: ["package", "math", "add"]`, `alias`, `public`, `span`.
- Functions, generics and methods have the records of
  [Declarations, types and expressions](#declarations-types-and-expressions).
- Global `variable.name` and `call.callee` preserve unresolved `::` paths.
  Locals and dependent indices remain lexical names. There are no
  frontend-supplied function IDs.

Lean validates package/module/declaration uniqueness, acyclic dependencies,
imports and reexports (including unused ones), visibility on every traversed
path, and exact-module generic method authority. Each resolution shares a
4096-member work budget across path components and aliases, as well as a
nesting bound; exhaustion returns `E_LIMIT` at the referring source span or,
inside a chain of aliases, at the import declaration where the bound ran out.
Completed dependency nodes are memoized, so duplicate aliases do not cause
repeated graph traversal. Unknown namespace metadata fields, including
claimed owners, are rejected (`unknown protocol field '<name>'`), and so are unknown fields in nested type/index, parameter,
expression, statement, block, declaration and span records and in the
envelope; no record tolerates an unrelated hint. Invalid membership scalar
names are rejected as `E_TYPE` before constructing their namespace authority
graph.

A public reexport preserves
its original target and requires a public declaration; private intermediates
must be accessible from the reexporting module. Private declarations are
visible from their declaring module and descendants only. Parent names are
not implicitly in scope. Dependency aliases are only initial path components.

`Indexed.AuthoritySource.checkProgram` validates the namespace and checks
every body in an audit pass and in an executable pass, and then the Core.
`Namespace.lower` assigns symbols from package identity + logical module path
+ declaration name; it lowers the headers that the authority assembler and the
dispatch families read. Only an ordinary root-package root-module `main`
becomes the core entrypoint.

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
for output collision protection. See [Packages](packages.md) and
[Modules](language/modules.md) for source syntax, commands and file loading.


## Finite abstract declarations

A module may contain `abstract_types`, `subtypes` and `abstract_methods`
arrays; absent arrays mean empty, and present arrays must be arrays. Each
abstract type has `name`, `parents`, `public` and `span`. A parent is an unresolved `{path: [String],
span: Span}`; an empty parent list means the default Any parent. Each subtype
has `scalar`, `target` (an unresolved path plus span), and declaration `span`.
Path components must be nonempty. Method selector `named` types retain their
unresolved path spelling until Lean resolves them in the defining module. No
selected IDs or hierarchy matrices are accepted from the frontend.

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

## Scoped edits and assembly

Edit declarations and the assembly keep every package identity, declaration,
hierarchy and unresolved path. There is no cached or pre-approved assembly
input. See [Edit authority](language/edit-authority.md) for the source rules
and [Edit authority acceptance](verification.md#edit-authority-acceptance)
for the proof boundary.

Each module additionally permits `grants: [Grant...]`,
`contributions: [Contribution...]` and `assembly: Assembly` (each optional; an
explicit `null` is rejected).
The decoded module determines each declaration's owner; the wire cannot assert
an issuer, owner, accepted flag or stable identity independently of that module.

```text
Grant = { name, target: [identifier...], grantee_package: package-name,
          grantee_path: [identifier...], region: [[scalar...], ...],
          delegable?: Bool, public, span }
Contribution = { name, target: [identifier...], methods: [Method...], public, span }
Assembly = { source: [AssemblyItem...], events: [Event...], span }
AssemblyItem = { kind: "family", target: [identifier...], span }
             | { kind: "borrow", grant: [identifier...], label: identifier | null, span }
             | { kind: "delegate", delegation: [identifier...], label: identifier | null, span }
             | { kind: "apply", contributions: [[identifier...]...], span }
             | { kind: "transfer", declaration: [identifier...], span }
             | { kind: "close", span }
Event = { op: "borrow", grant: [identifier...], loan: identifier, span }
      | { op: "apply", contribution: [identifier...], loan: identifier | null, span }
      | { op: "return", loan: identifier, span }
      | { op: "seal", target: [identifier...], span }
```

[Named recipients](#named-recipients) gives the rules of `grantee_package`.
A program with contributions or an assembly and no record of the list of
[Flat programs and the legacy geometry](#flat-programs-and-the-legacy-geometry)
has `legacy_geometry`.

Grant paths refer only to the selected dependency closure. Grant/contribution
IDs derive from package identity, module path and declaration name; method
ordinals distinguish methods within a contribution. Unknown fields in these
records and events are rejected. Ordinary expressions keep the records of
[Declarations, types and expressions](#declarations-types-and-expressions). A maximum of one assembly is permitted, exactly at
the root package's root module. An omitted root assembly is an empty trace;
all declaration, unapplied-body and completion audits still run.

The required `source` array records parsed family headers, lexical commands and
closing braces. Each grouped application keeps its paths together. Items have
nonempty, nonoverlapping byte spans in source order. A closing brace spans
one byte. The whole assembly spans its first header through its final brace.
After checking authority, the kernel expands these items with a fresh loan-name
counter shared by all blocks and compares every event, path, label and span.
A receipt pins both arrays. Rust tokenization and the original file mapping
remain inputs to this check.

Each source `assemble path { … }` contributes its events to this single
array in source order, ending in a seal of `path` at the closing brace.
Loan blocks emit returns at their closing braces. An `apply a, b;`
statement emits two applications in order with the same statement span.
The kernel checks every edit's independently resolved family against
the seal of its block, even for a borrow that applied no contribution.
Duplicate seals, including through aliases, and an unsealed suffix reject.

The kernel independently reconstructs grant and contribution lowering from
original scopes, checks exact module authority and unresolved references,
audits every exclusive borrow/apply/return/seal transition and complete replay
provenance, and requires all loans returned and edited generics sealed. It checks
completion in the final immutable environment, including domain-union coverage,
contract results, all-key ambiguity and each installed method's final winning
footprint. All applied bodies and every applicable ground instance of unapplied
contributions are checked; unapplied declarations never become dispatch candidates.
The executable Core comes from the source bodies through the function compiler
and the Core audits of every program.

The shared limits allow 4096 assembly events, 4096 contribution methods in the
whole closure, and 4096 ground functions in the separate unapplied-body audit.
Every per-event state and transition audit runs; the audits of one trace share
a 200,000,000-unit budget, charged before each audit, and exhaustion reports
`E_LIMIT`. An assembly of more than 4096 events is a decoder error
(`E_PROTOCOL`).
Existing per-family key, hierarchy, type-depth and specialization bounds remain.
No digest in this same input proves filesystem or author authenticity.

## Nested loans and current edit authority

Grants may carry `delegable: Bool` (default false). Modules may add:

- `delegations: [Grant...]`: the same record shape, with the issuer derived from
  its declaring module. It is usable only through an active explicitly delegable
  parent loan held by that module, with the same target and a contained region.
- `transfers: [{name, target, grantee_package, grantee_path, public, span}]`:
  a named permanent transfer operation, declared by its issuer module. The exact
  recipient must already exist in the selected closure.

The additional assembly events are
`{op: "reborrow", parent: String, delegation: Path, loan: String, span}` and
`{op: "transfer", declaration: Path, span}`. Unknown fields are rejected;
claimed issuer/current-owner IDs, accepted flags and supplied histories are not
wire fields.

`Authority.assemble`, which `Indexed.AuthoritySource.checkProgram` calls,
reconstructs histories and complete delegation chains and audits each
transition against an independent relation. `checkProgram` performs the same
namespace, membership, final dispatch, footprint, all-body and Core audits.
The original function identity never changes. A returned loan or transfer
preserves contributions and unresolved completion obligations. The final
winning region is contained in every ancestor's grant, and transfer requires
no outstanding loans. See [source semantics](language/edit-authority.md#transfers) and
[the proof boundary](verification.md#edit-authority-acceptance).

## Indexed declarations and rich package bodies

Each module may add `indexed_declarations`, defaulting to an empty array.
Every body of a request uses the rich source path, with the indexed
annotations, typed packs and ordered-field unpacks below.

A declaration has `{kind,name,public,span,...}` with these additional fields:

| Kind | Fields |
| --- | --- |
| `marker` | None |
| `implementation` | `marker:TypePath`, `representation:"affine_descriptor"`, `capabilities:["origin"\|"dim"]` |
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
| `dim` | `domain:ObjectType` |
| `compose` | `map_family:TypePath` |
| `apply` | `map_family:TypePath`, `point_family:TypePath` |

The source and the wire spell the op and the capability of the operation
`dim` as `dim`, as in `dim((Scheme, QQ))` and `capabilities(origin, dim)`.
The spelling `"dimension"` is an error (`E_PROTOCOL`) in both places: the op
is an `unknown indexed primitive contract` and the capability an
`unsupported implementation capability`. The kernel decodes both to the same
values as before the spelling changed: the op binds `PrimitiveBinding.dimension`
and the capability is `Capability.dimension`.

The field set of every operation, here and in the optional forms, comes from
one table: the families of `lean-kernel/VastitasKernel/IndexedPrimitiveFamilies.lean`.
Each family names an `op`, its fields with their kinds in wire order, and
whether it is one of the Stage 2 and later forms (`algebraic`). The decoder
admits every family, and admits a binding only with its family's fields. The
frontend reads `algebraic` to decide `legacy_geometry`
([Flat programs and the legacy geometry](#flat-programs-and-the-legacy-geometry)). The frontend reads `src/primitive_table.rs`, which
`scripts/check_primitive_table.py` generates from the same families, and
writes the fields in that order.

Data annotations retain concrete scalar `named` and homogeneous `pair` types and add
`{kind:"indexed_object",domain:TypePath,marker:TypePath}` and
`{kind:"indexed_apply",family:TypePath,arguments:[Argument]}`.
Arguments are `{kind:"name",reference:TypePath}` or
`{kind:"natural",value:String}`; expected parameter kinds determine whether a
name refers to a declaration or a preceding local object binding.
Fn types use the same nesting limit at every parameter and result.
The decoder accepts nested function, `finite_hom`, `named`, `pair`, `point`,
`morphism` and `pointed` components. Other tags produce `E_PROTOCOL`.
For each `finite_hom`, the kernel resolves the category and both endpoints in
the writing scope. A static use containing a Hom records these identities in
its recursive `signature` in the function revision. A decoded component
outside `Nat`, `Int`, `Bool`, `Unit`, finite Hom or Fn produces `E_TYPE` at the parameter,
function, lambda or `let` statement that declares it. The kernel reports the
first such type in the order of the program, after the namespace of the
request validates.

Ordinary expression and statement forms retain their schemas. Explicit packages
use `{kind:"indexed_pack",package:Type,witness:Expr,fields:[Expr],span}` and
`{kind:"unpack_fields",value:Expr,witness:String,fields:[String],span}`.
The legacy `pack`/`unpack`, named Scheme/CInfScheme and
`point`/`morphism`/`pointed` annotation schemas are decoded with their exact
fields. Their meaning requires exactly one validated compatibility export: a
`geometry_compat` export of a package, or the compatibility profile of
`legacy_geometry`. Inferred legacy pack types are an internal body-only form,
never a signature escape hatch.

A package may add `geometry_compat` (omission means no export; `null` is invalid):

```text
{
  point: String, morphism: String, pointed: String,
  compose: String, apply: String,
  scheme: GeometrySetting, smooth: GeometrySetting
}
GeometrySetting = {
  domain: String, marker: String, base_object: String,
  affine: String, base: String, origin: String, identity: String, dim: String
}
```

These are unresolved `::`-separated paths, as in the manifest’s
`[geometry_compat]`, `[geometry_compat.scheme]` and `[geometry_compat.smooth]`
tables. The slot that the manifest spells `dimension` is `dim` on the wire,
and the spelling `dimension` there is an error (`E_PROTOCOL`, `unknown
protocol field 'dimension'`). The kernel decodes it to the entry `dimension`
of its `GeometrySetting`, which names the primitive of `dim`, as `identity`
names the primitive of `id`. Lean resolves them in the exporting package’s root scope, preserving
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
acceptance.

`ResourceSource.Wire.check` retains the decoded request and the result of
`Indexed.AuthoritySource.checkProgram` on its pure program. The authority
assembler, all-key footprints, every applied/unapplied body, independent Fn
audits and both Core checks therefore run before success. For a program
without a resource entry, `emit` passes the compiled module of the pure
program to `Indexed.Core.Codegen.generate`: the executable Core with its
reverse passes compiled into Core and checked again by the Core audit. The
generator rechecks it independently.
See [source syntax and limitations](indexed-source.md).

## Other versions

A request whose `version` is a natural number other than `currentProtocol` is
an error (`E_PROTOCOL`). The kernel reads no other field, so the request fails
closed even when the rest of it is a request of the epoch. The message names
the version and asks for matching binaries:

```text
IR protocol version 9 is not protocol 10 of this kernel; the compiler and the kernel must come from the same Vastitas build: rebuild them together
```

The failure response keeps the request's version, so a driver of that
version shows the diagnostic as it is. The rule covers the retired versions 2
to 9, the versions 0 and 1, which were never public, and every later number.
No version falls back to another decoder, and the kernel converts no request
of another version. The wire is a boundary between a driver and a kernel of
the same build, not an interface for hand-written requests:
[History](#history) lists the retired versions.

The version check comes after the steps that read the request as a whole:
the byte bound, UTF-8 decoding, `WireScan.scan` and the JSON parser. A
request that fails one of them is an error (`E_PROTOCOL`) with the message of
that step and the response version `currentProtocol`, whatever its version.
For example, `{"version":9,"version":10}` gets the scanner's message
"duplicate JSON object key 'version'", and a request of version 9 with the
number `1e100` in another field gets "JSON number exponent exceeds 2
digits".

The kernel reads `version` with `getObjValAs? Nat`. Lean's JSON parser keeps
a number as an integer and a count of decimal places, and only a
non-negative integer without decimal places is a natural number:

- `1e1`, `10e0` and `1.0e1` are read as 10, and the request is decoded
  under the epoch.
- `10.0`, `100e-1` and `9.0` keep a decimal place. The request is an error
  (`E_PROTOCOL`) "IR version must be a natural number" with the response
  version `currentProtocol`, not the message above. So is a negative
  number, a string or a missing `version`.
- `-0` is read as 0 and gets the message above with the response version 0.

## Expected-rejection doctest consumer (reference only)

The [doctest result contract](reference/compiler-tools.md#doctest-result-reference) separates
ordinary language rejection from protocol, transport, and execution failure.
It reuses the diagnostic payload above without changing this wire protocol or
the driver's preservation of diagnostics on incompatible failure responses: its
regressions judge a version-9 failure response to a version-10 request as a
protocol mismatch.
The Python reference and fixture regressions do not implement production driver
receipts, doctest execution, or official package admission.

## Tests

- `tests/protocol_epoch.rs` pins the one epoch.
  `the_frontend_the_kernel_and_version_share_one_epoch` checks that the
  driver, the kernel's `currentProtocol` and `--version` name the same number,
  that the kernel answers the driver's requests at that version and that it
  rejects them at version 9. `every_version_below_the_epoch_fails_closed`
  takes the versions from 0 to `currentProtocol` − 1, and
  `the_next_protocol_fails_closed` takes `currentProtocol` + 1. Each sends a
  flat and a package request at each version, in the shape of the epoch and,
  for 2 to 9, in the shape that the version had, to `check` and `emit`; each
  answer is `E_PROTOCOL` with the message of [Other versions](#other-versions)
  and the request's version.
  `a_protocol_nine_envelope_relabelled_as_the_epoch_keeps_input_unknown`,
  `a_flat_module_labelled_as_the_epoch_is_rejected` and
  `the_dimension_spelling_of_dim_is_rejected` reject the field `input`, a flat
  module and the spelling `dimension` of the `dim` op, capability and
  `geometry_compat` slot. `a_kernel_of_another_epoch_is_reported_as_a_mismatched_build`
  shows the diagnostic of a kernel of another epoch through the CLI.
- `tests/driver_issues.rs::version_reports_package_and_the_wire_protocol`
  pins the output of `--version`, and
  `tests/stabilization.rs::unknown_wire_version_is_echoed_with_the_matching_binaries_message`
  the response to a version that the kernel does not accept.
- `tests/protocol_shape.rs::flat_requests_reject_unknown_fields_in_every_nested_record_shape`
  adds a field to every record shape of the requests of flat programs, the
  envelope included, and requires `E_PROTOCOL`.
  `public_decoder_rejects_unknown_fields_in_every_captured_record_shape`
  does the same for the requests that the driver writes for the example
  packages, and `frame_and_nature_records_reject_unknown_fields` for every
  frame and physical-dimension record of the fixture package
  `tests/fixtures/frame-dimension-declarations/`.
  `the_envelope_admits_no_hint_and_checks_membership_scalars` and
  `malformed_versions_and_non_utf8_input_return_protocol_json` of the same
  file pin an unknown top-level field, the scalar names of memberships and the
  responses to a request that the kernel cannot read.
- `tests/frame_dimension_declarations.rs::frame_and_nature_declarations_decode_in_the_current_envelope`
  and `tests/frame_primitives.rs::frame_primitives_decode_and_the_kernel_accepts_them`
  decode the frame and physical-dimension forms.
  `raw_wire_rejects_forged_frame_bindings` of the second file rejects a
  natural field that is not an unsigned decimal string of at most 64 digits,
  and a frame binding without one of its fields.
- `tests/spectral_declarations.rs::spectral_forms_decode_alone`,
  `tests/spectral_primitives.rs::spectral_primitives_decode_and_check` and
  `tests/spectral_observations.rs::the_example_emits_from_the_frontend_request`
  decode the spectral forms.
  `raw_wire_rejects_certificates_and_forged_spectral_fields` of the first
  file, `raw_wire_rejects_embedded_spectral_data` of the second and
  `raw_wire_rejects_spectral_certificates_and_forged_maps` of the third
  reject a certificate, an image, an embedded declaration, a missing field
  and a field of the wrong kind.
- `tests/gluing.rs::the_stage7_forms_serialize_to_their_records` pins the
  record of each gluing form and the `affine_localization` record of a
  smooth open. `forged_stage7_records_are_rejected_by_the_kernel` of the
  same file rejects forged images, opens, implementations, witnesses,
  dimensions, coefficients and homogeneous coordinates (`E_GLUE`), the
  fields `transition`, `certificate` and `isomorphism`, and a dimension that
  is no decimal string (`E_PROTOCOL`).
- `tests/edit_authority.rs::named_recipient_wire_rejects_forged_locations_and_unselected_records`
  and `module_recipients_are_unsupported_and_authority_keeps_optional_runtime_boundaries`
  pin the recipient fields.
- `tests/show.rs::show_adds_observations_to_the_flat_request_and_check_is_unchanged`
  pins the request of a flat program with and without observations of
  `show!` and their wire field, `show_stands_beside_legacy_geometry_in_flat_input`
  builds and runs a flat program that shows a value beside the legacy
  geometry, also from a `--lib` input, and
  `the_kernel_refuses_tampered_observations` refuses an observation
  outside `main`, of a function value, of a missing statement, an empty list
  and a foreign field. The kernel regression
  `VastitasKernel.ObservationRegression` decodes, checks and generates the
  observations without the driver.
- `tests/protocol_shape.rs::package_requests_carry_legacy_geometry_exactly_without_indexed_records`
  and `flat_requests_carry_legacy_geometry` pin the requests that carry
  `legacy_geometry`: every flat program and the package programs without a
  record of [Flat programs and the legacy geometry](#flat-programs-and-the-legacy-geometry),
  and no other. The kernel regression
  `VastitasKernel.CompatibilityProfileRegression` checks that the kernel
  accepts and generates a flat and a package program with the legacy geometry
  with the field and rejects them without it. It rejects the field with a
  value other than `true` and beside a `geometry_compat` export, and the
  profile's identity in a request.
- The kernel regressions `VastitasKernel.IndexedWireRegression` and
  `VastitasPublicTest.AuthorityRegression` decode and check requests without
  the driver. `VastitasKernel.FrameDeclarationRegression`,
  `VastitasKernel.FrameRegression` and `VastitasKernel.NatureRegression`
  decode every frame and physical-dimension form.
  `VastitasKernel.SpectralDeclarationRegression` and
  `VastitasKernel.SpectralRegression` do the same for the spectral forms.
  `VastitasKernel.ModelDeclarationRegression` decodes every transition-average
  and physical-model form, with the exact fields, the rational literals and
  the recorded texts; `VastitasKernel.AverageRegression` and
  `VastitasKernel.NatureModelRegression` check the averages, the models and
  the data that the kernel accepts and rejects.
  `VastitasKernel.GluingRegression` checks the glued objects, covers and
  claims that the kernel accepts and rejects, in both sites, without the
  driver. `VastitasKernel.NamespaceRegression` tests the
  shared namespace code and `Authority.assemble` on Lean values and decodes
  no request.
  `bash scripts/check_kernel_regressions.sh` builds them.

## History

- The wire had the versions 2 to 9 before the cutover to the single schema
  epoch 10 of [#533](https://github.com/MGYamada/Vastitas/issues/533), which
  retired them together, with their decoders, their checkers and their
  theorems. Protocol 2 was a flat module and protocol 4 a flat module or a
  package by its field `input`; protocols 3 to 6 were packages, checked
  through `Indexed.LegacySource`, which appended the compatibility profile to
  every program. Protocol 7 added indexed declarations
  (`Indexed.Wire.check`), protocol 8 resource functions and numerical
  representations, and protocol 9 named recipients and the Stage 2 to Stage 6
  forms as optional fields. Before the cutover the driver wrote every program
  as protocol 9, flat programs and the former legacy packages with
  `legacy_geometry`. A development-only harness compared those requests with
  the requests of the retired versions before the cutover, and the cutover
  removed it.
- The `input` field, the spelling `dimension` of the `dim` op, capability and
  `geometry_compat` slot, the version gates of the optional forms and the
  recipient field `grantee_source` of protocols 5 to 8 belonged to the
  retired versions.
- The doctest result contract of
  [Expected-rejection doctest consumer](#expected-rejection-doctest-consumer-reference-only)
  belongs to [#236](https://github.com/MGYamada/Vastitas/issues/236).
- [Source migrations](appendix/history.md#source-migrations) records the
  change of the recipient syntax.
