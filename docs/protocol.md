# Compiler protocols (versions 2–8)

The Rust frontend sends one JSON object on stdin to `vastitas-kernel check`
or `vastitas-kernel emit`. The Lean backend writes one response on stdout;
tool logs belong on stderr. Neither the frontend's annotations nor names are
trusted. The backend allocates nominal identities while checking lexical
bindings; the wire format cannot supply a trusted object identity.

Request: `{ "version": 2, "file": "input.vast", "functions": [...],
"generics": [...], "methods": [...] }`. All three declaration arrays are
present, including when empty. Protocol 3 uses the separate namespace request
below. Protocol 4 adds abstract declarations, protocol 5 adds package edit assemblies,
protocol 6 adds nested loans and permanent authority transfer, and package-only
protocol 7 adds indexed declarations and rich bodies as described below.

Package-only [protocol 8](resource-source.md) adds unresolved `resource_functions`
to modules while preserving the full protocol-7 declaration/Fn/dispatch/authority
checks. Each resource function carries `name`, `parameters`, ordered owned
`results`, resource `body`, pure `value_type`/`value_body`, `public` and `span`.
Calls carry unresolved paths and local names, not checked IDs. The strict schema
is defined by `storage.rs::source` and `ResourceProtocol.lean`. Emit responses
include `storage_runtime: Bool` and `numerical_runtime: Bool` to request optional
native packages only when the actual entry needs them. A numerical requirement
also requires storage and explicit driver build configuration. The [internal storage component schema](storage-ir.md)
is not an alternative public envelope; top-level `resources` and downgraded
`resource_functions` must not be silently discarded by legacy protocol 2.
Package requests never fall back to protocol 2. Other versions are rejected.

Protocol 8 also admits [numerical declaration profiles](numerical-declarations.md)
in the existing `indexed_declarations` array: `scalar_base` and
`linear_descriptor` representation objects preserve ideal coefficient kinds and
unresolved nominal base paths. They require version 8 even without resource
functions. Protocol 7 retains only `"affine_descriptor"`; it rejects these new
representations. Declaration acceptance alone does not enable GEMM.

Resource bodies also support `kind: "numerical"` statements carrying `operation`
and `span`. Operations are `space` (name, unresolved implementation path,
dimension), `basis` (name, space), `map` (name, loan, source/target bases), and
`gemm` (left, right, output, mode, policy). Mode is `overwrite` or `accumulate`;
policy is explicitly `native_fast`. See [the source contract](numerical-values.md).
All names remain unresolved. Numeric IDs, trusted certificates, raw GEMM flags
and extra fields are rejected. The old raw resource `action` schema does not
acquire a public GEMM operation. Version 8 composes independent path resolution,
nominal value checking and actual resource checks before native generation.

Numerical GEMM optionally carries `alpha`/`beta` operands, each either
`{kind:"literal",value:<resource literal>}` or `{kind:"loan",loan:<local name>}`.
Absent fields retain alpha one and beta zero/one. Explicit null and unknown
fields reject. Overwrite accepts no beta operand; accumulate requires initialized
output even for beta zero. A coefficient loan must be a matching initialized
readable 1x1 region disjoint from output. The checked allocation/offset reaches
native execution, where the current scalar is read before output writes.
See [coefficient semantics](numerical-values.md#explicit-and-computed-coefficients).

Owned numerical inputs use parameter `kind:"owned_map"` with `name`, `source`,
`target` and `span`. Result `type` may be `{kind:"owned_map",source,target}`;
the original `{scalar,elements,initialized}` raw owned-result form is unchanged.
Both refer only to preceding input basis contracts. Numerical operation
`owned_map` supplies `name`, raw `owner`, `layout`, `source` and `target` and moves
initialized storage into the interpretation. `borrow_owned` supplies `name`,
`owner` and `access`, using the actual stored layout; `owned_view` supplies `name`,
`loan` and `owner`, retaining exact allocation/layout/bases. These forms are
independently checked, contain no allocation IDs or trusted metadata, and are
rejected by older decoders. See [owned results](numerical-values.md#owned-numerical-results).
The bounded generative form uses parameter `kind:"owned_map_to"` with `name`,
`source`, `dimension`, `span`, and result `type:{kind:"owned_map_to",source,dimension}`.
Numerical `pack_map` takes `name,owner`; `unpack_map` takes
`package,space,basis,owner`. These are unresolved names; no allocation/brand or
success metadata is accepted. See [owned-map packages](owned-map-packages.md).


Resource parameters additionally support `kind: "space"` with unresolved
`implementation` and static `dimension`, `kind: "basis"` naming an earlier
`space` parameter, and `kind: "map"` naming earlier `source`/`target` basis
parameters plus `access` and `initializes`. Every parameter includes `name` and
`span`. [Dependent input checking](numerical-values.md#dependent-numerical-inputs)
preserves actual caller identities and creates scoped child loans for maps.
Unknown tags/fields fail closed on older kernels; these are additive protocol-8
forms. They do not add a shape-polymorphic signature language.

[Typed transforms](linear-transforms.md#wire-and-proof-boundary) add numerical
operations `involution`, `dual_space`, `conjugate_space`, `derived_basis`, `metric`
and `transform`. Their operands remain unresolved local names; `transform`
contains a strict operation naming derived bases or explicit metrics, never raw
native flags. Exact Gram entries are decimal strings. Corresponding dependent
parameter tags retain earlier space/basis/involution relationships and an explicit
orthonormal requirement for direct adjunction. Rust and Lean decode these forms
together; old envelopes and unknown nested metadata fail closed.

[Vector evaluation](vector-evaluation.md) adds `vector` (`name`, `loan`, `basis`),
`conjugate_vector` (`name`, `parent`, `basis`, `involution`) and `evaluate`
(`left`, `right`, `output`, `operation`, `mode`, `policy`, optional `alpha`/`beta`).
The nested operation is strictly `{kind: "dual"}` or
`{kind: "hermitian", metric: <local name>}`. Vector parameters use `kind: "vector"`
with `name`, `basis`, `access`, `initializes`, `span`. Actual vector and form
provenance, child loans, scalar output and emitted flags are reconstructed by
the independent checker; no supplied origin or native flag grants authority.

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
See [Stage 1a](stage1a.md) for the exact specialization order and limits.

Expressions use a `kind` tag and always include `span`:

`pair`, `pair_first`, and `pair_second` use ordinary `call` nodes. Both constructor
operands are inferred independently, with no expected-type conversion. Pair
values can occur in ordinary function contracts and data expressions, but not
in dispatch keys/selectors or recursive Fn contracts. These additions use the
existing protocol-2 and protocol-3 envelopes; older kernels reject the new tag.

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
`compose(g, f)`, `apply(f, p)`, `dimension(X)`, and `int(n)` (Nat to Int).
Only the ring argument of `Affine`/`Base` accepts the reserved variable
`QQ` or `CInfReal`. Their use as ordinary values is invalid.

Success: `{ "version": 2, "ok": true, "lean_source": "..." }` (the source
is present for emit and may be absent for check).
Failure: `{ "version": 2, "ok": false, "diagnostics": [
{ "code": "E_TYPE", "message": "...", "span": Span,
  "notes": [{ "message": "...", "span": Span }] }] }`.
Notes carry related source locations, including object introduction sites. They
are diagnostic metadata, not trusted identity evidence. Current backends emit
an empty array when there are no notes; drivers also accept omitted notes.
Failure responses preserve any readable natural-number request version, even
when unsupported. An unreadable version or invalid JSON uses version 2 as the
fallback. `supportedProtocolVersions` in the kernel defines the complete wire
version list. Drivers display failure diagnostics before adding a version
mismatch note; a mismatched success response is always rejected.

Frontend and backend use the same codes for name violations: `E_SHADOW` for a
binding conflicting with a function/generic, `E_RESERVED` for a reserved name,
`E_NAME` for an invalid or unresolved name (including an undeclared generic),
and `E_DUPLICATE` for repeated declarations or local bindings. `E_ARITY` and
`E_TYPE` identify argument-count and type violations. `E_LIMIT` reports bounded
implementation resources; core checking and dispatch lowering share the
4096-unit per-function checking-budget diagnostic. Diagnostic wording does
not change the acceptance rule or its proof boundary.
`E_CAPTURE` rejects references to outer lambda bindings; `E_STATIC_CALL`
rejects function values with unresolved or differing runtime targets.
Higher-order specialization has a separate 4096-instance bound.

The checker rejects recursion (including mutual recursion), duplicate function
names, reserved names, unbound references, incompatible annotations, escaping
nominal identities, and a main signature other than `fn main() -> Int`.
Check accepts modules without main; emit requires main.
Source declaration order does not constrain function calls.
The `__vastitas_` prefix is reserved for hygienic specialization names and is
rejected in source binders and references, including forged wire requests.

`decodeSurfaceModule` in `SurfaceProtocol.lean` decodes the extended request and
`Indexed.LegacySource` converts its unresolved syntax into the common
`Indexed.AuthoritySource.checkProgram` input. The old `checkSurfaceProgram`
remains an internal API with separate retained proofs. Function syntax remains separate from core
syntax. Every lambda and function body is checked, including unused functions;
signature probes for abstract function parameters are confined to a separate
audit pass. Executable specialization memoizes definition/function-argument
IDs, erases function values and produces only direct calls. The unchanged
finite engine still checks all applicable method bodies. See [Stage 1b](stage1b.md).

After the original wire decoder, protocols 2–6 adapt source functions, methods,
contributions and namespace metadata before semantic elaboration. Flat input uses
an adapter-owned module identity independent of the displayed filename. The
adapter supplies a closed, unresolved compatibility declaration package because
these wire versions cannot carry indexed declarations. The original namespace
must validate before injection; a source dependency cannot resolve through the
private profile. The same declaration/profile, authority, Fn/dispatch and Core
checks used by protocol 7 remain mandatory. Old wire versions continue to reject
new declaration fields. Internal Core formats are not alternative wire protocols.

Runtime representation: generated Lean code imports only
`VastitasKernel.IndexedRuntime`. Scalar types map to Lean `Nat`, `Int`, `Bool`,
`Unit`; geometric objects, indexed points/morphisms and existential payloads use
the common runtime representations. Nominal typing is established before erasure.
The old runtime remains for retained legacy evaluation proofs.
The [finite migration acceptance map](geometry-migration.md) records checked
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
nesting bound; exhaustion returns `E_LIMIT` at the referring source span.
Completed dependency nodes are memoized, so duplicate aliases do not cause
repeated graph traversal. Unknown namespace metadata
fields, including claimed owners, are rejected. A public reexport preserves
its original target and requires a public declaration; private intermediates
must be accessible from the reexporting module. Private declarations are
visible from their declaring module and descendants only. Parent names are
not implicitly in scope. Dependency aliases are only initial path components.

`Namespace.lower` assigns symbols from package identity + logical module path
+ declaration name; it also renames local bindings hygienically, including
geometric type indices. Only an ordinary root-package root-module `main`
becomes the core entrypoint. It checks every dependency and body, then the
existing surface/dispatch checker independently checks all applicable method
specializations and the final core. Protocol 2 keeps its flat namespace.
The namespace audit re-resolves recorded references and checks exact method
owners before calling the existing surface acceptance path.

`E_VISIBILITY` identifies private access or a nonpublic reexport; `E_OWNER`
identifies unauthorized method extension, including ordinary functions.
`E_CYCLE` identifies package or import cycles. Existing duplicate, name,
shadowing, capture, static-call and checking-limit codes remain in use.

These checks validate the supplied namespace graph, not the authenticity of
filesystem contents. Changing a graph into a different *valid* program is not
an authentication failure: the wire protocol is not a signed artifact format.
Rust is responsible for canonical file loading and retaining all input files
for output collision protection. Manifest mode selects protocol 3 explicitly; see [packages](packages.md) for
source syntax, CLI, file loading and compatibility details.


## Protocol 4: finite abstract declarations

Existing sources retain version 2 (flat, including explicit `--lib`) or version 3
(packages). Abstract declarations select version 4 with a required `input`
field whose value is exactly `flat` or `package`. Flat input keeps the version-2
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
the acceptance path. See [abstract selectors](abstract-types.md) for semantics
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
Inputs without edit declarations continue to use versions 2/3/4. There is no
cached or pre-approved assembly input. See [edit borrowing](edit-borrowing.md)
for the source contract and proof boundary.

Each module additionally permits `grants: [Grant...]`,
`contributions: [Contribution...]` and `assembly: Assembly | null` (each optional).
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

Grant paths refer only to the selected dependency closure. Grant/contribution
IDs derive from package identity, module path and declaration name; method
ordinals distinguish methods within a contribution. Unknown fields in these
new records and events are rejected. Ordinary expressions retain their existing
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
The resulting executable surface uses the common function lowerer and core audits.

The shared limits allow 4096 assembly events, 4096 contribution methods in the
whole closure, and 4096 ground functions in the separate unapplied-body audit.
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

`checkAuthorityProgram` reconstructs histories and complete delegation chains,
audits each transition against an independent relation, and performs the same
namespace, membership, final dispatch, footprint, all-body and Core audits.
The original function identity never changes. A returned loan or transfer
preserves contributions and unresolved completion obligations. The final
winning region is contained in every ancestor's grant, and transfer requires
no outstanding loans. See [source semantics](edit-authority.md) and
[the proof boundary](verification.md#edit-authority-acceptance-protocol-6).

## Protocol 7: indexed declarations and rich package bodies

The package-only envelope is `{version:7,input:"package",file,root,packages}`.
Package/module identity, dependencies, imports, abstract selectors/contracts and
all protocol-6 authority metadata retain their existing schemas and checks.
Each module may add `indexed_declarations`, defaulting to an empty array.
Rust selects 7 when any loaded module uses an indexed declaration, annotation,
typed pack or ordered-field unpack, or any package exports `geometry_compat`. Every body in that package closure then uses
the rich source path. Flat input and explicit `--lib` keep protocol 2/4.

A declaration has `{kind,name,public,span,...}` with these additional fields:

| Kind | Fields |
| --- | --- |
| `marker` | None |
| `implementation` | `marker:TypePath`, `representation:"affine_descriptor"`, `capabilities:["origin"|"dimension"]` |
| `classification` | `parents:[TypePath]`, `domain:[TypePath]` |
| `global` | `implementation:TypePath` |
| `family` | `parameters:[Parameter]`, `constraints:[Constraint]`, `representation:"token"|"point"|"morphism"` |
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
export still rejects the program. The [source contract](indexed-source.md)
defines fallback precedence and nominal identity behavior.

Declarations, rich types/bodies and the envelope reject unknown fields. No
serialized owner, winner, lifted lambda ID, certificate or checked Core can enter
acceptance. Older package versions reject `indexed_declarations` and
`geometry_compat`; flat protocol 2 also rejects these semantic fields rather
than ignoring them as unrelated metadata.

`Indexed.Wire.check` retains the exact decode and actual
`Indexed.AuthoritySource.checkProgram` result. The actual authority assembler,
all-key footprints, every applied/unapplied body, independent Fn audits and both
Core checks therefore run before success. `emit` passes that exact executable
Core to `Indexed.Core.Codegen.generate`, which independently rechecks it.
See [source syntax and limitations](indexed-source.md).

## Expected-rejection doctest consumer (reference only)

The [doctest result contract](doctest-result-reference.md) for #236 separates
ordinary language rejection from protocol, transport, and execution failure.
It reuses the diagnostic payload above without changing this wire protocol or
the driver's preservation of diagnostics on incompatible failure responses.
The Python reference and fixture regressions do not implement production driver
receipts, doctest execution, or official package admission.

The additive protocol-8 `network` resource statement and its strict finite graph
schema are specified in [finite-networks.md](finite-networks.md). It is checked
independently before lowering to the existing numerical/storage path.

The additive protocol-8 `tensor` operations (`view`, `pack`, `contract3`) and their
bounded ordered-axis/grouping schema are specified in [tensor-packing.md](tensor-packing.md).
Packing is explicit and checked independently from nominal contraction authority.
