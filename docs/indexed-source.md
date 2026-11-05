# Declaration-driven indexed source (protocol 7)

Protocol 7 adds package-only indexed declarations and typed existential payloads.
Rust serializes unresolved references; Lean composes declaration validation,
actual edit-authority assembly, finite dispatch, independent Fn specialization
and both Core audits on that same input. See [the foundation](#indexed-declarations)
for the internal contracts and [protocol](protocol.md) for the wire format.

The [geometry stdlib](https://github.com/MGYamada/Vastitas/blob/main/stdlib/src/geometry/README.md) exposes `std::geometry::scheme`
and `std::geometry::smooth` through `stdlib`, declaring the finite ordinary/smooth
affine profile through this path. An explicit checked `geometry_compat` library
export maps legacy syntax to those same declarations. The
[migration acceptance map](#geometry-migration) covers #49/#58–63 and separates
finite compatibility from broader source/native proof limits. Protocols 2–6
and explicit `--lib` retain their existing geometry syntax and wire formats.
`Indexed.LegacySource` adapts their decoded source into this same common checker
with a separately validated closed compatibility declaration package.
[Protocol 8 resource functions](storage/resource-programs.md#resource-source) and
[numerical declaration profiles](linalg/maps-and-gemm.md#numerical-declarations) compose with this same
checker. Public numerical maps are available inside resource functions
([numerical values](linalg/maps-and-gemm.md#numerical-values)); general public
numerical arrays and Fast like C performance acceptance remain pending.

## Legacy geometry syntax in packages

The geometry library manifest exports unresolved role paths under `geometry_compat`
(see [wire schema](protocol.md#protocol-7-indexed-declarations-and-rich-package-bodies)).
Lean resolves them in the provider’s root scope, checks the complete declaration
environment and validates each role. This is an explicit syntax facade, including
intentional access to the provider’s own declarations; it grants no edit authority.
The two settings require distinct markers, actual global base objects, compatible
finite affine implementations, exact origin/identity/dimension contracts, shared
Point/Morphism families with exactly the same-base constraint, and the matching
single-point existential cases. Names and equal dimensions grant no compatibility.

Exactly one export enables the original `Scheme`/`CInfScheme`, Point/Morphism/
Pointed annotations, old pack/unpack and unqualified geometry calls in the entire
closure. Explicit indexed syntax and old syntax then use the same canonical IDs.
A legacy `Base(QQ)` or `Base(CInfReal)` index is translated to the exported
base object; a bare coefficient marker is rejected as an object index. Local Fn bindings
and declared names are resolved first; only an unresolved unqualified builtin
spelling falls back, never a private-name rejection. Both forms emit the same
checked primitives. Legacy annotation references still participate in capture
checks, and both syntax forms retain independent unused-body and Core audits.

All exports are audited. With zero or multiple exports, qualified new syntax
continues to work and legacy syntax fails with the exact-one-export diagnostic.
This supports independent copies without collapsing nominal package identities.
Profile resolution has no generated runtime operation. The returned Core has
typed total evaluation and finite primitive result compatibility; full source
operational correspondence, native equivalence and C performance measurements
are separate unproved or unmeasured claims. Protocols 2–6 use the source adapter described in
[indexed declarations](#indexed-declarations--compatibility-adapter-for-protocols-26).

## Declarations and source example

Declarations start with contextual `indexed`, optionally preceded by `pub`, and
end in `;`. Declaration identity comes from the defining package/module/name;
names such as `Scheme` and `Point` do not grant capabilities by themselves.

```vast
pub indexed marker QQ;
pub indexed implementation Grid(QQ, affine_descriptor) capabilities(origin, dimension);
pub indexed classification Scheme { parents(); domain(Grid); };
pub indexed global Base(Grid);
pub indexed family Point(object(Scheme), object(Scheme)) = point constraints(same_base(0, 1));
pub indexed family Morphism(object(Scheme), object(Scheme)) = morphism constraints(same_base(0, 1));
pub indexed package Pointed {
    case(Scheme, QQ) { Point(witness, global(Base)); }
};
pub indexed primitive affine = descriptor(Grid);
pub indexed primitive origin = origin((Scheme, QQ), Point, Base);
pub indexed primitive dimension = dimension((Scheme, QQ));
```

A family parameter is `domain`, `marker`, `natural` or `object(Classification)`.
Constraints use zero-based parameter positions: `same_object(a,b)`,
`same_base(a,b)` and `over(object,marker)`. Natural indices are arbitrary-precision
unsigned literals; they do not become dispatch keys. Family representations are
the finite contracts `token`, `point` and `morphism`. These declarations are not
an arbitrary native representation escape hatch.

Package cases list the witness classification/marker and ordered field families.
Bound indices are `witness`, an unsigned literal, `global(path)`, `domain(path)`
or `marker(path)`. Every field must have the required nominal association with
the witness; matching dimensions cannot substitute for that association.

Primitive contracts are `descriptor(implementation)`, `global(declaration)`,
`origin((domain,marker),pointFamily,baseObject)`,
`identity((domain,marker),mapFamily)`, `dimension((domain,marker))`,
`compose(mapFamily)` and `apply(mapFamily,pointFamily)`. Declaration audits check
their actual representations, domains, arities, capabilities and family shapes.

Value annotations use `Object<domain,marker>` or `family<arguments...>`.
Use qualified forms such as `geo::Point<X,geo::Base>` for compatibility spellings
that the old parser also recognizes. An argument names a declaration or preceding
object binding, or supplies a natural literal, according to the family's contract.
Package annotations use `package<domain,marker>`.

```vast
fn make(n: Nat) -> geo::Pointed<geo::Scheme, geo::QQ> {
    let X = geo::affine(n);
    pack geo::Pointed<geo::Scheme, geo::QQ> { witness: X, fields: [geo::origin(X)] }
}
fn main() -> Int {
    let packed = make(42);
    unpack packed as { witness: Y, fields: [p] };
    int(geo::dimension(Y))
}
```

`unpack` introduces a fresh witness identity and binds every field in order.
A result whose **type indexes that witness** (for example a point, morphism, or
indexed token) must be repackaged before leaving the opening's scope. The bare
witness object is an ordinary first-class value: its `Object<domain,marker>`
type has no local object index, so it may leave the block directly:

```vast
let Z = { unpack packed as { witness: Y, fields: [p] }; Y };
let q: geo::Point<Z, geo::Base> = geo::origin(Z);
```

Here `Z` retains that opening's identity; ordinary local aliases retain it too.
This does not export `p` or identify `Z` with a witness from a second opening
of the same package. Returning an object through a function call introduces a
fresh caller identity, including repeated calls to the same function. A newly
constructed object with an equal descriptor also remains distinct. To carry an
existing dependent field across the boundary, return a package containing its
witness and fields together. These rules apply to both ordinary and smooth
geometry and to legacy geometry syntax through the common checker.

The complete [example](https://github.com/MGYamada/Vastitas/blob/main/examples/packages/indexed/main.vast) additionally uses
an identity morphism and a static lambda:

```sh
cargo run --locked -- check --manifest-path examples/packages/indexed/Vastitas.toml
cargo run --locked -- build --manifest-path examples/packages/indexed/Vastitas.toml -o target/indexed-demo
./target/indexed-demo
# 42
```

## Composition and limits

The ordinary import/visibility/shadowing rules apply. A declaration does not grant
edit authority over another module's methods, memberships or contracts. Protocol 7
uses the full protocol-6 assembly checks, including omitted empty root assemblies,
unapplied contribution body checking, nested loans and permanent transfer.

Indexed values can occur in ordinary data signatures and method bodies. Finite
dispatch still uses only the existing scalar/abstract selectors and capabilities;
all applicable bodies, including nonwinners and out-of-domain keys, are checked.
Fn signatures still contain only scalar/recursive-Fn types. Independent lambdas
cannot capture values or object names appearing in indexed annotations.
Separate signature probes audit unused bodies and cannot enter executable targets.

No indexed array allocation, storage loan, linear-algebra operation, new affine
map construction or general recursive function is introduced here. Presented
affine objects and their maps arrive later, through the separate Stage 2
profile in [affine geometry](affine-geometry.md). Source and
type depth bounds, 4096 specialization/key limits, arbitrary-precision integers
and nominal identity checks remain in force.

## Acceptance and proof scope

`Indexed.Wire.CheckedInput` retains the exact decoded JSON and exact result of
`Indexed.AuthoritySource.checkProgram`. `VastitasOracle.IndexedWire` connects it
to both typed Core passes, dependency order, main validity, returned loans and
final winning footprints. Native code generation receives the actual executable
Core certificate and independently rechecks that Core at its boundary.

`IndexedProgramSafety` now proves typed total evaluation, including dependent
calls and unpack bodies, for an actual checked Core module. `IndexedWire` and
`LegacySource` expose that theorem for the exact audit/executable modules returned
from protocols 2–7, and prove finite Int-valued main evaluation. This does not
prove whole-source rewriting correspondence, equality with the retained legacy
evaluator or native code-generation correctness. None of these proofs establishes the [Fast like C](storage-ownership.md)
performance goal.

<a id="indexed-declarations"></a>

## Indexed declaration foundation

`VastitasKernel.Indexed` supplies the finite declaration environment and
independent indexed audits used by every public protocol. Protocols 2–6 adapt
decoded source into the common checker, not an already accepted legacy Core.
Package-only protocol 7
exposes unresolved declarations and rich source bodies through the full authority
composition; see [source syntax](indexed-source.md). The [geometry stdlib package](https://github.com/MGYamada/Vastitas/blob/main/stdlib/src/geometry/README.md)
now supplies the finite affine declarations and an explicit checked compatibility
export for legacy syntax in protocol 7. Typed total evaluation covers the exact
returned Core. [Migration acceptance](#geometry-migration) maps #49/#58–63 to
implementation, proofs and regressions, including finite primitive compatibility
and the limits of the source/native guarantees.
The declaration base was merged in PR #188 (`09f9e9d`), and package/primitive
annotation contracts in PR #189 (`b3f8ff7`), and Core/native generation in PR #194
(`c29e1cd`). The compatibility adapter is described below.

### Identity and declarations

`Identity.lean` contains the existing package, logical-module and declaration
owner records. Both the existing namespace checker and indexed declarations use
these exact types. Import aliases, file basenames and displayed type names do
not replace this identity.

An environment contains uniquely identified coefficient markers, finite
implementations, classifications, canonical object declarations and families.
An implementation records its marker and finite backend representation. A
classification explicitly lists its complete finite domain and its parents.
Every member must be an implementation; a child's domain must be contained in
each parent's domain. Topological ranks are reconstructed with a bounded,
memoized pass, then independently checked for strict descent on every parent
edge. No rank, inferred membership or checked flag comes from a frontend.

The current foundation permits 4,096 declarations, 64 implementations in a
classification and 16 parameters in a family. Classifications have nonempty
explicit domains. A classification may contain implementations over different
markers: an `ObjectType` selects both a domain and a marker, and its admitted
implementations are the nonempty intersection. Classification and coefficient
base are therefore separate, even in the initial single-base geometry profile.

Implementation capability records currently contain the closed `origin` and
`dimension` tags for the finite affine descriptor representation. They are
explicit per implementation; classification or inheritance does not fill them
in. These records alone are not mathematical evidence or operation acceptance.
The closed primitive binding checker is described below. Executable source/
term use of these records is checked by the Core below. The declaration namespace
resolver uses actual package visibility and ownership. Public source acceptance
composes it with scalar membership/edit audits and complete term elaboration.

### Unresolved declaration input and namespace audit

`IndexedSource` and `IndexedSourceChecker` accept an internal unresolved
declaration program. Each declaration has a name, body, visibility and span; its
canonical owner is reconstructed from the enclosing package ID and logical
module. References contain paths, never frontend-selected owners or checked
flags. Package modules retain the existing function/generic/edit declarations,
imports and package graph in a shared namespace.

The backend builds its indexes once for resolution, then uses the existing
bounded `Namespace.resolve` and `Namespace.validate`. Dependency aliases and
public re-exports retain original declaration IDs. Private declarations and
private re-exports remain inaccessible, children obtain no parent identity, and
cross-category duplicate names or import/dependency collisions are rejected.
Compatibility spellings such as `Scheme`, `Point` or `origin` are permitted only
for real indexed declarations and their aliases; the spelling does not select
their role or representation. Scalar types, `Fn`, `Pair` and language keywords
remain reserved. Protocols 2–6 cannot create the new namespace kind.

All declarations, including unused dependency declarations, resolve to the
actual `Indexed.Core.Declarations` tables. Complete finite domain, index sort,
arity, package and closed primitive contracts then undergo the existing Core
declaration audit. The checked record retains the exact lowering equation,
original owner sequence, namespace validation and an independently re-resolved
reference ledger. `VastitasOracle.IndexedSource` proves that every output ID
comes from an actual enclosing input declaration, every recorded reference
resolves to its exact canonical target, and the same output environment has
valid package and primitive contracts.

`IndexedSourceRegression` adds 34 cases, including non-geometric token/package
contracts, coefficient-versus-object errors, whole-domain capability loss,
order/alias invariance, private access and forged reference ledgers. A sixth
standalone native fixture takes the resolved declaration environment through
actual Core checking/code generation and returns `7`.

This certificate accepts declarations only. It does not check function bodies,
finite dispatch or edit assemblies, and it is not a public protocol-7 entry
point. Rust parsing, the wire decoder and the full scalar/function/authority
composition are connected by `Indexed.Wire.check`; the separate internal data-body adapter is described below. The internal regression
constructs Core terms directly; it is not a `.vast` source migration test.

#### Dependent type annotations

`IndexedSourceTypes` elaborates internal data-type annotations against that
same declaration certificate. Inputs distinguish pure types, an explicit
object domain/coefficient pair, and a named family/package application. The
declared parameter contract determines whether each argument is an object,
domain, marker or natural literal. A local object name uses the exact reference
in its supplied Core binding; a qualified name uses the real namespace resolver
and must designate an appropriate declaration. Coefficient markers cannot be
used as global test objects. Package applications retain their explicit domain
and marker case, and natural indices cannot be runtime variables.

The type certificate retains the exact input, scope, context and lowering
equation. The checker validates supplied binding annotations, bans shadowing,
duplicate names/symbols and invented module scopes, re-resolves all declaration
references, and independently audits the resulting Core type and its scope.
The oracle proves deterministic output for the same inputs, exact local-index
selection from the binding, and that every local index in the result occurs in
an actual input binding. This includes empty-runtime token families. These
statements do not establish execution or freshness of arbitrary supplied
contexts; a complete term checker must derive those contexts from actual code.

Thirty-five regression cases cover wrong sorts/arity/endpoints, alias identity,
nominally different openings, malformed contexts and dependent Core calls. The
seventh native fixture uses an elaborated dependent parameter/result type in a
checked function and call and returns `13`. It still assembles Core terms
directly. Those individual annotation tests do not replace the public protocol-7
composition of scalar dispatch, Fn and authority checks described in
[indexed source](indexed-source.md). Protocols 2–6 retain their existing audits.

#### Internal data-function bodies

`IndexedSourceBodies` and `IndexedSourceProgram` now elaborate unresolved
internal data-function ASTs, including dependent parameters/calls, scalar and
Pair operations, branches, declared primitives, explicit package construction,
and unpacking of all ordered fields. Parameter, let and unpack contexts are
derived from the actual bodies. Imports and primitive calls resolve through
the real namespace index; primitive spelling and expected result types never
select implementations. Fresh object identities, scoped openings and exact
call substitutions pass through the common Core typing and freshness audit.
Both branches and every function in every package are checked, including unused
bodies. Integer literal hints remain symmetric, Pair operands infer independently,
and Nat-to-Int conversion remains explicit.

Calls retain their original source IDs through a stable dependency ordering.
An independent audit checks output count and each ID's original source owner;
Core ID uniqueness then excludes replacing an unused function with a duplicate.
`VastitasOracle.IndexedSourceBodies.source_covered` proves every input ID occurs
in the output, and `source_body_checked` establishes actual Core typing for all
of them. The same-input certificate retains the reconstruction equation,
independent declaration/call reference ledgers, exact accepted Core, dependency
order and entrypoint validation. A ledger by itself is not a source-to-Core
correspondence certificate.

The 52 new regression cases include private/re-exported functions, unused
dependency bodies, constant branches with distinct identities, non-geometric
token indices, object-return generativity, aliases, repeated unpacking, multiple
heterogeneous fields, repacking and forged origins/call records. Three additional
standalone native fixtures now start with these unresolved source AST bodies
and return `2`, a large arbitrary-precision integer, and `3`. These bring the native
fixtures to ten before the Fn extension below; executables import only IndexedRuntime.
These are internal AST tests, not Rust-parsed `.vast` fixtures.

The adapter explicitly rejects old function bodies, generic/method/abstract
metadata and edit/authority envelopes whose checks it cannot yet compose.
It has no Fn expressions or specialization; the separate adapter below extends
the internal syntax. The later adapters below compose finite dispatch and
authority and are now used by every public protocol, with source adaptation for
versions 2–6. The later program theorem establishes Core evaluation; native refinement remains unproved.

#### Internal independent functions and static specialization

`IndexedFunctionSource` adds an internal source AST for named function values,
independent lambdas, invocation and recursive `Fn` signatures. Data annotations
reuse the same indexed declarations, exact namespace resolver and dependent Core.
Higher-order signatures contain only Nat/Int/Bool/Unit and recursive Fn types;
Pair and indexed types remain available in direct data calls and local bodies.
Generic families are not Fn values. This is not a public wire format.

The backend reconstructs source IDs and lifted lambda IDs from the enclosing
package/module and traversal, independently audits their provenance, and rejects
frontend-supplied lifted references. The lambda scope audit traverses indexed
annotations and every ordered package field as well as expressions. Capturing
outer data or Fn bindings and shadowing enclosing bindings remain invalid.
Signature preparation preserves every original and lifted definition identity.

`IndexedFunctionCompiler` uses separate states for signature-probe and executable
specialization. The audit pass checks every definition, including unused
higher-order functions and lambdas; coverage is independently rechecked. Probes
are scalar/Fn signature placeholders and never executable targets. Concrete
specializations preserve exact Fn signatures; differing function targets across
branches are rejected without constant folding. There are at most 4,096 higher-
order/lambda instances in each pass. Ordinary dependency traversal uses a bounded
worklist separate from body fuel and rejects recursion after specialization.

Each executable instance records its original definition, static target tuple,
canonical owner and complete data signature. Calls preserve argument evaluation
order and evaluate every argument once, including erased Fn arguments. Private
functions may be intentionally returned by public functions, but direct access
still requires namespace visibility. Entry validity is checked before erasing Fn
parameters, so a malformed source `main` cannot become a valid scalar entrypoint.
Both passes undergo independent common-Core typing, freshness and dependency
audits; only the executable pass reaches native generation.

`VastitasOracle.IndexedFunctions` connects the exact source/declaration/lifting/
preparation/pass equations to both returned typed Core modules. It proves every
original source function and lifted definition has a typed audit instance,
executable static targets are concrete, their signatures match the original
definitions, emitted call IDs identify their exact specialization keys, and
recorded source calls resolve through the actual namespace. These are structural
acceptance guarantees. Typed termination follows from the later program theorem;
source evaluation preservation is a separate unproved claim.

Fifty-five cases cover capture, shadowing, unused bodies, malformed signatures,
private targets, probe separation, branch targets, nominal scope escape, forged
metadata, the 4,096/4,097 boundary and a 4,200-function dependency chain. Four more
standalone native fixtures exercise higher-order/lambda execution, indexed local
operations, a returned private function and ordered package fields. All fourteen
fixtures link only the minimal runtime. The subsequent adapters below add finite
dispatch/all-applicable-body and edit-authority composition. Public protocol 7
now exposes that composition and the geometry stdlib below uses it. Whole-term
Core evaluation is covered by the later program theorem.
This plain Fn entry rejects old dispatch/edit envelopes explicitly.

#### Internal finite dispatch over indexed method bodies

`IndexedDispatchSource` retains the same generic/abstract selector declarations
and rich method bodies. A method has the existing scalar selectors, capabilities
and scalar/Pair result contract; indexed values remain local data, never keys.
The adapter projects declaration headers into the actual namespace and finite
dispatch engines. Placeholder bodies are never accepted as method implementations.
Source positions and complete resolved headers are independently compared, with
the actual rich body retained at its original position. Ordinary method ownership,
scalar membership ownership, visibility and abstract contract authority still
use the exact defining module.

`IndexedDispatchPreparation` runs the real `DispatchChecker.prepareFamilies`,
retaining its accepted `Dispatch.checkWith` equation and fulfilled contracts.
The nominal/capability product order, complete key-space ambiguity checks,
contract-domain union and exact selected result contract are unchanged. Every
`applicablePairs` entry becomes a source specialization, including nonwinners
and concrete keys outside the callable domain. An independent equality check
rejects omitted or invented method/key entries. Each body can create indexed
objects, call ordinary data/higher-order functions and use independent lambdas.
Each lexical method lambda is lifted once and shared across concrete keys;
different source lambdas retain different identities even with identical spans
and bodies. Key expansion therefore does not multiply the lambda budget.

Both the complete audit pass and executable pass use the Fn compiler above.
Generic arguments infer independently, once and in source order; their scalar
tuple selects the actual checked winner without consulting an expected result.
A separate ledger re-resolves the generic path and checks its admitted key,
selected method and emitted source definition. Core typing independently checks
the resulting call signatures, nominal indices, scopes and dependency order.
All ordinary source functions and lifted lambdas retain the same coverage audit.

`VastitasOracle.IndexedDispatch.applicable_body_checked` connects every actual
applicable pair to a typed body in the returned audit Core. `source_body_checked`
and `lifted_definition_checked` cover original functions and lambdas.
`dispatch_call_selected` establishes the existing independent `Dispatch.Selection`
relation for every recorded generic call, together with namespace resolution and
exact source-target lookup. Reconstruction equations tie these results to the
same headers, rich bodies, declaration environment, expansion and final passes.

Thirty-seven new regressions cover nonwinning/out-of-domain bodies, abstract
contracts, nominal selectors with equal inhabitants, capability order, exact
ownership, capture/shadowing, recursion and forged expansion/target records.
Four additional native fixtures execute indexed/higher-order method bodies,
contract-domain calls, nominal selectors and Pair results (eighteen in total).
The adapter rejects edit/authority envelopes and old unconnected method bodies.
The authority composition below adds the entry used by public protocol 7.
The later stdlib and checked-Core evaluation increments below compose this
foundation; the plain dispatch adapter itself is not the public entry.

#### Internal edit authority over indexed contribution bodies

`IndexedAuthoritySource`, `IndexedAuthorityPreparation` and
`IndexedAuthorityCheck` connect the rich source AST to the actual
`Authority.assemble` result. Grants, nested loans, transfer histories,
returned-loan and seal checks, final finite families and winning footprints
come from that existing assembler. The complete final headers also pass the
existing declaration validator; placeholder bodies never replace rich body
checking. Transferred edit authority still grants neither scalar membership
nor abstract contract ownership.

Contribution declarations retain enclosing lexical scopes and rich methods.
Canonical contribution IDs and original method positions connect each applied
body to the checked trace; the complete resolved headers must match the final
assembled method list. Every applicable pair becomes a specialization,
including nonwinners and keys outside the callable domain. Unapplied methods
expand against the same final hierarchy and capabilities, with the existing
4,096 audit-specialization bound. Their complete reconstructed audit headers
must equal the actual assembler's discarded audit. They never enter the
dispatch candidate table.

Each prepared definition has both its canonical generic/function owner and
its lexical body scope. A contributed method keeps the defining generic ID
after a permanent transfer, while its private helper paths and indexed type
annotations resolve in the contributor's module. Lifted lambdas retain that
same source scope and original definition. Scope and identity are independently
audited before and after signature preparation.

The separate audit pass checks all ordinary functions, applied/unapplied
specializations and lifted lambdas. The executable pass excludes unapplied
definitions and any lambda originating in them. Independent instance, origin
and static-target checks reject a forged candidate mapping, exclusion set or
unapplied executable target. Both passes then undergo actual common-Core
typing/freshness/dependency audits. Only the executable result reaches native
generation.

`VastitasOracle.IndexedAuthority` retains the exact assembler, source-method,
expansion, lifting, preparation and lowering equations. Its theorems expose
the actual authorized trace and final footprints, nominal owner/lexical scope,
complete typed body coverage and executable exclusion of unapplied origins.
These are structural acceptance guarantees; the later program theorem supplies
typed termination. Whole-source evaluation preservation and native implementation
refinement remain unproved.

Thirty-nine regressions cover nested loan suspension/return, explicit delegation,
contained regions, transfer and revoked old authority, returned Open obligations
and repair, exact private scope, all-body checking, final out-of-domain footprints,
contribution order, empty-root assembly, scope escape and forged metadata.
Four additional native fixtures execute nested contribution helpers, transfer,
obligation repair and the empty-assembly path (twenty-two at that increment).
The bare opened-object fixture brings the current standalone native suite to
twenty-three, retaining its opening identity through a block and local aliases.
Public protocol 7 now decodes Rust source into this exact combined checker.
The geometry stdlib below now uses that public path; the explicit library export also supports legacy syntax in the same closure.

### Indexed applications and scopes

Family parameters distinguish classification domains, coefficient markers,
objects and natural indices. An object parameter admits the entire finite
implementation domain carried by the supplied object, not just one observed
implementation. Constraints express exact object equality, equal coefficient
bases and an object's stated coefficient marker. Point and morphism backend
representations are sealed, have two object arguments and require an explicit
same-base contract. The public declaration spelling does not choose one.

Canonical objects refer to global declaration IDs. Locals carry an object type
and a nominal brand. Equal markers, descriptors or dimensions do not equate
references. In particular, a coefficient marker cannot substitute for a global
object, and two global declarations of the same implementation remain distinct.

All object indices contribute to the generic scope traversal, including indices
of tokens with empty runtime representations. Substitution fixes globals,
requires unique local sources and preserves the source's exact object type.
The internal Core has a separate checked call substitution relation that permits
whole-domain refinement, rechecks every dependent argument after substitution
and fixes globals. `IndexedArgumentSafety`/`IndexedCallTransport` connect those
calls to typed evaluation. Native refinement remains outside the proof boundary.

### Independent checks and proof boundary

`Entry.Valid`, `Family.Valid`, `Parameter.Accepts`, `Constraint.Holds`,
`Environment.Valid` and `Application.Valid` specify logical conditions separately
from the executable environment/application checks. `CheckedEnvironment` retains
the exact environment and its successful audit; `CheckedApplication` is indexed
by that same checked environment. The public protocol does not deserialize either
checked record.

`VastitasOracle.Indexed` proves checker/proposition equivalence, validity of
those checked records, exact input correspondence, acyclicity of all nonempty
inheritance chains, preservation of globals and family IDs under substitution,
and the local-brand scope consequence. These proofs import the actual kernel
records and algorithms. They do not prove indexed program evaluation, frontend
resolution, source-to-Core correspondence, mathematical scheme axioms or native
code equivalence.

`IndexedRegression` exercises declaration-order changes, coherent renaming,
non-geometric `VectorShape` and `Position` families, missing/duplicate IDs,
wrong kinds/arity, base mismatch, cyclic/incompatible inheritance, complete
finite domains, distinct global/local identities, hidden token escapes and
invalid substitutions. It runs in the common no-mathlib regression script.

The public protocol-7 integration updates Rust and Lean together and retains
unresolved namespace provenance. All public protocols use the common checker and
native generator. Their exact returned Core is covered by `IndexedProgramSafety`;
the migration acceptance map separates this from full source/native equivalence.


### Single-witness existential contracts

`IndexedPackages.lean` gives package contracts one explicit object witness and
an ordered list of bound family applications. A bound index is the witness,
a declared global object, a coefficient/domain marker or a natural index; it
cannot contain an unbound local object. The complete finite witness domain is
retained after hiding and opening. A symbolic representative validates the
contract before any payload is inspected.

A payload must fit the declared witness domain, preserve its marker, and have
exactly the fields obtained by instantiating the same templates at that witness.
Every field application is independently checked. This rejects a point from a
different object, a changed base, dropped/extra fields and hidden free brands.
A narrower concrete implementation may be packaged under a broader admitted
domain, but that does not add capabilities to the domain visible after opening.

Opening synthesizes a local witness and fields, then independently audits them.
The brand serial must differ from every local serial in the supplied allocation
context, including locals with different claimed type metadata. The field
annotations must use that exact new witness and remain scoped with it. Opening
the same package twice therefore produces distinct brands while the first is
retained in the context. The internal Core supplies its complete variable context
and additionally audits unique allocation serials over all function parameters
and allocation nodes. Runtime value correspondence is established by
`IndexedPackageSemantics` and composed by `IndexedProgramSafety`.

`VastitasOracle.IndexedPackages` proves the executable audits equivalent to their
independent propositions, field/witness association, absence of any other free
local field index, scoped opening fields, brand freshness and distinct reopening.
These package-layer theorems concern the exact checked **type annotations**.
The Core layer below additionally checks actual field terms; the later
`IndexedPackageSemantics` lemmas connect them to runtime payloads.

### Closed primitive binding inventory

`IndexedPrimitiveBinding.lean` declares the explicit bindings of a closed finite
registry. `IndexedPrimitiveShapes.lean` defines the shape that describes a
binding's operands, their agreements and its result.
`IndexedPrimitiveValues.lean` defines the logical values of the Core semantics
(`Value`), the erased runtime values of generated programs
(`PrimitiveRuntimeValue`) and the erasure between them.
`IndexedPrimitiveDescriptors.lean` defines what a binding's
[registry entry](appendix/glossary.md#registry-entry)
(`PrimitiveDescriptor`) holds: its shape, its validity contract, its two
evaluators, its lowering and the literals a generated module declares once for
it. The evaluators are `eval` on logical values and `evalRuntime` on erased
values. `IndexedPrimitiveRegistry.lean` holds one registry entry per
binding, and `IndexedPrimitives.lean` derives every
binding's validity contract, operand association, result inference and operand
count from it; the argument hints of `IndexedCore.lean` and the role table of
`IndexedSourceDiagnostics.lean` come from the same shape. The two evaluators of
`IndexedSemantics.lean`, `evalPrimitive` and `evalRuntimePrimitive`, apply the
entry's evaluators. `IndexedCodegen.lean` lowers a call by its entry and
declares the literals that the entries share. Whether a call allocates comes
from the shape:
`Shape.allocates` holds when the result template is a fresh object, and
`PrimitiveBinding.allocates` reads it off the entry. The fresh-slot premise
`PrimitiveFresh` of `IndexedSemantics.lean`, the brand that
`IndexedSourceBodies.lean` draws for a call and the allocation serials of
`IndexedTypeAudit.lean` test that flag. The `descriptor` binding is the one
allocating binding.

The wire form of a primitive comes from one table. `IndexedPrimitiveFamilies.lean`
lists one [primitive family](appendix/glossary.md#primitive-family) per wire
`op`: its fields with their kinds, in wire order, whether only protocol 9
admits it, and how the resolved fields build the binding. The decoder of
`IndexedDeclarationProtocol.lean` admits only those fields. The resolver
`resolvePrimitive` of `IndexedSourceChecker.lean` resolves them and builds the
binding through the family. The frontend reads `src/primitive_table.rs`, which
`scripts/check_primitive_table.py` generates from the same table and checks
for drift. A binding that the checker derives from a morphism, isomorphism or
Cartesian-square declaration has no family.
[Add an indexed primitive](development/primitives.md) lists what one more
binding touches. `IndexedDescriptorExample` defines a `PrimitiveDescriptor`
value and a `PrimitiveFamily` value outside the registry.
`IndexedDescriptorRegression` runs on the first the shape derivations that
each derived table reads, the evaluators and the lowering, and on the second
the decoder and resolver steps that take a family.

No source spelling, arbitrary native symbol, certificate string or `trusted` flag
chooses an implementation. The binding IDs, operand annotations and result
annotation are independently audited against the same checked environment.

The table lists the bindings of this profile. [Presented affine
geometry](affine-geometry.md) describes the relative bindings, and [Smooth
affine declarations](language/smooth-declarations.md) describes the smooth,
fiber, tape and metric bindings.

| Registry entry | Operand and result contract | Additional obligation |
| --- | --- | --- |
| Descriptor construction | `Nat` to a local object of the named implementation | Implementation exists; supplied brand serial is fresh |
| Global object | No operand; exact canonical global reference | Global declaration resolves to a valid implementation |
| Origin | Object X to the bound point family at X and the explicitly bound global base | Every implementation in the binding domain supports origin; object/base markers agree |
| Identity | Object X to the bound morphism family at X,X | Family is a sealed morphism representation; complete input domain is admitted |
| Dimension | Object to `Nat` | Every implementation in the binding domain supports finite dimension |
| Composition | Bound-family Y→Z and X→Y to X→Z | Exact family IDs, exact middle object, valid input and output family constraints |
| Application | Bound-family X→Y and point at X over S to point at Y over S | Exact family IDs and source object; preserve S exactly |

Input object annotations must refine the binding's whole finite domain. Keeping
an original narrow brand cannot bypass a broader current annotation that admits
an implementation without the required capability. Conversely, the independently
checked reference/annotation relation rejects an unsupported narrowing.

Result synthesis is deliberately followed by `checkPrimitive`; directly supplied
or mutated candidates pass the same independent `PrimitiveTyped` audit. Oracle
proofs connect the checked result to that judgment, including application test
objects, composition endpoints, fresh descriptor construction and whole-domain
origin/dimension support. None of these contracts proves mathematical scheme
axioms or native equivalence. The common source checker uses these exact bindings;
`IndexedSemantics` and `IndexedProgramSafety` supply typed evaluation, and
`GeometryResults` supplies finite legacy result compatibility.

`IndexedPackageRegression` and `IndexedPrimitiveRegression` add 45 direct cases,
including repeated openings/repacking, false field associations, abstract-domain
capability loss, changed family IDs, false result endpoints and reused brands.
Wire versions 2–6 retain their source contracts; their final lowering now passes
through the common declaration-driven Core.

### Audited Core and native generation

`IndexedCore`, `IndexedTyping` and `IndexedTypeAudit` now compose the declaration,
package and primitive contracts over actual terms. Every node carries an audited
result, and every function body is checked, including unreachable functions and
both branches. Calls use signatures extracted from the same module and actual
call IDs feed the existing dependency-order audit. There is no separate trusted
dependency graph. The entrypoint must have no arguments and return `Int`.

Object ascription preserves the original reference but restricts operations by
the current static domain. Variable lookup checks the entire annotation, so a
forged variable type cannot recover a discarded capability. Dependent calls
preserve exact indexed endpoints; object-valued calls introduce a fresh caller
identity. Different branch results require a fresh merged identity even for a
constant condition. Numeric allocation serials are unique across all allocation
sites and object parameters, independently of claimed type metadata.

Lexical scopes and existential openings reject result types containing new local
indices. A bare object may leave an opening because its domain/marker type does
not index its own identity. The block result and its local aliases retain that
opening's brand; another opening, construction, or object-returning call does
not acquire it. Dependent fields still require repackaging. This is intentional
in both `HasType` and the source `checkEscape` rule; the actual module freshness
audit and typed evaluation cover the retained result reference. It does not add
a full source/native refinement theorem. References already present inside an
outer indexed value remain in scope even when that object's original binding
was anonymous. Packages use an
explicit finite case table indexed by domain and coefficient marker, at most
64 cases per declaration. Two cases cannot share a witness type, that is the
same domain and coefficient marker. Lookup uses that exact pair, so cases whose
domains are nominally related stay distinct and unambiguous. Runtime objects and dimensions
are never case or dispatch keys. Fields use the single-witness templates above.

`VastitasOracle.IndexedCore.checkModule_acceptance` identifies the exact input
module and combines its complete structural typing, declaration/freshness,
actual dependency order and entrypoint checks. Additional consequences cover
scopes, ascription, dependent substitution, primitive contracts and payload
association. Constructive checker/proposition equivalence lemmas shared with
the oracle live in `IndexedAudit` and `IndexedContractAudit`, allowing executable
decisions without classical choice or mathlib. Existing oracle names are exported.

`IndexedCodegen.generate` takes a checked module and repeats the complete audit
immediately before generation, then emits only reachable functions. Native
representations come from validated family contracts. Generated existential
structures retain the witness and every ordered field; numeric identifiers
avoid inserting source names into Lean code. The generated program imports only
`IndexedRuntime`, whose finite operations are descriptors, origins, identities
and their composition/application. Type identity, classification and coefficient
markers may be erased after checking; equal runtime descriptors confer no
static compatibility. This runtime is not an arbitrary scheme implementation.

`IndexedCoreRegression` has 34 cases, including actual package/function/primitive
composition and forged annotation, substitution, scope, freshness, declaration
and dependency failures. `bash scripts/check_indexed_native.sh` compiles and runs
three standalone fixtures (package output `2`, all primitives output `42`, and
arbitrary-precision scalar/Pair arithmetic). Both OS no-mathlib CI jobs run them.

Public protocol 7 parses and independently resolves declarations. The structural
theorem alone does not establish evaluation; `IndexedProgramSafety` supplies
typed evaluation and activation/world correspondence. Full source operational
correspondence and native refinement remain outside the migration's claims.

### Geometry standard-library declarations

`stdlib/src/geometry` is an explicit path package using the public source
checker; since its `scheme::affine` module declares
[presented affine geometry](affine-geometry.md), its closure uses protocol 9. It declares separate `QQ`/`CInfReal` markers and `Scheme`/`CInfScheme`
finite classifications in sibling `scheme`/`smooth` modules, actual global base
objects, shared indexed Point/Morphism families with same-base constraints, and
the two finite Pointed package cases. `stdlib` re-exports these canonical
modules as `std::geometry::scheme` and `std::geometry::smooth`, alongside the
original arithmetic declarations. No definitions are copied into the facade.
All existing affine descriptor/origin/identity/dimension/composition/application
operations use ordinary declared primitive contracts. Each module's `pointed`
is an ordinary `.vast` function that constructs and packages data.

Twenty-four integration tests exercise both settings, alias identity, coherent renaming,
separately generated/opened/copied nominal objects, coefficient versus test-object
distinction, missing capabilities, dependent morphism calls with retained test
objects/repacking, composition with arithmetic in the same protocol-7 closure,
private support visibility, external method authority, legacy client compatibility
and rejection of mutated actual wire contracts by both checking and emission.
The combined and pointed examples return `42`; the smooth example preserves
its explicit abstract annotation and returns `2` after unpacking. The implementation still uses the finite descriptor
representation; no general polynomial map, chart, tensor or numerical buffer is
added. Primitive/package proofs retain their original stated scope. Historical
Stage 2 later adds presented objects and polynomial maps as a separate,
separately checked profile ([affine geometry](affine-geometry.md)). It does not
change this migration's descriptor objects or two-index families.

The original `stdlib` entrypoint now supplies both libraries; the temporary
`stdlib/indexed` facade is removed. The geometry manifest explicitly exports
`geometry_compat` paths. Lean resolves them in the provider root, checks all
exports, and validates exact base/family/package/primitive contracts before
legacy syntax can use the same IDs and primitive emitter as new syntax. Exactly
one export is required only for legacy syntax; qualified calls to multiple
independent libraries remain supported. Existing declared/local names take
precedence, and visibility errors cannot fall back to builtin spelling.
Unchanged `examples/pointed.vast` and `examples/smooth.vast` run through the
same protocol-7 closure. Mixed syntax retains dependent endpoints and package
witnesses; capture, scope escape and unused-body checks are unchanged.

`GeometryCompatibilityRegression` checks twelve positive/negative profile cases.
`VastitasOracle.GeometryCompatibility` proves that actual public acceptance uses
the independently validated profile in the function compiler, with distinct
markers and matching origin/package roles. The program theorem supplies whole-term
Core evaluation; `GeometryResults` connects declared primitive results to the
retained finite runtime. Protocols 2–6 use the source adapter below. See the
[acceptance map](#geometry-migration) for the full migration boundary.

<a id="indexed-declarations--compatibility-adapter-for-protocols-26"></a>

### Compatibility adapter for protocols 2–6

`Indexed.LegacySource` retains the original wire decoders and converts decoded
source directly to `Indexed.AuthoritySource.checkProgram`, the same declaration,
function, finite-dispatch and edit-authority checker used by protocol 7. It does
not use the old geometry elaborator's acceptance or translate an old checked Core
on the public path. Both `check` and `build` require the common audit; code
emission uses the exact returned executable Core and independently audits it again.

Flat functions, methods, abstract declarations and contracts retain their actual
bodies and spans in a synthetic module whose identity is independent of display
filenames. Flat input gains no qualified module paths. Package inputs retain
original package IDs, module owners, imports, visibility, grants, contributions,
delegations, transfers and assemblies. Scalar header validation preserves the
old diagnostic ordering; it supplies no accepted bodies or checked Core.

Old wire formats cannot declare indexed types. The adapter therefore appends a
closed package of unresolved ordinary/smooth affine declarations and an explicit
compatibility export. The common declaration/profile checker validates its two
coefficient markers, finite implementations, canonical base objects, point and
morphism families, existential cases and primitive contracts. The adapter first
validates the original namespace and rejects a source package colliding with the
reserved profile identity. Injecting that package cannot repair an unknown source
dependency or grant imports, edits, memberships or contracts. Protocol 7 continues
to use explicit library exports and canonical stdlib declaration IDs.

The common source compiler retains object introduction sites for parameters,
constructors, object-returning calls, branch merges and unpacking. These names and
locations affect diagnostics only. Nominal references, scope, independent Core
typing and actual dependency ordering continue to determine acceptance. Aliases
retain the original introduction; equal descriptors never identify objects.

`LegacySourceRegression` exercises all six flat/package envelope combinations
across versions 2–6, library/entrypoint behavior, unused invalid bodies, flat path
rejection, reserved profile collisions, forged dependencies and a corrupted
injected profile. Existing source/native regressions cover both geometric
settings, dependent substitution, Fn specialization, full scalar dispatch and
edit authority, including all applied and unapplied bodies.

`VastitasOracle.LegacySource` connects the exact decoder and source-adapter results
to the actual common checker, both typed Core passes, real dependency order,
entrypoint validation, returned loans, final winning footprints, checked body
coverage and the same validated geometry profile used by the function compiler.
The same module's totality corollaries connect both returned Core passes to the
program theorem, which derives activation/world freshness. Full source
operational correspondence and native refinement remain separate unproved claims.

`LegacyIndexed` and `Codegen.generate` remain internal compatibility APIs for the
retained old Core and its regression/proof boundary. Their structural translation
theorem and nine direct regressions remain useful, but they no longer describe
public source acceptance. The old evaluation theorems still concern that old Core
and runtime. Public generated programs import only `IndexedRuntime`; ordinary
compilation needs neither mathlib nor OpenBLAS.

### Indexed runtime semantics: first proved fragment

`IndexedPrimitiveValues` defines the values; `IndexedSemantics` defines their
typing against worlds and a bounded observation of the Core terms, with
strict argument evaluation, separate function activations, explicit
package witnesses/fields and the closed primitive registry. The evaluator is
internal semantic test infrastructure, has no public CLI, and does not impose
its observation fuel on generated programs. It deliberately ignores result
annotations; independent acceptance must justify those annotations.

Logical objects retain their declaration's implementation ID alongside the
actual runtime descriptor. Object typing checks that ID against the complete
declared finite domain. An activation-local world maps numeric brand serials to
objects; changing a reference's claimed type does not change its slot. Worlds
need not be injective, so two different brands may denote equal descriptors
without making those brands interchangeable in the checker. Indexed tokens
retain every object-index obligation even though their runtime representation
is empty. A package's semantic type relates its actual ordered fields to its
actual witness under a private representative world.

`VastitasOracle.IndexedSemantics` proves whole-domain object upcasts, unique
denotation of a given reference, preservation of values/results under world
extension, and fresh local binding. For every accepted closed primitive, typed
runtime operands and (for construction) a fresh world slot produce a typed
result while preserving prior bindings. `VastitasOracle.IndexedPrimitiveSoundness`
states that obligation, and the erasure below, once for any descriptor as the
structure `Sound`. Each registry entry proves its own instance in the module
of its totality lemma; `registry_sound` dispatches to the instances by
constructor, and `primitive_total_and_typed` is its corollary. `checked_primitive_semantics` uses the
actual `CheckedPrimitive`; `core_primitive_semantics` obtains the contract from
the actual Core node's typing derivation, declaration lookup and exact operand/
result conversions. Composition's middle runtime endpoints agree through their
shared nominal reference.

`primitive_runtime_erasure`, the other corollary of `registry_sound`, proves
that a successful logical evaluation of a registry entry erases to the entry's
erased evaluator on the erased operands. The erased evaluator applies the
`IndexedRuntime`, `AlgebraRuntime` or `SmoothRuntime` operation that generated
programs link, including the explicit canonical base for origin.
This operation-level theorem does not prove the generated source or Lean/C
toolchain correct. Native representation does not retain implementation IDs and
cannot supply typing or authority evidence.

Twenty new semantic regressions evaluate the same three fixtures as the native
checks, repeated function/package activations, finite observation exhaustion,
nominal-world behavior, scalar and Pair boundaries, wrong arities/shapes, and
the distinction between operational evaluation and independent rejection of
forged/unused-branch annotations. They run without mathlib.

The later checked-program theorem derives typed total evaluation and allocation
freshness from the actual module audits, including dependent calls; see
[the precise premises and remaining obligations](verification.md#conditional-indexed-term-and-function-evaluation).
Full source operational correspondence and native refinement remain unproved.
These primitive lemmas alone do not establish the [migration acceptance](#geometry-migration)
or assert storage safety, arbitrary geometry or floating-point properties.

### Existential payload preservation

`IndexedPackageSemantics` now relates actual runtime fields to the bound witness
through packing and opening. The transport follows each `BoundIndex` in the
declared template. In particular, if the witness is a global object also named
explicitly by another index, opening replaces only the witness occurrence;
the explicit global remains global. This also applies to token families whose
runtime representation is empty and to multiple heterogeneous ordered fields.

`IndexedSubstitution.valid_opening_of_shape` proves that a valid shape remains
valid at a new witness serial. `openPackage_success` connects that fact and the
checked allocation context's freshness to the actual generated-opening audit.
`opening_fields_semantics` then preserves the actual witness and runtime fields
at the exact reference returned by that audit. `core_pack_semantics` and
`core_opening_semantics` obtain the exact shape and payload association from
actual typed Core nodes and their declaration environment. Fresh dynamic slots
preserve previous world bindings. `IndexedEvaluationSafety` now derives that
freshness throughout the unpack body; `IndexedProgramSafety` discharges its
callee contracts from the actual checked dependency order.

Eleven additional no-mathlib regressions cover a global witness equal to its
explicit global base, two fresh openings, repacking, heterogeneous field order,
forged global annotations, cross-opening field misuse, scope escape and a
non-geometric indexed token. Two new standalone native fixtures exercise the
global-witness round trip and both fields after opening and repacking, bringing
the native fixture suite to five. The package operation lemmas alone do not prove
unpack-body preservation; the later term/function/program theorems supply that
composition and dependent-call transport. Legacy correspondence and
native-toolchain refinement remain pending.

<a id="geometry-migration"></a>

## Finite geometry migration acceptance

This is the acceptance map for #49 and #58–63. It covers the existing ordinary
and smooth affine descriptor language. The [Stage 1 ledger](stage1-completion.md) records the later finite storage, linear algebra and network integration and the Stage 2 performance handoff.

The implementation is declaration driven in all public protocols. Protocol 7
loads `stdlib/src/geometry/{scheme,smooth}/mod.vast` through the single `stdlib`
entrypoint. Protocols 2–6 and explicit `--lib` retain their syntax and wire
formats; `Indexed.LegacySource` adapts their decoded source to the same
`Indexed.AuthoritySource.checkProgram`. The old checked-Core translator is not
a public acceptance path. The temporary `stdlib/indexed` facade is removed.

### Scope of completion

The migration preserves the supported source workflows, nominal rejection rules,
finite primitive results and typed terminating evaluation of the actual returned
Core. Source compatibility is tested through `check`, `build` and generated
executables. The primitive result equations are proved against the retained
runtime definitions. Full surface operational equivalence and native toolchain
equivalence are not proved; #62 explicitly excludes those claims from this gate.
Earlier progress notes saying “legacy semantics/native refinement pending” must
not be read as either a proof of those stronger results or a requirement to prove
an entire native compiler before completing this finite migration.

The old `Declaration.TypeAnnotation`, `Elaboration` and `SourceModuleSafety`
theorems describe the retained legacy Core APIs. Public declarations instead use
`IndexedSource`, `IndexedSourceTypes`, the common function/dispatch/authority
compiler and their input-indexed certificates. The new proofs import those actual
definitions and retain the exact resolution/lowering and returned-Core equations.
No accepted old geometric body is used as evidence for a new body.

### Special-case inventory and disposition

Paths in this table are relative to the repository. Kernel paths abbreviate
`lean-kernel/VastitasKernel/`; oracle paths abbreviate `lean/VastitasOracle/`.
“Adapter” means syntax compatibility followed by common independent checking,
not an alternative semantic acceptance rule.

| Concern / location | Current disposition and independent boundary |
| --- | --- |
| Legacy keywords, reserved names, ring positions and type syntax: `src/frontend.rs`, `src/ir.rs`, kernel `Surface.lean` | Adapter: retains Scheme/CInfScheme/Point/Morphism/Pointed syntax and QQ/CInfReal marker syntax. A marker is not a runtime object. Qualified indexed syntax is parsed separately. Rust diagnostics cannot certify types. |
| Indexed parsing and strict wire schema: `src/indexed.rs`, `src/packages.rs`, kernel `IndexedProtocol.lean`, `IndexedBodyProtocol.lean`, `IndexedAcceptance.lean` | General mechanism: unresolved paths, enclosing owners, family kinds/arity, explicit bindings and complete source bodies; no frontend-supplied authority or checked flag. Older versions reject new declarations/exports instead of discarding them. |
| Old wire conversion: kernel `LegacySource.lean` | Adapter: preserves original bodies, namespaces and edit metadata. Validates the original namespace before adding an ordinary closed unresolved profile; rejects collision with its reserved package identity. That profile passes the same declaration and role checks as a source library. |
| Namespace reservations and lookup: kernel `NamespaceChecker.lean`, `IndexedSourceChecker.lean` | General mechanism with compatibility reservations: canonical package/module/declaration IDs, actual visibility/re-exports and shared-name collision checks. Indexed declarations may use geometry spellings; an ordinary function alias cannot acquire those reserved declaration roles. |
| Classification and representation: kernel `Indexed.lean`, `IndexedAudit.lean`; stdlib `geometry/{scheme,smooth}/mod.vast` | Library plus general mechanism: distinct finite classifications, coefficient markers and implementations. Classification membership does not identify individual objects or add origin/dimension capability. |
| Point/Morphism/Pointed definitions: stdlib `geometry/mod.vast`; kernel `IndexedPackages.lean`, `IndexedContractAudit.lean` | Library plus general mechanism: declared indexed families, same-base constraints, sealed representations, finite single-witness package cases and ordered field templates. General test objects are permitted; Pointed specifically uses the declared base object. |
| Type annotations and legacy type names: kernel `IndexedSourceTypes.lean` | Adapter maps legacy syntax using a selected validated profile; general annotation checking validates declared kinds, sorts, arities, refinement and scope. Object-valued indices and coefficient markers remain distinct. |
| Profile selection: kernel `IndexedGeometryProfile.lean`, `IndexedSource.lean` | Explicit library contract: resolve role paths; validate both settings, distinct markers, exact family/primitive/package roles and complete domains. Exactly one export is needed for legacy syntax. Qualified new syntax needs no export and supports independent libraries. |
| Calls named Affine/Base/origin/id/dimension/compose/apply: kernel `IndexedSourceBodies.lean`, `IndexedFunctionBodies.lean` | Adapter chooses profile declaration IDs, then invokes the same primitive emitter as qualified calls. Fallback is permitted only for an unresolved legacy name (`E_NAME`); a resolved declaration or visibility error never falls back. Operands execute once, in source order. |
| Capture and global-name handling: kernel `IndexedFunctionScope.lean`, `IndexedFunctionBodies.lean` | General mechanism plus adapter names: traverse type indices and package fields as well as expressions; distinguish global declarations from local bindings. Independent lambdas cannot capture outer bindings. Scalar/Fn signature limits remain unchanged. |
| Object identity, substitution and escape: kernel `IndexedCore.lean`, `IndexedTyping.lean`, `IndexedTypeAudit.lean` | General mechanism: unique allocation serials, fixed globals, dependent substitution, generative ordinary object returns/branch merges/openings, and traversal of every free type index, including tokens. Equal descriptors are not identity evidence. |
| Primitive behavior: kernel `IndexedPrimitiveBinding.lean`, `IndexedPrimitiveShapes.lean`, `IndexedPrimitiveValues.lean`, `IndexedPrimitiveDescriptors.lean`, `IndexedPrimitiveRegistry.lean`, `IndexedPrimitiveFamilies.lean`, `IndexedPrimitives.lean`, `IndexedContractAudit.lean`, `IndexedSemantics.lean`, `IndexedRuntime.lean`; generated `src/primitive_table.rs` | Closed explicit registry; see the table below. The wire form comes from the family table of `IndexedPrimitiveFamilies.lean`: the decoder, the resolver and the generated Rust table read it, and a family grants no authority. No arbitrary native registration, certificate string or mathematical axiom is admitted. |
| Diagnostic names/locations: kernel `IndexedSourceDiagnostics.lean`, `IndexedSourceBodies.lean` | Presentation only. “Affine” introduction notes do not choose implementation, merge identities or authorize an operation. |
| Native lowering: kernel `IndexedCodegen.lean` | General Core lowering selected by validated binding/representation tags, not source spelling. Rechecks all declarations, types, scopes, freshness and actual dependencies before emitting reachable functions. Generated modules import only `IndexedRuntime`. Mutable storage is not yet represented. |
| Retained legacy `Checker`, `Declaration`, `Elaboration`, `FunctionChecker`, `FunctionScope`, `Core`, `Semantics`, `Runtime`, `LegacyIndexed` and old codegen | Internal API/regression/proof boundary. Old decoders and scalar/namespace header validation remain reusable; old geometric body acceptance is not called by public `check`/`build`. Their theorems do not substitute for proofs about public indexed Core. |

The adapter remains intentionally supported. Removal requires an explicit decision
to retire the corresponding old syntax/wire contract, not merely deleting reserved
names. No temporary second public geometry checker remains to remove.

### Primitive and proof inventory

Every binding is independently checked against the actual declaration environment.
Family constructors are sealed. `origin` and `dimension` require capabilities for
the complete input implementation domain; arbitrary future Scheme implementations
need not provide either operation.

| Role | Contract and finite runtime result | Evidence |
| --- | --- | --- |
| Affine descriptor | Nat dimension → fresh local object of the declared implementation; runtime stores dimension | `constructor_is_generative`, `descriptor_total`, `GeometryResults.affine_result` |
| Canonical base | No operands → the exact declared global; zero-dimensional runtime descriptor | `global_total`, `global_object_descriptor`, `GeometryResults.base_result` |
| Origin | X → Point<X, declared base>; whole-domain origin support and matching marker | `origin_requires_entire_domain`, `origin_total`, `GeometryResults.origin_result` |
| Identity | X → Morphism<X,X> in the bound family | `identity_total`, `GeometryResults.identity_result` |
| Dimension | Object in an explicitly supported finite domain → Nat dimension | `dimension_requires_entire_domain`, `dimension_total`, `GeometryResults.dimension_result` |
| Compose | (Y→Z, X→Y) → X→Z; exact middle nominal reference | `compose_endpoints`, `compose_middle_agrees`, `GeometryResults.compose_result` |
| Apply | (X→Y, Point<X,S>) → Point<Y,S>; S retained exactly | `apply_preserves_test_object`, `apply_total`, `GeometryResults.apply_result` |

The first names come from `IndexedPrimitives`/`IndexedSemantics` in the oracle.
`GeometryResults` uses the profile's actual declaration lookup and the existing
registry evaluator. `declared_primitive_erasure` connects logical evaluation to
these runtime equations. `GeometryCompatibility.checked_profile` and
`LegacySource.checked_profile` supply the validated profile for public inputs;
`wire_dimension_result` gives a direct public-checker instance.

The equations erase implementation/marker tags just as the runtime does. They
do not authorize mixing bases or identify two static objects; those obligations
are established before erasure. Worlds remain non-injective. The auxiliary
rational zero/identity coordinate interpretation is not a formalization of
arbitrary schemes, all points/maps, or smooth geometry.

### Acceptance-to-evidence map

| Issue / obligation | Implementation, proof and regression evidence |
| --- | --- |
| #58 declarations, kinds, finite domains, versioned unresolved IR | [declaration audits](#indexed-declarations) and this source reference, `IndexedSource` and `IndexedSourceTypes`; `tests/indexed.rs`, `IndexedRegression`, `IndexedSourceRegression`, `IndexedSourceTypeRegression` cover missing/duplicate IDs, sorts/arity, marker metadata, inheritance and order. |
| #58/#63 no privileged library spelling | `tests/stdlib_geometry.rs`: `coherent_renaming_retains_contracts_without_privileged_geometry_names`, `legacy_profile_paths_can_be_coherently_renamed`, `missing_or_ambiguous_profiles_do_not_supply_legacy_meaning`; `tests/indexed.rs::nongeometric_indexed_family_uses_the_same_annotation_checker`. Renaming source, references and profile together preserves native results. |
| #59 nominal identities, substitutions and package association | `IndexedCore`, `IndexedSubstitution`, `IndexedPackageSemantics`, `IndexedWorld`, `IndexedCallTransport`, `IndexedArgumentSafety`; `IndexedCoreRegression` rejects reused brands, forged call substitutions, global rewriting and erased index obligations; package regressions test wrong witnesses and repeated openings. |
| #60 explicit primitives and trust | Registry table above, `IndexedPrimitiveRegression` and actual wire mutations in `tests/stdlib_geometry.rs`; unknown bindings, false roles/capabilities, purported owner/trusted fields and invalid constructors are rejected. No arbitrary evidence registration. |
| #61 existing stdlib workflows and representation freedom | Canonical scheme/smooth module directories, ordinary `pointed` functions, independent abstract annotations, dependent calls/repacking and native 42/2 examples. [Library documentation](https://github.com/MGYamada/Vastitas/blob/main/stdlib/src/geometry/README.md#representation-and-future-design) describes future matrix/equation/subspace/opaque Stiefel/Grassmannian representations without mandatory stored charts. |
| #62 exact accepted Core, typing, all-body coverage and terminating evaluation | `IndexedWire`/`LegacySource` expose exact audit/executable Core; `IndexedFunctions`, `IndexedDispatch`, `IndexedAuthority` cover unused/lifted/nonwinning/out-of-domain/applied/unapplied bodies; `IndexedProgramSafety.checked_functions_total_and_typed` and `checked_main_total` discharge call contracts using the actual dependency order. |
| #62 final independent codegen audit | `IndexedCodegen.generate` requires a strong typed/ordered certificate and repeats the audit. `IndexedCoreRegression` rejects forged declarations/endpoints/substitutions/packages/brand reuse before that certificate can be constructed; `TypeAuditRegression` tests rejection of weaker legacy annotation-only certificates at codegen. `scripts/check_indexed_codegen.lean` and both OS native/no-mathlib CI exercise accepted native generation. |
| #63 compatibility and documentation | Public source matrix below; unchanged v2–6/`--lib`, strict old-version rejection, actual protocol-7 wire mutations, direct namespace/profile/Core regressions, full oracle/axiom audit, this inventory and linked current specifications. |

#### Public source regression matrix

These named tests are in `tests/stdlib_geometry.rs`, using an actual copied
library package and the normal Rust CLI/Lean backend. Valid fixtures run `check`,
`build` and the executable. The rejection matrix runs both `check` and `build`,
requires the diagnostic category, and verifies that an existing output file is
unchanged. Tests for flat old inputs remain in `tests/compiler.rs`,
`tests/functions.rs` and `tests/usability.rs`.

| Required behavior | Test |
| --- | --- |
| Unchanged pointed (42), smooth (2), declared equivalents | `unchanged_legacy_examples_use_the_declared_stdlib_profile`, `pointed_and_smooth_workflows_migrate_without_erasing_abstract_annotations` |
| Dependent Point<X,S> calls, aliases, same-identity branches, repacking, anonymous outer endpoint scope | `dependent_morphism_calls_retain_the_point_test_object_through_repacking`, `legacy_and_declared_types_share_endpoints_packages_and_primitives`, `legacy_alias_branches_and_anonymous_outer_endpoints_survive_library_lowering` |
| Equal-dimensional different objects in apply/compose; wrong base or coefficient-as-object; Affine(QQ,0) vs Base(QQ) | `legacy_endpoint_base_and_scope_failures_preserve_existing_output` |
| Wrong package witness/base; escaping point/morphism/opened field; two opens; ordinary object-return generativity; distinct-object branch merge | `legacy_endpoint_base_and_scope_failures_preserve_existing_output` |
| Bare opened object survives a block, aliases and repackaging; dependent fields still cannot escape or cross openings/call activations | `opened_objects_survive_blocks_in_both_geometry_modules`, `opened_objects_do_not_export_dependent_fields_or_merge_identities`, `legacy_opened_objects_remain_first_class`; Core `escapedObjectFixture` is checked, evaluated and compiled by the standalone native regression |
| Independent lambdas and unused invalid Fn bodies | `legacy_geometry_inside_independent_lambdas_is_checked` |
| Missing capabilities, module visibility, wrong owner/base and false compatibility roles | `classification_does_not_manufacture_missing_implementation_capabilities`, `kernel_reconstructs_module_visibility_and_geometry_contracts_from_wire`, `raw_compatibility_roles_and_old_wire_downgrades_are_rejected` |

### Verification and remaining boundaries

PR #240 (`f2876ef`) established the common public source checker. PR #250
(`6d1d752`) added total typed evaluation: 26 kernel regression targets,
22 native fixtures, full oracle, 14,719-declaration axiom audit and all eight
hosted checks passed. [PR #255](https://github.com/MGYamada/Vastitas/pull/255) adds the primitive result
equations and strengthens the public compatibility matrix. Its final validation
record covers 252 Rust tests (including 21 geometry tests), formatting/strict
Clippy, the 129-job kernel, 26 regression targets, 22 native fixtures, the 734-job
oracle and the 14,749-declaration axiom audit. The PR records the exact final head,
hosted macOS/Linux checks, review and merge; issue closure follows that merge.

The trust boundary includes Rust parsing/serialization, generated source and the
Lean/C/native toolchain. Tests exercise those boundaries; the formal guarantees
start at decoded input and refer to the actual accepted Core. No theorem here
claims complete source-specialization equivalence, general geometry, mutable
storage safety, floating-point accuracy or C-equivalent performance.

#23/#24's broader identity-result/applicative decisions, #28's provenance
architecture and the unimplemented portions of #48/#52/#64 remain open.
No new dispatch keys, geometric Fn signatures, polymorphic object construction,
charts, gluing, tensors or numerical buffers are introduced by this migration.
