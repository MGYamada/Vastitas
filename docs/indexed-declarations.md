# Indexed declaration foundation

This is internal infrastructure for #58/#59/#62, not completion of those issues
or #49. `VastitasKernel.Indexed` supplies a finite declaration environment and
an independently audited indexed application. The public compatibility path now
translates its checked legacy Core into this declaration-driven Core for an
additional independent audit and native generation. Package-only protocol 7 now
exposes unresolved declarations and rich source bodies through the full authority
composition; see [source syntax](indexed-source.md). Actual stdlib geometry migration,
the legacy syntax bridge inside protocol 7 and whole-term semantics remain pending.
The declaration base was merged in PR #188 (`09f9e9d`), and package/primitive
annotation contracts in PR #189 (`b3f8ff7`), and Core/native generation in PR #194
(`c29e1cd`). The compatibility adapter is described below.

## Identity and declarations

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
term use of these records is checked by the internal Core below. Public source
integration remains part of #60. The declaration namespace resolver below uses
the actual package visibility and ownership machinery. Scalar membership/edit
audits and complete term elaboration must still be composed before a public
program may install these declarations.

## Unresolved declaration input and namespace audit

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
composition remain pending; the separate internal data-body adapter is described below. The internal regression
constructs Core terms directly; it is not a `.vast` source migration test.

### Dependent type annotations

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

### Internal data-function bodies

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
the internal syntax. Public protocols 2–6 retain the
existing complete function/dispatch/authority path. The later adapters below
compose finite dispatch and authority and are used by the public protocol-7
entry. Stdlib declarations, whole-term evaluation and native refinement remain open.

### Internal independent functions and static specialization

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
acceptance guarantees, not source evaluation preservation or typed termination.

Fifty-five cases cover capture, shadowing, unused bodies, malformed signatures,
private targets, probe separation, branch targets, nominal scope escape, forged
metadata, the 4,096/4,097 boundary and a 4,200-function dependency chain. Four more
standalone native fixtures exercise higher-order/lambda execution, indexed local
operations, a returned private function and ordered package fields. All fourteen
fixtures link only the minimal runtime. The subsequent adapters below add finite
dispatch/all-applicable-body and edit-authority composition. Rust/public protocol
7, stdlib geometry declarations and whole-term evaluation proofs remain pending.
This plain Fn entry rejects old dispatch/edit envelopes explicitly.

### Internal finite dispatch over indexed method bodies

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
Stdlib declarations and whole-term semantics remain pending; the plain dispatch
adapter itself is not the public entry.

### Internal edit authority over indexed contribution bodies

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
These are structural acceptance guarantees; they do not prove whole-source
evaluation preservation, typed termination or native implementation refinement.

Thirty-nine regressions cover nested loan suspension/return, explicit delegation,
contained regions, transfer and revoked old authority, returned Open obligations
and repair, exact private scope, all-body checking, final out-of-domain footprints,
contribution order, empty-root assembly, scope escape and forged metadata.
Four additional native fixtures execute nested contribution helpers, transfer,
obligation repair and the empty-assembly path (twenty-two in total).
Public protocol 7 now decodes Rust source into this exact combined checker.
The protocol-7 legacy syntax bridge and actual stdlib geometry migration remain pending.

## Indexed applications and scopes

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
and fixes globals. Evaluator/codegen refinement proofs remain integration work;
the annotation foundation alone does not establish those broader properties.

## Independent checks and proof boundary

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
unresolved namespace provenance. Compatibility Core already uses
the common environment-driven checker and native generator. The existing geometry source
correspondence and typed-evaluation proofs must move with that path. No old
public spelling is a substitute for completing this work.


## Single-witness existential contracts

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
and allocation nodes. Runtime value correspondence remains a proof obligation.

`VastitasOracle.IndexedPackages` proves the executable audits equivalent to their
independent propositions, field/witness association, absence of any other free
local field index, scoped opening fields, brand freshness and distinct reopening.
These package-layer theorems concern the exact checked **type annotations**.
The Core layer below additionally checks actual field terms; evaluator/package-
value correspondence is not yet proved.

## Closed primitive binding inventory

`IndexedPrimitives.lean` represents explicit bindings to a closed finite registry.
No source spelling, arbitrary native symbol, certificate string or `trusted` flag
chooses an implementation. The binding IDs, operand annotations and result
annotation are independently audited against the same checked environment.

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
axioms, source-term typing, evaluation or native equivalence. Binding this
registry to the source checker and porting the existing evaluator proofs are
still required before #60/#62/#63 can close.

`IndexedPackageRegression` and `IndexedPrimitiveRegression` add 45 direct cases,
including repeated openings/repacking, false field associations, abstract-domain
capability loss, changed family IDs, false result endpoints and reused brands.
Wire versions 2–6 retain their source contracts; their final lowering now passes
through the common declaration-driven Core.

## Audited Core and native generation

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
indices. References already present inside an outer indexed value remain in
scope even when that object's original binding was anonymous. Packages use an
explicit finite case table indexed by domain and coefficient marker, at most
64 cases per declaration. Cases cannot overlap. Runtime objects and dimensions
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

Public protocol 7 now parses and independently resolves declarations;
source-to-Core semantic correspondence and stdlib geometry declarations remain pending. Typed
evaluation, activation/world correspondence and native refinement are not
claimed by the new structural theorem or by native regression tests. These
limits prevent closing #49/#58–63 at this increment.

## Compatibility adapter for protocols 2–6

`LegacyIndexed` translates the actual legacy checked Core into the same indexed
terms audited above. Its closed compatibility profile explicitly declares two
coefficient markers, the existing two affine implementations, canonical base
objects, indexed point/morphism families, two existential cases and the closed
primitive bindings. Each legacy object type admits exactly its existing affine
implementation; it does not grant operations to an arbitrary future classification.
Reserved compatibility declaration IDs come from the adapter itself, never a
source filename or displayed name. Object serials, dependent substitutions,
actual bodies, call IDs and entrypoint selection survive translation.

The public `check` path requires both existing acceptance and the common audit.
The public `build` path and legacy `Codegen.generate` API independently validate
legacy certificates, translate, audit the resulting indexed Core and invoke
`IndexedCodegen`. The former duplicate geometry/native renderer is removed.
Generated programs import only `IndexedRuntime`; the old runtime remains for
the existing legacy evaluation theorems. Ordinary compilation still needs
neither mathlib nor OpenBLAS.

The signature table is reconstructed once per module using a hash index.
`VastitasOracle.IndexedSignatures` proves membership, absence and actual-target
correspondence. The shared `Distinct` audit proves its hash-set check equivalent
to list distinctness; both old and indexed typing reuse it. The existing
20,000-function watchdog regression continues to pass through this added audit.

`VastitasOracle.LegacyIndexed.check_acceptance` connects the exact adapter input,
its actual converted module, complete typing on both sides and the real dependency
graphs. Nine `LegacyIndexedRegression` cases check the profile, executable package
translation, forged certificates, mutated converted Core and cross-base reuse of
a numeric serial. Existing source/native tests exercise both geometric settings,
unpack, higher-order specialization, dispatch, packages and edit authority through
the new path.

This is a structural compatibility bridge. It does not prove evaluation
preservation of the translation, activation/world correspondence or native
equivalence. Legacy source-to-Core and evaluation theorems still describe the
retained legacy intermediate; the indexed semantic bridge remains explicit work.
Source geometry declarations have not yet moved to `.vast` stdlib files, so
this adapter alone does not complete the migration.

## Indexed runtime semantics: first proved fragment

`IndexedSemantics` defines values and a bounded observation of the actual Core
terms, with strict argument evaluation, separate function activations, explicit
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
result while preserving prior bindings. `checked_primitive_semantics` uses the
actual `CheckedPrimitive`; `core_primitive_semantics` obtains the contract from
the actual Core node's typing derivation, declaration lookup and exact operand/
result conversions. Composition's middle runtime endpoints agree through their
shared nominal reference.

`primitive_runtime_erasure` proves that a successful logical registry operation
erases to the corresponding actual `IndexedRuntime` operation, including the
explicit canonical base for origin. This operation-level theorem does not prove
the generated source or Lean/C toolchain correct. Native representation does not
retain implementation IDs and cannot supply typing or authority evidence.

Twenty new semantic regressions evaluate the same three fixtures as the native
checks, repeated function/package activations, finite observation exhaustion,
nominal-world behavior, scalar and Pair boundaries, wrong arities/shapes, and
the distinction between operational evaluation and independent rejection of
forged/unused-branch annotations. They run without mathlib.

Whole-term preservation/totality, dependent-call world correspondence,
deriving dynamic freshness from the allocation audit, legacy
translation preservation and stdlib declaration migration
remain open. These primitive lemmas do not close #49/#58–63 or assert storage
safety, arbitrary geometry, floating-point properties or full native refinement.

## Existential payload preservation

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
preserve previous world bindings; deriving that freshness throughout execution
remains a whole-term obligation.

Eleven additional no-mathlib regressions cover a global witness equal to its
explicit global base, two fresh openings, repacking, heterogeneous field order,
forged global annotations, cross-opening field misuse, scope escape and a
non-geometric indexed token. Two new standalone native fixtures exercise the
global-witness round trip and both fields after opening and repacking, bringing
the native fixture suite to five. The package operation lemmas do not yet prove
the unpack body or dependent calls preserve types, the whole program terminates,
or the native toolchain refines the semantics.
