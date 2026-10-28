# Indexed declaration foundation

This is internal infrastructure for #58/#59/#62, not completion of those issues
or #49. `VastitasKernel.Indexed` supplies a finite declaration environment and
an independently audited indexed application. It is not yet the public source
checker. Protocol 7 remains unavailable, and the existing geometry checker has
not yet been replaced. No new public source syntax or operation is claimed here.
The declaration base was merged in PR #188 (`09f9e9d`), and package/primitive
annotation contracts in PR #189 (`b3f8ff7`). The internal Core now connects those
contracts to actual terms and standalone native generation, as described below.

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
integration remains part of #60. The ordinary namespace/membership authority audit must also be connected
before a public program may install these declarations.

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

The next integration must update Rust and Lean together, retain unresolved
namespace provenance, introduce protocol 7, and route compatibility syntax into
the same environment-driven type checker. The existing geometry source
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
The existing public compiler and its wire versions 2–6 remain unchanged.

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

Public protocol 7, Rust parsing/resolution, source-to-Core correspondence,
stdlib geometry declarations and the legacy adapter remain pending. Typed
evaluation, activation/world correspondence and native refinement are not
claimed by the new structural theorem or by native regression tests. These
limits prevent closing #49/#58–63 at this increment.
