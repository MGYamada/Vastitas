# Verification boundaries

The proof oracle in `lean/` imports the implementation's definitions from
`lean-kernel/`. It has no executable target and is not consulted when compiling
or executing `.vast` programs. mathlib is pinned to v4.35.0; the executable
kernel and generated runtime depend only on the Lean distribution.

Flat protocol versions 2 and 4 enter through `checkSurfaceProgram`. Package
versions 3 and 4 resolve namespaces before entering the same surface checker.
Protocol 5 additionally validates the edit assembly and final contributions.
Protocol 6's `checkAuthorityProgram` additionally validates nested delegations
and current-owner transfer histories before entering that same surface checker.
The first-order `checkProgram` API is an input adapter to that checker.
All inputs check independent lambdas, static function contracts and finite
dispatch families, then use one lowering and specialization implementation.
They pass the exact lowered module to
`checkModule`, the internal Stage 0 core checker. The
combined core theorem, `VastitasOracle.checkModule_sound`, establishes decoded
core source correspondence, independent typing, a strict function dependency
order, and finite typed evaluation. Stage 1a has additional finite-selection
and checker-composition theorems, extended in Stage 1b as described below.

## Checked language and independent audits

The checked `Term` language retains normalized integer literals, finite
operator and builtin constructors, resolved variable and function symbols,
types, object references, and dependent call substitutions. Object identity
metadata remains available through checking and is erased during code
generation. The formal evaluation relation operates on this actual `Term`
language and uses the actual runtime objects, points, morphisms, and packages.
It also includes the closed `Pair<Nat>` / `Pair<Int>` types, construction and
projections. The declaration/expression correspondence and whole-core safety
proofs cover these operations. Separate [stdlib numerical contracts](promotion.md)
cover the value policy of promotion and its arithmetic callers.

Successful core `checkModule` runs two independent audits after elaboration:

- `Typing.auditModule` checks the structural typing rules for every term,
  including variable lookup, operand types, dependent arguments and their
  final substitutions, branch identities, packages, parameter and return
  scopes, and uniqueness of function IDs and fresh nominal references.
- `Dependency.auditModule` checks that every call refers to an earlier
  function in the finalized order. This establishes acyclicity independently
  of the topological sorter's implementation.

The typing rules are defined separately from the elaborator's control flow;
they are not defined as the statement that elaboration succeeded.
`VastitasOracle.checkModule_typed_and_ordered` unfolds the actual core checker
and proves that acceptance yields its actual elaborated module satisfying
both `Typing.ModuleWellTyped` and `Dependency.ModuleOrdered`.

`CertifiedModule` still carries the smaller annotation postcondition:
compatible endpoint bases and agreement between each body's annotated result
and its declared return type. `certifiedModule_annotation_property` is the
projection of that subtype property. It does not establish the stronger
typing, dependency, or source-correspondence results. The public
`Codegen.generate` boundary repeats the independent audits, so constructing
this weaker certificate directly cannot bypass them.

## Stage 0 source correspondence and type safety

`VastitasOracle.Elaboration.checkModule_source_correspondence` proves the
independent `ModuleCorresponds` relation between an accepted decoded core
`RawModule` and the actual checked module. Parameter and return annotations
retain their source type and index resolution. Expression and block
correspondence covers name resolution, normalized literals, finite operators,
calls, local annotations, lexical scope, and `let`/`pack`/`unpack` lowering.
Every core source declaration has a corresponding checked function, every
checked function has a core source declaration, and reordering cannot drop or
synthesize functions. The selected entrypoint corresponds to the finalized
function named `main`.

`VastitasOracle.Safety.evaluation_total_and_typed` proves finite big-step
evaluation and type preservation for every checked term constructor, assuming
typed contracts for its callees. The verified dependency order discharges
those contracts for the entire module.
`VastitasOracle.ActivationSafety.checkModule_total_for_arguments` states that
if the actual core `checkModule` accepts, every function in its result
evaluates to a value of its declared return type for every well-typed argument
environment. The caller does not need to supply an additional freshness or
injectivity hypothesis.

Nominal references are interpreted in a world local to each function
activation. These interpretations are deliberately **not injective**:
different static identities may denote equal runtime descriptors. For example,
an object-returning helper can give its result a new static identity while
returning the same descriptor it received. Fresh activation and local
allocation preserve existing meanings without equating distinct identities.

For `Point<X, S>`, value typing states that the runtime point's target and
source equal the interpretations of `X` and `S`. Morphisms preserve the same
endpoint correspondence. Packages hide their object's identity while retaining
the association with their point; opening a package introduces a fresh local
reference. The proofs also connect the actual `checkApply`, `checkCompose`,
`checkPack`, scope-checking rules, and dependent substitutions to these runtime
properties. Scope permits canonical bases and references already represented
by enclosing object bindings or the types of enclosing values.

## Stage 1a finite dispatch and checker composition

The actual reusable finite engine is `VastitasKernel.Dispatch.check`; the
theorems below are in `VastitasOracle.Dispatch`. Public ground types are Nat,
Int, Bool, and Unit. Specificity uses the product of nominal subtyping and
implication of normalized requirements, including `HasOrder ⇒ HasEq`. It does
not compare the sets of keys on which methods happen to apply. Static tuple
facts are the intersection of argument facts; the empty tuple has no facts.

`Optimal` and `Selection` are independent of the candidate-selection algorithm,
but are stated over the kernel's executable `applicable`, `moreSpecific`,
normalization, tuple-fact and hierarchy definitions. Those definitions specify
the order used by the theorems. Their correspondence with the prose product
order is supported by code inspection and regressions, not a separate theorem
deriving these helpers from an independent mathematical specification.

- `check_sound` connects successful execution to the independent `Optimal`
  and `Selection` conditions. It also establishes actual normalization,
  unique method identities and normalized signatures, realizable method
  conditions, and the correctness of every selected row. Ambiguity checking
  covers the entire enumerated universe, including keys outside the declared
  callable domain.
- `check_key_universe` proves that the enumeration contains every concrete
  tuple of the declared arity, has exactly `4^arity` elements, and has at most
  4096 elements. `domain_coverage` proves that every declared callable key has
  a selected method.
- `winner_sound` proves that the selected ID belongs to the unique optimal
  method. `winner_identity_unique` additionally proves that no other record
  in the accepted family has that ID, including inapplicable records.
- `applicablePairs_complete` characterizes the exact list of applicable
  method/key pairs exposed for ground body checking. It includes losing
  methods and keys outside the callable domain.
- `check_permutation_success` proves that permuting method records preserves
  acceptance and the exact winner rows. `check_order_independent` states the
  corresponding equality of selections. Stable IDs remain attached to their
  records; these theorems do not equate unrelated IDs reassigned by a frontend.

The generic `checkWith` engine and its soundness/permutation theorems use the
same algorithm for other validated finite hierarchies. Synthetic multiple
inheritance and triple-intersection tests exercise that engine. They do not
add user-defined types or capabilities to the public language.

`VastitasOracle.DispatchLowering.selected_target_sound` connects the backend's
actual family-check and target-selection evidence to domain membership and
the unique optimal method. The same namespace provides the public checker
composition results:

- `checked_call_pair_result` proves that the independently audited call result
  equals the Pair element type of its actual looked-up signature. It applies
  to the typed cores returned by all three public acceptance paths; it does
  not add a full source-rewriting equivalence claim.
- `checkProgram_core` proves that successful `checkProgram` execution produced
  an exact lowered core module accepted by the actual `checkModule`.
- `checkProgram_typed_and_ordered` establishes independent whole-module typing
  and an acyclic dependency order for the resulting checked core.
- `checkProgram_total_for_arguments` proves that every function in that exact
  result evaluates to a value of its declared return type for all well-typed
  argument environments. This includes the core's runtime endpoint and
  package correspondence guarantees.

The finite Stage 1a implementation passed repository validation and hosted CI,
including the proof/axiom audit and macOS/Linux compiler builds without mathlib
([acceptance run](https://github.com/MGYamada/Vastitas/actions/runs/40336834442)).
This is not completion of all Stage 1 features in the historical design.

The proofs contain no `sorry`, `admit`, or project-specific unproved axioms.
CI audits the oracle namespace against Lean's standard logical axioms
(`propext`, `Classical.choice`, and `Quot.sound`).

## Stage 1b capture and static function contracts

`VastitasOracle.Functions` imports the actual `FunctionChecker`. Surface Fn
syntax is separate from core Raw/Checked IR. The actual acceptance path checks
`CaptureFree`: lexical free names of every independent lambda (including type
indices, with parameters and ordered local bindings accounted for) are global
names. Nested lambdas are checked in their own scopes. This predicate is
specified separately from lifting and specialization.

- `checkSurfaceProgram_capture_free` proves the predicate for every accepted
  surface program; `lambda_free_names_are_global` exposes its scope/name result.
- `checkSurfaceProgram_static_calls` identifies the exact
  `lowerFunctions` result, proves `StaticCallsValid` for its recorded calls, and
  retains the equation showing that the very same core passed `checkModule`.
- `static_target_signature` and `function_argument_signature` state structural
  type equality with actual backend definitions for recorded targets and erased
  function arguments. They follow from the independent audit established by
  the preceding actual-checker theorem, not from a trusted frontend annotation.
- `checkSurfaceProgram_core` connects the common surface lowering to
  actual core acceptance. `checkSurfaceProgram_typed_and_ordered` and
  `checkSurfaceProgram_total_for_arguments` establish independent typing,
  dependency order and terminating typed evaluation of the returned module.

The static audit concerns the actual recorded selection ledger. These results
are not a theorem that this ledger corresponds operationally to every source
application, or that lambda lifting, abstract signature probes and erasure
preserve the full surface-language meaning. The audit checking pass and the
executable specialization pass use separate state; probes never reach codegen.
Regressions test unused-body checking, static selection and native results
across the remaining correspondence boundary. No new unproved axiom is used.

## What is outside these claims

The [dense layout/preflight reference](storage-layout-preflight.md) separates
byte bounds, alignment, write injectivity, native narrowing and loan conflicts.
Its Python regressions and successful-session receipts do not establish Lean
resource safety or authorize native check elimination. The linked document
states the pending all-access, exact-return and successful-branch soundness
obligations for the actual Ownership/Borrow Checker.

The separate [internal resource IR](storage-ir.md) now has actual-checker
theorems in `StorageLayout`, `StorageRegions` and `StorageSafety`: all-cell
bounds/alignment/byte separation, footprint containment and initialization
entailment, normalized write/join meaning, and nonoverlap of distinct active
loans when either writes. Exact decoder/checker certificates start from an
empty logical environment. `StorageCodegen` proves that successful native-plan
lowering follows those actual transitions, has unique instructions for the same
input, and requires the rechecked schedule before returning code. The optional
native runtime has sanitizer and generated-executable regression evidence for
real/complex buffers, output preservation and failure cleanup. These results now compose with the initial static protocol-8 source profile;
they do not extend pure-Core totality to mutable storage. Actual memory initialization,
allocator liveness, native cleanup and native refinement are not proved; C
performance comparisons remain pending. The [internal resource function component](storage-functions.md)
adds actual call-slice replay, restored caller loans, unique live owned results
with declared initialized bytes, and checked probes for every source body.
Probes are separate from executable expansion and do not prove a universal
parametric contract; actual calls are independently checked again. The raw component does not change pure-Core semantics.
[Protocol 8 resource source](resource-source.md) composes the actual authority/Fn/dispatch
checker, independently resolved resource calls, every resource-body probe and exact
entry schedule. `VastitasOracle.ResourceSource` proves complete resource identities,
actual call provenance, original authority trace, typed totality of its returned
pure Core and closed logical entry resources. The public decoder/checker equations
refer to that same input. Dynamic shapes/value flow and native/source refinement
remain separate obligations.

The internal [Graph crossing checker](graph-crossings.md) has separate
profile/port/return audits and conditional structural rewrite theorems in
`VastitasOracle.Graph`. It does not extend these source/Core evaluation claims
to tensor syntax. Its categorical law provider, selected-method realization,
and bridge from `Graph.Core` to actual returned indexed terms remain pending.

The [exact real ℓ² tail reference](l2-tail-reference.md) checks closed geometric
and reciprocal certificate rules with rational arithmetic in Python. Its
generator/environment/returned-record audits are reference tests only. The
document states the Lean analytic soundness goals and actual returned-Core
integration obligations; no new Hilbert theorem, compiler acceptance,
completeness proof, or iterator memory-safety claim follows from those tests.

The Stage 0 source-correspondence theorem starts at decoded core `RawModule`.
The full Stage 1 rewriting pass from decoded surface `Program` (or legacy
`RawProgram`) to that core does
**not** yet have a source-correspondence theorem. Finite selection tables and
actual target evidence are proved correct, and the entire resulting core is
proved well typed and terminating; this does not establish correspondence of
every rewritten source call or method body to its original generic syntax.

These results do not verify Rust lexing, parsing, source-library composition, JSON
serialization or decoding, diagnostic spans, or the accuracy of diagnostic
prose. The core correspondence relation records elaboration into checked
syntax; it is not a separate operational-equivalence theorem for source text.

The big-step semantics evaluates both operands of Boolean `&&` and `||`;
generated Lean uses short-circuit evaluation. The proved contract concerns
values and types in the pure, terminating Stage 0 core. It does not assert
identical evaluation order, execution traces, or resource costs. Nor is there
a proof that generated Lean source, Lean's compiler, generated C, the C
toolchain, linker, OS, and hardware preserve the denotation. Native regression
tests establish observed results for tested programs across that boundary.
Mathematical termination is not a bound on compilation or execution time,
memory use, or stack consumption.

The ordinary/smooth affine descriptors remain a restricted geometric core.
These results do not formalize all schemes or C-infinity schemes, prove
general geometric constructions, establish numerical accuracy, or certify
physical adequacy. The auxiliary coordinate interpretation is limited to the
stated zero/identity fragment. User-defined types and
capabilities, ownership transfer, storage ownership, linear
algebra, iteration, and recursion remain unimplemented and outside these
theorems. Finite static dispatch does not establish those later Stage 1 goals.

## Validation

The [initial promotion contract](promotion.md) documents the arbitrary-input
numerical proofs in `VastitasOracle.Promotion`, reflection of the actual checked
stdlib bodies, frontend-fixture agreement, and the distinction between proof
statements and executable fixture/namespace/native checks.

Run from the repository root:

```sh
cargo fmt --all -- --check
cargo clippy --locked --all-targets -- -D warnings
lake -d lean-kernel build vastitas-kernel
bash scripts/check_kernel_regressions.sh
cargo test --locked --all-targets
lake -d lean build VastitasOracle
python3 -m unittest discover -s scripts -p 'test_*.py'
python3 scripts/check_boundaries.py
```

`TypeAuditRegression` is an explicit build target: its executable checks forge
checked terms directly, bypassing elaboration. They exercise invalid operand
and result annotations, variables, nominal identities, substitutions,
packages, symbol reuse, and dependency cycles. They also verify that the code
generator rejects forged modules carrying only the legacy annotation
certificate. These tests complement the logical soundness theorems.

`DispatchRegression` directly exercises the same finite checker used by the
backend, including product-order ambiguity, capability normalization,
ambiguity outside the callable domain, missing coverage, zero-argument facts,
invalid hierarchies, multiple inheritance, unresolved triple intersections
after pair repairs, complete triple repairs, permutations, and the 4096-key
boundary. It also checks that applicable losing methods and keys outside the
domain appear in the ground-body work list.

`FunctionRegression` exercises actual public function acceptance, capture
rejection and forged static signatures, including mismatched types with equal
arities and unknown targets for erased function arguments. Rust function tests
cover native higher-order composition, independent nesting, all Fn arities,
dispatch and multiple libraries, unused invalid bodies, changed diagnostic
spans, the 4096-instance limit and reachability after whole-module checking.

Rust integration tests exercise parsing and diagnostics, malformed raw IR,
semantic rejection codes, native execution, source libraries, implementation
limits, dispatch specialization and rejection, and preservation of existing
output artifacts on failure. The compiler CI jobs build and test on macOS and
Linux from a checkout without `lean/` or mathlib, including the direct kernel
regression targets. A separate job builds the proof oracle and audits its
axioms. Dependency-boundary checks prevent the normal compiler path from
acquiring a mathlib dependency.


## Package namespace acceptance

`VastitasOracle.Namespaces` imports the actual `NamespaceChecker` implementation.
`checkNamespaceProgram_audited` connects acceptance to the actual namespace
lowering result, unique declaration owners, re-resolution of the recorded
reference ledger through the actual resolver,
and acceptance of that exact surface program. `reference_resolves` establishes
that each recorded reference resolves to its recorded target through the real
visibility/import resolver. `method_owner` requires a generic in the exact
referencing module; children and imports acquire no edit authority.
`alias_preserves_target` unfolds the actual import branch and proves that it
returns the original target. The reference audit uses the same resolver as
lowering; it does not independently specify name resolution. Correspondence
between the ledger entries and names emitted into the surface program is not
proved.

The kernel builds one internal declaration index per namespace check and shares
it across lowering, binding checks, validation and reference auditing.
`indexed_owner_lookup` and `indexed_scope_lookup` prove equality with the
original list search/filter, including first-declaration behavior on duplicate
input. No index is accepted from wire IR. `alias_preserves_target` retains the
original list-search premise while unfolding the actual indexed resolver.

`same_logical_owner_same_symbol` is congruence: equal owners have equal symbols.
The `Owner` structure contains package identity, logical module path and
definition name, but no source-file placement or alias spelling. This structural
fact is not a proof of filesystem-layout invariance. Injectivity of `encode`
and `Owner.symbol` is not proved; namespace validation checks that the actual
generated symbols are distinct with a separate runtime `Nodup` check.

The typed/ordered and total-for-arguments namespace theorems compose with the
existing surface/core theorems for the exact returned `CertifiedModule`.
`NamespaceRegression` and `tests/namespaces.rs` check aliases, duplicate owners,
visibility, cycles, unauthorized methods, forged reference-ledger entries,
malformed raw protocol metadata, unused invalid bodies and v2 compatibility.
These regressions and `PairRegression` run in no-mathlib CI.

This does not prove Rust filesystem loading/authenticity, full source namespace
syntax preservation, native toolchain equivalence, or general
abstract values. Package metadata identifies entries in the supplied IR graph; it does
not certify the bytes on disk. The general Stage 1 design remains incomplete.


## Finite abstract selector acceptance

`VastitasOracle.AbstractTypes` imports `VastitasKernel.Abstract`. The checked
hierarchy retains proof fields for the actual `hierarchyValid` and
`preservesBuiltins` predicates, the fixed four concrete keys, and the unchanged
capability fact function. `build_order_independent` proves that the actual
canonical-name/edge/closure construction is equal under permutations of the
type and membership declaration lists. `selected_nominal_target` connects the
actual family `checkWith` equation to the finite engine's selection theorem.
This is nominal order, not containment of current inhabitant sets.

`Namespaces.membership_owner` establishes exact defining-module authority from
the independently re-resolved ledger; alias visibility follows the same resolver
as calls. `AbstractRegression` and `tests/abstract_types.rs` cover multiple
inheritance, same-inhabitant ambiguity, uninhabited declarations, limits, cycles,
builtin changes, aliases, unauthorized membership edits, raw IR tampering,
ordinary/Fn value-type rejection, and native execution. The source/core/native
and mathematical-geometry proof boundaries described above remain unchanged.


## Abstract method contract acceptance

`VastitasOracle.Contracts` imports the actual `Contracts` and `DispatchChecker`
definitions. The checker retains evidence that each expanded domain satisfies
its parameter selectors/capabilities, that every contract key belongs to the
actual callable union, and that the selected source result equals the contract
result. `contract_covered` composes those checks with the existing finite engine
soundness theorem: every contract key has its unique optimal concrete winner
and the required result annotation. Contracts are not candidate methods.

`expanded_key_iff` and `callable_key_iff` characterize the actual expansion
and union as membership propositions. `expand_order_independent` proves invariance under domain-clause permutation;
`effective_domain_order_independent` proves the actual canonical union invariant
under permutations of the base keys and validated contracts. Together with the
hierarchy construction and finite engine's method-permutation theorems, these
cover the order-independent components used for selection. They do not assert
that diagnostics have identical ordering, or prove all parser/lowering behavior.
The existing `Functions.checkSurfaceProgram_core` and namespace composition
continue to connect protocol-4 acceptance to the exact independently checked
core, its typing, dependency order, endpoint preservation and termination.
No theorem asserts native toolchain equivalence or mathematical properties of
uninhabited Variety/Manifold declarations. Compiler/runtime remain mathlib-free.

## Stabilization audits

`checkNamespaceProgram_full_audit` and `accepted_memberships_authorized` connect
the public package checker to a separately reconstructed membership graph.
Every inherited scalar membership has support declared in the ancestor's exact
module, using an abstract-only inheritance path. This is a decoded-input
authority guarantee, not filesystem or author authentication.

The common function lowerer indexes structural function/instance identities.
`definitionLookup_matches_list` proves equality with the original first-match
list lookup, even before duplicate-name validation. The independent static-call
audit has a different contract: it must find *any* definition with both the
requested identity and structural signature. Its backend-built index therefore
retains every definition in each identity bucket. `definitionBuckets_matches_list`
proves exact equality with filtering the original list; this evidence is erased
at runtime. `staticTargetValid_iff`, `staticBindingValid_iff` and
`staticCallsValid_iff` establish full equivalence to the original existential
specification, without a uniqueness premise, including duplicate identities
with different signatures. `checkSurfaceProgram_static_calls` uses that
equivalence for the actual lowered result and the same accepted core.

Ordered output arrays and active diagnostic stacks remain explicit. Completed
instances are memoized in a separate map; active membership uses a set, and
completion pops the stack and erases the key without filtering the entire stack.
Signature-probe and executable passes have separate state. Type shape checks do
not count a synthesized Fn wrapper toward the 64-level declared-type limit.
See [the indexing regression and measurement notes](stage1b-indexing.md).

Run the transitive local axiom audit with:

```sh
(cd lean && lake env lean ../scripts/audit_axioms.lean)
```

`python3 scripts/benchmark_lowering.py` measures parameterized call chains. On
the local macOS host, three-run medians for 2,000 / 4,000 / 8,000 functions were
0.080 / 0.190 / 0.531 seconds without a lambda and 0.080 / 0.190 / 0.519 with one.
These are observations, not timing guarantees or a proof of total compiler
complexity. The integration suite also checks 20,000 functions in both modes
under its 60-second watchdog.

## Scoped edit assembly acceptance (protocol 5)

`VastitasOracle.EditBorrowing` imports the actual `VastitasKernel.Edit` checker.
Its `runTrace_sound` proves that successful execution has a `Trace` whose every
step satisfies the independent `TransitionAllowed` relation and `StateValid`
provenance/exclusivity predicate. `trace_final_exclusive` and
`assembled_applications_authorized` connect that trace to canonical generic loans
and exact owner/grantee/region records. `return_preserves_contributions` preserves
the full installed method list, including bodies and provenance, while allowing
Open returns. Exact replay compares those complete records, not hashes or names.

`grant_lowering_correspondence` and `contribution_lowering_correspondence` connect
the accepted prepared records to re-resolution of every original decoded grant
and contribution from its declaring scope. The accepted certificate also retains
namespace uniqueness/reference audits, inherited membership authority, and the
actual `Namespace.lower` result. `final_method_provenance` witnesses every added
method in a complete original contribution. No frontend owner flag is trusted.

`final_winner_authorized` proves that every final table row won by an externally
installed method belongs to that application's approved region. The certificate
retains the actual `completeFamilies` equation, using the existing finite dispatch
and abstract contract checks for all-key uniqueness, union coverage and exact
contract results. Seal prevents subsequent edits of that generic; completion is
checked over the final immutable environment before acceptance. This does not
claim an intermediate Open state is callable or complete.

`checkEditProgram_audited` unfolds the public checker: its exact discarded audit
surface and exact final executable surface both pass `checkSurfaceProgram`.
The audit adds ground instances of unapplied contribution bodies without adding
dispatch candidates. Existing all-applicable-method checks include losing applied
bodies. `checkEditProgram_typed_and_ordered` and
`checkEditProgram_total_for_arguments` compose the final accepted module with
existing core typing, dependency and terminating typed-evaluation theorems.
This composition does not prove arbitrary Rust parsing or native codegen correct.

`EditRegression` runs through `NamespaceRegression` in the common eight-target
script. It exercises actual acceptance and direct Lean API forgery attempts.
`tests/edit_borrowing.rs` covers source packages, tampered protocol 5, alias replay,
exclusive loans, owner suspension, Open repair, final footprints, losing/unused
bodies, changed hierarchy/contracts and native execution. Both run in macOS/Linux
no-mathlib CI; the proof oracle and transitive axiom audit remain separate.
Guarantees start at decoded input, not filesystem authenticity or authorship.

### First finite edit composition contract (v1)

`VastitasOracle.EditBorrowing.checkEditProgram_finite_acceptance`, in
[`EditAcceptance.lean`](../lean/VastitasOracle/EditAcceptance.lean), has the premise
`checkEditProgram program requireMain = .ok certified` and concludes
`∃ assembled : Assembled program.indexed,
FiniteEditAcceptance program requireMain certified assembled`.
It calls `checkEditProgram_audited` **once**, then composes existing results for
that witness and its final-surface acceptance equation. No executable checker,
lowering pass or underlying soundness proof is reimplemented.
This includes the current omitted-assembly/empty-trace path; no new condition
requires a call-only consumer to provide an explicit assembly.

The proposition is indexed by the complete decoded `Namespace.Program`, the
entrypoint policy, the exact returned `CertifiedModule`, and one assembly.
The assembly retains the actual preparation/base-lowering equations, namespace
and membership authority, sealing, `completeFamilies` for its final surface,
and construction of its unapplied-body audit. The new bundle adds:

| Evidence | Exact object and established contract |
| --- | --- |
| `assembledFrom`, `auditAccepted`, `finalAccepted` | This input produces this assembly; its discarded audit passes; its final surface returns exactly `certified`. The audit result is deliberately not the executable Core. |
| `trace`, `exclusive`, `returned` | Each finite edit step satisfies `TransitionAllowed` and the next state's `StateValid`; the final state is exclusive and has no outstanding edit loans. Owner suspension, exact grantee authority and return preservation are the existing transition contracts. |
| `grantsFrom`, `grantsAuthorized`, `contributionsFrom` | Grants and complete contribution records are reconstructed from this decoded input; authority uses exact defining/grantee scopes. |
| `applicationsAuthorized`, `methodProvenance` | Applied records have their exact grant/owner provenance; every final method belongs to the base or an original reconstructed contribution. |
| `winnerAuthorized`, `dispatchCorrect` | In this assembly's completed families, external winners stay in their approved regions and the finite engine satisfies `Dispatch.Correct`, including unique optimal selections and callable-domain coverage. All-key rows include keys outside callable domains. |
| `loweredAccepted` | The same final surface produces an actual `Surface.Lowered`, its static-call ledger is valid, and its exact raw Core passes `checkModule` with the same policy and returned `certified`. |
| `typed`, `ordered`, `total` | `certified.val` is independently well typed and acyclic; every function in that same module has finite typed evaluation for every well-typed argument environment. |

`FiniteEditAcceptance.accepted` recovers the actual acceptance equation from
the bundle. `FiniteEditAcceptance.unique` proves equality of both assemblies
and returned certificates for two bundles with the same decoded input and
policy. Changing the input, assembly, policy or returned Core requires new
proofs or explicit equality transport. A different independently well-typed
Core or the legacy annotation-only certificate is insufficient. This is a
proof-only `Prop` with proof-requiring constructors, not a serialized success
flag or a new runtime `AcceptedProgram` API.

This is a **limited first composition for #184**, not completion of that issue,
all eight Domain Checkers, or the independent Ownership/Borrow checker. It adds
no release condition. The stable architecture remains **8 Domain Checkers + 1
independent Ownership/Borrow Core Safety Checker**. Only the finite dispatch,
provenance, edit-loan and Core facts above are composed; no missing domain is
given a fabricated `Verified` field.

| Remaining obligation | Status relative to this theorem |
| --- | --- |
| Full Source → Core correspondence | Still unproved for Stage 1 surface rewriting, specialization and erasure. Exact execution equations and static-ledger validity do not establish operational correspondence of every source call/body. Existing Stage 0 decoded-Core results remain narrower. |
| Input/snapshot authenticity | Fixed decoded data and structural package/module identities only. Rust loading, parser/JSON decoding, dependency snapshots, on-disk bytes and authorship are not authenticated by this theorem. |
| General storage ownership/borrowing | Not covered. Exclusive whole-generic edit loans and their return do not establish storage alias safety, moves, reborrowing or lifetimes. |
| Domain applicability and obligation ledger | No general claims/profile applicability or transformation-preserved obligation ledger is proved. Existing finite checks do not complete Graph, Fiber/Basepoint, Linearity, Regularity, Descent, Base/Coefficient/Grading, Coherence or Provenance as general domains; separate finite results are not silently incorporated. |
| Effects, transforms and backends | Totality is the existing pure terminating Core semantics, not a general effect/partiality policy, AD/optimizer preservation, numerical refinement, native equivalence or a resource bound. |

The proof adds no axiom or native reflection shortcut. The existing transitive
oracle audit checks its dependencies against `propext`, `Classical.choice` and
`Quot.sound`; the pinned Lean toolchain/kernel remains part of the trust boundary.

#### Regression connection and validation

[`scripts/check_edit_acceptance.lean`](../scripts/check_edit_acceptance.lean)
contains compile-time attempts to reuse evidence for a different program,
policy, assembly or even another well-typed Core. They must fail. It also proves
that a genuinely different returned Core cannot have a bundle for the same
accepted input, and that a rejected input cannot acquire a bundle. The existing
oracle CI runs this script after building the oracle.

The existing executable regressions exercise the hypotheses of the composition:

| Existing suite | Rejection boundary connected to the bundle |
| --- | --- |
| `EditRegression` | Changed contribution bodies, forged grant origins/regions, changed-body replay, overlapping loans, invalid footprints and invalid unapplied bodies exercise reconstruction, trace, authorization and audit premises. |
| `TypeAuditRegression` | Forged operands, nominal endpoints, substitutions and dependency cycles exercise `typed`/`ordered`; codegen rejects forged legacy annotation certificates independently. |
| `tests/edit_borrowing.rs` | Raw protocol-5 authority/target/stale-input mutations, unreturned loans, final footprints and unused/losing bodies exercise the actual source/IR route. These are executable regressions, not proofs of snapshot authenticity or full source correspondence. |

Run the existing suites and the new proof-index regressions with:

```sh
lake -d lean build
(cd lean && lake env lean ../scripts/audit_axioms.lean)
(cd lean && lake env lean ../scripts/check_edit_acceptance.lean)
lake -d lean-kernel build
bash scripts/check_kernel_regressions.sh
cargo test --locked --test edit_borrowing
python3 scripts/check_boundaries.py
```

These are reproduction commands, not a claim that a particular host or CI run
executed them; report actual validation results with each change.

### Polynomial symplectic reference (#211)

The [exact symplectic reference](symplectic-reference.md) separates subject
binding, alternation, exterior derivative and domain-qualified inverse checks
for polynomial 2-forms on `R^4` or `D(1+q1)`. It has executable Python regressions,
including same-determinant evidence replay and invalid global extension, but no
Lean soundness proof or connection to the actual accepted Core. Its S1–S6 proof
obligations and production bridge preserve Lawvere-first implementation and the
existing 8+1 division. It does not extend the finite acceptance theorem above.

### Finite CAR and ordinary-spin reference (#246)

The [CAR/spin reference](car-spin-reference.md) checks one/two-mode CAR,
ordinary spin-site commutation, explicit adjoints over Q(i), and the
nonfaithful three-generator Pauli image. It reuses the existing crossing
reference for all exchange coefficients and structural-rule tests. Full
model/basis/parity/profile metadata is retained, but these finite matrix
observations are neither Graph authority nor Lean certificates. Named-model
resolution, actual accepted-Core correspondence and Lean soundness remain
explicit obligations; no production acceptance theorem is extended.

### Finite time-reversal reference (#301)

The [time-reversal reference](time-reversal-reference.md) reuses the CAR
reference's exact Q(i) arithmetic for separately selected spin-1/2 and
spinless semilinear actions. It checks coefficient conjugation in composition,
antilinearity, unitarity, the selected square, explicit phase/basis transport,
and distinct Hamiltonian/state invariance claims. Expected model, basis,
embedding, profile and phase are supplied independently of candidates;
reported observations are recomputed and cannot be replayed by name alone.
These Python regressions add no Lean theorem, accepted-Core connection or
empirical physical identification. The wider #301 design remains open.

## Edit authority acceptance (protocol 6)

`VastitasKernel.Authority` is the actual implementation used by public wire
version 6. It imports the namespace, contribution-lowering, final dispatch and
unapplied-body mechanisms from the existing compiler. Its `TransitionAllowed`,
`StateValid`, `ChainValid` and `HistoryValid` propositions are defined separately
from `step`; acceptance audits every prefix. `DeclarationsCorrespond` compares
complete reconstructed declarations and reference provenance with the prepared
records. The final executable surface is assembled from those same bodies.

`VastitasOracle.Authority.runTrace_sound` connects successful execution to the
declarative trace. `assembled_trace` and `assembled_state_valid` give exclusive
leaf editing, valid ownership histories and returned loans. The reborrow,
application, return and transfer theorems establish explicit delegation,
contained regions, suspended parents, inner-first return, current-owner
authority and preservation of complete contribution records. A transfer changes
the editor, not the canonical definition identity. `applied_region_contained`
and `final_winner_authorized` connect final winning footprints to every ancestor
region. Membership and abstract-contract authority continue through the existing
exact-defining-module namespace audits.

`checkAuthorityProgram_audited` connects the actual returned `CertifiedModule`
to both the checked unapplied-body audit surface and the exact checked final
surface. `checkAuthorityProgram_typed_and_ordered` and
`checkAuthorityProgram_total_for_arguments` compose with the existing Core
theorems. No claim is made that an Open intermediate family is executable.

`AuthorityRegression` is an additional target in the shared regression script.
It exercises actual acceptance, rejected legacy API bypasses, forged parent
links/regions/recipient records and invented histories. `tests/edit_authority.rs`
covers source and wire paths, native execution, alias replay, transfer before
or after borrowing, retained grants and Open obligations, repaired ambiguity,
invalid bodies, final footprints and immutable membership/contract authority.
The regression target runs without mathlib; the oracle and axiom audit remain
separate. The trust boundary still excludes Rust parsing, JSON decoding, input
authenticity and native/backend equivalence. This is edit authority, not storage
borrow safety or a claim to have implemented all eight domain checkers.


## Internal indexed declaration foundation

`VastitasOracle.IndexedSource` now connects internal unresolved declarations to
the actual namespace resolver and `Indexed.Core.Declarations` audit. Its checked
record is indexed by the same input package/module program and retains the
exact lowering equation. Output IDs originate in the enclosing input package
and logical module; reference ledgers are independently re-resolved with real
visibility/import checks. The proved output contracts include complete finite
domains, package cases and the closed primitive registry. This is declaration
acceptance only: it does not certify function bodies, scalar dispatch, edit
assemblies, a public protocol-7 decoder or source-term translation. The six
native fixtures include one using this exact resolved declaration environment.

`VastitasOracle.IndexedSourceTypes` connects internal type elaboration to the
same declaration certificate, raw annotation, requesting scope and supplied
Core bindings. Its exact-lowering and uniqueness theorems prevent replacing
that output with a type from a different context. `local_argument_exact`
follows the actual variable lookup, and `local_index_from_binding` shows that
elaboration invents no local index, including within non-geometric families.
The checked type satisfies the actual Core validity and scope predicates.
Execution/freshness of arbitrary input bindings, source body elaboration and
protocol-7 function/dispatch/authority composition remain outside these claims.
The seventh native fixture uses the elaborated dependent function type.

`VastitasOracle.IndexedSourceBodies` now connects a separate internal data-body
adapter to the exact accepted Core. `checked_program` retains the reconstruction
equation, actual Core typing, dependency order and entrypoint. `function_source`
and `function_owner` recover original input positions and enclosing owners.
`source_covered` combines count equality, original-position checks and actual
Core ID uniqueness to prove that no input function is dropped or replaced by a
duplicate; `source_body_checked` covers every such body, including unused ones.
`call_resolves` proves that recorded calls resolve to the actual output function,
and `declaration_resolves` checks canonical declaration references. `data_only`
proves that unsupported old bodies or dispatch/authority envelopes cannot be
silently discarded. The certificate includes the exact lowering equation;
independent ledgers alone are insufficient. This is structural acceptance,
not source evaluation preservation, public protocol-7 acceptance, or native
refinement. Fifty-two new cases and three additional standalone native fixtures
exercise actual internal source bodies. Public parsing and full Fn/dispatch/edit
composition use the later public checker described below.

`VastitasOracle.IndexedFunctions` adds structural acceptance for the internal
Fn adapter. `pipeline_reconstructed` connects the actual declaration input,
lambda lifting, signature preparation and both separate lowering passes.
`both_passes` establishes Core typing for the same returned audit/executable
modules. `source_body_checked` and `lifted_definition_checked` cover every input
function and lambda, including unused higher-order bodies. `lambda_scope`
includes type-index free names and the shadowing ban. `target_signature_exact`,
`executable_target_concrete`, `function_origin`, `emitted_call_exact` and
`source_call_resolves` extract the independent static-target, origin and namespace
audits. Coverage cannot be replaced with a list of executable winners or probes
reused as executable targets. Fifty-five regressions and four more standalone
native fixtures exercise this path. These statements do not prove source
operational correspondence, typed termination, dispatch/edit composition,
protocol-7 acceptance or correctness of the native toolchain.

`VastitasOracle.IndexedDispatch` connects the internal rich-method adapter to
that same Fn/Core path and the existing finite dispatch checker. The actual
family certificate retains `Dispatch.checkWith` acceptance and fulfilled scalar
contracts. `applicable_expansion` and `applicable_body_checked` cover every
applicable method/key, including nonwinners and keys outside the callable domain;
an independent expansion check and full audit coverage prevent dropping them.
`source_body_checked` and `lifted_definition_checked` cover original functions
and lambdas. `dispatch_call_selected` derives the independent `Dispatch.Selection`
relation from the actual generic resolution, domain/winner and exact source
specialization. The reconstruction theorem retains the same input, headers,
rich method bodies, expanded definitions and returned Core passes. Thirty-seven
regressions and four native fixtures exercise the composition. Edit/authority
envelopes remain rejected. Public protocol 7, whole-term typed evaluation and
native refinement are still outside these structural guarantees.

`VastitasOracle.IndexedAuthority` connects rich contribution bodies to the
actual `Authority.assemble` certificate. `authority_trace`, `applied_authorized`
and `final_footprints` retain the existing independent loan/transfer/history and
all-key winning-footprint guarantees. `lifted_owner_and_scope` separates
canonical definition identity from the contributor's lexical scope.
`applicable_expansion`, `instance_body_checked`, `seed_body_checked` and
`lifted_definition_checked` connect the complete source/specialization/lambda
set to typed functions in the actual audit Core, including unapplied bodies.
`executable_excludes_unapplied` checks every returned executable origin and
its lambda origin against the unapplied set. Reconstruction equations retain
the same assembly, original bodies, discarded-audit headers, lifted definitions
and both Core outputs. The compiler also independently rejects unapplied static
targets. Thirty-nine regressions and four native fixtures exercise these checks.
Public protocol-7 decoding, whole-term semantics, stdlib migration and native
refinement remain separate; synthetic header bodies are never certified as
the contribution implementations.

`VastitasOracle.IndexedWire` now connects public protocol-7 JSON to this combined
authority path. `reconstructed` retains the exact decoder input/result and the
actual combined checker's acceptance equation. `checked_cores` gives typing of
both returned passes, executable dependency order and the main contract;
`codegen_input` identifies the exact executable Core passed to generation.
`returned_loans` and `final_footprints` retain the actual authority guarantees.
The underlying individual-adapter theorems above retain their narrower scope.
Twelve direct kernel wire regressions and actual Rust-source integration tests
cover old-envelope rejection, forged metadata, all-body checking, nominal identity,
scope escape, nongeometric indices and nested authority composition.
These are structural acceptance results. The later program theorem supplies
whole-term indexed evaluation. Full source operational correspondence, native
refinement and C-level performance remain unproved or unmeasured.

`VastitasOracle.Indexed` proves `validEnvironment_iff` and
`validApplication_iff` for the actual kernel algorithms and their independently
stated logical judgments. Checked applications retain the same checked
environment; `checkEnvironment_input` and `checkApplication_input` identify the
exact original input. `inheritance_acyclic` rules out every nonempty chain of
class-parent edges from a declaration to itself. Scope traversal and global/family
identity preservation are also proved for these internal records.

These declaration-only lemmas are prerequisites for the public checker, not its
entire acceptance theorem. Every public protocol now uses the common indexed
source checker and returned Core. See [indexed-declarations.md](indexed-declarations.md)
for exact checks and [migration acceptance](geometry-migration.md) for the complete
source/namespace/primitive/existential/Core evidence map.


The internal package/primitive extension is proved in
`VastitasOracle.IndexedPackages` and `VastitasOracle.IndexedPrimitives`. Its checked
records preserve the same environment, package contract, allocation context,
operands and result. Package proofs cover exact field association, only bound or
global free references, freshness and distinct reopening. Primitive proofs cover
closed binding validity, complete-domain capabilities, fresh construction,
composition endpoints and application test-object preservation. The 45 added
kernel cases exercise these audits directly. The propositions concern internal
type annotations; the internal Core layer below connects them to actual terms.
The common source checker and the evaluation theorems below compose these
contracts with actual accepted terms.

`VastitasOracle.IndexedCore.checkModule_acceptance` proves exact input identity,
complete module typing (including every body and declaration), actual call-graph
dependency order and the entrypoint contract for `Indexed.Core.Typing.checkModule`.
Consequences cover unique allocation serials, scope escape rejection, ascription,
dependent call substitution and the primitive/package associations of typed
terms. The executable decision procedures use constructive checker equivalences
in `IndexedAudit` and `IndexedContractAudit`, also exported by the existing oracle
modules. No frontend-selected signatures or dependency graph enter this theorem.

The internal generator repeats the audit, emits native Lean functions and imports
only `IndexedRuntime`. Thirty-four structural regressions and three standalone
native fixtures run without mathlib. This structural theorem alone is not a source
acceptance, typed evaluation or native equivalence theorem. The public acceptance
and program evaluation results described here compose with it; native equivalence
remains unproved. See [indexed-declarations.md](indexed-declarations.md).

`VastitasOracle.LegacyIndexed.check_acceptance` connects the exact legacy input
to the actual translated indexed module, with complete typing and actual
dependency order on both sides. This retained internal API is a structural
association theorem, not evaluation preservation or the current public path.
Existing legacy source/evaluation theorems remain about the old Core and runtime;
translation semantics and native equivalence remain unproved.

Public protocols 2–6 now use `Indexed.LegacySource`: original wire decoding,
source adaptation, then the same `Indexed.AuthoritySource` checker as protocol 7.
`VastitasOracle.LegacySource` connects the exact decoder/adapter/checker equations
to both typed Core passes, dependency order, entrypoint validation, returned edit
loans, final footprints and body coverage. It also connects the validated profile
to the one used by the actual function compiler. Thirteen adapter regressions
exercise all supported old envelopes and profile injection boundaries. These
structural checks alone do not establish evaluation preservation. The new
`LegacySource` totality corollaries below concern their exact returned indexed
Core; they do not extend the retained legacy evaluator's result-correspondence
theorems to the current compiler.

Indexed signatures now use a once-per-module hash table. The oracle's
`IndexedSignatures` lemmas establish actual member/absent/target correspondence.
The shared constructive `Finite.distinctFrom_iff` and `Finite.distinct_iff`
connect the linear hash-set audit to mathematical list distinctness; the existing
legacy distinctness soundness theorem now uses this same implementation.

The first indexed evaluation fragment is in `VastitasOracle.IndexedSemantics`.
It imports the actual Core semantics and proves domain upcasts, reference
denotation and world-extension lemmas. `primitive_total_and_typed` covers every
closed registry binding; `checked_primitive_semantics` and
`core_primitive_semantics` connect it to the real primitive checker and a real
typed Core node. Typed runtime arguments and constructor-slot freshness are
explicit premises, not inferred from an unrelated certificate. Composition's
shared middle reference denotes the same runtime object on both sides.

`primitive_runtime_erasure` connects successful logical registry evaluation to
the actual minimal runtime operations. The bounded Core evaluator and twenty
regressions test the same source-independent fixtures as native generation, but
are not whole-program proofs. The term/function/program theorem below supplies
typed total evaluation, dependent-call transport and allocation freshness from
the actual module audits. Legacy translation and generated native code still
need their correspondence theorems. The operation lemmas do not
extend the retained legacy whole-program theorems to the indexed backend.

`VastitasOracle.IndexedSubstitution` proves validity under reference maps that
preserve object types, and connects valid package templates and fresh serials to
the real `openPackage` audit. These reference-map lemmas are proof helpers, not
additional admitted call substitutions or authority operations.
`IndexedPackageSemantics` proves runtime-field transport by the bound template,
including global witnesses, explicit globals, token indices and ordered fields.
Its `core_pack_semantics` and `core_opening_semantics` use the exact declaration
lookup and association of actual typed Core nodes. Runtime operand typing and
fresh dynamic slots are explicit premises. Eleven kernel regressions and two
additional native fixtures support that operation-level increment; the later
program theorem below composes it through lexical bodies and activations.
Backend refinement remains a separate obligation.

<a id="conditional-indexed-term-and-function-evaluation"></a>

### Indexed term, function and checked-program evaluation

`IndexedEvaluation.Evaluates` is an equation about the actual
`Indexed.Core.Semantics.eval`: it provides a finite bound and the same value at
every larger observation fuel. It is not a second interpreter or an assumption
that evaluation succeeds. `IndexedEvaluationSafety.evaluation_total_and_typed`
proves this property by structural induction over every actual Core constructor,
including branches, argument sequencing, primitives, calls, pairs, let bindings,
packing, unpack bodies and scopes. Its premises are actual `HasType`, a valid
declaration environment, a typed value context, unique fresh allocation slots,
and an explicit `CallReturns` contract for every called function.

The conclusion includes result typing, world extension and an exact allocation
frame: slots outside the term's `allocatedSerials` remain unchanged. This frame
and the real numeric uniqueness audit preserve freshness during sequential
evaluation. Descriptor primitives expose their exact world update; branch
rebranding and package opening obey the same frame discipline. Field binding
uses the actual ordered `bindFields` operation and preserves the enclosing
context. Explicit globals are retained through the existing template-based
package transport.

`IndexedFunctionSafety.checked_function_returns_under_calls` consumes a member
of the actual `CheckedModule`. It derives a fresh activation by restricting the
world to parameter slots, evaluates the body, applies the declared result
compatibility and uses the checked return scope to discard local allocations.
It requires no freshness or injectivity premise on the ambient world.
`checked_call_free_function_returns` discharges the callee premise for functions
whose actual body has no calls.

`IndexedCallTransport` transports indexed values through actual reference
substitution. It uses the same runtime object on both sides, allowing a narrower
actual finite domain than the formal parameter domain. It does not assume equal
type metadata. Points and morphisms retain both endpoints; tokens retain all
object-index obligations. Valid existential package indices are fixed by call
substitution. `IndexedArgumentSafety.call_activation` uses the actual
`bindArguments`, checked parameter scopes, and `FinalArgumentsMatch` to construct
a typed callee environment and the required reference correspondence. The
declared return scope transports the result back to the caller; object results
receive the caller's fresh audited slot.

`IndexedProgramSafety.checked_functions_total_and_typed` discharges every
`CallReturns` premise by induction over the actual `Dependency.OrderedFrom`
certificate obtained from `CheckedModule.ordered`. The real signature table and
runtime function lookup resolve to the same unique declaration. Every function
therefore has finite typed evaluation for every typed parameter environment,
without a callee-safety, evaluator-success or ambient-freshness assumption.
`checked_main_total` proves finite Int-valued evaluation of the accepted main.

`IndexedWire.executable_functions_total`, `audit_functions_total` and `main_total`
apply those theorems to the exact Core modules returned from protocol 7.
`LegacySource` exposes the same three corollaries for protocols 2–6. Their
`coreInput` equations tie the proofs to the same executable Core passed to native
generation, and to the audit Core that also includes unapplied/unused bodies.

These are theorems about the actual indexed Core evaluator, not equality with a
source interpreter or the retained legacy evaluator, native-code refinement,
storage safety, mathematical geometric axioms or numerical accuracy. Legacy
whole-source result correspondence and native refinement remain open; typed totality does not
complete the historical Stage 1 plan or establish Fast like C.

## Geometry standard-library migration regressions

The ordinary `.vast` modules behind `std::geometry::scheme` and
`std::geometry::smooth` use the existing public `Indexed.Wire.check` acceptance
path. The single `stdlib` entrypoint re-exports their canonical declarations and
arithmetic; the temporary `stdlib/indexed` facade is removed. Its explicit
`geometry_compat` export supplies old syntax through independently resolved and
validated declaration roles, without runtime forwarding or new editing rights.

`tests/stdlib_geometry.rs` contains twenty-one integration tests: native `42`/`2`
workflows including unchanged original source, mixed annotations/pack/unpack,
dependent test objects, coherent source/profile renaming, re-export identity,
nominal separation, visibility, missing capabilities, Fn capture and unused-body
checking. Actual wire mutations change visibility, primitive/base roles,
capabilities, purported owner or compatibility metadata; both checking and
emission reject them. Old wire versions reject the new export. Twelve direct
`GeometryCompatibilityRegression` cases check role contracts and additional
family constraints that would invalidate the legacy interface.

`VastitasOracle.GeometryCompatibility` imports the actual checker and proves:

- `checked_profile`: selected exports satisfy `GeometryProfile.valid` in the
  same independently accepted declaration environment.
- `settings_distinct`, `setting_contracts`, `origin_and_package`: the settings
  have distinct markers and exact checked origin/package roles using the same
  Point family and actual global base object.
- `prepared_profile`, `lowered_profile`, `compiler_uses_checked_profile`: the
  actual function compiler uses the exact profile certified by declaration
  checking, through their shared path resolver.
- `wire_profile`: the exact decoded protocol-7 input is accepted by the actual
  authority checker, has that validated profile, and yields a typed executable
  Core. Existing all-body, authority, capture and codegen audits still apply.

These are structural checker guarantees. Whole-term indexed evaluation is supplied
by `IndexedProgramSafety`; protocols 2–6 use the common source checker via
`LegacySource`. General scheme/manifold mathematics, native equivalence and C
performance measurements are not established by these theorems or tests. See the
[library contract](../stdlib/src/geometry/README.md) and
[completion ledger](stage1-completion.md).

### Finite geometry result compatibility

`VastitasOracle.GeometryResults` connects the actual validated profile's seven
primitive roles to the retained finite `Runtime` operations after descriptor
erasure. `affine_result`, `base_result`, `origin_result`, `identity_result`,
`dimension_result`, `compose_result` and `apply_result` use the profile's actual
declaration lookup, including coherently renamed profiles. They do not require
singleton implementation domains or any specific library spelling.

`declared_primitive_erasure` composes that declaration lookup with the existing
`IndexedSemantics.primitive_runtime_erasure` theorem. It requires successful
logical primitive evaluation; typed total evaluation of accepted Core is supplied
independently by `IndexedProgramSafety`. `wire_dimension_result` instantiates the
role contract from the exact public checker. `GeometryCompatibility.checked_profile`
and `LegacySource.checked_profile` supply the same premise for the other roles.

Erasure drops nominal/marker tags. These equations do not permit mixing bases,
equating distinct brands or fabricating endpoint evidence; the typing and world
theorems establish those obligations before erasure. This is operation-level
finite result compatibility, not whole-source equivalence or native compilation
correctness. [The migration map](geometry-migration.md) records how the separate
proofs and actual-source regressions fulfill #49/#58–63 without expanding their
claims to arbitrary geometry or the complete native toolchain.
