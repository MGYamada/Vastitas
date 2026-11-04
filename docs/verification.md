# Verification boundaries

The proof oracle in `lean/` imports the implementation's definitions from
`lean-kernel/`. It has no executable target and is not consulted when compiling
or executing `.vast` programs. Both packages pin Lean v4.35.0; the oracle,
executable kernel and generated runtime depend only on that Lean distribution
and the local implementation. Mathlib mathematical alignment is a separate
semantic obligation, not an Oracle build dependency; see
[ADR 0001, amendment for #285](adr/0001-mathematics-first-stdlib.md#9-mathematical-alignment-and-oracle-dependency-independence).

The first #285 increment replaces the two direct Mathlib imports with core
`Rat.intCast_inj`, `List.mergeSort_perm`, `List.pairwise_mergeSort` and
`List.Perm.eq_of_pairwise`. `Rat` is the same type previously written `ℚ`;
nonempty coordinate dimension and all theorem hypotheses remain in place.
The transitive Batteries import in `ModuleEffects` is also removed: its
pointwise list relation is now the proof-local
`VastitasOracle.Elaboration.Forall₂`, with the same nil/cons rules (including
equal length and positional correspondence). `ModuleElaborated` and
`ModuleCorresponds` use that relation without changing their obligations.
No global `List.Forall₂` declaration is shadowed, so a future separate Bridge
can import Batteries without a name collision. No proof or theorem is removed.

`scripts/check_boundaries.py` reuses the Lean header scanner for every Oracle
source, allowing only distribution, actual kernel/promotion-fixture and Oracle
modules. Both declarative Lake configs and complete manifests are checked:
the kernel has no packages and the Oracle has exactly the local kernel.
Inherited dependencies, renamed/forked packages, redirected local paths, stale
locks and executable Lake overrides are rejected. Local wrapper modules are
scanned as well. This deliberately closed graph must be amended when future
packages are actually introduced; it is not a general Lake dependency resolver.
CI checks the boundary before resolution and after the official build, disables
Mathlib cache downloads, and preserves the allowed axiom set.

`scripts/audit_axioms.lean` does not depend on any import closure. It finds each
project package from its `<package>/.lake/build/lib/lean` directory on the Lean
search path and enumerates every `.lean` source module of `lean/` and
`lean-kernel/`, skipping `.lake` and the nested native/numerical Lake packages.
Every source module must belong to an audited group (`VastitasOracle`,
`VastitasKernel`, `VastitasPromotion`, `VastitasPublicTest`,
`VastitasStorageTest`, `VastitasAlgebraTest`, `Main`) and have a built `.olean`.
All library modules, including the `*Regression` modules, are imported together.
Each executable root (`Main`, `VastitasStorageTest.Emit`,
`VastitasStorageTest.NumericalEmit`) defines `main`, so each gets its own
environment. Every oracle module must also be imported by the `VastitasOracle`
root. The audit then selects declarations by their actual defining module,
including private declarations and declarations in other namespaces. It collects
the axioms reachable from them through types, values and constructors in one
exact search; only `propext`, `Classical.choice` and `Quot.sound` are allowed, so
`sorry` (`sorryAx`) fails. It also rejects project declarations whose compiled
code is not their logical definition: `extern`, `implemented_by`, `partial`,
`unsafe` and `opaque`. Structural, well-founded and `partial_fixpoint`
definitions remain permitted, as do proved `csimp` rewrites. The remaining
exceptions are listed in the script with their reasons, and each must still
exist:

- `Main.readBounded`, the bounded stdin reader of the kernel process (#580);
- `VastitasKernel.WireScan.digitRun`, `value`, `array` and `object`, the wire
  pre-scan before `Lean.Json.parse`, which can only reject a request; and
- the `partial` functions that Lean generates for `deriving Repr` on nested and
  mutual inductive types. They return `Std.Format` and only render text.

`IndexedCodegen.renderTerm` is now total, and the nested `Statement` types no longer
derive a `partial` `BEq`; `==` uses their total `DecidableEq`. The audit excludes
Lean distribution implementations and the separately built optional native/FFI
packages. It also cannot see elaboration-time evaluation, such as the
`Promotion` and `IndexedPromotion` fixture reifications described below, or
`example` bodies, which create no declaration (`warningAsError` still rejects a
`sorry` there, but not `native_decide`). The derived-`Repr` rule matches by name
and `Std.Format` result type. `partial_fixpoint` definitions (none exist today)
would be accepted although their code may diverge where the logical value is the
bottom element. The audit does not replay declarations through the Lean kernel,
and it checks that each `.olean` exists, not that it is current, so the CI run
from a clean checkout is the authoritative one. Both Lake packages set
`leanOptions.warningAsError = true`, and `check_boundaries.py` requires it, so a
warning such as a declaration using `sorry` fails the kernel and oracle builds.
CI runs the oracle `lake env lean` checks with `-DwarningAsError=true`.
`scripts/check_axiom_audit.py` builds isolated fixture packages and checks that the
audit rejects: unused private axioms in each library; unrelated namespaces;
`sorry`; `extern`, `implemented_by`, `partial`, `unsafe` and `opaque`
declarations; a `partial` function that only looks like a derived `Repr`; a
source module without an object file or outside the audited groups; an oracle
module that the root does not import; a missing oracle package; and a stale
exception. These are CI policy checks, not a
native-refinement theorem. `check_oracle_core.lean` exercises nonempty/empty
coordinate spaces, duplicate/Unicode names and positional lists.
That dependency-removal increment added neither `VastitasMath` nor
`VastitasBridge`, and claimed no new std correspondence or constitutional theorem.
The subsequent, separately built mathematical bridge is described below.

## Independent mathematical bridge

`lean-bridge/` now supplies the important
[Daleckii–Krein theorem](daleckii-krein.md) in
`VastitasBridge.Analysis.DaleckiiKrein`. It proves the real Fréchet derivative of
Mathlib's actual `cfc` on self-adjoint elements at a finite-spectrum basepoint,
and specializes to finite complex Hermitian matrices without a simple-spectrum
assumption. The theorem documentation records all regularity assumptions and
the separate obligations for future AD/Core/native realization.

This independent Lake package uses Lean v4.35.0 and Mathlib commit
`56a005855ea17e0b0958f73ec801ae140b0a1679`, with every transitive package locked.
The existing kernel/Oracle closed dependency graphs remain unchanged; neither
may import `VastitasBridge` or Mathlib. The boundary checker additionally checks
the optional bridge's toolchain, sole direct dependency, pinned Git manifest
and current mathematical-only imports. Its negative regressions cover bridge
leakage into kernel/Oracle, unpinned/redirected dependencies and Lake overrides.

`.github/workflows/lean-bridge.yml` builds and checks this package independently,
using only the Mathlib cache needed by its imports. `lean-bridge/Audit.lean`
requires the principal theorem names to exist and audits the transitive axiom
dependencies of every declaration in `VastitasBridge`; only `propext`,
`Classical.choice` and `Quot.sound` are allowed. Official `leanchecker` replays
the bridge modules against their imported environment. This is not a separate
verifier or a fresh replay of all imported Mathlib declarations. No public
`std` API, executable AD implementation or source/native refinement is claimed.

## Current public checker routes

`lean-kernel/Main.lean` currently uses these entry points:

| Wire input | Independent acceptance | Native generation |
| --- | --- | --- |
| Protocols 2–6 | `Indexed.LegacySource.check`, including original decoder/namespace validation and conversion into `Indexed.AuthoritySource.checkProgram` | `Indexed.Core.Codegen.generate` on the exact returned executable Core |
| Protocol 7 | `Indexed.Wire.check` and the same full indexed authority/function/dispatch composition | The same indexed Core generator |
| Protocols 8/9 | `ResourceSource.Wire.check`, composing indexed pure bodies with resource/numerical checks | `ResourceSource.Codegen.generate` rechecks the accepted source and both components |

Protocol 9 changes only edit recipient identity syntax within the full resource
wire composition. `VastitasOracle.EditRecipients.named_recipient_iff` characterizes
actual acceptance by exactly one root-reachable manifest-name candidate;
`named_recipient_preserves_identity` retains the original package record.
`lower_grant_resolves` and `lower_transfer_resolves` connect the real lowering
functions to that resolver, their exact returned scope and their issuing module.
`reconstruct_declared` is proved by induction over the actual `for` loops of
`Authority.reconstruct`: every delegation and transfer it returns is the lowering
of a raw entry that a module of the input declares. `reconstruct_grants_declared`
proves the same for the `mapM` in `Edit.reconstructGrants`. The composed theorem
`public_named_recipients` holds for every `ResourceSource.Wire.CheckedInput`.
Each grant, delegation and transfer of the accepted certificate is issued by the
declaring module. Its recipient is the declared module path in the resolved
package; a manifest name resolves only to the unique root-reachable package with
that name, and a source location resolves by location lookup. The certificate's
`DeclarationsCorrespond` still replays `reconstruct` exactly as `prepare` runs it,
so that conjunct is an executable consistency check, not independent evidence.
These are decoded-input guarantees, not authentication of files/authors or a
proof of Rust parsing/native refinement.

The current pure Core typing and terminating-evaluation chain is
`IndexedCore` → `IndexedEvaluationSafety` → `IndexedFunctionSafety` →
`IndexedArgumentSafety` → `IndexedProgramSafety`, with the public receipt
connections in `IndexedAcceptance`, `IndexedWire` and `LegacySource`.
The actual promotion/add/maximum fixture is covered by `IndexedPromotion`.
The indexed Core type audit builds a first-match symbol table from each
function's ordered lexical context. A `let` extends only its body and an
`unpack` introduces the witness and fields in their original order.
`ContextIndex.get?_eq` proves each indexed lookup equals the specified list
lookup even for repeated symbols. `ContextIndex.exactRefs` preserves the
ordered object references used by scope, freshness and primitive checks.
`letTyped_iff` derives the validity of a `let` result from its checked body.
The type audit still checks the value, rejects a symbol already in scope and
checks the body in the extended context. This avoids walking a nested chain
to inspect the same terminal result at every enclosing `let`.
Resource receipts, native generation and floating-point results keep the
separate boundaries described below. These results do not supply full source
specialization correspondence or native refinement.

The repository also retains the earlier Stage 0–1b checker and proofs.
`checkModule`, `checkProgram`, `checkSurfaceProgram`, `checkNamespaceProgram`,
`checkEditProgram`, `checkAuthorityProgram` and `LegacyIndexed.check` are **not
Main's public entry points**. Their theorem statements remain valid for those
APIs; their source correspondence and old `Semantics.Eval` results cannot be
transferred to the current indexed pipeline without a separate proof. Shared
namespace, dispatch and authority helpers can still be live. The sections below
identify the retained compositions explicitly; the indexed sections describe
the current Core and public acceptance connections.

## Checked language and independent audits

**Retained legacy Core.** This section describes the earlier `Term`,
`CertifiedModule` and their audits. Current public compilation uses
`Indexed.Core.Term` and `Indexed.Core.Typing.CheckedModule` instead.

The checked `Term` language retains normalized integer literals, finite
operator and builtin constructors, resolved variable and function symbols,
types, object references, and dependent call substitutions. Object identity
metadata remains available through checking and is erased during code
generation. The formal evaluation relation operates on this actual `Term`
language and uses the actual runtime objects, points, morphisms, and packages.
It also includes the closed `Pair<Nat>` / `Pair<Int>` types, construction and
projections. The declaration/expression correspondence and whole-core safety
proofs cover these operations. Separate [stdlib numerical contracts](stage1a.md#promotion)
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
typing, dependency, or source-correspondence results. The retained legacy
`Codegen.generate` boundary repeats the independent audits, so constructing
this weaker certificate directly cannot bypass them.

## Stage 0 source correspondence and type safety

**Retained legacy theorem scope.** These source-correspondence theorems
apply to the old decoded `RawModule`/`CheckedModule` pipeline. They do not prove
source correspondence for the current protocol 2–7 indexed adapter.

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

**Shared finite selection facts; retained legacy body composition.** The
finite engine and selection relations remain useful, but the
`DispatchLowering.checkProgram_*` composition below targets the old Core.
Current all-body/target/Core correspondence is in the indexed dispatch and
authority acceptance theorems.

The live reusable finite engine is `VastitasKernel.Dispatch.checkWith`, called
with the independently reconstructed nominal hierarchy. The old `Dispatch.check`
is a retained wrapper fixing that hierarchy to the builtins. The
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

- `checkWith_sound` connects successful execution to the independent `Optimal`
  and `Selection` conditions. It also establishes actual normalization,
  unique method identities and normalized signatures, realizable method
  conditions, and the correctness of every selected row. Ambiguity checking
  covers the entire enumerated universe, including keys outside the declared
  callable domain.
- The builtin-wrapper corollary `check_key_universe` proves that the enumeration contains every concrete
  tuple of the declared arity, has exactly `4^arity` elements, and has at most
  4096 elements. `domain_coverage` proves that every declared callable key has
  a selected method.
- `winner_selection` applies to the current parameterized engine; `winner_sound`
  is the builtin-wrapper corollary that the selected ID belongs to the unique optimal
  method. The wrapper's `winner_identity_unique` additionally proves that no other record
  in the accepted family has that ID, including inapplicable records.
- `applicablePairs_complete` characterizes the exact list of applicable
  method/key pairs exposed for ground body checking. It includes losing
  methods and keys outside the callable domain.
- `checkWith_permutation_success` proves that permuting method records preserves
  acceptance and the exact winner rows. `checkWith_order_independent` states the
  corresponding equality of selections. Stable IDs remain attached to their
  records; these theorems do not equate unrelated IDs reassigned by a frontend.

The generic `checkWith` engine and its soundness/permutation theorems use the
same algorithm for other validated finite hierarchies. Synthetic multiple
inheritance and triple-intersection tests exercise that engine. They do not
extend the public four concrete key types or authorize new capabilities.

`VastitasOracle.DispatchLowering.selected_target_sound` connects the backend's
actual family-check and target-selection evidence to domain membership and
the unique optimal method. The same namespace provides the retained legacy checker
composition results:

- `checked_call_pair_result` proves that the independently audited call result
  equals the Pair element type of its actual looked-up signature. It applies
  to the typed cores returned by the three retained legacy acceptance APIs; it does
  not add a full source-rewriting equivalence claim.
- `checkProgram_core` proves that successful `checkProgram` execution produced
  an exact lowered core module accepted by the actual `checkModule`.
- `checkProgram_typed_and_ordered` establishes independent whole-module typing
  and an acyclic dependency order for the resulting checked core.
- `checkProgram_total_for_arguments` (retained `checkProgram`, not one of Main's
  current entry points) proves that every function in that exact
  result evaluates to a value of its declared return type for all well-typed
  argument environments. This includes the core's runtime endpoint and
  package correspondence guarantees.

The finite Stage 1a implementation passed repository validation and hosted CI,
including the proof/axiom audit and macOS/Linux compiler builds without mathlib
([acceptance run](https://github.com/MGYamada/Vastitas/actions/runs/40336834442)).
This is not completion of all Stage 1 features in the historical design.

The proofs contain no `sorry`, `admit`, or project-specific unproved axioms.
CI audits declarations from the actual project modules against Lean's standard logical axioms
(`propext`, `Classical.choice`, and `Quot.sound`).

## Stage 1b capture and static function contracts

**Retained `checkSurfaceProgram` composition.** Its exact old-Core
conclusions are distinct from current `Indexed.FunctionSource` acceptance and
`IndexedProgramSafety`. See the indexed function section for that connection.

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

## Independent internal Lean export audit (v0.1.0 gate)

`vastitas audit-lean EXPORT.ndjson` is an opt-in cross-check of an already
generated `lean4export` NDJSON proof environment. It runs the third-party
external checker `nanoda_bin` that the official Lean release toolchain
distributes. Vastitas neither bundles nor builds a checker
([#539](https://github.com/MGYamada/Vastitas/issues/539)). That Lean distributes
nanoda does **not** make nanoda the official Lean kernel. A completed receipt
names the checker, its toolchain and the declaration count, and states that the
result is internal-only, conditional on the supplied environment, and not
authenticated against the standard Lean axioms. It **must not** be interpreted
as `kernel_verified` or `official_kernel_checked`, as successful public
source/IR acceptance, a completed constitutional theorem, or checked native
refinement.

**Distribution and identity.** The checker is the `bin/nanoda_bin` of the
pinned `leanprover/lean4:v4.35.0` toolchain in the elan directory under
`ELAN_HOME` (default `~/.elan`), as Lake locates its bundled checkers. It is
never taken from `PATH`. Before checking an export, Vastitas requires:

- the toolchain directory exists, and its `lean` and `nanoda_bin` are regular
  executable files in its own `bin` directory;
- `lean --version` reports exactly version 4.35.0, release commit
  `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`, and this host's platform
  (macOS or Linux, arm64/aarch64 or x86_64);
- `nanoda_bin --help` reports `nanoda_bin 0.4.19`, the version Lean 4.35.0
  builds from nanoda commit `3a24072` with upstream's release profile
  (overflow checks on).

Any other outcome is an `E_LEAN_AUDIT_CHECKER` error. There is no Cargo,
source-download or alternate-checker fallback. These checks detect missing,
stale, foreign-platform and mismatched installations. They rely on the
binaries' own version reports and do not authenticate the files against local
tampering: the installed toolchain is trusted exactly as the official-kernel
path trusts it. The pinned identity lives in `src/internal_lean_audit.rs`, and a
unit test requires it to match every checked-in `lean-toolchain` file, so a
toolchain bump must update it.

**Policy and protocol.** `config/nanoda-internal-audit.json` is an upstream
nanoda configuration without its export path. Vastitas adds the absolute
`export_file_path`, writes the file to a private temporary directory and runs
`nanoda_bin CONFIG` there. Upstream ignores unknown configuration keys, so the
driver rejects a policy with any key outside its reviewed set. The policy allows
exactly three axiom **names**: `propext`, `Classical.choice`, and `Quot.sound`.
`unpermitted_axiom_hard_error` is true, and `unsafe_permit_all_axioms` is false.
This deliberately rejects even *unused* exported declarations of other axioms.
`sorryAx` and `Lean.trustCompiler` are not whitelisted; any relaxation requires
explicit constitutional review. In Lean 4.35.0, `Lean.trustCompiler` was
removed. An ordinary Lean/Mathlib environment containing other declarations of
axioms may fail this strict export policy even when the intended theorem does
not use those axioms. Prepare an appropriately scoped export instead of
silently weakening the policy.

The name policy does not authenticate statements or the referenced
environment. For example, a supplied `propext : ∀ P : Prop, P` is well-typed
as an assumption and passes the policy, and a theorem that every proposition
holds then checks against it. It proves nothing under the standard Lean
assumptions. nanoda also compares rendered names, so a single-component name
spelled `Classical.choice` passes as well. The CLI therefore reports a
**conditional** check relative to the supplied environment, even for exports
with no axioms. It never reports that the standard axiom environment was
verified. Regressions exercise both spoofs, unsafe and duplicate declarations
of allowed names, and unpermitted names.

**Supervision.** nanoda runs in its own process group under the compiler's
supervised capture. Rejection, panic, crash or an unexpected report becomes an
`E_LEAN_AUDIT` error with the checker's exit status and a bounded diagnostic
excerpt whose control and bidirectional formatting characters are escaped.
Success requires nanoda's exact success message with at least one declaration
and no diagnostics. An interrupt stops and reaps the checker. Like the compiler
backend, a live checker has no wall-clock limit. The included minimal theorem
fixture is hand-assembled from documented format 3.1.0 nodes (with illustrative
historical metadata). Building and invoking `audit-lean` does not require the
`lean/` proof oracle project or Mathlib.

**Differences from the former bundled checker.** Until #539, Vastitas
compiled a vendored copy of nanoda_lib 0.4.31. The maintainer accepted the
toolchain's 0.4.19 without a parity gate. Known differences are findings, not
gates: 0.4.19 has no `stack_size_bytes` option and checks serially on the main
thread with the operating system's default stack, so a deeply nested but valid
export can fail closed with a stack overflow. Later upstream hardening
(quotients, recursors and projections) is absent until a Lean toolchain ships
it.

**Trust separation:**

- GitHub CI proof/axiom audit, independent `lean-kernel/` compilation,
  the public `check`/`build` checker and the constitutional CS/MS/CF proof
  obligations retain the **official Lean kernel** as the sole authority.
  The planned Official mode ([#282](https://github.com/MGYamada/Vastitas/issues/282))
  still requires the official kernel; nanoda never satisfies it.
- nanoda checks a *supplied* proof term for independent diagnostic feedback.
  It does not generate a proof or elaborate Mathlib source itself.
- A future proof-carrying compilation path must bind the exported theorem,
  axiom environment and evidence to the exact accepted source/Core and
  generated artifact, then have the official kernel validate the relevant
  obligation. Merely passing a separately supplied export to nanoda does
  not provide that binding (see #159/#184 and release gate #282).

## What is outside these claims

The [dense layout/preflight reference](storage/checked-storage.md#storage-layout-preflight) separates
byte bounds, alignment, write injectivity, native narrowing and loan conflicts.
Its Python regressions and successful-session receipts do not establish Lean
resource safety or authorize native check elimination. The linked document
states the pending all-access, exact-return and successful-branch soundness
obligations for the actual Ownership/Borrow Checker.

`StorageGemm` additionally proves facts about the actual internal GEMM resource
transition: input and accumulate initialization, reconstructed allocation subject,
output byte separation and initialized output bytes in its exact post-state.
It does not establish nominal endpoint/basis/metric typing, ideal multiplication,
floating-point accuracy, native no-read behavior or source/native refinement.
The [generated numerical runtime checks](linalg/maps-and-gemm.md#numerical-adapter) provide separate
execution and cleanup evidence; the optional native package is not an oracle dependency.

The separate [internal resource IR](storage/checked-storage.md#storage-ir) now has actual-checker
theorems in `StorageLayout`, `StorageRegions` and `StorageSafety`: all-cell
bounds/alignment/byte separation, footprint containment and initialization
entailment, normalized write/join meaning, and nonoverlap of distinct active
loans when either writes. `StorageLayout.all_accesses_at_element_boundary`
also connects the accepted layout to whole-element allocation offsets, including
16-byte complex elements; component ABI alignment remains a separate 8-byte
property. Initialization entailment now includes bounded unions
of contiguous writes, branch intersections and separate padded columns.
`reach_sound`, `interval_sound` and `columns_sound` feed the actual
`initialization_bytes` theorem used by read/GEMM safety; `remaining_nodes` and
`checked_initialization_work_bound` relate the fallback work budget to the actual
bounded metadata traversal. These are logical-byte and arithmetic bounds, not
native memory or elapsed-time theorems. The kernel's `Storage.auditState_eq_indexed`
and `compatibleWith_eq_indexed` prove equality of the reconstructed indexed
implementation and the original predicates for every state, including malformed
ones. Lean uses those `csimp` equations for executable checking; the same reference
predicate remains the premise of the safety theorems. `Finite.firstIndex_lookup`,
`countIndex_lookup` and `Storage.AuditIndex.lineage_contains` connect actual hash
tables/sets to first-match lookup, exact multiplicities and bounded ancestry.
These equations neither eliminate repeated audits/replay nor prove a global
compiler work bound; #422 remains open. Exact decoder/checker certificates start from an
empty logical environment. `StorageCodegen` proves that successful native-plan
lowering follows those actual transitions, has unique instructions for the same
input, and requires the rechecked schedule before returning code. The optional
native runtime has sanitizer and generated-executable regression evidence for
real/complex buffers, output preservation and failure cleanup. These results now compose with the initial static protocol-8 source profile;
they do not extend pure-Core totality to mutable storage. Actual memory initialization,
allocator liveness, native cleanup and native refinement are not proved; C
performance comparisons remain pending. The [internal resource function component](storage/checked-storage.md#storage-functions)
adds actual call-slice replay, restored caller loans, unique live owned results
with declared initialized bytes, and checked probes for every source body.
Probes are separate from executable expansion and do not prove a universal
parametric contract; actual calls are independently checked again. The raw component does not change pure-Core semantics.
[Protocol 8 resource source](storage/resource-programs.md#resource-source) composes the actual authority/Fn/dispatch
checker, independently resolved resource calls, every resource-body probe and exact
entry schedule. `VastitasOracle.ResourceSource` proves complete resource identities,
actual call provenance, original authority trace, typed totality of its returned
pure Core and closed logical entry resources. The public decoder/checker equations
refer to that same input. `VastitasOracle.ResourceValueFlow` additionally connects
actual mixed-run slot typing and branch scope, exact source fragment/Core target
reconstruction, and demanded scalar returns after completed resource calls.
Both-arm resource acceptance and scalar typing are separate certificates; the
resource projection alone does not establish their operational equivalence.

The actual emit entries now have acceptance theorems, in addition to the older
component-generation results. `StorageCodegen.compiled_checked` connects
`Storage.Native.compile` to its exact original input and successful `Native.audit`;
`compiled_closed` extracts the checked transition run, final audit and empty
allocations/loans. `IndexedCodegen.library_checked` and `generated_checked` retain
the actual repeated Core check, unchanged module, typing, dependency order and
main signature. `library_roots_present` checks every requested root; the executable
wrapper theorem records the actual generated library and selected main.

`ResourceCodegen.public_generated_checked` connects successful protocol-8/9
`Wire.emit` to the exact `Wire.check` result, its namespace receipt and the
successful `Codegen.generateChecked` call on that result. The public emitter
reuses the accepted source program. The internal component entry's
`generate_eq_checked` preserves its independently checkable equation.
`public_resource_plan` identifies the `Native.compile` call on the same
accepted entry schedule and its audited closed native plan. `generated_pure_entry` retains
the same returned pure Core and the disabled optional-runtime flags when there
is no resource entry. `generated_pure_entry_total` adds that this generated
module is the certificate's `pureProgram.executable` module, that every function
has typed, finite evaluation and that its `main` evaluates to an `Int`. `ResourceSource.pure_entry_functions_total` and
`pure_entry_main_total` state the same for `checked.pureProgram.executable`,
while `pure_value_functions_total` covers the value library of the mixed path.
These theorems establish acceptance and identify the exact
inputs to native generation. Native heap and floating-point refinement remain open.

**Static numerical receipt coverage.** For protocols 8 and 9,
`VastitasOracle.NumericalCoverage.public_action` proves that every GEMM,
diagonal adjoint and diagonal pairing at an actual address in the returned
storage schedule has a typed receipt with the same operation and declaration
environment. The address includes the enclosing branch arms and the offset
within the innermost arm. Repeated calls and identical instructions in
different arms each require their own occurrence. Network operations also
require their companion product receipts.

`coverage` relates these occurrences with multiplicity and checks their order
against an independent traversal of the lowered source from the actual entry.
Each source site includes its function, lexical position and enclosing call
sites. `original_emission` and `full_slice` cover the entire certified expansion
at its physical addresses, including the loans around a vector evaluation and
the dependency check before a cached contraction. The symbolic runtime-shape
event schedule has its own realization theorems.

The [runtime-shape profile](storage/resource-programs.md#runtime-shapes) adds universal guard-to-checker
proofs in `StorageShapes`: exact frame audits, each actual `checkAction`, the
instantiated `Storage.run`, and restored caller loans/allocations.
Its compiled frame audit and incoming-loan compatibility scan use reconstructed
finite indexes through `Shapes.auditFrame_eq_indexed` and
`Shapes.compatibleWith_eq_indexed`. These unconditional equalities retain the
reference predicates on malformed frames as well as valid ones; bounded ancestry
sets preserve first-match lookup and dangling-parent behavior.
`Finite.LoanChain.comparable` and `acyclic` establish the chain case for both
static and symbolic loans. The checker verifies the actual order, distinct
names and terminating root before using either lemma. Repeated audit and
call/probe work remains outside these per-frame equations.
`StorageShapeNumerical` proves acceptance by the actual nominal `checkProduct`
for the same maps and coefficients. `ResourceRuntimeShapes` connects those
results to public entry projections, declaration origins, live integral slots
and scalar returns after both resource components complete. Separately,
[`prove_runtime_shape_guards.lean`](https://github.com/MGYamada/Vastitas/blob/main/scripts/prove_runtime_shape_guards.lean)
proves and audits 13 universal facts about the actual optional runtime helpers:
Lean `UInt64` layout decisions equal the concrete checker, LP64 span arithmetic cannot
wrap, narrowing agrees with actual Nat/Int admission, and the bound/equality/cell
expressions agree with Nat arithmetic for representable constants. Its layout
corollary reaches actual `Shapes.Guard.eval` under explicit representation
premises. This validation-only import does not add runtime/FFI dependencies to
the oracle, interpret generated text, or prove source execution/native refinement.
Shape results and floating scalar expression interfaces remain open.

The [numerical declaration profiles](linalg/maps-and-gemm.md#numerical-declarations) use the same
complete declaration certificate. `IndexedSource.checked_implementation_contract`,
`checked_linear_base`, `checked_smooth_complex_base`, `checked_coefficient_unique`
and `checked_descriptor_is_affine` establish the actual accepted metadata
contracts. `ResourceSource.public_numerical_declaration` connects them to the
same decoded protocol-8 input and authority checker. These are structural type
and provenance facts; by themselves they do not establish field/module laws,
linear object construction, public GEMM, floating-point accuracy or native refinement.

The [numerical-value compiler](linalg/maps-and-gemm.md#numerical-values) now has a separate
`StorageNumerical` certificate composed with that resource checker.
`accepted_profiles` derives each map endpoint's actual declaration contract;
`nominal_endpoints` preserves exact objects and basis identities;
`actual_loan_layout` binds the type to the live loan snapshot;
`exact_storage_check` connects it to the existing GEMM access/initialization
check; and `actual_emission` binds the certificate to the exact emitted request
and resource transition. Public `ResourceSource` supplies its full accepted
declaration environment to resource probes and actual expansion.
`numerical_provenance` checks original caller scopes and independently resolved
profile references; `public_product_origin` binds each returned product receipt
to that same public input and accepted declaration environment.
`StorageGemm.coefficient_read_contract` and `coefficient_initialized_bytes`
recover live one-element read provenance, matching representation, initialized
bytes and output separation for an actual checked scalar loan.
`coefficient_output_bytes_disjoint` derives byte-level output separation from
that same checked loan.
`overwrite_has_no_beta_read` fixes overwrite's beta operand to absent;
`StorageNumerical.coefficient_emission` preserves requested alpha/beta in the
exact emitted GEMM. Explicit coefficients do not weaken accumulate's initialized
output requirement. These facts do not evaluate floating payloads or prove FFI
loads, BLAS results or native refinement.
For numerical inputs, `actual_input` records the actual accepted contract,
`input_space_identity` and `input_basis_identity` preserve caller identities,
and `input_map_reborrow` extracts unchanged endpoints/conjugation and the exact successful
borrow transition. `public_numerical_input_origin` ties these receipts to the
same accepted public declaration environment. These contracts have explicit
static dimensions; no universal claim is derived from synthetic probes.
`actual_owned_result` derives actual dependent result acceptance, exact endpoints,
initialized coordinates and the returned owned interpretation.
`owned_result_initialized_bytes` derives byte initialization from that same
post-body certificate. `owned_transfer` and `owned_input_transfer` retain the
exact accepted move and unchanged allocation/layout/endpoints under a fresh
owner. `ResourceSource.public_numerical_result_origin` connects those result
checks to the public request's accepted declaration environment. Callee-local
identities and outstanding loans cannot become owned results. These are logical
checker/transfer facts, not native heap or floating arithmetic proofs.

For [typed map transforms](linalg/transforms-and-metrics.md#linear-transforms), `actual_transform` ties the
accepted operation to its original map, independently checked read reborrow,
full provenance audit and exact emitted schedule. `transform_storage` retains
the allocation, parent and physical layout; `dual_flags`, `conjugate_flags` and
`adjoint_flags` distinguish their coordinate operations. `adjoint_forms` recovers
the actual declared metrics, exact used bases, selected involution and identity
Gram requirements from the same certificate. `declared_metric` states the
checked nondegenerate-data contract. `public_numerical_transform_origin` connects
actual transform receipts to the declaration environment of the public request.
These are structural/source-checker facts, not ideal Hermitian-module laws or
native floating-point refinement. `TransformRegression` adds independent
provenance/metric/loan/flag mutations; public source tests execute scalar and
rectangular real/complex transforms, nested calls and owned materialized results.

For [vector evaluation](linalg/transforms-and-metrics.md#vector-evaluation), `vector_space` and
`vector_input_reborrow` retain actual profile/basis identity and the exact child
borrow, including conjugation. `actual_vector_conjugation` connects the selected
derived space/involution to the real resource transition. `actual_evaluation`
connects the exact accepted dual or Hermitian request to its emitted schedule
and successful replay; `dual_evaluation_types` and `hermitian_evaluation_form`
recover the actual corresponding bases and explicit identity Gram form.
`evaluation_preserves_interpretation` shows that the request inserts no extra
conjugation, and `evaluation_returns_inputs_and_scalar` states restored input
loans and initialized scalar output. The public origin theorems bind these
receipts to the same accepted declaration environment. Native bit examples and
forged-IR regressions are separate evidence, not ideal-module or float laws.

General generative numerical result packages, broader runtime shape/scalar interfaces,
general dual/metric laws and native refinement remain pending. Activation freshness, scope and stale-view rejection are tested
by `NumericalRegression`; generated real/complex fixtures provide separate native
execution evidence. Raw internal GEMM operations retain only their resource
certificate and do not acquire nominal authority from this optional typed path.

The [finite two-map network profile](linalg/networks-and-packing.md#finite-networks) is independently checked
by `Storage.TensorNetwork` before reusing the existing typed product and exact
GEMM emitter. `VastitasOracle.TensorNetwork.ports_used_once` derives exact single
consumption of every occurrence port. `admitted_bilinear_edge`, `output_boundary`
and `no_implicit_conjugation` retain exact bases, variance and ordered boundaries.
`same_input_plan`, `actual_lowering` and `public_network_origin` connect the actual
accepted graph to its deterministic emitted GEMM, resource transition and the
public checker's declaration environment. These do not prove tensor-category
laws, floating arithmetic or native refinement. `NetworkRegression` and public
source/wire/native tests cover nominal mismatches, duplicate/unconnected ports,
forged transforms, immutable reuse and nested calls. General networks and
structural nodes remain outside this two-occurrence profile.

The internal [Graph crossing checker](verification/core-models.md#graph-crossings) has separate
profile/port/return audits and conditional structural rewrite theorems in
`VastitasOracle.Graph`. It does not extend these source/Core evaluation claims
to tensor syntax. Its categorical law provider, selected-method realization,
and bridge from `Graph.Core` to actual returned indexed terms remain pending.

The [exact real ℓ² tail reference](reference/analysis-and-effects.md#l2-tail-reference) checks closed geometric
and reciprocal certificate rules with rational arithmetic in Python. Its
generator/environment/returned-record audits are reference tests only. The
document states the Lean analytic soundness goals and actual returned-Core
integration obligations; no new Hilbert theorem, compiler acceptance,
completeness proof, or iterator memory-safety claim follows from those tests.

The [exact real-plane metric reference](reference/geometry.md#metric-reference) separately tests
metric-free polynomial differentials/cotangent pullbacks, selected constant
metrics and their musical maps. Exact inverse and real positivity checks are
distinct, and evidence retains the object/base/frame/basepoint/metric identity.
Its coordinate-change regressions and nominal-evidence audits are Python
reference results only; the document lists separate future Lean soundness and
same-returned-Core obligations. It adds no AD primitive or compiler acceptance.

The [polynomial first-variation reference](reference/geometry.md#variational-reference) compares the
linear epsilon coefficient of the expanded action with a separately computed
Euler–Lagrange integral plus oriented boundary terms. It checks actual variation
endpoint values and binds evidence to the complete independent polynomial
subject. These are finite Python calculations and mutation regressions; general
function-space differentiation, Lean soundness and the actual returned-Core
connection remain separate obligations. No implicit metric or gradient, new
AD engine, integral-enclosure verifier or variational compiler feature is added.

The retained Stage 0 source-correspondence theorem starts at decoded core `RawModule`.
The full Stage 1 rewriting pass from decoded surface `Program` (or legacy
`RawProgram`) to that core does
**not** yet have a source-correspondence theorem. Finite selection tables and
actual target evidence are proved correct, and the entire resulting core is
proved well typed and terminating; this does not establish correspondence of
every rewritten source call or method body to its original generic syntax.

Resource diagnostic wrappers `Storage.Functions.atStatement_success`,
`atSite_success` and `atFunction_success` preserve the exact successful result
and state of their enclosed checks. Failed expansion carries function/branch
positions and operand identities to the public source renderer. These equations
do not verify the reconstructed source spans or prose; actual-source diagnostic
regressions assert positions and names across calls, branches and nominal errors.

These results do not verify Rust lexing, parsing, source-library composition, JSON
serialization or decoding, diagnostic spans, or the accuracy of diagnostic
prose. The core correspondence relation records elaboration into checked
syntax; it is not a separate operational-equivalence theorem for source text.

The retained legacy big-step semantics evaluates both operands of Boolean `&&` and `||`;
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
stated zero/identity fragment. Later indexed declarations, abstract capabilities,
edit-authority transfer, resource ownership and finite numerical profiles have
their own checker/proof contracts described above and below. They are outside
these retained Stage 0 theorems. Implementation status and remaining extensions
are tracked in the README and the Stage 1 acceptance/completion ledgers.

## Validation

The [initial promotion contract](stage1a.md#promotion) documents the arbitrary-input
numerical proofs in `VastitasOracle.IndexedPromotion`, reflection of the stdlib's
actual public `Indexed.LegacySource.check` executable Core, frontend-fixture
agreement, and the distinction between proof
statements and executable fixture/namespace/native checks. The reflection is a
trusted build step: an elaborator runs the checker, prints the returned module
with `reprStr` and elaborates the text, and a build-time `#eval` compares the
renderings. The theorems are about that reflected module; equality with the
checker's result is not proved from kernel-checked evidence.

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

`TypeAuditRegression` is a retained old-Core build target: its executable checks forge
legacy checked terms directly, bypassing elaboration. They exercise invalid operand
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

`FunctionRegression` exercises retained `checkSurfaceProgram` acceptance, capture
rejection and forged static signatures, including mismatched types with equal
arities and unknown targets for erased function arguments. Rust function tests
cover native higher-order composition, independent nesting, all Fn arities,
dispatch and multiple libraries, unused invalid bodies, changed diagnostic
spans, the 4096-instance limit and reachability after whole-module checking.

Current JSON acceptance is exercised directly by `LegacySourceRegression`:
protocols 2–6, strict metadata/provenance rejection, unused bodies, Fn capture and
signature failures, recursion, Pair construction/projection, abstract-contract
coverage/results, and mutations of the exact returned indexed Core. Its positive
Core is evaluated and passed to `Indexed.Core.Codegen.generate`.
`VastitasPublicTest.AuthorityRegression` retains the historical protocol-6 fixture
and adds the actual frontend protocol-9 fixture
agreement, nested reborrowing/transfer through protocols 6 and 7, and direct
exclusive edits through protocol 5. It checks parent suspension, inside-out
returns, recipient/region provenance, final footprints, old-owner revocation,
applied/unapplied/losing bodies and downgrade rejection under both check/emit
entry policies. All nine accepted cases evaluate the actual returned Core and
pass it to current code generation. The fixture is separate from the compiler
library; its relocated paths assert IR provenance, not filesystem authenticity.
`VastitasPromotion.IndexedRegression` supplies the numerical public-route cases.
The current indexed Core/function/dispatch/authority regression targets retain
their more detailed internal forged-IR cases. Keeping the old tests provides
additional coverage of retained APIs; it does not turn them into public-path tests.

Regenerate `tests/fixtures/edit-recipients.json` when its current source changes.
Keep `tests/fixtures/edit-authority.json` as historical protocol-6 evidence:

```sh
VASTITAS_UPDATE_RECIPIENT_FIXTURE=1 cargo test --locked --test edit_authority authority_ir_matches_public_checker_fixture -- --exact
lake -d lean-kernel build VastitasPublicTest.AuthorityRegression
```

Rust integration tests exercise parsing and diagnostics, malformed raw IR,
semantic rejection codes, native execution, source libraries, implementation
limits, dispatch specialization and rejection, and preservation of existing
output artifacts on failure. The compiler CI jobs build and test on macOS and
Linux from a checkout without `lean/` or mathlib, including the direct kernel
regression targets. A separate job builds the proof oracle and audits its
axioms. Dependency-boundary checks prevent the normal compiler path from
acquiring a mathlib dependency.

The workspace observation job restores the 13 source-workspace archives before
replay and mutation tests with `python3 experiments/source_workspace/fetch.py --all`.
Their original manifests bind each release download to its byte count and SHA-256.
The latest source tree holds the manifests and summaries. A fresh shallow checkout
omits 616,677,342 bytes of ZIPs. Full clones that include earlier commits retain
the old blobs. [Retrieval and offline replay](https://github.com/MGYamada/Vastitas/blob/main/experiments/source_workspace/README.md#retrieve-a-retained-archive)

Other CI jobs retain their non-cone sparse checkout patterns. The pinned checkout
action selects `blob:none` when given those patterns. Its `filter` input would
override them. Compiler jobs retain a separate no-oracle allowlist. The retrieval
regression also checks which source-workspace ZIPs appear in the Git index.


## Package namespace acceptance

**Shared namespace audits; retained legacy body composition.**
`checkNamespaceProgram_*` targets the old surface/Core checker. The public
protocol-3 decoder now enters `Indexed.LegacySource.check`, preserving original
namespace provenance before the common indexed authority check.

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

The kernel builds internal namespace indexes per namespace check and shares
them across lowering, binding checks, validation and reference auditing.
`indexed_owner_lookup` and `indexed_scope_lookup` prove equality with the
original list search/filter, including first-declaration behavior on duplicate
input. `first_index_matches_list`, `indexed_package_matches_list`,
`indexed_module_matches_list`, `indexed_import_lookup` and
`indexed_dependency_lookup` also connect package/module/import/dependency
tables to the original first-match list searches. Module lookup retains the
full package identity check. `rich_package_index` and `rich_module_lookup`
connect the indexed-source entry to the same reconstructed tables. No index is
accepted from wire IR. `alias_preserves_target` retains the original list-search
premise while unfolding the actual indexed resolver.

Active imports use a persistent ordered set. `active_import_key_injective`
preserves every package identity, module path and alias field;
`active_import_membership` equates the actual set's cycle test with the
previous list membership. `Namespace.AliasHit.resolves` ties each cached
unqualified alias to the original resolver at any diagnostic span in its exact
namespace and scope. `importWorkStep_exact` connects the import debit to
the actual remaining member budget. The public `namespace_work_bound`
theorems in `LegacySource`, `IndexedWire` and `ResourceSource` connect each
accepted JSON request to its wire price and the sum of its body-pass
receipts. These bounds concern logical work; they do not establish a
wall-clock bound. The long-chain cases in `tests/namespace_scaling.rs` cover
public check/build/execution, unused bodies, cycles, import sums across
modules, repeated queries in unused functions and output preservation.

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
These shared contract facts are used by the current indexed dispatch/authority
composition. `LegacySource` connects public protocol-4 acceptance to its exact
independently checked indexed Core, typing and total evaluation.
`Functions.checkSurfaceProgram_core` and the old namespace composition remain
separate corollaries about retained APIs.
No theorem asserts native toolchain equivalence or mathematical properties of
uninhabited Variety/Manifold declarations. Compiler/runtime remain mathlib-free.

## Stabilization audits

**Retained composition lemmas.** The namespace/function top-level theorems in
this section concern the old checker; current indexed namespace and static-call
connections are in `IndexedSource`, `IndexedFunctions` and `IndexedAuthority`.

`checkNamespaceProgram_full_audit` and `accepted_memberships_authorized` connect
the retained package checker to a separately reconstructed membership graph.
Every inherited scalar membership has support declared in the ancestor's exact
module, using an abstract-only inheritance path. This is a decoded-input
authority guarantee, not filesystem or author authentication.

The retained function lowerer indexes structural function/instance identities.
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
See [the indexing regression and measurement notes](stage1b.md#stage1b-indexing).

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

**Retained protocol-5 composition.** The `Edit.runTrace`/`Edit.assemble` and
`checkEditProgram_*` entry points below are historical APIs. Current protocol 5
is adapted into `Indexed.AuthoritySource`, using `Authority.assemble` and its
full indexed-body audits. Shared transition/footprint facts retain their stated
premises; the old-Core conclusions are not current wire-acceptance corollaries.

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

`checkEditProgram_audited` unfolds the retained legacy checker: its exact discarded audit
surface and exact final executable surface both pass `checkSurfaceProgram`.
The audit adds ground instances of unapplied contribution bodies without adding
dispatch candidates. Existing all-applicable-method checks include losing applied
bodies. `checkEditProgram_typed_and_ordered` and
`checkEditProgram_total_for_arguments` compose the final accepted module with
existing core typing, dependency and terminating typed-evaluation theorems.
This composition does not prove arbitrary Rust parsing or native codegen correct.

`EditRegression` runs through `NamespaceRegression` in the common eight-target
script. It exercises retained legacy acceptance and direct Lean API forgery attempts.
`tests/edit_borrowing.rs` covers source packages, tampered protocol 5, alias replay,
exclusive loans, owner suspension, Open repair, final footprints, losing/unused
bodies, changed hierarchy/contracts and native execution. Both run in macOS/Linux
no-mathlib CI; the proof oracle and transitive axiom audit remain separate.
Guarantees start at decoded input, not filesystem authenticity or authorship.

### First finite edit composition contract (v1)

**Retained legacy contract.** This proposition and its regression script
remain about `checkEditProgram`, not the current public JSON entry point.

`VastitasOracle.EditBorrowing.checkEditProgram_finite_acceptance`, in
[`EditAcceptance.lean`](https://github.com/MGYamada/Vastitas/blob/main/lean/VastitasOracle/EditAcceptance.lean), has the premise
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

[`scripts/check_edit_acceptance.lean`](https://github.com/MGYamada/Vastitas/blob/main/scripts/check_edit_acceptance.lean)
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

The [exact symplectic reference](reference/geometry.md#symplectic-reference) separates subject
binding, alternation, exterior derivative and domain-qualified inverse checks
for polynomial 2-forms on `R^4` or `D(1+q1)`. It has executable Python regressions,
including same-determinant evidence replay and invalid global extension, but no
Lean soundness proof or connection to the actual accepted Core. Its S1–S6 proof
obligations and production bridge preserve Lawvere-first implementation and the
existing 8+1 division. It does not extend the finite acceptance theorem above.

### Rational SOS cover reference (#244 / #237)

The [SOS cover reference](reference/analysis-and-effects.md#sos-reference) independently checks exact rational
polynomial identities, permutation-qualified LDL^T factors with zero pivots, and
a strictly positive rational lower bound for real-polynomial cozero covers.
It shares arity-aware sparse polynomial arithmetic with the symplectic reference
while preserving that consumer's four-variable contract. Tiny rational mutations,
false covers with PSD residuals, wrong orders/domains and floating-point evidence
have executable rejection regressions. SOS1–SOS4 and Core1–Core3 are **pending**
Lean soundness and actual-returned-Core obligations. This Python-only experiment
does not extend any public acceptance theorem or complete #244 / #237.

## Edit authority acceptance (protocol 6)

`VastitasKernel.Authority.assemble` supplies the authority assembly used by
the current indexed public composition, including adapted protocol 6. It imports the namespace, contribution-lowering, final dispatch and
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

`checkAuthorityProgram_audited` describes the retained legacy top-level checker.
It connects that checker's returned `CertifiedModule`
to both the checked unapplied-body audit surface and the exact checked final
surface. `checkAuthorityProgram_typed_and_ordered` and
`checkAuthorityProgram_total_for_arguments` compose with the existing Core
theorems. No claim is made that an Open intermediate family is executable.

`AuthorityRegression` is an additional target in the shared regression script.
It exercises retained legacy acceptance, rejected API bypasses, forged parent
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
`executable_target_concrete`, `function_origin`, `emitted_call_origin` and
`source_call_resolves` extract the independent static-target, origin and namespace
audits. `emitted_call_exact` retains exact requested-key correspondence for the
executable pass. Audit-only template reuse records both the original requested
key and the emitted origin; `emitted_call_probe_renaming` and
`probe_renaming_aliases` establish the independently checked positional
bijection, and `reused_input_return` preserves the exact caller argument when
the template returns an input Fn. Separate receipts check local-result freshness
against the template result and caller inputs; the actual lowering equation
retains the fresh-name counter and repeated-request cache. These structural
facts are not a source-specialization equivalence theorem.

The public Fn composition also checks converse call coverage against the actual
returned Core. `coreCallEdges` traverses every body, including both branches,
and pairs each target ID with its caller's specialization key. A reconstructed
count table must match the emitted-call ledger in both directions; duplicate
caller keys are independently rejected. `caller_instances_unique`,
`core_call_count`, `core_call_recorded` and `core_call_exact` connect every
actual call and its multiplicity to the recorded caller and exact executable
target origin. Dropping a repeated call's record cannot pass merely because
another matching record exists. This is structural correspondence of returned
Core calls and checked records; it does not prove source evaluation preservation
or completeness of the separate ordinary-source `CallReference` ledger.

`checked_elaboration_budget` connects the actual reconstructed pass and its exact
returned Core to the independently checked 1,000,000-unit work-counter bound.
`FunctionSource.WorkBudget.charge_exact` proves exact accumulation without
overflow or a discarded charge. Source preflight includes every expanded body;
each actual specialization consumes work again in its separate pass, while a
memoized instance does not. This is the syntax/binding-slot admission policy in
[Stage 1b](stage1b.md), not a time-complexity theorem or a bound on namespace and
resource-plan work. The all-body coverage and exact Core audits still run for
every accepted input. Overspent receipt mutations and public check/emit/build
regressions cover aggregate families, unapplied contributions and concrete Fn
specializations; rejecting a large program supplies no proof of its semantics.
Coverage cannot be replaced with a list of executable winners or probes
reused as executable targets. `IndexedFunctionRegression` includes scalar/Fn
forwarding chains, alias patterns, forged reuse receipts, unused-body rejection
and unchanged specialization limits; source tests also check, build and execute
the 90-wrapper examples. The earlier standalone native fixtures remain.
These statements do not prove source
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

`DispatchCall` additionally records the caller specialization and emitted Core
target ID. `dispatch_target_iff` characterizes generic targets using the actual
origin array and reconstructed method/key definition table, independently of
receipt flags. `core_dispatch_call_count` and `core_dispatch_call_recorded`
prove converse occurrence coverage for those actual Core calls.
`core_dispatch_call_selected` connects each to the independently selected
method and exact emitted origin; `dispatch_caller_scope` checks the original
lexical body scope. These checks run in both the audit and executable passes,
including the authority composition used by public protocols. Regressions
delete, duplicate and alter records and cover repeated calls and both branches.
`CallCoverage.legacy_wire`, `indexed_wire` and `resource_wire` apply the
count, origin and winner facts directly to the exact returned Core of public
protocols 2–9, including both ordinary and resource-fragment passes. Matching
is by caller specialization and emitted target with multiplicity; it does not
assign distinct source locations to otherwise identical edges.
The static numerical schedule has a separate positional coverage theorem,
`NumericalCoverage.public_action`, described above.

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
source checker and returned Core. See [indexed-declarations.md](indexed-source.md#indexed-declarations)
for exact checks and [migration acceptance](indexed-source.md#geometry-migration) for the complete
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
remains unproved. See [indexed-declarations.md](indexed-source.md#indexed-declarations).

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
[library contract](https://github.com/MGYamada/Vastitas/blob/main/stdlib/src/geometry/README.md) and
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
correctness. [The migration map](indexed-source.md#geometry-migration) records how the separate
proofs and actual-source regressions fulfill #49/#58–63 without expanding their
claims to arbitrary geometry or the complete native toolchain.

The finite [rank-three tensor/packing profile](linalg/networks-and-packing.md#tensor-packing) adds actual
ordered-axis and corresponding-dual certificates. `VastitasOracle.TensorNumerical`
connects accepted physical groupings, coordinate bounds and initialized packing
outputs to exact emitted transitions and public declaration origins. The finite
coordinate-reference equality retains summation order without field axioms.
Native/C/FFI refinement, floating laws, general tensor-category laws and C parity
are separate obligations; the tensor source and native tests do not prove them.

### Generative owned-map packages

`VastitasOracle.StorageOwnedPackages` imports the actual resource/source checker.
`actual_transition`, `preserves_storage`, `opening_fresh`, `opening_witnesses`,
`closed_target`, `opening_target_profile` and `actual_result` expose accepted pack/open/move and dependent
return contracts; `result_initialized_bytes` derives actual byte initialization.
`move_has_no_native_instruction` states exact erasure by the
existing native lowerer. `public_operation_origin` and `public_result_origin`
connect receipts to the declaration environment of the same protocol-8 checker
result. Both branch receipts and independent unused-body probes are retained.
See [the bounded package contract](linalg/maps-and-gemm.md#owned-map-packages) for rejection/native
coverage and remaining general-package, dynamic-shape and refinement boundaries.

The [bounded contraction-tree profile](linalg/networks-and-packing.md#contraction-trees) adds
`TensorContraction` and `TensorTree` oracle modules over actual checker receipts.
They prove generic grouping bounds/injectivity, rank-two neutral physical
embedding, selected-axis finite coordinate references, reconstructed connected
producer coverage, ordered nominal boundaries, exact resource replay and public
origins. Native permutation tests and matched C evidence remain separate from
C/FFI/BLAS refinement and floating or categorical laws.

`VastitasOracle.StorageDependencies` imports the actual dependency table and
resource runner. An accepted raw prefix ending with a live dependency decomposes
into an actual earlier capture and an accepted action suffix preserving that
entry throughout. Freshness and used-name monotonicity exclude recapture after
invalidation or forgetting; writes and joins invalidate the dependency. The
actual checked-cache/consumer and receipt corollaries require an explicit accepted
intervening replay. The right-arm theorem includes the accepted left run and
exact allocator reseed; it does not treat branch-local receipt code as a root
prefix. Automatic extraction from arbitrary nested source receipts remains a
separate source-correspondence obligation.

`VastitasOracle.StorageCachedPacking` extracts accepted pack/capture transitions,
current source/scratch versions, exact nominal packed operands, emitted
capture/require/GEMM schedules, public environment origins and metadata erasure.
Closed plans require all dependency handles forgotten. These are logical
resource/history and actual-checker facts; they do not prove copied heap contents,
BLAS arithmetic, whole-source/native refinement or AD residual correctness.
See [the bounded packing cache](linalg/networks-and-packing.md#cached-packing).


## Explicit diagonal metric certificates and ideal laws

[Diagonal metrics](linalg/transforms-and-metrics.md#diagonal-metrics) use the actual `StorageMetric` acceptance
certificates. `VastitasOracle.StorageMetric` links declared form/basis identity,
exact bounded-Int realization, live original inputs, initialized output and
precise emitted actions. Pairing includes acceptance of its full eight-action
scratch-write/release/read/GEMM/release expansion and restores caller loans and
allocation owners. Public receipt origins refer to the same accepted declaration
environment; arbitrary supplied coefficient tables are not metric witnesses.
The existing dependency-history proofs cover the new writes, including the
compound scratch/output invalidation and fresh temporary-name ledger.

`StorageMetricLaws` imports these definitions and Lean core's `Grind.Field`,
with an explicit additive/multiplicative involution. `IsCharP K 0` embeds the
actual metric's nonzero Int entries without introducing a fresh nondegeneracy
assumption. The finite-coordinate laws include linearity, semilinearity,
Hermitian symmetry, the defining adjoint pairing equation, and contravariance
under equality of the entire intermediate form. Actual-certificate corollaries
specialize exactly those selected metric fields. They do not assert that an
unrelated buffer contains a matrix product or that NativeFast arithmetic refines
the ideal formulas. No mathlib, custom axiom, numerical error bound, or native
refinement claim is added. Native bit/cost and failure-preservation tests are
separate evidence.

## Exact affine algebra checker (Stage 2, #571)

Stage 2's finite affine-geometry profile ([tracker](https://github.com/MGYamada/Vastitas/issues/571)) rests on an exact QQ polynomial core. It is internal for now: no source syntax or wire field reaches it until the protocol-9 surface lands.

- **Runtime arithmetic.** `lean-kernel/VastitasKernel/AlgebraRuntime.lean` imports only Init, and `scripts/check_boundaries.py` enforces this as a runtime boundary. It keeps sparse polynomials canonical: exact core `Rat` coefficients, nonzero terms, and strictly decreasing monomials in degLex order (total degree first, then lexicographic with coordinate 0 most significant). Division takes fuel from an order embedding of the dividend's leading monomial, so evaluation is total and the exact invariant `dividend = Σ qᵢgᵢ + remainder + rest` holds at every step. Maps between presented objects carry their source ring's basis, so composition, pairing, equality and coefficient reads need no environment.
- **Bases.** In `AlgebraBasis.lean`, `compute` runs Buchberger's algorithm with cofactor tracking. It is untrusted. `verify` independently checks a stored certificate:
  - the basis is canonical, monic, strictly ordered and reduced;
  - each basis element is its cofactor combination of the relations;
  - each relation and each S-pair divides to remainder zero, with the quotient identity, and for S-pairs the standard-representation bound, checked exactly.

  Both phases share the `algebraWork` budget, and every produced polynomial is bounded by `algebraTerms`. A violation is `E_LIMIT`; a failed identity is `E_AFFINE_RELATION`.
- **Proved.** `VastitasOracle.AlgebraBasis.verify_sound` and `certify_sound` show that a successful verification establishes every recorded identity (`CertificateValid`). These are identities between kernel `Poly` operations. The correspondence of those operations with `MvPolynomial (Fin n) ℚ`, and the canonical normal forms given by Buchberger's criterion, belong to the mathlib bridge and are not claimed here.
- **Tested.** `VastitasAlgebraTest.BasisRegression`, run by `scripts/check_kernel_regressions.sh`, compares the kernel's bases and normal forms with the independent Python model `scripts/affine_algebra_reference.py`, using the shared fixture `tests/fixtures/algebra-bases.json`. It also checks:
  - that ε survives, and ε² vanishes, in QQ[e]/(e²);
  - the written order of pullback composition;
  - forged, unordered, non-reduced and incomplete certificates;
  - the 16/17-generator and 32/33-relation boundaries;
  - the term and work budgets.

  `python3 scripts/affine_algebra_reference.py --check` keeps the fixture current, and `scripts/test_affine_algebra_reference.py` checks the Python model's own Buchberger, reducedness and divisor-order invariants.
