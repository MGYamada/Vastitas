# Verification boundaries

The proof oracle in `lean/` imports the implementation's definitions from
`lean-kernel/`. It has no executable target and is not consulted when compiling
or executing `.vast` programs. mathlib is pinned to v4.35.0; the executable
kernel and generated runtime depend only on the Lean distribution.

Protocol version 2 enters through `checkSurfaceProgram`. The unchanged-syntax
path uses `DispatchChecker.checkProgram`; the extended path checks independent
lambdas and static function contracts, then specializes function calls. Both
paths check finite dispatch families and pass the exact lowered module to
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
- For extended syntax, `checkSurfaceProgram_static_calls` identifies the exact
  `lowerFunctions` result, proves `StaticCallsValid` for its recorded calls, and
  retains the equation showing that the very same core passed `checkModule`.
- `static_target_signature` and `function_argument_signature` state structural
  type equality with actual backend definitions for recorded targets and erased
  function arguments. They follow from the independent audit established by
  the preceding actual-checker theorem, not from a trusted frontend annotation.
- `checkSurfaceProgram_core` connects both legacy and extended branches to
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
capabilities, function edit ownership, borrowing, storage ownership, linear
algebra, iteration, and recursion remain unimplemented and outside these
theorems. Finite static dispatch does not establish those later Stage 1 goals.

## Validation

Run from the repository root:

```sh
cargo fmt --all -- --check
cargo clippy --locked --all-targets -- -D warnings
lake -d lean-kernel build vastitas-kernel
lake -d lean-kernel build VastitasKernel.TypeAuditRegression
lake -d lean-kernel build VastitasKernel.DispatchRegression
lake -d lean-kernel build VastitasKernel.FunctionRegression VastitasKernel.NamespaceRegression
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
Linux from a checkout without `lean/` or mathlib, including all four direct kernel
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
All four direct regression targets run in no-mathlib CI.

This does not prove Rust filesystem loading/authenticity, full source namespace
syntax preservation, native toolchain equivalence, edit borrowing, or abstract
methods. Package metadata identifies entries in the supplied IR graph; it does
not certify the bytes on disk. The general Stage 1 design remains incomplete.
