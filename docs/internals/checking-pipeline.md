# Checking pipeline

This chapter describes how the compiler checks generics, abstract types and
function values: how it enumerates dispatch keys, specializes function values
and audits the Core that code generation receives. The rules themselves are in
[Generics and dispatch](../stage1a.md) and [Function values](../stage1b.md).
[Verification boundaries](../verification.md) states which of these checks are
proved.

## The public path

Protocol 2 carries surface types, lambda expressions and expression invocation.
Protocols 2–6 decode that unresolved syntax through `Indexed.LegacySource.check`
into the common `Indexed.AuthoritySource` composition used by protocol 7's
`Indexed.Wire.check`. Its `Indexed.FunctionSource` compiler lowers functions into
independently audited indexed Core, including programs without Fn constructs.
`checkSurfaceProgram`, `checkProgram` and their old Raw/Checked Core remain retained
internal APIs; Main does not call them. Their older source-correspondence results
do not imply correspondence for the current source lowering.

## Dispatch checking

For a generic with `n` parameters, the kernel enumerates every key in
`{Nat, Int, Bool, Unit}^n`, at most 4096 keys, checks every key for ambiguity
and checks that every key of the callable domain has a winner.
[Selection](../stage1a.md#selection) gives the rules. A diagnostic for an
ambiguous key shows the normalized signatures, the components that conflict
and, when one exists, a signature that resolves the key. Such a hint addresses
the reported key only; the edited family must still pass every check.

The kernel specializes and type-checks every method body for every key at
which the method applies, so an invalid broad method cannot hide behind more
specific ones. Selected calls become ordinary calls of the checked Core. The
kernel rejects recursion after specialization, including cycles through
ordinary functions; a call from one specialization to another is valid when
the resulting dependency graph has no cycle.

## Abstract types and contracts

Inputs with abstract types, `subtype` declarations or abstract methods use
[protocol 4](../protocol.md#protocol-selection) or a later protocol, explicitly
marked `flat` or `package`. Sources without them may use protocols 2 and 3. Rust retains
unresolved paths and spans; Lean independently resolves names, audits edit
authority, constructs the hierarchy, and selects executable methods. The
backend creates the indexes and hierarchy; the wire cannot supply trusted
owners, capabilities, resolved targets or selected winners.

`VastitasOracle.AbstractTypes` imports the actual hierarchy implementation.
It exposes its retained validation evidence (hierarchy validity, built-in
relations, concrete values and capability facts), proves the actual hierarchy
construction invariant under permutations of type and membership declarations,
and connects selected targets to the existing finite engine's nominal
optimality theorem. Namespace membership authority is independently audited.
The existing checked-core typing, dependency and termination theorems continue
to concern the exact returned core. Source-to-IR preservation, filesystem
identity authenticity and native toolchain equivalence remain outside the proof
boundary. Ordinary compilation and generated executables require no mathlib.

Package inputs also audit every scalar-to-abstract relation in the transitive
closure. The ancestor's exact module must have declared a membership for that
scalar into the ancestor or one of its descendants. Support paths use abstract
inheritance alone, so scalar membership cannot circularly justify itself.
Foreign inheritance and aliases remain legal when they reuse independently
owner-authorized scalars; introducing another foreign membership reports `E_OWNER`.
The audit reconstructs origins from decoded package/module declarations.

## Function specialization

No function value survives into the generated program. A definition that
returns a function value becomes a definition with a `Unit` result in the
internal Core, and the compiler carries its static result target separately.

Lean independently checks lambda free names, assigns lambda IDs by syntax
traversal, validates signatures, and constructs every applicable dispatch
specialization. Whole-key ambiguity, explicit-domain coverage, nonwinning
methods, out-of-domain applicable bodies, and the 4096-key bound remain intact.

All definitions, including unused higher-order functions and lambdas, undergo
a signature-probe checking pass. Abstract function parameters can supply typed
probe results only in this pass; arguments and erased computations are still
checked. The resulting audit module is passed through the core checker.
A separate pass with fresh state specializes executable calls by definition ID
and function-argument IDs. Audit probes never enter that pass or native output.
Each function instance has its own 4096-unit body-checking budget. A bounded
worklist suspends calls until their specialized callee is available, including
calls returning Fn values; the caller's body budget is retained on resumption.
Call-chain length, declaration order, and an unrelated lambda do not share or
reduce that budget. Completed instances are memoized and active cycles rejected.

All-probe audit requests reuse a body by source definition and the complete
equality pattern of its Fn arguments, after checking each exact formal
signature. For example, `(p, p)` and `(p, q)` have distinct templates. Returned
input probes are renamed back to the actual caller argument; a template-local
probe receives a fresh caller-side name, retained for repeated identical
requests. Concrete and mixed probe/concrete calls keep their original keys.
Non-input probe results are abstract signature witnesses; reuse does not infer
that results of different wrapper calls denote the same function. Executable
specialization independently reconstructs their concrete targets, including
factories returning Fn values through long forwarding chains.
The independent audit checks the positional bijection, signatures, emitted
origin and return renaming. A 90-function forwarding chain does not spend
4095 instances rechecking fresh names: its audit has one probe template and
one concrete instance per wrapper, plus the ordinary entry and scalar callback.
This also applies when wrappers return Fn values. The normalization and
independent alias check are quadratic in Fn parameter arity; the regression
establishes linear instance counts for forwarding chains, not a general linear
compiler bound or achieved native performance.

Each pass permits at most 4096 specialized instances in a compilation unit.
Every lambda instance counts, as does every instance of a higher-order function;
plain first-order named functions do not consume that budget. Limits report `E_LIMIT`.
Recursive specialization is rejected, followed by the core dependency audit.

The common indexed function compiler also has a **1,000,000-unit aggregate
elaboration budget** per pass. `IndexedFunctionWork` counts each expression,
statement, block and function header once, plus parameter slots and unpacked
binding slots. Both branches, nested lambda bodies and all call arguments count.
These units are an admission policy, not elapsed time, allocation bytes, or
native instructions. Type syntax and namespace traversal have separate limits.

Before lifting/preparation, work is summed across ordinary functions, every
applicable method/key, unapplied contributions and extra pure fragments. Method
expansion also charges before retaining each instance, so separate families
cannot each spend a fresh budget. Nonwinning and out-of-domain instances count.
The actual audit and executable passes independently charge every compiled
Fn specialization before checking its body; an already cached instance is not
charged twice. Each pass additionally caps worklist requests at the smaller of
a structural bound and 2,000,001, which is two requests per unit of the
elaboration budget plus one final completion step. The passes retain separate
counters and target states.

Exceeding any budget rejects the entire input with `E_LIMIT`; it never licenses
omitting an unused body or accepting a partial dispatch audit. The exact returned
pass carries its accumulated work and independently checks the upper bound.
Protocols 2–9 use this common pure-function path, including pure resource
fragments. This does not bound resource-plan expansion/replay, all namespace
resolution, quadratic local-context operations, or total compiler wall time.
Separate budgets bound two of these:
[Resource checking work](../storage/checked-storage.md#storage-functions--resource-checking-work)
bounds resource checking, and the limits of
[Protocol 3](../protocol.md#protocol-3-package-namespaces) bound namespace
work. The [History](#history) section names the issues that reported these
limits. Existing per-body, dispatch-key and higher-order-instance limits remain
in force.

An independent structural predicate checks the recorded static target and
erased function-argument signatures against backend definitions. The actual
returned core then passes the existing whole-module typing and dependency
audits. Only after those checks does code generation retain functions reachable
from the validated `main` entry point. Unused bodies cannot escape checking by
being absent from generated code.

The oracle proves capture freedom, static signature consistency, and typing,
dependency order and termination of the exact returned core through the actual
public acceptance path. Full operational correspondence from surface lambda
syntax through specialization, Rust/JSON correctness and native code equivalence
remain outside these proofs. See [verification boundaries](../verification.md).

### Internal identities and resource limits

In the retained lowering API, source functions, lifted lambdas and method instances have distinct
`FunctionName` constructors. Static targets distinguish executable definitions
from signature probes, and an `InstanceKey` stores a function identity and its
ordered function-argument identities. Lookup, memoization, branch equality and
cycle detection use these types. Generated strings are rendered when producing
the preserved core. Current `Indexed.FunctionSource` uses its own checked
definition/origin and specialization keys, with the same separate audit/executable
policy; see [indexed acceptance](../verification.md). Public JSON names and protocol
versions are unchanged.

Resource values are defined in
[`lean-kernel/compiler-limits.json`](https://github.com/MGYamada/Vastitas/blob/main/lean-kernel/compiler-limits.json).
Cargo generates frontend constants from it; Lean reifies the kernel's values
as transparent natural-number definitions in `VastitasKernel.Limits`. Both build
systems track changes to the file. Parsing depth, source traversal, body checking,
generated lets, aggregate elaboration work, specialization count, dispatch keys, dispatch-table
work, authority-trace work and namespace resolution
retain separate named budgets even when their numeric values coincide.

## Pairs in Core

The actual core carries finite Pair types and primitive operations. Native code
uses Lean `Prod Nat Nat` or `Prod Int Int`. Current indexed typing, evaluation and
termination proofs include these cases. The old raw-Core source-correspondence
theorems cover Pair only in the retained pipeline. Neither set establishes
general tuples or source-function rewriting correspondence.

## Regression coverage

The [contract example](https://github.com/MGYamada/Vastitas/blob/main/examples/abstract-contracts.vast) checks, builds and
runs to 42. `ContractRegression` and `tests/abstract_contracts.rs` exercise the
actual checker, native flat/package/--lib paths, higher-order lowering, unions,
empty domains, overlapping/conflicting results, authority and tampered IR.

`tests/functions.rs` checks native calls, aliases, parameters/results, nested
Fn contracts and lambdas, zero/Unit/multiple arguments, dispatch, multiple
explicit libraries, captures, invalid unused bodies, mismatched types/arity,
runtime target choices, recursion, the 4096-instance boundary and forged IR.
`VastitasKernel.LegacySourceRegression` checks current JSON acceptance and
rejection directly; `IndexedFunctionRegression` covers the common function
compiler and forged static ledgers. The current function compiler additionally
reconstructs caller/target occurrence counts from the returned Core and checks
them against its emitted-call ledger. Generic-call records retain the emitted
target ID and caller specialization and must cover all actual generic calls,
including repeated calls and both branches. These audits apply separately to
the signature and executable passes; they are not source operational or native
refinement proofs. `FunctionRegression` retains the old
`checkSurfaceProgram` API tests. Both macOS and Linux CI run these
with no oracle/mathlib checkout; a separate job builds and audits the proofs.

The indexed audit also checks duplicate identities with different signatures
against the original existential predicate, including witnesses at every
position. Declaration-order/shared-callee cases pin the emitted dependency
order, while the existing 60-second watchdog covers 20,000 functions with and
without a lambda, reversed declarations, and a shared callee. The reproducible
[indexing measurements](#history) distinguish those regressions from
timing claims.

`tests/pairs.rs` checks Pair source/raw-IR typing and native execution in both
input modes. `LegacySourceRegression` checks current public Pair calls and
mutations of their returned Core; `IndexedCoreRegression` audits indexed Pair
terms. `PairRegression` retains old-Core construction, projection, call and
code-generation audit tests.

## Promotion proofs and fixture

The specification [std::arithmetic::generic](../spec/std-arithmetic-generic.md)
states the contract of promotion, and [Promotion](../stage1a.md#promotion)
describes it. `tests/promotion.rs::stdlib_ir_matches_proof_fixture` runs the real Rust
`parse_sources` frontend on the three canonical stdlib files using stable
virtual diagnostic filenames/offsets. It compares the complete JSON against
`tests/fixtures/promotion.json`; it does not substitute a handwritten AST.
Both no-mathlib CI jobs run this test.

`VastitasPromotion.IndexedFixture` runs `Indexed.LegacySource.check json false`,
the public protocol-2 library path used by Main, while elaborating the fixture.
It reflects the exact returned `executable.core.module` as ordinary transparent
Lean data. Build-time checks compare that module with a fresh public-checker
result and independently check its indexed Core typing/dependency audits. Lake tracks the
JSON as an input dependency of this separate test/proof library; it is not a
dependency of ordinary compiler builds. Concrete fixture acceptance and this
reflection agreement are executable checks, not a general decoder proof.
The reflection runs the checker and `reprStr` at elaboration time, so the
agreement rests on compiled evaluation that the axiom audit cannot see.

`VastitasOracle.IndexedPromotion` proves `IndexedEvaluation.Evaluates` on those
exact indexed Core bodies for arbitrary Nat/Int arguments. This states an equation
for the actual `Indexed.Core.Semantics.eval` at every sufficiently large bound.
Function selection in this fixed fixture uses the source name and actual input
scalar types; an expected result does not select a method. The proofs include
the actual argument/temporary lets, scope/ascription wrappers and helper calls:

| Theorem | Contract |
| --- | --- |
| `promotion_total` | Each of the four bodies evaluates to the specified Pair and has its exact concrete return type |
| `promotion_preserves_values` | Each evaluated component has its original integer value, interpreting Nat with `Int.ofNat` |
| `same_type_identity_nat`, `same_type_identity_int` | Same-type promotion preserves type, values and component order |
| `reversal` | Swapping inputs preserves common type and swaps components; the reversed actual body evaluates accordingly |
| `idempotence` | Re-promoting the resulting components preserves type and values |
| `embedding_preserves_addition`, `embedding_preserves_order`, `embedding_preserves_maximum` | The Nat-to-Int embedding preserves the required arithmetic/order facts |
| `addition_correct`, `maximum_correct` | The actual mixed bodies evaluate through their shared let, promotion call, projections and homogeneous kernel to the specified numerical result |

The individual `promote_nn/ni/in/ii`, `add_nn/ni/in/ii` and
`maximum_nn/ni/in/ii` lemmas expose the actual evaluation derivations. The
general current `IndexedProgramSafety` and `LegacySource` acceptance theorems
provide the separate indexed typing/order/termination chain.
Idempotence does not replace the dependency-order proof.

This does not prove Rust parsing, general JSON decoding, filesystem authenticity,
full surface/namespace rewriting equivalence, or native-toolchain equivalence.
Package source parity, namespace acceptance and flat/package native behavior
are covered by regression checks; the numerical fixture uses flat input.

### Regression and maintenance

`VastitasPromotion.IndexedRegression` enters the real JSON checkers for flat
protocols 2/4, package protocols 3–6 and protocol 7. It checks all three returned
finite families, the 16 binary keys and selected method identities, exact Core
numerical results, executable entry/code generation and rejected forged
Core/source metadata. It uses the existing bounded indexed evaluator as test
infrastructure; the oracle proofs above establish arbitrary-input contracts.

The earlier `VastitasPromotion.Fixture`/`Regression` and
`VastitasOracle.Promotion` remain explicitly labelled legacy checks/proofs of
`checkSurfaceProgram` and the old `Semantics.Eval`. Those entry points are not
Main's current route and do not establish current source correspondence.

Two mutations are accepted by ordinary typing but rejected by the
stdlib contract: a mixed method returning `pair(0, 0)` and a Nat/Nat method
returning `Pair<Int>`. The compiler has no special policy keyed on `promote`.
The native and raw-IR suites additionally cover large integers, zero, negatives,
invalid Pair forms, expected-type mismatch, ambiguity outside the domain,
coverage, nonwinners, cycles, ownership, aliases and function boundaries.

After an intentional stdlib change, regenerate and review the fixture:

```sh
VASTITAS_UPDATE_PROMOTION_FIXTURE=1 cargo test --locked --test promotion stdlib_ir_matches_proof_fixture
lake -d lean-kernel build VastitasPromotion.IndexedRegression VastitasPromotion.Regression
lake -d lean build VastitasOracle
```

A semantic change may require further proofs; regeneration alone is not approval
of a changed numerical policy. Run the full validation documented in
[verification](../verification.md), including hosted axiom and no-mathlib checks.
No `sorry`, `admit`, native-decision axiom or custom unproved axiom is used by
these numerical proofs.

The stdlib has one tracked set of definitions. Run
`python3 scripts/build_stdlib_package.py` to create the ignored manifest-mode
sources under `stdlib/target/package/`; `--check` verifies freshness. The
manifest location and logical module owners are unchanged.

## History

- Finite dispatch and abstract contracts are the initial increment of
  [#48](https://github.com/MGYamada/Vastitas/issues/48), not the complete
  historical Stage 1 design. Shared type variables and relational
  capabilities remain design work in
  [#37](https://github.com/MGYamada/Vastitas/issues/37).
- Function values were tracked in
  [#50](https://github.com/MGYamada/Vastitas/issues/50), and promotion
  completed the initial scope of [#55](https://github.com/MGYamada/Vastitas/issues/55).
  The standard-library sources were consolidated by #72–#76.
- The work that the elaboration budget does not bound, and its indexing
  costs, were reported in [#422](https://github.com/MGYamada/Vastitas/issues/422),
  [#423](https://github.com/MGYamada/Vastitas/issues/423) and
  [#426](https://github.com/MGYamada/Vastitas/issues/426). The three issues
  are closed: the resource work budget bounds resource checking, and the
  import and namespace budgets bound namespace work.

### Retained pipeline: lowering type information

The following `ResultType`/raw-expression optimization describes the retained
`FunctionChecker` pipeline. Current `IndexedFunctionBodies` instead constructs
typed indexed Core directly; old raw-Core proofs do not transfer to that lowering.

The common lowering retains backend-inferred `ResultType` information with the
raw expression. It includes nominal object references. Generic keys, scalar/Pair
call arguments, let/unpack bindings, and block results reuse that information
when it is already fixed; nested scalar generic calls do not recheck all
inner calls merely to discover their result types. A generic operand is inferred
independently before the selected method's parameter types are considered.

Context-dependent integer/operator/conditional expressions remain unresolved
until their expected type is available. Geometric calls still use the core's
dependent argument substitution and fresh-object construction, and reusing a
block result retains the original escape check. This is a conservative reuse
optimization, not a global AST cache: uncached expressions still use core
inference. No metadata is trusted by the final independent function/module
check, which rechecks the retained raw bodies and performs the typing/dependency
audits as before.

### Stage 1b indexing: issue #141 follow-up

This is a historical implementation and measurement record for the retained
`FunctionChecker`/`checkSurfaceProgram` pipeline at the commits below. Main
uses the indexed source composition. These measurements and old-Core theorems
are not current-pipeline performance or source-correspondence claims; see
[current verification routes](../verification.md#current-public-checker-routes).

#### Starting point

On 2026-10-28, issue [#141](https://github.com/MGYamada/Vastitas/issues/141)
was closed by merged [PR #167](https://github.com/MGYamada/Vastitas/pull/167).
This follow-up starts from main `5d12a7e2cb4d3a41d7bbf0ef69c684abe588b994`.
A final main check found `10454414dc1684df82e1dad6a8861bf1e19343f8`;
its only subsequent changes were the stdlib ADR and its design-index link.
The compiler sources are identical to the measured `5d12a7e` baseline.
That baseline already contains the State definition/instance/global indexes,
active-set membership and constant-time stack pop, the two separate lowering
passes, an indexed final static audit, and a lambda-containing 20,000-function
watchdog case. Those changes are retained, not reimplemented.

The remaining semantic gap was audit completeness: the main audit index retained
only the last definition of each identity. For a forged ledger with two `f`
definitions of types `Fn<Int, Int>` and `Fn<Bool, Int>`, a call to the former
satisfied `StaticCallsValid` but failed `staticCallsValid`. This is a false
rejection of the audit helper's existential specification; it is not evidence
that a duplicate source program bypasses declaration validation.

#### Correspondence and order

- `definitionLookup` is the ordinary lookup index. Its theorem proves exact
  agreement with `List.find?`, including first-declaration behavior on duplicates.
  The original ordered definitions remain the driver of each lowering pass.
- `definitionIndex` is rebuilt inside the backend from `lowered.definitions`.
  It stores all definitions of each identity, in list order. A proof field states
  that each bucket equals the original list filter; the proof is runtime-erased.
- `staticCallsValid_iff` proves equivalence with `StaticCallsValid` on every
  ledger, including duplicate identities and signatures. Targets and function
  bindings use full structural type equality. Probe arguments are rejected.
  No uniqueness assumption or frontend-provided index is needed for the theorem.
- The existing `checkSurfaceProgram_static_calls` applies this equivalence
  to the actual `lowerFunctions` result, and retains acceptance of that same
  lowered core by `checkModule`.

The ordered declaration list, call ledger and generated function array are not
reordered by hash iteration. The scheduler still uses its explicit active stack
for cycle diagnostics, set membership for recursion detection, and stack pop/set
erasure on completion. Signature probes never enter executable state. Body fuel,
the administrative worklist bound and the 4096-specialization limit are unchanged.

For normally prepared distinct identities, buckets have one element. Expected
index construction and target auditing cost is linear in definitions plus
recorded targets/bindings, excluding hashing and structural signature comparison
costs. Forged duplicate-heavy ledgers scan the matching bucket, not all unrelated
definitions. This is not a worst-case hash-table bound or a claim that the entire
compiler is linear.

#### Regression and reproduction

`VastitasKernel.FunctionRegression` covers first/middle/last duplicate signature
witnesses, missing identities/signatures, same-arity type mismatches, invalid
function-argument contracts, probes and distinct identities with equal rendered
names. It compares the executable index against the independent original
predicate. Public acceptance cases pin dependency output order with shared
callees and with/without an unrelated lambda, and preserve duplicate diagnostic
precedence. Rust tests exercise shared higher-order memoization through native
output (42), both declaration orders, and unchanged cycle diagnostics.

`kernel_checks_twenty_thousand_functions_within_the_watchdog` retains the
60-second harness and checks four workloads: a plain forward chain, that chain
with an invoked lambda, the lambda chain in reverse declaration order, and
20,000 functions sharing a callee with an invoked lambda.

Build baseline and candidate kernels with the same pinned Lean version, then:

```sh
python3 scripts/benchmark_lowering.py \
  --baseline-kernel /path/to/baseline/vastitas-kernel \
  --kernel lean-kernel/.lake/build/bin/vastitas-kernel \
  --sizes 2000 4000 8000 --runs 3 > comparison.csv
```

The default matrix includes chain/shared call graphs, forward/reverse declaration
order, and lambda absent/present. The size counts the parameterized functions;
`main` and, when enabled, its lambda are additional. Every binary/workload receives
one warmup; measured runs alternate binary order. CSV includes individual samples,
median, minimum and maximum. Timings cover process startup, JSON decoding, both
lowering passes and final static/core audits. Payload construction and Rust
parsing are excluded. Rejected or timed-out workloads abort rather than produce
misleading timings. The script does not infer a speedup or assert a timing ratio.

#### Validation record

Executed locally on Linux x86_64 (AMD EPYC 9V74, shared container), with pinned
Lean 4.35.0 release and Rust 1.99.1. The container exposes the current executable
at `/proc/self/exe` but restricts numeric `/proc/<pid>/exe`; Lean compilation
used a local compatibility shim for that self-path lookup. The measured kernel
subprocesses ran without the shim. Build/test jobs were finished before timing.
Dependency lockfiles and compiler limits were unchanged.

| Check | Result |
| --- | --- |
| `lake -d lean-kernel build` | Passed, including the added kernel equivalence proofs |
| `bash scripts/check_kernel_regressions.sh` | All eight targets passed, including expanded FunctionRegression |
| `lake -d lean build` | Passed, including Functions and all downstream oracle users |
| `(cd lean && lake env lean ../scripts/audit_axioms.lean)` | Passed for 6,386 declarations; standard allowed axioms only |
| `cargo fmt --check` | Passed |
| `cargo clippy --locked --all-targets -- -D warnings` | Passed |
| `cargo test --locked --all-targets` | 205 passed; all four 20,000-function watchdog workloads passed |
| `python3 scripts/check_boundaries.py` | Passed |
| `python3 -m unittest discover -s scripts -p 'test_*.py'` | 14 passed |
| CLI `check` / `build` of `examples/functions.vast`, then native execution | Passed; output 42 |
| Same duplicate-ledger fixture against main and candidate | Main: predicate true / index false; candidate: true / true |

The added Rust test initially used reserved `apply` and an unformatted diagnostic
expectation. Those fixture mistakes were corrected; the final full run above
passed. There are no `sorry`/`admit` additions. Local proof compilation had only
pre-existing mathlib module-system notices in unchanged oracle files.

Not executed here: hosted macOS/Linux CI for this branch, local macOS validation,
or the original issue's debug-CLI timing procedure. Native integration tests and
kernel regressions ran locally; this does not establish native-toolchain formal
correctness or an end-to-end compiler complexity bound.

#### Measured comparisons

All numbers below are seconds, medians of three accepted runs after one warmup.
The workloads use `fi(x) = f(i+1)(x)` and a final identity. Unlike the issue's CLI
example, they do not add 1 at each edge and exclude Rust parsing. They therefore
must not be compared directly with the issue's 0.76 / 3.36 / 14.6 seconds.

Original issue commit `d620b2f8e9349d8d54b5ce036d0a2c26fad0f1d4` versus this
follow-up, using forward call chains (command adds `--orders forward --shapes chain`):


| Functions | Baseline plain | Baseline lambda | Candidate plain | Candidate lambda |
| --- | ---: | ---: | ---: | ---: |
| 2,000 | 0.146 | 0.517 | 0.143 | 0.152 |
| 4,000 | 0.400 | 1.852 | 0.360 | 0.320 |
| 8,000 | 1.297 | 8.181 | 0.998 | 1.176 |

[Raw samples: original comparison](../benchmarks/stage1b-original-comparison.csv).

Already-fixed main `5d12a7e` versus this follow-up, forward-chain subset of the
full 24-workload matrix (chain/shared × forward/reverse × plain/lambda × 3 sizes):

| Functions | Baseline plain | Baseline lambda | Candidate plain | Candidate lambda |
| --- | ---: | ---: | ---: | ---: |
| 2,000 | 0.166 | 0.181 | 0.138 | 0.157 |
| 4,000 | 0.320 | 0.327 | 0.293 | 0.307 |
| 8,000 | 1.070 | 1.132 | 1.099 | 1.255 |

[Raw samples: full main comparison](../benchmarks/stage1b-main-comparison.csv).
The candidate was measured separately in the two comparisons; run-to-run ranges
are in the CSV files. The major improvement over the issue commit already came
from #167. This follow-up repairs audit completeness and pins order/scale
regressions; it does not show a uniform additional speedup over the indexed main
(some cases are slower). The 8,000-function forward-chain timings also do not
justify a claim that total compilation is linear. No performance ratio is used
as a correctness assertion; the only scale regression deadline is the existing
per-process 60-second watchdog.
