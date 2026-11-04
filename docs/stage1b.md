# Stage 1b: independent lambdas and static higher-order functions

Stage 1b extends the scalar/geometry core and [Stage 1a dispatch](stage1a.md)
with capture-free function values.
Later increments added abstract selectors/contracts, edit borrowing and authority
transfer, resource ownership and finite numerical profiles. Their initial
contracts and final integrated revision are in the [delivery ledger](stage1-completion.md). All public wire
versions now use the common declaration-driven function/dispatch/authority checker;
see [the compatibility boundary](indexed-source.md#indexed-declarations--compatibility-adapter-for-protocols-26).
The source contracts below remain implemented; retained Stage 1b lowering APIs
and older proofs are identified separately. Tracking: [#50](https://github.com/MGYamada/Vastitas/issues/50).

## Syntax and values

| Contract | Type |
| --- | --- |
| One Int argument | `Fn<Int, Int>` |
| Two Int arguments | `Fn<(Int, Int), Int>` |
| Zero arguments | `Fn<(), Int>` |
| One Unit argument | `Fn<Unit, Int>` |
| Function argument and result | `Fn<Fn<Int, Int>, Fn<Int, Int>>` |

Parentheses inside the first Fn slot describe a parameter sequence. They do
not introduce general tuple values or tuple types. `Fn` is reserved in Rust
and Lean. The old proposed type spelling `fn(Int) -> Int` is rejected.
Anonymous expressions use `fn(x: Int) -> Int { x + 1 }`; all parameter and
result types are explicit. Supported function contracts recursively contain
Nat, Int, Bool, Unit and Fn. Geometry-dependent function contracts are rejected.
Existing ordinary functions can still accept/return geometric values, and a
scalar-signature lambda can perform checked geometric operations internally.

```vast
fn invoke(callback: Fn<Int, Int>, x: Int) -> Int { callback(x) }
fn keep(callback: Fn<Int, Int>) -> Fn<Int, Int> { callback }
fn main() -> Int {
    let increment = fn(x: Int) -> Int { x + 1 };
    let alias = keep(increment);
    invoke(alias, 41)
}
```

Named ordinary functions are also values. Values can be bound, aliased, passed,
returned and invoked, including chained applications such as `factory()(42)`.
Each lambda has independent parameters and local bindings, but cannot shadow
an enclosing binding with a parameter, `let`, or `unpack` name. Separate sibling
lambdas may reuse their own local names. This lexical check runs before lifting
and is independently enforced by Lean. Referring to an
outer argument, local function value, or local geometric endpoint is
`E_CAPTURE`; pass needed values explicitly. Top-level functions, generics and
builtins remain callable. Nested lambdas obey the same independent-scope rule.

A generic family is not a Fn value. Use an ordinary function or lambda wrapper
to call it. Generic and ordinary/lambda bodies may call one another. Function
values do not extend dispatch keys or method selectors/results; dispatch
remains over Nat/Int/Bool/Unit with its existing product order.

## Static target rule

After substituting function arguments, every application must resolve to one
backend definition. An `if` returning a function is accepted only when both
branches have the same type and resolve to the same definition. Passing the
same function as both parameters to a selector is therefore permitted.
Two separately written lambdas have distinct identities even when their text
or diagnostic spans match. Different targets produce `E_STATIC_CALL`, even
with a literal `true` condition; there is no constant-folding exception.

No runtime closure or function-pointer selection is introduced. Runtime scalar
computations involved in producing a function value are checked and retained
when function values are erased. Function-returning definitions become Unit
results in the internal core; their static result target is carried separately.

## Checking and specialization

Protocol 2 adds surface types, lambda expressions and expression invocation.
Protocols 2–6 now decode that unresolved syntax through `Indexed.LegacySource.check`
into the common `Indexed.AuthoritySource` composition used by protocol 7's
`Indexed.Wire.check`. Its `Indexed.FunctionSource` compiler lowers functions into
independently audited indexed Core, including programs without Fn constructs.
`checkSurfaceProgram`, `checkProgram` and their old Raw/Checked Core remain retained
internal APIs; Main does not call them. Their older source-correspondence results
do not imply correspondence for the current source lowering.

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
origin and return renaming. A 90-function forwarding chain no longer spends
4095 instances rechecking fresh names: its audit has one probe template and
one concrete instance per wrapper, plus the ordinary entry and scalar callback.
This also applies when wrappers return Fn values. The normalization and
independent alias check are quadratic in Fn parameter arity; the regression
establishes linear instance counts for forwarding chains, not a general linear
compiler bound or achieved native performance.

Each pass permits at most 4096 higher-order instances in a compilation unit;
plain first-order functions do not consume that budget. Limits report `E_LIMIT`.
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
The actual audit and executable passes independently charge every newly compiled
Fn specialization before checking its body; an already cached instance is not
charged twice. Each pass additionally caps worklist requests at 2,000,000, plus
one final completion step. The passes retain separate counters and target states.

Exceeding any budget rejects the entire input with `E_LIMIT`; it never licenses
omitting an unused body or accepting a partial dispatch audit. The exact returned
pass carries its accumulated work and independently checks the upper bound.
Protocols 2–8 use this common pure-function path, including pure resource
fragments. This does not bound resource-plan expansion/replay, all namespace
resolution, quadratic local-context operations, or total compiler wall time.
Those remaining work limits and indexing costs are tracked in #422, #423 and
[#426](https://github.com/MGYamada/Vastitas/issues/426). Existing per-body,
dispatch-key and higher-order-instance limits remain in force.

An independent structural predicate checks the recorded static target and
erased function-argument signatures against backend definitions. The actual
returned core then passes the existing whole-module typing and dependency
audits. Only after those checks does code generation retain functions reachable
from the validated `main` entrypoint. Unused bodies cannot escape checking by
being absent from generated code.

The oracle proves capture freedom, static signature consistency, and typing,
dependency order and termination of the exact returned core through the actual
public acceptance path. Full operational correspondence from surface lambda
syntax through specialization, Rust/JSON correctness and native code equivalence
remain outside these proofs. See [verification boundaries](verification.md).

## Homogeneous data pairs

The data extension adds `Pair<Nat>` and `Pair<Int>` to ordinary function
parameters/results, local bindings and equal-type branches. `pair(x, y)` infers
both operands independently and requires identical Nat or Int types;
`pair(1, 2)` is always `Pair<Int>`, even under an expected `Pair<Nat>` annotation.
`pair_first(p)` and `pair_second(p)` return the ordered components with exactly
the element type. A bound producer is evaluated once, with ordinary let sharing.

Heterogeneous, nested, Bool/Unit and geometric pairs are unsupported. Pair is
not a dispatch key/selector or part of a Fn contract; a scalar-signature lambda
may use Pair internally. `Fn<(A, B), C>` remains an argument sequence, not a Pair.
Methods may return Pair; their selected signature determines the call and
projection types in both first-order and function-containing programs. The
[stdlib](https://github.com/MGYamada/Vastitas/blob/main/stdlib/README.md#explicit-promotion) supplies four Nat/Int promotion methods.
See [the executable example](https://github.com/MGYamada/Vastitas/blob/main/examples/pairs.vast) and [protocol](protocol.md).

The actual core carries finite Pair types and primitive operations. Native code
uses Lean `Prod Nat Nat` or `Prod Int Int`. Current indexed typing, evaluation and
termination proofs include these cases. The old raw-Core source-correspondence
theorems cover Pair only in the retained pipeline. Neither set establishes
general tuples or source-function rewriting correspondence.

## Regression coverage

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
[indexing measurements](#stage1b-indexing) distinguish those regressions from
timing claims.

`tests/pairs.rs` checks Pair source/raw-IR typing and native execution in both
input modes. `LegacySourceRegression` checks current public Pair calls and
mutations of their returned Core; `IndexedCoreRegression` audits indexed Pair
terms. `PairRegression` retains old-Core construction, projection, call and
code-generation audit tests.


### Lowering type information

The following `ResultType`/raw-expression optimization describes the retained
`FunctionChecker` pipeline. Current `IndexedFunctionBodies` instead constructs
typed indexed Core directly; old raw-Core proofs do not transfer to that lowering.

The common lowering retains backend-inferred `ResultType` information with the
raw expression. It includes nominal object references. Generic keys, scalar/Pair
call arguments, let/unpack bindings, and block results reuse that information
when it is already fixed; nested scalar generic calls no longer recheck all
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

### Internal identities and resource limits

In the retained lowering API, source functions, lifted lambdas and method instances have distinct
`FunctionName` constructors. Static targets distinguish executable definitions
from signature probes, and an `InstanceKey` stores a function identity and its
ordered function-argument identities. Lookup, memoization, branch equality and
cycle detection use these types. Generated strings are rendered when producing
the preserved core. Current `Indexed.FunctionSource` uses its own checked
definition/origin and specialization keys, with the same separate audit/executable
policy; see [indexed acceptance](verification.md). Public JSON names and protocol
versions are unchanged.

Resource values are defined in
[`lean-kernel/compiler-limits.json`](https://github.com/MGYamada/Vastitas/blob/main/lean-kernel/compiler-limits.json).
Cargo generates frontend constants from it; Lean reifies the kernel's values
as transparent natural-number definitions in `VastitasKernel.Limits`. Both build
systems track changes to the file. Parsing depth, source traversal, body checking,
generated lets, aggregate elaboration work, specialization count, dispatch keys, dispatch-table
work, authority-trace work and namespace resolution
retain separate named budgets even when their numeric values coincide.

<a id="stage1b-indexing"></a>

## Stage 1b indexing: issue #141 follow-up

This is a historical implementation and measurement record for the retained
`FunctionChecker`/`checkSurfaceProgram` pipeline at the commits below. Main now
uses the indexed source composition. These measurements and old-Core theorems
are not current-pipeline performance or source-correspondence claims; see
[current verification routes](verification.md#current-public-checker-routes).

### Starting point

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

### Correspondence and order

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
- The existing `checkSurfaceProgram_static_calls` now applies this equivalence
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

### Regression and reproduction

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

### Validation record

Executed locally on Linux x86_64 (AMD EPYC 9V74, shared container), with pinned
Lean 4.35.0 release and Rust 1.99.1. The container exposes the current executable
at `/proc/self/exe` but restricts numeric `/proc/<pid>/exe`; Lean compilation
used a local compatibility shim for that self-path lookup. The measured kernel
subprocesses ran without the shim. Build/test jobs were finished before timing.
Dependency lockfiles and compiler limits were unchanged.

| Check | Result |
| --- | --- |
| `lake -d lean-kernel build` | Passed, including the new kernel equivalence proofs |
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

The new Rust test initially used reserved `apply` and an unformatted diagnostic
expectation. Those fixture mistakes were corrected; the final full run above
passed. There are no `sorry`/`admit` additions. Local proof compilation had only
pre-existing mathlib module-system notices in unchanged oracle files.

Not executed here: hosted macOS/Linux CI for this branch, local macOS validation,
or the original issue's debug-CLI timing procedure. Native integration tests and
kernel regressions ran locally; this does not establish native-toolchain formal
correctness or an end-to-end compiler complexity bound.

### Measured comparisons

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

[Raw samples: original comparison](benchmarks/stage1b-original-comparison.csv).

Already-fixed main `5d12a7e` versus this follow-up, forward-chain subset of the
full 24-workload matrix (chain/shared × forward/reverse × plain/lambda × 3 sizes):

| Functions | Baseline plain | Baseline lambda | Candidate plain | Candidate lambda |
| --- | ---: | ---: | ---: | ---: |
| 2,000 | 0.166 | 0.181 | 0.138 | 0.157 |
| 4,000 | 0.320 | 0.327 | 0.293 | 0.307 |
| 8,000 | 1.070 | 1.132 | 1.099 | 1.255 |

[Raw samples: full main comparison](benchmarks/stage1b-main-comparison.csv).
The candidate was measured separately in the two comparisons; run-to-run ranges
are in the CSV files. The major improvement over the issue commit already came
from #167. This follow-up repairs audit completeness and pins order/scale
regressions; it does not show a uniform additional speedup over the indexed main
(some cases are slower). The 8,000-function forward-chain timings also do not
justify a claim that total compilation is linear. No performance ratio is used
as a correctness assertion; the only scale regression deadline is the existing
per-process 60-second watchdog.
