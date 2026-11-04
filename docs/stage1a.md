# Stage 1a: finite multiple dispatch

Stage 1a adds static scalar dispatch to the Stage 0 language. A compilation
unit consists of one entry file and explicitly selected `--lib` sources. All
generic declarations and methods are available together; there is no runtime
method registration or generic-dispatch fallback.

## Declarations

```vast
generic add(left, right) {
    domain (Int, Int), (Nat, Nat);
}

method add(left: Int, right: Int) -> Int {
    int_add(left, right)
}

method add(left: Nat, right: Nat) -> Nat {
    nat_add(left, right)
}
```

The generic declares an argument count and the concrete tuples callers may
use. `domain;` declares an empty domain; `domain ();` declares the single
zero-argument tuple. Tuple lengths must agree with the generic's arity.
Methods name an existing generic, give every parameter a selector, and declare
a concrete scalar, `Pair<Nat>`, or `Pair<Int>` result. Result types need not agree
between distinct keys or between a winner and its nonwinners. Lean selects the
winner using only argument types, then checks calls against that method's exact
declared result. Projections expose the selected Pair's element type to later
generic calls. Pair does not extend the scalar key universe or selectors.
Generic `main` is not an entrypoint; native programs still require an ordinary
`fn main() -> Int`.

The canonical condition syntax is after the result type:

```vast
method maximum(left: Int, right: Int) -> Int requires (HasOrder) {
    int_max(left, right)
}
```

For convenience, `requires (...)` before `->` is also accepted. One method
cannot have two condition clauses. The selector names and capability names
are fixed by the compiler; users cannot declare additional ones.

## Selectors and capabilities

| Name | Meaning |
| --- | --- |
| `Nat`, `Int`, `Bool`, `Unit` | Concrete scalar types |
| `Number` | Abstract selector above `Nat` and `Int` |
| `Any` | Abstract selector above every concrete scalar type |
| `HasEq` | Static fact for every concrete scalar type |
| `HasOrder` | Static fact for `Nat` and `Int`; implies `HasEq` |

`Any` and `Number` are selector-only names, not first-class value types. Nat
and Int are siblings: `Nat <: Int` is not introduced. There are no implicit
conversions or dispatch choices based on geometric identity, runtime state,
or a caller's expected result type.

A tuple has the capability facts common to all its arguments. A zero-argument
tuple has no capability facts. Requirements are normalized using
`HasOrder ⇒ HasEq`; therefore `requires (HasOrder)` and
`requires (HasEq, HasOrder)` are the same condition. Unknown capabilities,
unrealizable method conditions, and duplicate normalized signatures are errors.

## Selection and whole-program checking

For arity `n`, Lean enumerates every tuple in `{Nat, Int, Bool, Unit}^n`, up to
4,096 tuples. This bound permits arity six and rejects arity seven, even with
an empty declared domain. All keys are checked for ambiguity. The declared
domain is additionally checked for coverage: every callable key needs exactly
one best method. Restricting the domain cannot hide ambiguity elsewhere.

A method is applicable when every concrete argument is a nominal subtype of
its selector and the tuple has its required capability facts. A method is
more specialized when its selectors are no broader and its normalized
requirements are no weaker, with at least one strict component. The unique
undominated applicable method wins. Declaration order is not a tiebreaker.

This is an order on the declarations, not on the sets of currently applicable
keys. For example, `(Number)` without requirements and `(Any)` with
`requires (HasOrder)` both happen to apply to Nat and Int. Neither declaration
dominates the other: one has the narrower selector, the other the stronger
condition. Their intersection is ambiguous.

Even `(Int)` without requirements is incomparable with `(Number)` requiring
`HasOrder`: concrete selectors do not imply declaration requirements. Adding
`requires (HasOrder)` to the Int method makes it more specific in both
components. Ambiguity diagnostics show the normalized signatures, the
conflicting components, and a resolving signature when available. Such a hint
addresses the reported key; the edited family must still pass all checks.

Capabilities are unary facts intersected across arguments, not relations
between them. A `(Number, Number)` method requiring `HasOrder` also applies to
`(Nat, Int)`, even if the callable domain contains only equal-type pairs. A body
using `left < right` therefore fails there. For now, write separate `(Nat, Nat)`
and `(Int, Int)` methods, plus explicit mixed methods that call `promote` and
delegate to a homogeneous method, as in the arithmetic library. Shared type variables
and relational capabilities remain design work (#37); narrowing the domain
does not suppress body checking.

Every method body is specialized and type-checked for every key to which the
method applies, even if it never wins or that key lies outside the domain.
Consequently, an invalid broad fallback cannot be hidden behind more specific
methods. The selected calls become ordinary checked core function calls;
recursion is rejected after specialization, including cycles through ordinary
functions. A call from one specialization to another is allowed when the
resulting dependency graph is acyclic.

Generic arguments are inferred before selecting a method. Bare integer
literals therefore have type Int in generic calls. To choose the Nat method,
pass a Nat value, for example a `let n: Nat = 20;` binding. An expected Nat
result does not change `add(20, 22)` to the Nat specialization. Use `int(n)` or
`nat_to_int(n)` when an explicit Nat-to-Int conversion is needed.

## Standard library and use

The [initial promotion increment](#promotion) adds exact Pair return types and
shared mixed Nat/Int arithmetic, with numerical contracts for the actual bodies.

`stdlib/src/arithmetic/generic.vast` provides `add` and `maximum` using the
existing `int_*` and `nat_*` functions. Existing operators and prefixed
functions retain their behavior, including saturating Nat subtraction.

```sh
cargo run --locked -- build examples/dispatch-arithmetic.vast \
  --lib stdlib/src/arithmetic/int.vast \
  --lib stdlib/src/arithmetic/nat.vast \
  --lib stdlib/src/arithmetic/generic.vast -o target/dispatch-arithmetic
./target/dispatch-arithmetic
# 42
```

No implicit prelude is loaded. The generic library needs both prefixed source
libraries; declarations can be split across explicit inputs and each keeps its
original diagnostic position.

## Scope

Stage 1a is not all of Stage 1. Independent lambdas and static higher-order
functions are added separately by [Stage 1b](stage1b.md). [Finite abstract
selectors and bodyless contracts](#abstract-types) extend the same four-key
engine, with contract domains added to the callable domain. User-defined concrete data types,
user-declared capabilities and runtime dispatch remain unimplemented. Edit
permissions and borrowing ([packages](packages.md#edit-borrowing)), storage ownership
([resource programs](storage/resource-programs.md)) and linear algebra
([numerical maps](linalg/maps-and-gemm.md)) were added by later increments. The existing
shadowing and recursion prohibitions, generative geometric identities, and
arbitrary-precision integer semantics remain in force.

The [verification boundary](verification.md) distinguishes finite dispatch and
checked-core guarantees from Rust parsing, wire decoding, and native toolchain
correctness. Future extensions are tracked in the [roadmap](guide/historical-roadmap.md).

<a id="abstract-types"></a>

## Finite abstract scalar selectors and contracts

The first abstract-type increment adds nominal selectors to the existing finite
Nat/Int/Bool/Unit dispatch universe. It does not add concrete values, value-type
upcasts, Union types, ownership, storage, linear algebra, or geometric models.
Bodyless abstract method contracts extend callable domains and constrain the
selected concrete result without creating runtime methods.

```vast
abstract type Numeric <: Number;
abstract type NaturalNumeric <: Numeric;
subtype Int <: Numeric;
subtype Nat <: NaturalNumeric;

generic classify(x) { domain (Nat), (Int); }
method classify(x: Numeric) -> Int { 0 }
method classify(x: NaturalNumeric) -> Int { 42 }
```

`abstract type A;` has `Any` as its default parent. Multiple parents use
`abstract type A <: (B, C);`; a single parent may omit the parentheses. Parents
are `Any`, `Number`, or user-defined abstract selectors. `subtype` adds one of
the four concrete scalars to a user-defined abstract type. Membership flows to
parents. No membership declaration may modify a built-in type.

There are at most 64 nominal types including Nat, Int, Bool, Unit, Number and
Any. The kernel rejects cycles (including self-parents), duplicate names,
parents or memberships, unknown references, and any resulting change to the
relations between the six built-ins. For example, adding Bool to an abstract
child of Number is invalid. Capability facts remain the established scalar
facts: the source cannot declare new ones.

Nominal identity is independent of inhabitants. If unrelated A and B both
contain only Int, neither is more specific than the other. Two methods using
those selectors remain ambiguous at Int. If B explicitly inherits A, B is
more specific even when their inhabitant sets coincide. The nominal/capability
product order, ambiguity checks over all keys, explicit concrete generic
domains, and checks of every applicable body (including nonwinners and keys
outside the callable domain) are unchanged. The key-space bound remains 4096.

Abstract selectors cannot appear as ordinary parameter/result types, Fn
contracts, Pair elements, or generic domain keys. They introduce no implicit
Nat-to-Int conversion. `Variety` and `Manifold` in
[the runnable example](https://github.com/MGYamada/Vastitas/blob/main/examples/abstract-selectors.vast) are uninhabited
nominal declarations, without mathematical axioms or geometric claims.

In packages, `pub abstract type` and imports/reexports follow existing path
visibility. Identity is the defining package/module/name; aliases preserve it.
Only the exact defining module may add scalar memberships. A child module,
importer, or public reexport does not gain edit authority. A new abstract type
may name visible abstract parents without modifying those parents' declarations.
Flat inputs and explicit `--lib` files share one compilation namespace.

Inputs using these declarations use [protocol 4](protocol.md), explicitly
marked `flat` or `package`. Existing sources keep protocols 2 and 3. Rust retains
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

### Abstract method contracts

```vast
abstract type Numeric;
subtype Nat <: Numeric;
subtype Int <: Numeric;
generic widen(x) { domain; }
abstract method widen(x: Numeric) -> Int { domain (Numeric); }
method widen(x: Nat) -> Int { int(x) }
method widen(x: Int) -> Int { x }
```

The callable domain is the union of the generic's concrete tuples and every
abstract method's expanded domain. A domain tuple contains scalar or abstract
selectors. Lean enumerates the existing four-key universe and expands each
tuple component through the validated hierarchy. For example, `(Numeric, Bool)`
expands to `(Nat, Bool)` and `(Int, Bool)`. Repeated clauses and overlapping
contracts do not duplicate callable keys. Generic domains retain their existing
concrete-only syntax and duplicate-key rejection.

Every expanded key must satisfy that contract's parameter selectors and
`requires` clause. This checks concrete keys, so an unrelated selector with the
same inhabitants may describe a contract domain without creating a nominal
subtype relation. Requirements use the established HasEq/HasOrder facts.
`domain;` is an explicit empty contract and is allowed. A written tuple that
expands to no keys is an error, even if another tuple expands nonempty. `domain
();` describes the single nullary key; that key has no capability facts.

Contracts have no executable body and never participate in dispatch. The usual
nominal/capability product order chooses the unique concrete winner. Its result
annotation must exactly match every contract covering the key, including
`Pair<Nat>` versus `Pair<Int>`. Results do not influence selection; no numeric
coercions are introduced. Missing or ambiguous concrete winners are rejected.
All applicable concrete bodies, including nonwinners and bodies outside the
callable domain, still undergo the independent core checks.

Only the generic's exact defining module may add abstract contracts. Imports,
public exposure, aliases and child modules grant no edit authority. Domain and
parameter paths use ordinary visibility/alias resolution. An alias in the same
module preserves the original owner's authority. Contracts have no `pub`
modifier of their own. Flat sources and explicit `--lib` inputs retain their
shared namespace.

The [contract example](https://github.com/MGYamada/Vastitas/blob/main/examples/abstract-contracts.vast) checks, builds and
runs to 42. `ContractRegression` and `tests/abstract_contracts.rs` exercise the
actual checker, native flat/package/--lib paths, higher-order lowering, unions,
empty domains, overlapping/conflicting results, authority and tampered IR.
The implementation is the finite initial increment of #48, not the complete
historical Stage 1 design.

### Inherited membership authority

Package inputs also audit every scalar-to-abstract relation in the transitive
closure. The ancestor's exact module must have declared a membership for that
scalar into the ancestor or one of its descendants. Support paths use abstract
inheritance alone, so scalar membership cannot circularly justify itself.
Foreign inheritance and aliases remain legal when they reuse independently
owner-authorized scalars; introducing a new foreign membership reports `E_OWNER`.
The audit reconstructs origins from decoded package/module declarations.

<a id="promotion"></a>

## Initial Nat/Int promotion

The implemented increment consists of homogeneous numeric Pair data, selected
method result types, four stdlib `promote` methods, and their reuse by `add` and
`maximum`. It completes the initial scope of #55, not the full historical
Stage 1 proposal. Abstract types, relational selectors, edit borrowing, general
conversion search, geometry promotion and variadic promotion remain separate.

### Public contract

| Input key | `promote` result | `add` / `maximum` result |
| --- | --- | --- |
| Nat, Nat | `Pair<Nat>` | Nat |
| Nat, Int | `Pair<Int>` | Int |
| Int, Nat | `Pair<Int>` | Int |
| Int, Int | `Pair<Int>` | Int |

`pair` requires independently inferred operands of one identical numeric type.
Thus `pair(0, 1)` has type `Pair<Int>` even at a `Pair<Nat>` parameter. Bind
`let a: Nat = 0; let b: Nat = 1;` first and pass `pair(a, b)` when Nat is intended.
Projections preserve that type and component order. Pair is not a dispatch
key, a Fn contract component, a nested/general tuple or a geometric package.
Generic selection uses scalar argument types and the existing finite
nominal/capability product order. A caller's expected result never chooses a
winner or changes a bare literal from Int to Nat.

The only nonidentity conversion is explicit `int(n)`. Each mixed arithmetic
method binds promotion once and calls the homogeneous Int method using the
Pair's projections. Homogeneous methods still call their scalar kernels.
Primitive operators do not gain mixed-type coercions. All applicable bodies,
including losing/out-of-domain/unused instances, must check; the complete
specialized call graph must be acyclic before pruning.

See [stdlib usage](https://github.com/MGYamada/Vastitas/blob/main/stdlib/README.md), [dispatch](stage1a.md),
[Pair and Fn boundaries](stage1b.md#homogeneous-data-pairs) and
[protocol](protocol.md). In package mode, the exact owner is
`arithmetic::generic`; imports and reexports confer call access only. Flat
`--lib` mode preserves its existing whole-assembly semantics.

### Actual-body proofs and fixture agreement

`tests/promotion.rs::stdlib_ir_matches_proof_fixture` runs the real Rust
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
reflection agreement are executable checks, not a new general decoder proof.

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

Two mutations are deliberately accepted by ordinary typing but rejected by the
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

A semantic change may require new proofs; regeneration alone is not approval
of a changed numerical policy. Run the full validation documented in
[verification](verification.md), including hosted axiom and no-mathlib checks.
No `sorry`, `admit`, native-decision axiom or custom unproved axiom is used by
these numerical proofs.

The stdlib now has one tracked set of definitions. Run
`python3 scripts/build_stdlib_package.py` to create the ignored manifest-mode
sources under `stdlib/target/package/`; `--check` verifies freshness. The
manifest location and logical module owners are unchanged. This source consolidation followed #72–#76.
