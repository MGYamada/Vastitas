# Finite abstract scalar selectors and contracts

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
[the runnable example](../examples/abstract-selectors.vast) are uninhabited
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

## Abstract method contracts

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

The [contract example](../examples/abstract-contracts.vast) checks, builds and
runs to 42. `ContractRegression` and `tests/abstract_contracts.rs` exercise the
actual checker, native flat/package/--lib paths, higher-order lowering, unions,
empty domains, overlapping/conflicting results, authority and tampered IR.
The implementation is the finite initial increment of #48, not the complete
historical Stage 1 design.
