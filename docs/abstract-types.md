# Finite abstract scalar selectors

The first abstract-type increment adds nominal selectors to the existing finite
Nat/Int/Bool/Unit dispatch universe. It does not add concrete values, value-type
upcasts, Union types, ownership, storage, linear algebra, or geometric models.
Abstract method contracts are a separate increment.

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
