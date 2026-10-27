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

The [initial promotion increment](promotion.md) adds exact Pair return types and
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
functions are added separately by [Stage 1b](stage1b.md). User-defined data types,
profiles and capabilities, edit permissions, borrowing, storage ownership,
linear algebra, and runtime dispatch remain unimplemented. The existing
shadowing and recursion prohibitions, generative geometric identities, and
arbitrary-precision integer semantics remain in force.

The [verification boundary](verification.md) distinguishes finite dispatch and
checked-core guarantees from Rust parsing, wire decoding, and native toolchain
correctness. The [historical design](design.md) remains a proposal for later
stages, not an implementation claim.
