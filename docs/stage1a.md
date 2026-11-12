# Generics and dispatch

A **generic** is a function whose body the compiler chooses from a finite set
of **methods**, by the types of the arguments. The choice, called
**dispatch**, happens at compile time: every call of a generic becomes a call
of one method. The argument types that dispatch uses are the four scalar types
`Nat`, `Int`, `Bool` and `Unit`. Abstract types name sets of them, and abstract
methods widen the set of argument types that a generic accepts. Programs cannot
declare their own scalar types or capabilities, and no method is chosen at run
time.

## Generic declarations

> **Syntax**
>
> ```text
> GenericDeclaration -> `generic` IDENTIFIER `(` GenericParameters? `)` `{` `domain` Domain `}`
> GenericParameters -> IDENTIFIER ( `,` IDENTIFIER )* `,`?
> Domain -> `;` | DomainKey ( `,` DomainKey )* `,`? `;`
> DomainKey -> `(` ( ScalarType ( `,` ScalarType )* `,`? )? `)`
> ```

`generic add(left, right) { domain (Int, Int), (Nat, Nat); }` declares the
generic `add` with two parameters. A **key** is a tuple of scalar types, one per
parameter. The **domain** of the declaration lists keys at which callers may
call the generic: `domain;` is the empty domain, and `domain ();` the single
key of a generic without parameters. The **callable domain** of the generic is
its domain together with the keys of its abstract methods, as
[Abstract methods](#abstract-methods) describes.

Rules:

- Every key of the domain must have one type per parameter. Another key is an
  error (`E_DISPATCH_DOMAIN`).
- A key must list scalar types. An abstract type in a key is an error
  (`E_TYPE`).
- A key must not occur twice in a domain (`E_DUPLICATE`).
- A generic has at most six parameters, because the compiler enumerates every
  key of its parameters, at most 4096. A seventh parameter is an error
  (`E_LIMIT`). [Appendix D](appendix/limits.md#generics-and-abstract-types) lists these
  limits.
- A generic is not a function value, as
  [Path expressions](language/expressions.md#path-expressions) says.

## Method declarations

> **Syntax**
>
> ```text
> MethodDeclaration ->
>     `method` Path `(` MethodParameters? `)` MethodSignature BlockExpression
> MethodParameters -> MethodParameter ( `,` MethodParameter )* `,`?
> MethodParameter -> IDENTIFIER `:` Path
> MethodSignature -> Requirements? `->` MethodResult | `->` MethodResult Requirements
> Requirements -> `requires` `(` ( IDENTIFIER ( `,` IDENTIFIER )* `,`? )? `)`
> MethodResult -> ScalarType | PairType
> ```

A method declares a **selector** for each parameter of its generic and a
result type, and it may require **capabilities** of its arguments:

```vast
method maximum(left: Int, right: Int) -> Int requires (HasOrder) {
    int_max(left, right)
}
```

The `requires` clause may also come before `->`.

| Selector | Accepts |
| --- | --- |
| `Nat`, `Int`, `Bool`, `Unit` | That scalar type |
| `Number` | `Nat` and `Int` |
| `Any` | Every scalar type |
| An [abstract type](#abstract-types) | The scalar types that belong to it |

| Capability | Holds for |
| --- | --- |
| `HasEq` | Every scalar type |
| `HasOrder` | `Nat` and `Int`. It implies `HasEq` |

`Nat` and `Int` are siblings under `Number`: neither is a subtype of the other.
A key has a capability when every type of the key has it. The key `()` of a
generic without parameters has no capability.

Rules:

- A method must name a generic in scope. A name that is not in scope is an
  error (`E_NAME`). The name of another declaration is an error (`E_NAME` in
  flat mode, `E_OWNER` in manifest mode).
- In manifest mode a method must be in the module that defines its generic, as
  [Owners](language/edit-authority.md#owners) says.
- A method has one selector per parameter of its generic. Another number is an
  error (`E_ARITY`).
- A selector must be a scalar type, `Number`, `Any` or an abstract type.
  Another type, such as a pair type, a function type or a geometric type, is
  an error (`E_TYPE`), and so is the name of a function. A name that is not in
  scope is an error (`E_TYPE` in flat mode, `E_NAME` in manifest mode).
- A capability must be `HasEq` or `HasOrder` (`E_CAPABILITY`). A program
  cannot declare capabilities.
- A method has at most one `requires` clause (`E_PARSE`).
- The result type of a method must be a scalar type, `Pair<Nat>` or
  `Pair<Int>` (`E_TYPE`). Methods of one generic may have different result
  types.
- Two methods of one generic must not have the same selectors and equal
  requirements (`E_DUPLICATE`). `requires (HasOrder)` equals
  `requires (HasEq, HasOrder)`, and `requires ()` equals no clause.
- The requirements of a method must hold for some key that its selectors
  accept. A method that applies to no key is an error (`E_CAPABILITY`).
- `Number`, `Any` and abstract types are not types of values, as
  [Types](language/types.md) says. They appear as selectors, as parents of
  abstract types and in the keys of abstract methods.

## Selection

A method **applies** at a key when each type of the key belongs to its
selector and every type of the key has the required capabilities. Method `a`
is **more specific** than method `b` when three conditions hold. Each selector
of `a` is no broader than the matching selector of `b`. The requirements of
`a` are no weaker than those of `b`. One of these comparisons is strict. At a
key, the **winner** is the one applicable method that no other applicable
method is more specific than. The order of declarations never decides, and
neither does the expected type of the call, the identity of a geometric
object or any state at run time.

Rules:

- At every key of all scalar types, not only at the keys of the domain, the
  applicable methods must not have two incomparable best methods. Such a key
  is an error (`E_DISPATCH_AMBIGUOUS`).
- Every key of the callable domain must have a winner. A key without one is an
  error (`E_DISPATCH_COVERAGE`).
- The compiler checks the body of every method at every key at which it
  applies, even where it never wins and outside the callable domain. Each of
  these checks counts against the work budget of
  [Specialization](stage1b.md#specialization).
- A call of a generic must have one argument per parameter (`E_ARITY`), and
  each argument must have a scalar type (`E_TYPE`). The types of the
  arguments are the key of the call.
- The key of a call must be in the callable domain. Another key is an error
  (`E_DISPATCH_DOMAIN`), even when a method applies at it.
- The compiler infers the types of the arguments of a call before it selects a
  method. An integer literal argument therefore has type `Int`, and the
  expected type of a call never selects a method.
- A call of a generic selects its winner at compile time, and the call has the
  winner's result type. Calls through generics follow the rule against
  recursion of [Calls](language/functions.md#calls) after selection
  (`E_RECURSION`).
- The work of building the dispatch table of one generic has a limit, which
  [Appendix D](appendix/limits.md#generics-and-abstract-types) gives (`dispatchWork`).
  Exceeding it is an error (`E_LIMIT`).

Capabilities hold for single types, not for relations between arguments. A
method with selectors `(Number, Number)` that requires `HasOrder` also applies
at `(Nat, Int)`, where `left < right` is an error. Write separate methods for
`(Nat, Nat)` and `(Int, Int)` instead.

Neither method below is more specific than the other: the first has the
narrower selector, the second the stronger requirement. They are ambiguous at
the keys `(Nat)` and `(Int)`, although `(Nat)` is outside the callable domain.
Adding `requires (HasOrder)` to the first method makes it more specific and
removes the ambiguity:

```vast
{{#include ../examples/reject/dispatch/incomparable-methods.vast}}
```

```text
{{#include ../examples/reject/dispatch/incomparable-methods.stderr}}
```

## Abstract types

> **Syntax**
>
> ```text
> AbstractTypeDeclaration -> `abstract` `type` IDENTIFIER ( `<:` AbstractParents )? `;`
> AbstractParents -> Path | `(` Path ( `,` Path )* `)`
> SubtypeDeclaration -> `subtype` IDENTIFIER `<:` Path `;`
> ```

An **abstract type** is a selector with a name. `abstract type A <: B;`
declares `A` under the parent `B`, and `abstract type A <: (B, C);` under
several parents. Without `<:` the parent is `Any`. `subtype Int <: A;` places a
scalar type in `A`, and so in every ancestor of `A`. An abstract type has no
values and adds no conversions.

Rules:

- A parent must be `Any`, `Number` or an abstract type in scope. An unknown name
  is an error (`E_NAME`), and a scalar type as a parent is an error
  (`E_TYPE`).
- The abstract types must not form a cycle, and no abstract type may be its own
  parent (`E_HIERARCHY`).
- A `subtype` must place one of the four scalar types (`E_TYPE`) in an
  abstract type in scope (`E_NAME`). `Number`, `Any` or a scalar type after
  `<:` is an error (`E_OWNER`). The name of another declaration there is an
  error (`E_NAME` in flat mode, `E_OWNER` in manifest mode).
- A `subtype` must not change the relations between the built-in types. An
  example is `Bool` in an abstract type under `Number` (`E_HIERARCHY`).
- A name, a parent of one abstract type or a membership must not be declared
  twice (`E_DUPLICATE`).
- A program has at most 64 nominal types, counting `Nat`, `Int`, `Bool`, `Unit`,
  `Number` and `Any` (`E_LIMIT`), as
  [Appendix D](appendix/limits.md#generics-and-abstract-types) lists.
- In manifest mode, only the module that defines an abstract type may declare
  `subtype` memberships of it (`E_OWNER`). For each scalar type that an
  abstract type holds, its defining module must declare that scalar type into
  the abstract type or into one of its descendants (`E_OWNER`). Foreign
  inheritance therefore cannot add a scalar type to an abstract type.
- An abstract type may name a visible abstract type of another module as its
  parent. This edits no declaration of that module.
- An abstract type is distinct from every other abstract type, whatever its
  members. Two unrelated abstract types with the same members are
  incomparable selectors. A child is more specific than its parent.

[`examples/abstract-selectors.vast`](https://github.com/MGYamada/Vastitas/blob/main/examples/abstract-selectors.vast)
declares a small hierarchy and dispatches on it:

```vast
{{#include ../examples/abstract-selectors.vast}}
```

The executable prints `42`. `Variety` and `Manifold` are declarations without
members; they carry no mathematical axioms.

## Abstract methods

> **Syntax**
>
> ```text
> AbstractMethodDeclaration ->
>     `abstract` `method` Path `(` MethodParameters? `)` MethodSignature
>     `{` `domain` ContractDomain `}`
> ContractDomain -> `;` | ContractKey ( `,` ContractKey )* `,`? `;`
> ContractKey -> `(` ( Path ( `,` Path )* `,`? )? `)`
> ```

An **abstract method** has no body. It adds keys to the callable domain of its
generic and fixes the result type that the winner at those keys must have. The
keys of its domain may name selectors. Such a key stands for every key of
scalar types that it accepts: `(Numeric, Bool)` stands for `(Nat, Bool)` and
`(Int, Bool)` when `Numeric` holds `Nat` and `Int`.

Rules:

- An abstract method follows the rules of
  [Method declarations](#method-declarations) on the name of its generic, on
  the number and the form of its selectors, on the names of its capabilities
  and on its result type. Its requirements need not hold for any key.
- Every key of the domain must have one entry per parameter (`E_ARITY`). A
  selector name that is not in scope is an error (`E_NAME`) in both modes, in
  a parameter and in a key.
- Every key of scalar types that the domain stands for must satisfy the
  selectors and the requirements of the abstract method
  (`E_CONTRACT_DOMAIN`). The domain may name other selectors than the
  parameters do.
- A key that stands for no key of scalar types is an error
  (`E_CONTRACT_EMPTY`), even when another key of the domain is not empty.
  `domain;` declares no keys.
- At each key of an abstract method, the winner's result type must equal the
  abstract method's result type. `Pair<Nat>` and `Pair<Int>` are different
  result types (`E_CONTRACT_RESULT`).
- A key that several written keys or several abstract methods stand for counts
  once.
- An abstract method never wins and never runs.
- In manifest mode, only the module that defines the generic may declare its
  abstract methods (`E_OWNER`). An abstract method has no visibility, as
  [Visibility](language/items.md#visibility) says.

```vast
{{#include ../examples/abstract-contracts.vast}}
```

The executable prints `42`.

## Promotion

The arithmetic library `stdlib/src/arithmetic/generic.vast` defines the generic
`promote`, which turns two values of the types `Nat` and `Int` into a pair of
one common type, and uses it in `add` and `maximum`. These are library
methods, not rules of the language: the only conversion that they perform is
`int`. In manifest mode the module `std::arithmetic::generic` owns these
generics and their methods. The specification
[std::arithmetic::generic](spec/std-arithmetic-generic.md) states their
contract and its evidence.

| Key | `promote` result | `add` and `maximum` result |
| --- | --- | --- |
| `(Nat, Nat)` | `Pair<Nat>` | `Nat` |
| `(Nat, Int)` | `Pair<Int>` | `Int` |
| `(Int, Nat)` | `Pair<Int>` | `Int` |
| `(Int, Int)` | `Pair<Int>` | `Int` |

```vast
{{#include ../examples/promotion.vast}}
```

```sh
vastitas build examples/promotion.vast \
  --lib stdlib/src/arithmetic/int.vast \
  --lib stdlib/src/arithmetic/nat.vast \
  --lib stdlib/src/arithmetic/generic.vast -o target/promotion
```

The executable prints `42`.

## Moved sections

These anchors keep older links working.

- <a id="declarations"></a>Declarations: [Generic declarations](#generic-declarations) and [Method declarations](#method-declarations).
- <a id="selectors-and-capabilities"></a>Selectors and capabilities: [Method declarations](#method-declarations).
- <a id="selection-and-whole-program-checking"></a>Selection and whole-program checking: [Selection](#selection).
- <a id="standard-library-and-use"></a>Standard library and use: [Promotion](#promotion).
- <a id="scope"></a>Scope: the introduction of this chapter and [Checking pipeline, History](internals/checking-pipeline.md#history).
- <a id="finite-abstract-scalar-selectors-and-contracts"></a>Finite abstract scalar selectors and contracts: [Abstract types](#abstract-types).
- <a id="abstract-method-contracts"></a>Abstract method contracts: [Abstract methods](#abstract-methods).
- <a id="inherited-membership-authority"></a>Inherited membership authority: [Abstract types](#abstract-types).
- <a id="initial-natint-promotion"></a><a id="public-contract"></a>Promotion contract: [Promotion](#promotion).
- <a id="actual-body-proofs-and-fixture-agreement"></a><a id="regression-and-maintenance"></a>Proofs, fixtures and regressions: [Checking pipeline](internals/checking-pipeline.md#promotion-proofs-and-fixture).
