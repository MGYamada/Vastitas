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
parameter. The **domain** lists the keys at which callers may call the generic:
`domain;` is the empty domain, and `domain ();` the single key of a generic
without parameters. The abstract methods of the generic add keys to its
domain, as [Abstract methods](#abstract-methods) describes.

Rules:

- Every key of the domain must have one type per parameter. Another key is an
  error (`E_DISPATCH_DOMAIN`).
- A key must list scalar types. An abstract type in a key is an error
  (`E_TYPE`).
- A key must not occur twice in a domain (`E_DUPLICATE`).
- A generic has at most six parameters, because the compiler enumerates every
  key of its parameters, at most 4096. A seventh parameter is an error
  (`E_LIMIT`).
- The name of a generic is not a value (`E_TYPE`). A function that calls the
  generic is a value.

## Method declarations

> **Syntax**
>
> ```text
> MethodDeclaration -> `method` Path MethodParameters MethodSignature BlockExpression
> MethodParameters -> `(` ( MethodParameter ( `,` MethodParameter )* `,`? )? `)`
> MethodParameter -> IDENTIFIER `:` Path
> MethodSignature -> Requirements? `->` MethodResult | `->` MethodResult Requirements
> Requirements -> `requires` `(` ( IDENTIFIER ( `,` IDENTIFIER )* `,`? )? `)`
> MethodResult -> ScalarType | PairType
> ```

A method of the generic `f` declares a **selector** for each parameter and a
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

- A method must name a generic in scope. Another name is an error (`E_NAME`).
  In manifest mode the method must be in the module that defines the generic,
  as [Owners](language/edit-authority.md#owners) says.
- A method has one selector per parameter of its generic. Another number is an
  error (`E_ARITY`).
- A capability must be `HasEq` or `HasOrder` (`E_CAPABILITY`). A program
  cannot declare capabilities.
- A method has at most one `requires` clause (`E_PARSE`).
- The result type of a method must be a scalar type, `Pair<Nat>` or
  `Pair<Int>` (`E_TYPE`). Methods of one generic may have different result
  types.
- Two methods of one generic must not have the same selectors and the same
  requirements after `HasOrder` implies `HasEq` (`E_DUPLICATE`).
- The requirements of a method must hold for some key that its selectors
  accept. A method that applies to no key is an error (`E_CAPABILITY`).
- A selector is not a type of values. `Number`, `Any` and abstract types appear
  only as selectors.

## Selection

A method **applies** at a key when each type of the key belongs to its
selector and every type of the key has the required capabilities. Method `a`
is **more specific** than method `b` when each selector of `a` is no broader
than the matching selector of `b`, the requirements of `a` are no weaker than
those of `b`, and one of these comparisons is strict. At a key, the **winner**
is the one applicable method that no other applicable method is more specific
than. The order of declarations never decides, and neither does the expected
type of the call, the identity of a geometric object or any state at run
time.

Rules:

- At every key of all scalar types, not only at the keys of the domain, the
  applicable methods must not have two incomparable best methods. Such a key
  is an error (`E_DISPATCH_AMBIGUOUS`).
- Every key of the domain must have a winner. A key without one is an error
  (`E_DISPATCH_COVERAGE`).
- The compiler checks the body of every method at every key at which it
  applies, also where it never wins and outside the domain.
- The compiler infers the types of the arguments of a call before it selects a
  method. An integer literal argument therefore has type `Int`, and the
  expected type of a call never selects a method.
- A call of a generic selects its winner at compile time, and the call has the
  winner's result type. Calls through generics follow the rule against
  recursion of [Calls](language/functions.md#calls) after selection
  (`E_RECURSION`).

Capabilities hold for single types, not for relations between arguments. A
method with selectors `(Number, Number)` that requires `HasOrder` also applies
at `(Nat, Int)`, where `left < right` is an error. Write separate methods for
`(Nat, Nat)` and `(Int, Int)` instead.

Neither method below is more specific than the other: the first has the
narrower selector, the second the stronger requirement. They are ambiguous at
every key of `Number`, also outside the domain:

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

- A parent must be `Any`, `Number` or an abstract type in scope. Another name is
  an error (`E_NAME`).
- The abstract types must not form a cycle, and no abstract type may be its own
  parent (`E_HIERARCHY`).
- A `subtype` must name one of the four scalar types and an abstract type of
  the program. It must not change the relations between the built-in types,
  such as placing `Bool` under `Number` (`E_HIERARCHY`), and it must not edit
  a built-in type itself (`E_OWNER`).
- A name, a parent of one abstract type or a membership must not be declared
  twice (`E_DUPLICATE`).
- A program has at most 64 nominal types, counting `Nat`, `Int`, `Bool`, `Unit`,
  `Number` and `Any` (`E_LIMIT`).
- In manifest mode, only the module that defines an abstract type may declare
  `subtype` memberships of it (`E_OWNER`). Every membership that a type
  inherits must come from such a declaration, so foreign inheritance cannot
  add a scalar type to an abstract type.
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
>     `abstract` `method` Path MethodParameters MethodSignature `{` `domain` ContractDomain `}`
> ContractDomain -> `;` | ContractKey ( `,` ContractKey )* `,`? `;`
> ContractKey -> `(` ( Path ( `,` Path )* `,`? )? `)`
> ```

An **abstract method** has no body. It adds keys to the domain of its generic
and fixes the result type that the winner at those keys must have. The keys of
its domain may name selectors, and each one stands for every key of scalar
types that it accepts: `(Numeric, Bool)` stands for `(Nat, Bool)` and
`(Int, Bool)` when `Numeric` holds `Nat` and `Int`. The **callable domain** of
a generic is the union of its domain and the keys of its abstract methods.

Rules:

- Every key of an abstract method must satisfy its selectors and its
  requirements (`E_CONTRACT_DOMAIN`).
- A key that stands for no key of scalar types is an error
  (`E_CONTRACT_EMPTY`), also when another key of the clause is not empty.
  `domain;` is an empty contract.
- At each key of an abstract method, the winner's result type must equal the
  abstract method's result type, also `Pair<Nat>` versus `Pair<Int>`
  (`E_CONTRACT_RESULT`). Every key of the callable domain needs a winner
  (`E_DISPATCH_COVERAGE`).
- Keys that several clauses or several abstract methods share count once.
- An abstract method never wins and never runs.
- In manifest mode, only the module that defines the generic may declare its
  abstract methods (`E_OWNER`). An abstract method has no visibility, and `pub`
  before it is an error (`E_PARSE`).

```vast
{{#include ../examples/abstract-contracts.vast}}
```

The executable prints `42`.

## Promotion

The arithmetic library `stdlib/src/arithmetic/generic.vast` defines the generic
`promote`, which turns two integers into a pair of one common type, and uses it
in `add` and `maximum`. These are library methods, not rules of the language:
the only conversion that they perform is `int`. The specification
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
- <a id="finite-abstract-scalar-selectors-and-contracts"></a>Finite abstract scalar selectors and contracts: [Abstract types](#abstract-types).
- <a id="abstract-method-contracts"></a>Abstract method contracts: [Abstract methods](#abstract-methods).
- <a id="inherited-membership-authority"></a>Inherited membership authority: [Abstract types](#abstract-types).
- <a id="initial-natint-promotion"></a><a id="public-contract"></a>Promotion contract: [Promotion](#promotion).
- <a id="actual-body-proofs-and-fixture-agreement"></a><a id="regression-and-maintenance"></a>Proofs, fixtures and regressions: [Checking pipeline](internals/checking-pipeline.md#promotion-proofs-and-fixture).
