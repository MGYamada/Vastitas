# Abstract types

The selectors `Number` and `Any` are built in. An
[**abstract type**](../appendix/glossary.md#abstract-type) is a selector that
a program declares: a name for a set of scalar types. An
[**abstract method**](../appendix/glossary.md#abstract-method) is a method
without a body. It states at which keys callers may call a generic and what
the generic returns there.

## Declaring a selector

[`examples/abstract-selectors.vast`](https://github.com/MGYamada/Vastitas/blob/main/examples/abstract-selectors.vast)
declares four abstract types and dispatches on two of them:

```vast
{{#include ../../examples/abstract-selectors.vast}}
```

`abstract type Numeric <: Number;` declares the selector `Numeric` under the
parent `Number`. `NaturalNumeric` has the parent `Numeric`. Without `<:`, as
for `Variety`, the parent is `Any`. A declaration can also name several
parents, as in `abstract type Whole <: (Signed, Exact);`.

A `subtype` declaration places a scalar type in an abstract type. `Int`
belongs to `Numeric`. `Nat` belongs to `NaturalNumeric`, and with it to every
ancestor of `NaturalNumeric`, so `Nat` belongs to `Numeric` too.

Both methods of `classify` apply at the key `(Nat)`. A child is narrower than
its parent, so the method for `NaturalNumeric` is more specific, and
`classify(n)` is a call of it.

```sh
target/debug/vastitas check examples/abstract-selectors.vast
target/debug/vastitas build examples/abstract-selectors.vast -o target/abstract-selectors
./target/abstract-selectors
```

The program prints `42`.

`Variety` and `Manifold` have no members, and no method uses them. Such a
declaration is valid. An abstract type is a name and its place among the
selectors, and it states nothing about the mathematics that the name
suggests.

## A selector is not a type of values

An abstract type selects methods. It has no values, and it converts nothing:
in the body of a method for `Numeric`, an argument is still a `Nat` or an
`Int`. A function cannot take a parameter of an abstract type:

```vast
{{#include ../../examples/reject/abstract-types/value-type.vast}}
```

```text
{{#include ../../examples/reject/abstract-types/value-type.stderr}}
```

## Identity comes from the declaration

Two abstract types are different selectors, even when they hold the same
scalar types. Only a parent declared with `<:` relates one abstract type to
another:

```vast
{{#include ../../examples/reject/abstract-types/same-members.vast}}
```

```text
{{#include ../../examples/reject/abstract-types/same-members.stderr}}
```

`Left` and `Right` both hold `Int` and nothing else. Neither is the parent of
the other, so neither method is more specific, and the key `(Int)` has two
best methods. The compiler never compares the members of two abstract types
to order them.

A declaration also cannot change how the built-in selectors relate. With
`abstract type Numeric <: Number;`, the declaration `subtype Bool <: Numeric;`
is an error, because it would place `Bool` under `Number`.
[Abstract types](../stage1a.md#abstract-types) gives the rules of both
declarations.

## Abstract methods

A generic can promise a result type for every scalar type of a selector.
[`examples/abstract-contracts.vast`](https://github.com/MGYamada/Vastitas/blob/main/examples/abstract-contracts.vast)
makes such a promise for `Numeric`:

```vast
{{#include ../../examples/abstract-contracts.vast}}
```

`domain;` gives `widen` an empty domain of its own. The `abstract method`
declaration has no body: its braces hold a domain. A key of that domain may
name a selector, and it then stands for every key of scalar types that the
selector accepts. `(Numeric)` stands for `(Nat)` and `(Int)`.

The abstract method does two things. It adds its keys to the
[**callable domain**](../appendix/glossary.md#callable-domain) of the
generic, the keys at which callers may call it. It also fixes the result type
at those keys: the winner at `(Nat)` and the winner at `(Int)` must both
return `Int`. The abstract method itself never wins and never runs. The two
methods with bodies do the work, and the program prints `42`.

A winner with another result type breaks the promise:

```vast
{{#include ../../examples/reject/abstract-types/contract-result.vast}}
```

```text
{{#include ../../examples/reject/abstract-types/contract-result.stderr}}
```

The compiler reports the error at the abstract method. A key of an abstract
method without any applicable method is an error too: the callable domain
needs a winner at each of its keys.
[Abstract methods](../stage1a.md#abstract-methods) gives the rules.

> **What is checked.** The compiler checks the abstract types of a program
> together: the parents form no cycle, and the built-in selectors keep their
> relations. For every key of an abstract method, it checks that the generic
> has a winner and that the winner returns the promised type. The proofs
> cover two things. Selection follows the declared parents and does not
> depend on the order of the declarations; see
> [Finite abstract selector acceptance](../verification.md#finite-abstract-selector-acceptance).
> In an accepted program, each key of an abstract method has a winner with
> the promised result type; see
> [Abstract method contract acceptance](../verification.md#abstract-method-contract-acceptance).
> Tests cover the diagnostics and native execution. No proof says anything
> about the mathematics behind a name such as `Variety`.

## See also

- [Abstract types](../stage1a.md#abstract-types): `abstract type` and
  `subtype` declarations, parents and membership.
- [Abstract methods](../stage1a.md#abstract-methods): the keys of an abstract
  method and the result type of the winner.
- [Selection](../stage1a.md#selection): how the compiler compares methods
  whose selectors are abstract types.
- [Types](../language/types.md): the types of values, which exclude
  selectors.
- [Appendix D](../appendix/limits.md#checker-limits): the limit on the number
  of abstract types.
