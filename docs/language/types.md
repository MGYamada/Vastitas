# Types

Every expression, parameter and binding has a **type**. The checker infers the
types of expressions, and parameters and results declare theirs. This chapter
describes the types of pure programs. [Geometric types](geometric-types.md)
describes objects, points, morphisms and packages, and the storage chapters
describe the types of [resource programs](../storage/resource-programs.md).

> **Syntax**
>
> ```text
> Type -> ScalarType | PairType | FunctionType | GeometricType | IndexedType
> ```

Rules:

- A type name that this chapter or [Geometric types](geometric-types.md) does
  not define is an error (`E_UNSUPPORTED`), unless it names an
  [indexed type](#indexed-types) in manifest mode.
- Parameters of a method may also have selector types, such as `Number` and
  `Any`, which [Finite dispatch](../stage1a.md#selectors-and-capabilities)
  describes. Selector types are not types of values.

## Scalar types

> **Syntax**
>
> ```text
> ScalarType -> `Nat` | `Int` | `Bool` | `Unit`
> ```

| Type | Values |
| --- | --- |
| `Nat` | The natural numbers 0, 1, 2, …, without an upper bound |
| `Int` | The integers, without a lower or an upper bound |
| `Bool` | `true` and `false` |
| `Unit` | The single value `()` |

`Nat` and `Int` are distinct types, and no value converts implicitly from one
to the other. `int(n)` converts a `Nat` to an `Int`, and no function converts
back. [Operator expressions](expressions.md#operator-expressions) give the
operations on scalars. A pure program has no floating-point, string or
character types.

## Pair types

> **Syntax**
>
> ```text
> PairType -> `Pair` `<` ( `Nat` | `Int` ) `>`
> ```

A value of type `Pair<T>` holds two values of type `T`, in order.
[`pair`](expressions.md#built-in-functions) builds a pair, and `pair_first`
and `pair_second` return its components.

Rules:

- The element type must be `Nat` or `Int`. Another element type is an error
  (`E_TYPE`). The language has no pairs of other types, no nested pairs and no
  general tuples.
- A pair type may be the type of a parameter, a result, a binding or the
  branches of an `if`. A pair type in a [function type](#function-types) is an
  error (`E_TYPE`). A lambda whose signature has no pair may use pairs in its
  body.
- A pair is not a dispatch key, and `Pair` is not a method selector. A method
  may return a pair, as [promotion](../stage1a.md#promotion) does.

[`examples/pairs.vast`](https://github.com/MGYamada/Vastitas/blob/main/examples/pairs.vast)
passes pairs to functions and returns them:

```vast
{{#include ../../examples/pairs.vast}}
```

The executable prints `42`.

## Function types

> **Syntax**
>
> ```text
> FunctionType -> `Fn` `<` FunctionInputs `,` Type `>`
> FunctionInputs -> Type | `(` ( Type ( `,` Type )* `,`? )? `)`
> ```

A value of type `Fn<A, R>` is a function from `A` to `R`. Parentheses in the
first position list several parameter types. They describe a parameter list,
and they are not a tuple type.

| Function | Type |
| --- | --- |
| One `Int` parameter | `Fn<Int, Int>` |
| Two `Int` parameters | `Fn<(Int, Int), Int>` |
| No parameters | `Fn<(), Int>` |
| One `Unit` parameter | `Fn<Unit, Int>` |
| A function parameter and a function result | `Fn<Fn<Int, Int>, Fn<Int, Int>>` |

Rules:

- The parameter and result types of a function type must be scalar types or
  function types. Another type, such as a pair or a geometric type, is an error
  (`E_TYPE`).
- `fn(Int) -> Int` is not a type. Written as a type, it is an error
  (`E_PARSE`).
- A function value is not data: it has no equality, as
  [Operator expressions](expressions.md#operator-expressions) says.

[Function values](functions.md#function-values) and
[lambda expressions](expressions.md#lambda-expressions) are the values of
function types.

## Indexed types

> **Syntax**
>
> ```text
> IndexedType -> Path `<` IndexedArguments? `>` | `Object` `<` Path `,` Path `>`
> IndexedArguments -> IndexedArgument ( `,` IndexedArgument )* `,`?
> IndexedArgument -> INTEGER_LITERAL | Path
> ```

In manifest mode, a program declares its own families of types with `indexed`
declarations. An **indexed type** applies such a family to its arguments, as in
`geo::Point<X, geo::Base>`. Its family and its arguments are paths, as
[Modules and paths](../packages.md#modules-and-paths) describes. `Object<D, M>` is the type of an object of the
domain `D` with the coefficient marker `M`.
[Indexed source](../indexed-source.md#declarations-and-source-example) and
[Smooth affine declarations](smooth-declarations.md) give the families and
their rules.

Rules:

- A type is an indexed type in three cases. It is a path with `::`, or it is
  `Object<…>`, or it is a name followed by `<`. In the third case the name is
  not a type name of this chapter or of [Geometric types](geometric-types.md).
- Indexed types are valid only in manifest mode. In flat mode an indexed type
  is an error (`E_UNSUPPORTED`).
