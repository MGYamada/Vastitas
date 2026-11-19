# Types

Every expression, parameter and binding has a **type**. The checker infers the
types of expressions, and parameters and results declare theirs. This chapter
describes the types of pure programs. [Geometric types](geometric-types.md)
describes objects, points, morphisms and existential packages, and
[Resource programs](../storage/resource-programs.md#storage-types) describes
the types of storage.

> **Syntax**
>
> ```text
> Type -> ScalarType | PairType | FunctionType | GeometricType | IndexedType
> ```

Rules:

- A type name that the syntax of this chapter or
  [Geometric types](geometric-types.md) does not admit is an error
  (`E_UNSUPPORTED`), unless it names an
  [indexed type](#indexed-types) in manifest mode.
- Parameters of a method have selectors, such as `Number` and `Any`, which
  [Method declarations](../stage1a.md#method-declarations) describes. A
  selector that is not a scalar type is not a type: as a type of a value it
  falls under the previous rule.

## Public type names

Public type names begin with an uppercase letter by convention, preferably
in `UpperCamelCase`. Mathematical acronym and model names, such as `ZZ`,
`QQ`, `RR`, `CC` and `GF`, retain their spelling. Modules, functions and
value bindings use `snake_case` by convention. These conventions do not
restrict the [identifier grammar](lexical-structure.md#identifiers).

The following names are the sole canonical vocabulary for bounded machine
integer types. Their implementation is separate from this naming contract;
they are not alternatives in `ScalarType` and do not make a bounded integer
type usable in a program.

| Signed name | Unsigned name | Width |
| --- | --- | --- |
| `I8` | `U8` | 8 bits |
| `I16` | `U16` | 16 bits |
| `I32` | `U32` | 32 bits |
| `I64` | `U64` | 64 bits |
| `I128` | `U128` | 128 bits |
| `ISize` | `USize` | The selected target's pointer width |

Rules of the naming contract:

- Public bindings for these machine types must use the names of the table.
  Lowercase Rust spellings, such as `i32`, `u32`, `isize` and `usize`, and
  alternatives such as `Int32` and `UInt32`, must not be public aliases for
  these types. Rust and Lean implementation identifiers keep their own
  spellings.
- A signed name denotes its signed two's-complement value range; an
  unsigned name denotes its nonnegative range. The target determines the
  width of `ISize` and `USize`; no host-width assumption determines it.
- These identities must remain distinct from the unbounded `Nat` and `Int`.
  The naming contract changes neither integer-literal typing nor the
  explicit conversion `int(n)`.
- A width, a signedness or a name grants no conversion, arithmetic operation
  or overflow policy. Such operations require their own admitted contract.
  `U8`, a finite field of 256 elements, a residue ring modulo 256 and a bit
  sequence of length 8 have distinct mathematical meanings.

[Scalar types](#scalar-types) lists the executable pure scalar types.
[Literal expressions](expressions.md#literal-expressions) specifies their defaults.

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

`Nat` and `Int` are distinct types. Only division of a `Nat` and an `Int`
converts its `Nat` operand implicitly. `int(n)` converts a `Nat` to an `Int`, and no function converts
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
  branches of an `if`. [Function types](#function-types) excludes pair types
  from function types, and [Function values](functions.md#function-values)
  from the signature of a function that takes or returns a function.
- A pair type must not stand in a key of the domain of a generic, a pair type
  must not be a method selector, and a pair must not be an argument of a
  generic. Each is an error (`E_TYPE`). A method may return a pair, as
  [promotion](../stage1a.md#promotion) does.

[`examples/book/values/pairs.vast`](https://github.com/MGYamada/Vastitas/blob/main/examples/book/values/pairs.vast)
passes pairs to functions and returns them:

```vast
{{#include ../../examples/book/values/pairs.vast}}
```

The executable writes these lines and exits with status 0:

```text
reverse(pair(big, zero)) = (0, 123456789012345678901234567890)
choose(false, pair(0, 0), pair(-7, 42)) = (-7, 42)
offset(40) = 42
```

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
| No parameters, returning a finite arrow | `Fn<(), Hom<C, X, Y>>` |

Rules:

- Its parameter and result types may be scalars, finite Hom fibers or function
  types. A Hom in an ordinary function is resolved in its declaration scope.
  Passing its value across a package boundary preserves the category identity
  and both endpoints. Another type, such as a pair or a geometric type, is an error
  (`E_TYPE`). The body of a lambda may still use pairs and geometric values.
- In some programs the compiler reports the error of the previous rule with
  another code. They are the programs that write an
  [indexed type](#indexed-types), and the programs whose package graph holds
  an `indexed` declaration, a resource function, a grant, a delegation, a
  transfer or a
  [geometry compatibility export](../packages.md#geometry-compatibility-exports).
  There the error has the code `E_PROTOCOL`, and the compiler reports it at
  the root manifest, as
  [Diagnostics](diagnostics.md#diagnostics-without-a-place-of-their-own)
  describes.
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
> IndexedType -> IDENTIFIER ( `::` PathSegment )* `<` IndexedArguments? `>`
>     | `Object` `<` Path `,` Path `>`
>     | `Hom` `<` Path `,` HomEndpoint `,` HomEndpoint `>`
> HomEndpoint -> Path | Path `::` `T` `<` HomEndpoint `>`
> IndexedArguments -> IndexedArgument ( `,` IndexedArgument )* `,`?
> IndexedArgument -> INTEGER_LITERAL | Path
> ```

In manifest mode, a program declares its own families of types with `indexed`
declarations. An **indexed type** applies such a family to its arguments, as in
`geo::Point<X, geo::Base>`. Its family and its arguments are
[paths](names-and-paths.md), which defines `Path` and `PathSegment`. `Object<D, K>` is the type of an object of the
[classification](../appendix/glossary.md#classification) or implementation
`D` with the coefficient marker `K`.
[Object types](../indexed-source.md#object-types) gives the rules of
`Object<D, K>`, and [Families](../indexed-source.md#families) the rules of the
indexed family applications. `Hom<C, Obj::x, Obj::y>` is the type of arrows
from `x` to `y` in a named finite category. A Monad parameter may supply the
category and an endpoint. For example, `Hom<M::category, X, M::T<Y>>`
denotes arrows from `X` to the image of `Y` under the selected
endofunctor. Repeated application such as `M::T<M::T<Y>>` is a bounded
static lookup. See
[Finite carriers and tables](../indexed-source.md#finite-carriers-and-tables).
[Smooth affine declarations](smooth-declarations.md) and
[Presented affine declarations](../affine-geometry.md) give further families.

Rules:

- Indexed types include the explicit forms `Object<…>` and `Hom<…>`,
  qualified paths and applications of a name followed by `<`. The latter
  form requires a name other than the type names of this chapter or of
  [Geometric types](geometric-types.md). `Point<>` and `Object<>` are errors
  (`E_PARSE`).
- Indexed types are valid only in manifest mode. In flat mode an indexed type
  is an error (`E_UNSUPPORTED`). A path whose first segment is a type name of
  this chapter or of [Geometric types](geometric-types.md), such as
  `Nat::F<a>` or `Point::F`, is an error (`E_PARSE`) in flat mode instead,
  because the type name begins its own type. In manifest mode such a path
  resolves as any other path.
- The path of the family must not begin with the keyword `generic`. A type
  such as `generic::Point<X, generic::Base>` is an error (`E_PARSE`). A later
  segment of that path may be `generic`, and so may a segment of an
  argument or of the two paths of `Object<…>`.
