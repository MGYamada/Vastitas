# Expressions

An **expression** computes a value. Every construct inside a function body that
is not a [statement](statements.md) is an expression, including blocks,
conditionals and calls. Evaluating an expression has no effects, and integers
have arbitrary precision, so arithmetic never overflows.

> **Syntax**
>
> ```text
> Expression -> LiteralExpression | UnitExpression | PathExpression
>     | GroupedExpression | BlockExpression | IfExpression | CallExpression
>     | OperatorExpression | LambdaExpression | PackExpression
> ```

## Literal expressions

> **Syntax**
>
> ```text
> LiteralExpression -> INTEGER_LITERAL | `true` | `false`
> UnitExpression -> `(` `)`
> ```

`true` and `false` have type `Bool`, and `()` is the value of type `Unit`.
An [integer literal](lexical-structure.md#integer-literals) has type `Nat` or
`Int`, as the rules below decide. The **expected type** of an expression is the
type that its position requires:

- for the expression of a `let` statement, its annotation;
- for an argument of a call, the type of its parameter, including a call of
  a function value;
- for the body of a function or a lambda, its result type;
- for the result of a block and for each branch of an `if`, the expected type
  of the block or of the `if`;
- for the left operand of `+`, of binary `-` and of `*`, the expected type
  of the operation, where it has one;
- for the dimension argument of `Affine`, `Nat`.

The operands of a comparison have no expected type from the comparison.

Rules:

- An integer literal has type `Nat` where the expected type is `Nat`, and type
  `Int` otherwise.
- An expression built only from integer literals, unary minus, `+`, `-` and
  `*` takes its type from the expected type in the same way.
- The right operand of a binary operation takes the type of the left operand
  as its expected type, and the `else` branch of an `if` takes the type of the
  first branch.
- Where the left operand, or the result of the first branch, is an integer
  expression of the previous two rules and the other side is not, the other
  side supplies the expected type instead: `1 + n` has type `Nat` for
  `n: Nat`. A literal nested in a block or in an `if` on the left takes no type
  from the right. For `n: Nat`, `let c = { 1 } + n;` is an error (`E_TYPE`):
  the operation has no expected type, so the block has type `Int`. With an
  expected type the block takes it, and `let c: Nat = { 1 } + n;` is valid.
- These rules assign types. They do not evaluate the expression. A binding
  keeps its type, and unary minus requires `Int`, so
  `let n: Nat = -1;` is an error (`E_TYPE`).
- The arguments of [`pair`](#built-in-functions) take no expected type from
  the call.

```vast
let a: Nat = 2 * 3 + 1;  // Nat
let b = 2 * 3 + 1;       // Int
let c = a + 5;           // Nat: the literal takes the type of a
```

## Path expressions

> **Syntax**
>
> ```text
> PathExpression -> IDENTIFIER ( `::` PathSegment )*
>     | `generic` ( `::` PathSegment )+
> ```

A path expression names a parameter, a binding or a function. It is a
[path](names-and-paths.md) that is not the keyword `generic` alone, and
[Names and paths](names-and-paths.md) defines `PathSegment`. A path of one
segment is a bare name, and a path with `::` names a declaration of another
module. The
value of a function name is the function, as
[Function values](functions.md#function-values) describes. A coefficient marker
is not a value, as [Settings and markers](geometric-types.md#settings-and-markers)
says, and a lambda refers only to its own bindings, as
[Lambdas](../stage1b.md#lambdas-and-their-names) says.

Rules:

- A name that no parameter, binding or function in scope declares is an error
  (`E_NAME`).
- A path with `::` is valid only in manifest mode. In flat mode it is an error
  (`E_PARSE`).
- `generic` alone is not a path expression. Where an expression begins, it is
  an error (`E_PARSE`) in both modes, as
  [Keywords](lexical-structure.md#keywords) says of a strict keyword.
- The name of a generic is not a value. A generic as a value is an error
  (`E_TYPE`). A function or lambda that calls the generic is a value.
- The name of an abstract type or of a module is not a value. An abstract type
  as a value is an error (`E_NAME` in flat mode, `E_TYPE` in manifest mode),
  and a module as a value is an error (`E_NAME`).

## Grouped expressions

> **Syntax**
>
> ```text
> GroupedExpression -> `(` Expression `)`
> ```

A grouped expression has the value and the type of the expression inside it.
Parentheses change only how operators group.

## Block expressions

> **Syntax**
>
> ```text
> BlockExpression -> `{` Statement* Expression? `}`
> ```

A block evaluates its statements in order and then its final expression, the
**result** of the block. The value of the block is the value of its result. A
block without a result has the value `()`, of type `Unit`. The language has
no `return`, as [Keywords](lexical-structure.md#keywords) says. A block is a
scope for the names that its statements bind, as
[Scopes of bindings](statements.md#scopes-of-bindings) describes.

Rules:

- A `;` after the result of a block is an error (`E_UNSUPPORTED`). The
  language has no expression statements.

```vast
let total: Int = {
    let a: Int = 20;
    a + 22
};
```

## `if` expressions

> **Syntax**
>
> ```text
> IfExpression ->
>     `if` Expression BlockExpression `else` ( BlockExpression | IfExpression )
> ```

`if c { a } else { b }` evaluates `c`, and then the branch that `c` selects:
`a` when `c` is `true` and `b` when it is `false`. `else if` is short for an
`else` block whose result is another `if` expression.

Rules:

- The condition must have type `Bool`. Another type is an error (`E_TYPE`).
- `else` is required. An `if` without `else` is an error (`E_PARSE`).
- Both branches must have the same type, which is the type of the expression.
  Branches of different types are an error (`E_TYPE`).
- A chain of `else if` branches must not have more conditions than the limit
  that [Appendix D](../appendix/limits.md#source-text) gives. A longer chain
  is an error (`E_LIMIT`).

```vast
let sign = if x < 0 { -1 } else if x == 0 { 0 } else { 1 };
```

## Call expressions

> **Syntax**
>
> ```text
> CallExpression -> Expression `(` CallArguments? `)`
> CallArguments -> Expression ( `,` Expression )* `,`?
> ```

A call whose callee is the name of a function, a generic or a
[built-in function](#built-in-functions) calls it. [Calls](functions.md#calls)
gives the rules for functions, and
[Selection](../stage1a.md#selection) the rules
for generics. Any other callee is an expression whose value is a function, and
the call applies that function to the arguments.

Rules:

- The callee of an application must have a function type. Another type is an
  error (`E_TYPE`).
- The number of arguments must equal the number of parameters of the function
  type. Another number is an error (`E_ARITY`).
- A call binds more tightly than any operator. `-f(x)` negates the result of
  `f(x)`, and `factory()(42)` applies the function that `factory()` returns.
- Parentheses around the name of a callee do not change the call: `(f)(x)` is
  the call `f(x)`.

## Operator expressions

> **Syntax**
>
> ```text
> OperatorExpression -> UnaryOperator Expression
>     | Expression BinaryOperator Expression
> UnaryOperator -> `-` | `!`
> BinaryOperator -> `*` | `+` | `-` | `==` | `!=` | `<` | `<=` | `>` | `>=`
>     | `&&` | `||`
> ```

The operators group by precedence, from the operators that bind most tightly
to those that bind least tightly:

| Operators | Grouping |
| --- | --- |
| Calls `f(…)` | Left to right |
| Unary `-` `!` | Prefix |
| `*` | Left to right |
| `+` `-` | Left to right |
| `==` `!=` `<` `<=` `>` `>=` | Parentheses required |
| `&&` | Left to right |
| `\|\|` | Left to right |

Each operator accepts the operand types in this table:

| Operator | Operands | Result |
| --- | --- | --- |
| Unary `-` | `Int` | `Int` |
| `!` | `Bool` | `Bool` |
| `+` `*` | Two `Nat`, or two `Int` | The operand type |
| Binary `-` | Two `Nat` | `Nat`, and 0 where the difference is negative |
| Binary `-` | Two `Int` | `Int` |
| `==` `!=` | Two `Nat`, two `Int`, two `Bool` or two `Unit` | `Bool` |
| `<` `<=` `>` `>=` | Two `Nat`, or two `Int` | `Bool` |
| `&&` `\|\|` | Two `Bool` | `Bool` |

`!a` is `true` when `a` is `false`. `a && b` is `true` when both operands are
`true`, and `a || b` is `true` when at least one operand is `true`.

Rules:

- The two operands of a binary operator must have the same type. Operands of
  different types, such as a `Nat` and an `Int`, are an error (`E_TYPE`). The
  language has no implicit conversions; [`int`](#built-in-functions) converts
  explicitly.
- The operands of `!`, `&&` and `||` must have type `Bool`, and the operand of
  unary `-` must have type `Int`. Another type is an error (`E_TYPE`).
- Two operands of one type that the table does not list for an arithmetic
  operator, an ordering or an equality are an error (`E_OPERATOR`). Examples
  are arithmetic or ordering on `Bool` or `Unit`, and equality of pairs or of
  geometric values.
- A function value as an operand of any operator is an error (`E_TYPE`).
- A comparison must not be an operand of another comparison without
  parentheses. `a < b < c` is an error (`E_PARSE`). `(a < b) == c` and
  `a < b && b < c` are valid.

This program shows a saturating subtraction, an explicit conversion and the
grouping of operators:

```vast
{{#include ../../examples/book/expressions/operators.vast}}
```

The executable prints `42`. A comparison chain is an error:

```vast
{{#include ../../examples/reject/expressions/chained-comparison.vast}}
```

```text
{{#include ../../examples/reject/expressions/chained-comparison.stderr}}
```

`Nat` and `Int` operands do not mix:

```vast
{{#include ../../examples/reject/expressions/mixed-integers.vast}}
```

```text
{{#include ../../examples/reject/expressions/mixed-integers.stderr}}
```

## Built-in functions

These functions are always in scope, and their names are reserved:

| Call | Arguments | Result |
| --- | --- | --- |
| `int(n)` | `n: Nat` | `n` as an `Int` |
| `pair(x, y)` | Two `Nat`, or two `Int` | The [pair](types.md#pair-types) of `x` and `y` |
| `pair_first(p)` | `p: Pair<T>` | The first component, of type `T` |
| `pair_second(p)` | `p: Pair<T>` | The second component, of type `T` |

[Geometric types](geometric-types.md#operations) gives the built-in functions of
geometry.

Rules:

- The argument of `int` must have type `Nat`. Another type is an error
  (`E_TYPE`). No function converts an `Int` to a `Nat`. A difference of natural
  numbers below zero is `int(a) - int(b)`.
- The two arguments of `pair` must have the same type, `Nat` or `Int`, which
  each argument determines alone. Other arguments are an error (`E_TYPE`).
  `pair(0, 1)` is a `Pair<Int>`, so `let p: Pair<Nat> = pair(0, 1);` is an
  error (`E_TYPE`).
- The argument of `pair_first` and of `pair_second` must be a pair. Another
  argument is an error (`E_TYPE`).
- One of these four functions called with the wrong number of arguments is an
  error (`E_ARITY`).

The [arithmetic standard library](https://github.com/MGYamada/Vastitas/blob/main/stdlib/README.md)
defines `nat_to_int` as a function that calls `int`.

## Lambda expressions

> **Syntax**
>
> ```text
> LambdaExpression -> `fn` `(` FunctionParameters? `)` `->` Type BlockExpression
> ```

A lambda expression is an anonymous function. Its value has the
[function type](types.md#function-types) of its parameters and result, as in
`fn(x: Int) -> Int { x + 1 }`, of type `Fn<Int, Int>`. Its parameter and
result types are those that [Function types](types.md#function-types) allows.
A lambda refers only to its own parameters and bindings and to items.
[Function values](../stage1b.md#lambdas-and-their-names) gives the rules on
captures and shadowing, and the rules for calls of function values.

## Pack expressions

> **Syntax**
>
> ```text
> PackExpression ->
>     `pack` `{` `scheme` `:` Expression `,` `point` `:` Expression `,`? `}`
>     | `pack` Type `{` `witness` `:` Expression `,`
>       `fields` `:` `[` PackFields? `]` `,`? `}`
> PackFields -> Expression ( `,` Expression )* `,`?
> ```

`pack { scheme: X, point: p }` builds an
[existential package](geometric-types.md#existential-packages) from the object
`X` and the point `p` on it. The second form builds an existential package of
an indexed profile in manifest mode, with its witness object and its fields in
order, as [Packing](../indexed-source.md#packing) describes.

Rules:

- The fields must appear as `scheme`, then `point`. Another order or another
  field name is an error (`E_PARSE`).
- The form with a type must not occur in flat mode, where it is an error
  (`E_PARSE`).

`make_origin` in this program packs an object with its origin, and `main`
packs the object that it opened with another point of it:

```vast
{{#include ../../examples/pointed.vast}}
```

The executable prints `42`.
[Packing](../indexed-source.md#packing) shows the form with a type.
