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
- for an argument of a call, the type of its parameter, also in a call of a
  function value;
- for the body of a function or a lambda, its result type;
- for the result of a block and for each branch of an `if`, the expected type
  of the block or of the `if`;
- for the dimension argument of `Affine`, `Nat`.

Rules:

- An integer literal has type `Nat` where the expected type is `Nat`, and type
  `Int` otherwise.
- An expression built only from integer literals, unary minus, `+`, `-` and
  `*` takes its type from the expected type in the same way.
- In a binary operation, an operand of type `Nat` makes `Nat` the expected type
  of a literal in the other operand. In an `if` expression, a branch of type
  `Nat` makes `Nat` the expected type of a literal in the other branch. Either
  side may supply the type.
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
> PathExpression -> IDENTIFIER | Path
> ```

A path expression names a parameter, a binding or a function. A path with `::`
names a declaration of another module, as
[Modules and paths](names-and-paths.md) describes. The value of a
function name is the function, as [Function values](functions.md#function-values)
describes. A coefficient marker is a value only where
[Settings and markers](geometric-types.md#settings-and-markers) allows it, and a
lambda refers only to its own bindings, as
[Lambdas](../stage1b.md#lambdas-and-their-names) says.

Rules:

- A name that no parameter, binding or function in scope declares is an error
  (`E_NAME`).
- A path with `::` is valid only in manifest mode. In flat mode it is an error
  (`E_PARSE`).
- The name of a generic is not a value. A generic as a value is an error
  (`E_TYPE`). A function or lambda that calls the generic is a value.

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
- A chain of `else if` branches has a length limit, which
  [Appendix D](../appendix/limits.md#parser-and-checker-budgets) gives.

```vast
fn sign(x: Int) -> Int {
    if x < 0 { -1 } else if x == 0 { 0 } else { 1 }
}
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
[Finite dispatch](../stage1a.md#selection) the rules
for generics. Any other callee is an expression whose value is a function, and
the call applies that function to the arguments.

Rules:

- The callee of an application must have a function type. Another type is an
  error (`E_TYPE`).
- The number of arguments must equal the number of parameters of the function
  type. Another number is an error (`E_ARITY`).
- A call binds more tightly than any operator. `-f(x)` negates the result of
  `f(x)`, and `factory()(42)` applies the function that `factory()` returns.

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

Rules:

- The two operands of a binary operator must have the same type. Operands of
  different types, such as a `Nat` and an `Int`, are an error (`E_TYPE`). The
  language has no implicit conversions; [`int`](#built-in-functions) converts
  explicitly.
- `!`, `&&` and `||` require `Bool` operands, and unary `-` an `Int` operand.
  Another type is an error (`E_TYPE`).
- Two operands of one type that the table does not list for an arithmetic
  operator, an ordering or an equality are an error (`E_OPERATOR`). Examples
  are arithmetic or ordering on `Bool` or `Unit`, and equality of pairs or of
  geometric values.
- Equality of function values is an error (`E_TYPE`).
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

- The argument of `int` must have type `Nat` (`E_TYPE`). No function converts
  an `Int` to a `Nat`. A difference of natural numbers below zero is
  `int(a) - int(b)`.
- The two arguments of `pair` must have the same type, `Nat` or `Int`, which
  each argument determines alone (`E_TYPE`). `pair(0, 1)` is a `Pair<Int>`, so
  `let p: Pair<Nat> = pair(0, 1);` is an error (`E_TYPE`).
- A built-in function called with the wrong number of arguments is an error
  (`E_ARITY`).

The [arithmetic standard library](https://github.com/MGYamada/Vastitas/blob/main/stdlib/README.md)
defines `nat_to_int` as a function that calls `int`.

## Lambda expressions

> **Syntax**
>
> ```text
> LambdaExpression -> `fn` FunctionParameters `->` Type BlockExpression
> ```

A lambda expression is an anonymous function. Its value has the
[function type](types.md#function-types) of its parameters and result, as in
`fn(x: Int) -> Int { x + 1 }`, of type `Fn<Int, Int>`. A lambda refers only to
its own parameters and bindings and to items.
[Lambdas and static higher-order functions](../stage1b.md) gives the rules on
captures and shadowing, and the rules for calls of function values.

Rules:

- The parameter and result types of a lambda must be scalar types or function
  types. Another type is an error (`E_TYPE`).

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
order, as
[Indexed source](../indexed-source.md#declarations-and-source-example)
describes.

Rules:

- The fields must appear as `scheme`, then `point` (`E_PARSE`).
- The form with a type must not occur in flat mode, where it is an error
  (`E_PARSE`).
