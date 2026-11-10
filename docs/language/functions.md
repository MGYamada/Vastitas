# Functions

A **function** declares typed parameters, a result type and a body. The body is
a [block expression](expressions.md#block-expressions), and its value is the
result of the function.

> **Syntax**
>
> ```text
> Function -> `fn` IDENTIFIER `(` FunctionParameters? `)` `->` Type BlockExpression
> FunctionParameters -> FunctionParameter ( `,` FunctionParameter )* `,`?
> FunctionParameter -> IDENTIFIER `:` Type
> ```

A function has no effects. Its result depends only on its arguments. The
parameters are bindings of the body, and they follow the rules of
[Scopes of bindings](statements.md#scopes-of-bindings).

Rules:

- The type of the body must be the result type of the function. Another type
  is an error (`E_TYPE`).
- The type of a parameter may name an earlier parameter as an object, as in
  `fn keep(X: Scheme, p: Point<X, Base(QQ)>)`. The result type may name any
  parameter. A type that names a later parameter or an unknown object is an
  error (`E_NAME` in flat mode, `E_TYPE` in manifest mode). In an
  [indexed type](types.md#indexed-types) it is an error (`E_NAME`).
  [Geometric types](geometric-types.md#object-identity) describes these
  dependent types.
- A function body refers only to its parameters, the bindings of its body and
  items. There is no enclosing scope that a function could capture.

[`examples/arithmetic.vast`](https://github.com/MGYamada/Vastitas/blob/main/examples/arithmetic.vast)
calls a function that the file declares after the caller:

```vast
{{#include ../../examples/arithmetic.vast}}
```

The executable prints `1234567890123456789012345678900`.

## Calls

A call `f(a₁, …, aₙ)` of a function `f` evaluates the arguments and then the
body of `f` with each parameter bound to its argument.
[Call expressions](expressions.md#call-expressions) give the syntax.

Rules:

- The number of arguments must equal the number of parameters. Another number
  is an error (`E_ARITY`).
- Each argument must have the type of its parameter. Another type is an error
  (`E_TYPE`). Where a parameter type names an earlier parameter, the call
  substitutes the object of that argument, so its identity, not only its
  dimension, must match.
- A call may name a function that the program declares later.
- A function must not call itself, directly or through other functions. A
  cycle of calls is an error (`E_RECURSION`).
- A call of a name that no function, generic,
  [built-in function](expressions.md#built-in-functions), parameter or binding
  declares is an error (`E_NAME`). A call of a parameter or binding that does
  not have a [function type](types.md#function-types) is an error (`E_TYPE`).

In this program `even` and `odd` call each other:

```vast
{{#include ../../examples/reject/functions/mutual-recursion.vast}}
```

```text
{{#include ../../examples/reject/functions/mutual-recursion.stderr}}
```

## Function values

The name of a function whose parameter and result types are scalar or function
types is also a value of a [function type](types.md#function-types). A
[lambda expression](expressions.md#lambda-expressions) is an anonymous
function. [Function values](../stage1b.md) says what a program may do with a
function value.

Rules:

- The name of a function with a pair type, a geometric type or an indexed type
  among its parameter and result types is not a value. Using it as a value is
  an error (`E_TYPE`). A program may only call such a function by its name.
- A function that has a function type among its parameter and result types
  must have only scalar types and function types in its signature. Another
  type there is an error (`E_TYPE`). Its body may still use pairs and geometric
  values.
- A built-in function is not a value. Its name used as a value is an error
  (`E_NAME`).


```vast
{{#include ../../examples/book/functions/function-values.vast}}
```

The executable prints `42`.
