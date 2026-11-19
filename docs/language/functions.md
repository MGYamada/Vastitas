# Functions

A **function** belongs to its defining module. Its simplest form is a
singleton declaring typed parameters, a result type and one body. The body
is a [block expression](expressions.md#block-expressions) whose value is the
result of the function. Multiple scalar methods with the same name form a
family with finite [selection](../stage1a.md#selection).

> **Syntax**
>
> ```text
> Function -> `fn` IDENTIFIER FiniteBinders? `(` FunctionParameters? `)` `->` Type BlockExpression
> FiniteBinders -> `<` FiniteBinder ( `,` FiniteBinder )* `,`? `>`
> FiniteBinder -> IDENTIFIER `:` Path | IDENTIFIER `:` `Obj` `<` IDENTIFIER ( `::` `category` )? `>`
> FunctionParameters -> FunctionParameter ( `,` FunctionParameter )* `,`?
> FunctionParameter -> IDENTIFIER `:` Type
> ```

A function has no effects. Its result depends only on its arguments. The
parameters are bindings of the body, and they follow the rules of
[Scopes of bindings](statements.md#scopes-of-bindings).

A finite function declares a category parameter such as `C: Category`
and object parameters such as `X: Obj<C>`. The path after `C:` names a
visible finite category schema. Each object parameter belongs to an earlier
category parameter. These indices occur in parameter and result types such
as `Hom<C, X, Y>`. A Monad parameter `M: Monad` selects its underlying
category as `M::category`. The binder `X: Obj<M::category>` ranges over
the objects of that category. The endpoint `M::T<X>` applies the selected
endofunctor to the object at specialization. If two Monads have the same
underlying category, an arrow alone cannot select between them. An explicit
call such as `monad::kleisli::unit::<M, Obj::lo>()` supplies both indices. See [Finite carriers and tables](../indexed-source.md#finite-carriers-and-tables).

A finite family may declare a forwarding method alongside its method on
data. For example, the second parameter of `monad::kleisli::bind` can be a
nullary function returning the required Hom. The forwarding method has the
same owner, visibility, model binders and result as the data method. Its
body calls that method with the same indices and parameters in order, and
invokes each declared producer once. Each list of callable positions can
select one forwarding method. At the call site, argument expressions are
evaluated from left to right before any producer is invoked. [Kleisli operations](https://github.com/MGYamada/Vastitas/blob/main/monad/docs/kleisli.md)

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

[`examples/book/values/arithmetic.vast`](https://github.com/MGYamada/Vastitas/blob/main/examples/book/values/arithmetic.vast)
calls a function that the file declares after the caller:

```vast
{{#include ../../examples/book/values/arithmetic.vast}}
```

The executable writes `value * 10 = 1234567890123456789012345678900` and
exits with status 0.

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
- A call of a name that no function family,
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

The call of `missing_function` has no declaration to resolve to.

```vast
{{#include ../../examples/reject/names/unresolved-function.vast}}
```

```text
{{#include ../../examples/reject/names/unresolved-function.stderr}}
```

## Function values

The name of an ordinary function whose parameter and result types are scalars,
finite Hom fibers or function types is also a value of a [function type](types.md#function-types). A
[lambda expression](expressions.md#lambda-expressions) is an anonymous
function. [Function values](../stage1b.md) says what a program may do with a
function value.

Rules:

- The name of a function with a pair type, a geometric type or an indexed type other than finite Hom
  among its parameter and result types is not a value. Using it as a value is
  an error (`E_TYPE`). A program may only call such a function by its name.
- A function that has a function type among its parameter and result types
  admits scalar types, finite Hom fibers and function types in its signature. Another
  type there is an error (`E_TYPE`). Its body may still use pairs and geometric
  values.
- The five [exact arithmetic families](expressions.md#operator-expressions)
  are function values. In `let minus = std::operator::sub;`, `minus` can
  select either integer method at a call. Passing it to a parameter of
  type `Fn<(Nat, Nat), Nat>` selects the method on two natural numbers. The
  parameter types choose the method; an incorrect result type is an error
  (`E_TYPE`).
- A built-in function such as `int` or `pair` is not a value. Its name used
  as a value is an error (`E_NAME`).


```vast
{{#include ../../examples/book/functions/function-values.vast}}
```

The executable writes `invoke(alias, 41) = 42` and exits with status 0.
