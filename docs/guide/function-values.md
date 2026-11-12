# Independent functions and specialization

A function is also a value. A program binds it to a name, passes it to
another function, returns it and calls it. A
[*function value*](../appendix/glossary.md#function-value) is the name of a
function, or a [*lambda*](../appendix/glossary.md#lambda): a function
written as an expression.

Function values are independent of the code around them: a lambda uses
nothing from the function that contains it. The compiler therefore knows
which function each call runs before it generates code. An executable holds
no closures and no function pointers.

## Function types and lambdas

[`examples/functions.vast`](https://github.com/MGYamada/Vastitas/blob/main/examples/functions.vast)
passes a function to a function:

```vast
{{#include ../../examples/functions.vast}}
```

`Fn<Int, Int>` is the type of a function from an `Int` to an `Int`. `invoke`
takes such a function as its parameter `f` and calls it. `keep` returns the
function that it receives. In `main`, `fn(x: Int) -> Int { x + 1 }` is a
lambda. Like a named function, it declares the type of each parameter and its
result type.

```sh
target/debug/vastitas check examples/functions.vast
target/debug/vastitas build examples/functions.vast -o target/functions
./target/functions
```

The program prints `42`.

A function type lists its parameter types in parentheses when the function
has several parameters or none.
[`examples/book/function-values/signatures.vast`](https://github.com/MGYamada/Vastitas/blob/main/examples/book/function-values/signatures.vast)
returns functions of both kinds:

```vast
{{#include ../../examples/book/function-values/signatures.vast}}
```

`Fn<(), Int>` is the type of a function without parameters, and
`Fn<(Int, Int), Int>` of a function with two. The parentheses list
parameters. They are not a tuple type, and `Fn<Unit, Int>` is a different
type: a function with one parameter of type `Unit`. Calls chain: `constant()`
returns a function, and `constant()()` calls that function. The program
prints `42`.

The parameter and result types of a function type are scalar types and
function types. A function with another type in its signature, such as a
pair, is not a value, and a program calls it only by its name.
[Function types](../language/types.md#function-types) and
[Function values](../language/functions.md#function-values) give the rules.

## No captures

A lambda refers to its own parameters and bindings, to the functions and
generics of the program, and to the built-in functions. It does not refer to
a binding of the function around it:

```vast
{{#include ../../examples/reject/function-values/capture.vast}}
```

```text
{{#include ../../examples/reject/function-values/capture.stderr}}
```

`offset` is a binding of `main`, outside the lambda. The lambda receives the
value as a parameter instead, in
[`examples/book/function-values/explicit-parameter.vast`](https://github.com/MGYamada/Vastitas/blob/main/examples/book/function-values/explicit-parameter.vast):

```vast
{{#include ../../examples/book/function-values/explicit-parameter.vast}}
```

This program prints `42`.

The rule holds for everything that the surrounding function binds,
including its parameters and a function value in one of its bindings. A
parameter or a binding of a lambda also cannot reuse a name that is visible
outside the lambda. [Lambdas and their names](../stage1b.md#lambdas-and-their-names)
gives both rules.

## One static target per call

Every call of a function value has one
[*static target*](../appendix/glossary.md#static-target): the function
definition that the call runs. The compiler finds it by putting the function
values that each call passes in the place of the function parameters.
[`examples/book/function-values/static-targets.vast`](https://github.com/MGYamada/Vastitas/blob/main/examples/book/function-values/static-targets.vast)
returns one of two function parameters:

```vast
{{#include ../../examples/book/function-values/static-targets.vast}}
```

The call in `main` passes the named function `increment` for both `f` and
`g`. Both branches of the `if` are therefore the same definition, and the
call that follows has the static target `increment`. The program prints
`42`.

When the branches are different definitions, the target would depend on a
value that the program computes:

```vast
{{#include ../../examples/reject/function-values/two-targets.vast}}
```

```text
{{#include ../../examples/reject/function-values/two-targets.stderr}}
```

Two lambdas are two definitions, even when their text is the same. The
compiler does not evaluate the condition to choose a branch, even when the
condition is the literal `true`. A call of `pick` with two different
functions, such as `pick(true, increment, decrement)`, is the same error.
[Static targets](../stage1b.md#static-targets) gives the rules.

## Generics are not function values

The name of a generic stands for several methods, not for one definition. It
is not a function value:

```vast
{{#include ../../examples/reject/function-values/generic-value.vast}}
```

```text
{{#include ../../examples/reject/function-values/generic-value.stderr}}
```

A function or a lambda that calls the generic is a function value.
[`examples/book/function-values/wrapper.vast`](https://github.com/MGYamada/Vastitas/blob/main/examples/book/function-values/wrapper.vast)
passes such a function:

```vast
{{#include ../../examples/book/function-values/wrapper.vast}}
```

This program prints `42`. Inside `add_ints`, the compiler chooses the method
of `add` by the argument types, as for every call of a generic. A function
type is never part of a key: dispatch uses the scalar types only.

## Specialization

A [*higher-order function*](../appendix/glossary.md#higher-order-function)
is a function with a function parameter or a function result, such as
`invoke`, `keep` and `pick`. The compiler checks each lambda and each
higher-order function once on its own. It checks a higher-order function
once more for each combination of function values that the program passes to
it. Each of these checks is a
[*specialized instance*](../appendix/glossary.md#specialized-instance), and
the step is [*specialization*](../appendix/glossary.md#specialization).
After it, no function value remains: the generated program calls each static
target directly.

The compiler checks every function and every lambda of a program, including
those that no call reaches. A lambda with a type error is an error even when
the program never calls it.

A program has at most 4096 specialized instances.
[Specialization](../stage1b.md#specialization) gives this limit and the work
budget of the check.

> **What is checked.** The compiler rejects a capture, a reused name and a
> call with two possible targets before it generates code. It then replaces
> every function value by its static target and checks the resulting program
> again. The proofs cover three properties of an accepted program. Its
> lambdas capture nothing. Each static target has the type of the function
> value that it replaces. The program that the compiler generates code from
> is well typed and terminates. The proofs do not cover that this program
> computes what the source with its lambdas describes. Tests cover that
> step, the diagnostics and native execution.
> [Function specialization](../internals/checking-pipeline.md#function-specialization)
> describes the check, and
> [Verification boundaries](../verification.md#indexed-term-function-and-checked-program-evaluation)
> states the proofs.

## See also

- [Function values](../stage1b.md): what a program may do with a function
  value, with the rules on [lambdas](../stage1b.md#lambdas-and-their-names),
  [static targets](../stage1b.md#static-targets) and
  [specialization](../stage1b.md#specialization).
- [Function types](../language/types.md#function-types): the types `Fn<…>`.
- [Function values](../language/functions.md#function-values): which named
  functions are values.
- [Lambda expressions](../language/expressions.md#lambda-expressions): the
  syntax of a lambda.
- [Appendix D](../appendix/limits.md#functions): the limits on
  specialized instances and on the work of the check.
