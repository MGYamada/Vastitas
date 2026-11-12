# Function values

A **function value** is a function used as a value: the name of a function, or
a [lambda expression](language/expressions.md#lambda-expressions). A function
value may be bound, passed, returned and called. Every call of a function value
has one **static target**, a function definition that the compiler knows
before it generates code. Programs have no closures and no function pointers
at run time. [Function types](language/types.md#function-types) gives the
types of function values.

## Using function values

A binding, a parameter or a result of a [function type](language/types.md#function-types)
holds a function value. A call of such a value applies the function, and calls
may chain, as in `factory()(42)`.
[Function values](language/functions.md#function-values) says which named
functions are values.

Rules:

- A generic is not a function value, as
  [Path expressions](language/expressions.md#path-expressions) says.
- Function types are not dispatch keys or selectors. Dispatch uses the four
  scalar types only, as [Generics and dispatch](stage1a.md) describes.
- Generic methods, functions and lambdas may call one another.
- A module may call a function value that it receives, even when the value is
  a private function of another module, as
  [Visibility](language/names-and-paths.md#visibility) says.

```vast
{{#include ../examples/functions.vast}}
```

The executable prints `42`.

## Lambdas and their names

A lambda is an independent definition. Its body refers only to its own
parameters and bindings, to items and to the built-in functions.
[Lambda expressions](language/expressions.md#lambda-expressions) gives the
production `LambdaExpression`.

Rules:

- A reference in a lambda to a binding outside it is an error (`E_CAPTURE`).
  This includes an outer parameter, a function value bound outside the lambda
  and an object that a type in the lambda names. Pass such a value as a
  parameter.
- A parameter or binding of a lambda must not reuse a name that is visible
  outside the lambda (`E_SHADOW`). Among the parameters and bindings of the
  lambda itself, the rule of
  [Scopes of bindings](language/statements.md#scopes-of-bindings) holds
  (`E_DUPLICATE`).
- Two lambdas that do not contain one another may bind the same names. A
  lambda inside a lambda follows the same rules.
- Functions, generics and built-in functions remain callable in a lambda.

```vast
{{#include ../examples/reject/function-values/capture.vast}}
```

```text
{{#include ../examples/reject/function-values/capture.stderr}}
```

## Static targets

After the compiler substitutes the function arguments of a call, every call of
a function value resolves to one function definition. Two lambda expressions
are different definitions, even when their text is the same. One lambda
expression is one definition, however many calls reach it, and a named
function is one definition however often a program names it.

Rules:

- An `if` whose branches are function values must resolve to the same
  definition in both branches. Different definitions are an error
  (`E_STATIC_CALL`), which the compiler reports at the `if`.
- The rule holds even when no call uses the value of the `if`, and when its
  condition is the literal `true`. The compiler does not evaluate conditions
  to choose a target.
- A branch that is a function parameter is compared for each call of the
  enclosing function, with the function values that the call passes.
- Passing the same function value for two parameters is valid.

```vast
{{#include ../examples/reject/function-values/two-targets.vast}}
```

```text
{{#include ../examples/reject/function-values/two-targets.stderr}}
```

The compiler erases function values after it has checked them. A computation
of scalars that produces a function value is still checked and evaluated.

## Specialization

A **higher-order function** is a function with a function parameter or a
function result. The compiler checks each lambda and each higher-order
function once on its own. It checks a higher-order function once more for
each combination of function values that the program passes to its function
parameters. Each of these checks makes one **specialized instance**. The
compiler checks every function, lambda and method of the program, including
those that no call reaches.

Rules:

- A program has at most 4096 specialized instances. More instances are an
  error (`E_LIMIT`). A function that is not higher-order has no specialized
  instance. [Appendix D](appendix/limits.md#functions) says what counts as
  an instance.
- The elaboration of a program has a work budget, which
  [Appendix D](appendix/limits.md#functions) gives (`elaborationWork`).
  Exceeding it is an error (`E_LIMIT`). The compiler never accepts part of a
  program or skips an unused body to stay within a budget.
- A cycle of calls through specialized instances is an error (`E_RECURSION`).

[Checking pipeline](internals/checking-pipeline.md#function-specialization)
describes how the compiler specializes and checks function values.
