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

- The name of a generic is not a value (`E_TYPE`). A function or lambda that
  calls the generic is a value.
- Function types are not dispatch keys or selectors. Dispatch uses the four
  scalar types only, as [Generics and dispatch](stage1a.md) describes.
- Generic methods, functions and lambdas may call one another.

```vast
{{#include ../examples/functions.vast}}
```

The executable prints `42`.

## Lambdas and their names

A lambda is an independent definition. Its body refers only to its own
parameters and bindings, to items and to the built-in functions.

Rules:

- A reference in a lambda to a binding outside it is an error (`E_CAPTURE`),
  also to an outer parameter, to a function value bound outside it, or to an
  object that a type in the lambda names. Pass such a value as a parameter.
- A parameter or binding of a lambda must not reuse a name that is visible
  outside the lambda (`E_SHADOW`).
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
a function value must resolve to one function definition. Two lambdas are
different definitions, also when their text is the same. A named function is
one definition however often a program names it.

Rules:

- A call whose function value may come from more than one definition is an
  error (`E_STATIC_CALL`).
- An `if` whose branches are function values must resolve to the same
  definition in both branches. Different definitions are an error
  (`E_STATIC_CALL`), also when the condition is the literal `true`. The
  compiler does not evaluate conditions to choose a target.
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

The compiler makes one **specialized instance** of a function for each
combination of function values that the program passes to it, and it checks
every instance. It checks every function, lambda and method of the program,
also those that no call reaches.

Rules:

- A program has at most 4096 specialized instances in each checking pass.
  Every instance of a lambda and every instance of a function with a function
  parameter or result counts; a function without either does not. More
  instances are an error (`E_LIMIT`).
- The elaboration of a program has a work budget, which
  [Appendix D](appendix/limits.md#checker-limits) gives (`elaborationWork`).
  Exceeding it is an error (`E_LIMIT`). The compiler never accepts part of a
  program or skips an unused body to stay within a budget.
- A cycle of calls through specialized instances is an error (`E_RECURSION`).

[Checking pipeline](internals/checking-pipeline.md#function-specialization)
describes how the compiler specializes and checks function values.

## Moved sections

These anchors keep older links working.

- <a id="syntax-and-values"></a>Syntax and values: [Using function values](#using-function-values) and [Lambdas and their names](#lambdas-and-their-names).
- <a id="static-target-rule"></a>Static target rule: [Static targets](#static-targets).
- <a id="checking-and-specialization"></a>Checking and specialization: [Specialization](#specialization) and [Checking pipeline](internals/checking-pipeline.md#function-specialization).
- <a id="homogeneous-data-pairs"></a>Homogeneous data pairs: [Pair types](language/types.md#pair-types).
- <a id="regression-coverage"></a><a id="lowering-type-information"></a><a id="internal-identities-and-resource-limits"></a>Regressions, lowering and internal identities: [Checking pipeline](internals/checking-pipeline.md).
- <a id="stage1b-indexing"></a>Indexing follow-up record: [Checking pipeline, History](internals/checking-pipeline.md#history).
