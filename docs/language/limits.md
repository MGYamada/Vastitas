# Limits

A **limit** is a fixed bound of the compiler on the size of a program or on
the work of checking it. The limits keep every check finite. They are bounds
of the implementation, not of the mathematics that a program describes. This
chapter gives the rules that hold for every limit. The chapter of a construct
states the limits that the construct meets in ordinary use, and
[Appendix D](../appendix/limits.md) lists the limits with their values.

## Kinds of limits

| Kind | Bounds | Examples | Code |
| --- | --- | --- | --- |
| Nesting | The depth of a construct inside constructs of its kind | Nested expressions, types and branches, modules inside modules, a chain of package dependencies, the levels of a polynomial expression | `E_LIMIT` |
| Count | The number of things of one kind | The parameters and the keys of a generic, the abstract types, the specialized instances, the modules and the input files of a program, the events of an assembly, the statements and the `value` blocks of resource functions, the records of the writes to an allocation, the occurrences, the declarations and the steps of a contraction tree | `E_LIMIT`; `E_RESOURCE_LIMIT` in resource functions; `E_RESOURCE_TYPE` for the views of one `initialized` contract; `E_TENSOR_TREE` for a contraction tree |
| Size of a number | The digits or the bits of a number that the checker computes with | A literal of a polynomial expression, an entry of a Gram matrix, a position in a constraint of a family, an integer of a storage type, the numbers of a layout, the dimension of an axis of a tensor, an entry of a metric of a numerical map | `E_LIMIT`; `E_RESOURCE_LIMIT` for an integer of a storage type; `E_RESOURCE_LAYOUT` for a layout; `E_TENSOR` for an axis; `E_NUMERICAL_METRIC` for an entry of a metric |
| Size of data | The bytes of an input, of an allocation or of a space | One input file, all inputs of a program, one allocation, one static space | `E_LIMIT` for inputs; `E_RESOURCE_OVERFLOW` for an allocation; `E_NUMERICAL_TYPE` for a space |
| Work budget | The units of work of one check | The elaboration of a program, the dispatch table of a generic, the resolution of names, the checking of resource functions, the exact algebra of a declaration, the query of the initialized cells of a view | `E_LIMIT`; `E_RESOURCE_LIMIT` for the expansion of resource calls; `E_RESOURCE_INIT` for the initialization query |
| Depth of checking and of calls | The length of one path of the checker through a body, and of a chain of calls of resource functions | A long list of statements in one function, resource functions that call each other in a chain | `E_LIMIT` for a body; `E_RESOURCE_LIMIT` for calls of resource functions |

A **work budget** counts units of work that the checker defines, such as the
bindings that it expands or the entries of a table that it compares. It does
not count time.

Rules:

- The compiler has no option that changes a limit.
- A program beyond a limit is an error. Its code is `E_LIMIT`, unless the
  chapter of the construct gives another code. The table gives the codes of
  each kind, and the next six rules name the chapters with other codes.
- A program beyond a limit on the statements, the `value` blocks, the
  parameters, the calls or the integers of resource functions, or on the
  records of the writes to one allocation, is an error (`E_RESOURCE_LIMIT`).
  [Resource functions](../storage/resource-programs.md#resource-functions) and
  [Storage types](../storage/resource-programs.md#storage-types) give the
  limits on statements, `value` blocks and integers, and
  [Resource statements](../storage/resource-programs.md#resource-statements)
  the limit on the records of writes. A resource function also
  has a limit on its parameters and on its owned results, a call has the same
  limit on its arguments and results, and a chain of calls of resource
  functions has a limit on its depth. The work budget of the checking of
  resource functions has the code `E_LIMIT`, and the budget of the expansion
  of resource calls has the code `E_RESOURCE_LIMIT`.
- An `initialized` contract of an owned parameter or result beyond the limit
  on its views is an error (`E_RESOURCE_TYPE`), as
  [Storage types](../storage/resource-programs.md#storage-types) says.
- An allocation beyond its largest size is an error
  (`E_RESOURCE_OVERFLOW`), and so is a layout beyond its largest numbers
  (`E_RESOURCE_LAYOUT`), as
  [Storage types](../storage/resource-programs.md#storage-types) says. A
  space beyond its largest size is an error (`E_NUMERICAL_TYPE`), as
  [Spaces and bases](../linalg/maps-and-gemm.md#spaces-and-bases) says.
- A tensor with an axis beyond the largest dimension is an error
  (`E_TENSOR`), as [Tensors](../linalg/networks-and-packing.md#tensors)
  says. A metric with an entry beyond the largest value that
  `adjoint_into` and `hermitian_diagonal` accept is an error
  (`E_NUMERICAL_METRIC`), as
  [Adjoints for diagonal metrics](../linalg/transforms-and-metrics.md#adjoints-for-diagonal-metrics)
  and [Pairings](../linalg/transforms-and-metrics.md#pairings) say.
- A contraction tree beyond a limit on its occurrences, its declarations or
  the steps of its plan is an error (`E_TENSOR_TREE`), as
  [Contraction trees](../linalg/networks-and-packing.md#contraction-trees)
  says.
- A `borrow` for reading whose query of the initialized cells is beyond its
  bound is an error (`E_RESOURCE_INIT`), even when the stores of the program
  write every cell, as
  [Resource statements](../storage/resource-programs.md#resource-statements)
  says.
- The compiler never accepts a part of a program to stay within a limit. A
  rejected program produces no executable.
- A limit holds for the whole program. The checker checks every body, even
  one that no call reaches, and each of these checks counts.
- The diagnostic of most limits points to the construct that exceeds the
  limit. For a nesting limit this is the token that is nested too deeply. For
  a count or a budget it is the declaration, the function or the statement
  that exceeds it. A limit on a part of an `indexed` declaration, such as the
  domain of a classification, has the place of the declaration. The budgets
  on the resolution of one path and on the `use` declarations have the place
  of a path or of a `use` declaration that exceeds them.
- The diagnostic for the number of indexed declarations has the place of the
  first declaration beyond the limit. The compiler counts the declarations of
  the packages that a package depends on before its own. In one package, the
  declarations of an inline module come before those of the module that holds
  it, and those of a module file, which `mod name;` declares, after those of
  the module that declares it. In one module they come in the order of the
  text.
- Some limit diagnostics point to no construct. A diagnostic for a limit on
  the inputs as a whole, or on a chain of package dependencies, has no place.
  [Diagnostics without a place of their own](diagnostics.md#diagnostics-without-a-place-of-their-own)
  lists the limits whose diagnostic has the place `FILE:1:1`, and describes
  both forms.

This expression stands inside 64 pairs of parentheses, one more than the
nesting limit admits there:

```vast
{{#include ../../examples/reject/limits/nested-parentheses.vast}}
```

```text
{{#include ../../examples/reject/limits/nested-parentheses.stderr}}
```

> **Implementation note.** The frontend writes a program as one request of
> the wire protocol, and the request of a program within the limits on its
> inputs can be larger than the kernel reads. The frontend rejects such a
> program with the limit on the size of a request (`E_LIMIT`) before the
> kernel runs, as [Request](../appendix/limits.md#request) of Appendix D
> says.

## Source limits and limits of the checked program

A limit measures either the source of a program or the program that the
checker builds from it.

A **source limit** bounds the text and the files of a program. The source
limits bound the nesting of expressions, types and modules and the chain of
package dependencies. They also bound the sizes and the number of the inputs
and the statements of resource functions. Two programs with the same meaning
can differ in a source limit. A pair of parentheses adds a level of nesting
and changes nothing else.

A limit of the checked program bounds what the checker builds. Examples are
the keys of a generic, the specialized instances and the bindings that the
compiler generates for a function. The steps of a resource function after
the expansion of its calls are another example, and so is every work budget.
These limits do not follow from the length of the source.

Rules:

- The compiler decides the limits on nesting and on the inputs before the
  checker runs. It rejects a program beyond one of them without checking it.
- A generic with `n` parameters has 4ⁿ keys, one for each tuple of the four
  scalar types. The limit on keys therefore admits six parameters, as
  [Generic declarations](../stage1a.md#generic-declarations) says.
- The checker checks a method at every key at which it applies, as
  [Selection](../stage1a.md#selection) says, and a higher-order function once
  for each combination of function values, as
  [Specialization](../stage1b.md#specialization) says. Each of these checks
  counts against the work budget of the program.
- A work budget of the whole program counts all its declarations together.
  Dividing a program into more functions, generics or modules does not start
  a budget again.
- [Appendix D](../appendix/limits.md) says for each limit what it counts, and
  whether it holds for a program, a package, a generic or a function.

This generic has seven parameters and therefore 16384 keys. The domain of the
declaration lists one key, and the limit counts them all:

```vast
{{#include ../../examples/reject/limits/seven-parameters.vast}}
```

```text
{{#include ../../examples/reject/limits/seven-parameters.stderr}}
```

## What has no limit

Rules:

- The values of `Nat` and `Int` have no limit, and neither has an integer
  literal, as [Scalar types](types.md#scalar-types) and
  [Integer literals](lexical-structure.md#integer-literals) say. The limits on
  the size of a number hold only where a chapter gives one.
- No limit counts the functions of a program or the calls of a chain of calls
  between functions. The work budgets of the whole program bound both,
  because every function uses units of work.
- Resource functions differ. Each ends with a `value` block, so the limit on
  `value` blocks bounds their number, and a chain of their calls has a limit
  on its depth.
- The limits do not bound the time that a check takes or the memory that it
  uses. A work budget bounds the units of one kind of work.

## Limits at run time

The limits of this chapter bound the program that the compiler checks. They do
not bound what an executable computes.

Rules:

- An executable computes with integers of any size. It has no work budget, and
  its run has no limit of time, memory or stack that the language defines.
- A resource program takes some sizes from values that it computes. The
  compiler cannot decide the limits on these sizes, and the executable checks
  them when it runs, before the statement that needs them.
  [Runtime extents](../storage/resource-programs.md#runtime-extents) gives
  the conditions, and
  [Running a resource program](../storage/resource-programs.md#running-a-resource-program)
  says how an executable reports a failure.
- An executable stops with a
  [run-time diagnostic](diagnostics.md#run-time-diagnostics) when an extent
  that the program computes does not fit the range of native sizes, or when
  an allocation fails.
  [Appendix B](../appendix/diagnostics.md#native-runtime) lists the codes.
- An allocation whose size the compiler accepts can still fail when the
  program runs.

> **Implementation note.** The storage runtime counts the bytes of the live
> allocations of an executable, with one count for the static allocations and
> one for the allocations with runtime extents. An allocation that would bring
> a count above 2⁶³ − 1 bytes fails (`E_NATIVE_ALLOCATION`), before the
> runtime asks the system for memory. The bound is the largest size of one
> allocation, so only several live allocations together reach it.

## Limits and platforms

Rules:

- The limits are the same on every platform and on every machine. No limit
  depends on the speed or the memory of the machine or on the time that a
  check takes.
- A program is therefore within the limits or beyond them wherever the same
  compiler checks it.
- The parts of the compiler have one set of limits. The compiler accepts no
  program with a kernel that was built with other limits: it reports an error
  (`E_BACKEND`), as [Appendix A](../guide/cli.md) describes.

> **Implementation note.** Most limits come from the file
> `lean-kernel/compiler-limits.json`, which the frontend and the kernel read
> when they are built. The limits on the inputs are constants of the
> frontend. The executable checks the sizes of the 64-bit native profile.

## Bounds that reject nothing

Some bounds of the compiler change what it does for a program and reject no
program.

Rules:

- The compilation of reverse passes has budgets. A reverse pass beyond one
  keeps the [runtime reverse pass](../appendix/glossary.md#runtime-reverse-pass):
  the compiler compiles less of the pass and rejects nothing.
  [Appendix D](../appendix/limits.md#bounds-that-reject-nothing) gives these
  budgets with their values and says what the compiler does at each.
  [Reverse-pass primitives](smooth-declarations.md#reverse-pass-primitives)
  gives the rules of reverse passes, which no budget changes.
- A diagnostic of a resource program has a largest number of notes. The
  search for the cell that such a diagnostic names has a bound.
  [Diagnostics of resource programs](../storage/resource-programs.md#diagnostics)
  describes both. Neither bound changes which programs the compiler accepts.
