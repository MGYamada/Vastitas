# Limits

A **limit** is a fixed bound of the compiler on the size of a program or on
the work of checking it. The limits keep every check finite. They are bounds
of the implementation, not of the mathematics that a program describes. This
chapter gives the rules that hold for every limit. The chapter of a construct
states the limits that the construct meets in ordinary use, and
[Appendix D](../appendix/limits.md) lists every limit with its value.

## Kinds of limits

| Kind | Bounds | Examples | Code |
| --- | --- | --- | --- |
| Nesting | The depth of a construct inside constructs of its kind | Nested expressions, types and branches, modules inside modules, a chain of package dependencies, the levels of a polynomial expression | `E_LIMIT` |
| Count | The number of things of one kind | The parameters and the keys of a generic, the abstract types, the specialized instances, the modules and the input files of a program, the events of an assembly, the statements of resource functions | `E_LIMIT`; `E_RESOURCE_LIMIT` in resource functions; `E_TYPE` for the parts of one `indexed` declaration |
| Size of a number | The digits or the bits of a number that the checker computes with | A literal of a polynomial expression, an entry of a Gram matrix, an integer of a storage type | `E_LIMIT`; `E_RESOURCE_LIMIT` for an integer of a storage type |
| Size of data | The bytes of an input or of an allocation | One input file, all inputs of a program, one allocation | `E_LIMIT` for inputs; `E_RESOURCE_OVERFLOW` for an allocation |
| Work budget | The units of work of one check | The elaboration of a program, the dispatch table of a generic, the resolution of names, the checking of resource functions, the exact algebra of a declaration | `E_LIMIT` |
| Depth of checking and of calls | The length of one path of the checker through a body, and of a chain of calls of resource functions | A long list of statements in one function, resource functions that call each other in a chain | `E_LIMIT` for a body; `E_RESOURCE_LIMIT` for calls of resource functions |

A **work budget** counts units of work that the checker defines, such as the
bindings that it expands or the entries of a table that it compares. It does
not count time.

Rules:

- The compiler has no option that changes a limit.
- A program beyond a limit is an error. Its code is `E_LIMIT`, unless the
  chapter of the construct gives another code. The table gives the codes of
  each kind, and the next four rules name the chapters with other codes.
- A program beyond a limit on the statements, the `value` blocks, the
  parameters, the calls or the integers of resource functions is an error
  (`E_RESOURCE_LIMIT`).
  [Resource functions](../storage/resource-programs.md#resource-functions) and
  [Storage types](../storage/resource-programs.md#storage-types) give these
  limits. The work budget of the checking of resource functions has the code
  `E_LIMIT`, like every other work budget.
- [Storage types](../storage/resource-programs.md#storage-types) gives the
  codes for an allocation and for a layout beyond their largest sizes, and
  [Spaces and bases](../linalg/maps-and-gemm.md#spaces-and-bases) the code
  for a space beyond its largest size.
- A contraction tree beyond a limit on its occurrences, its declarations or
  the steps of its plan is an error (`E_TENSOR_TREE`), as
  [Contraction trees](../linalg/networks-and-packing.md#contraction-trees)
  says.
- An `indexed` declaration beyond a limit on the implementations of a
  classification, the parameters of a family, or the cases or the fields of a
  package declaration is an error (`E_TYPE`), as
  [Indexed declarations](../indexed-source.md) says. A program beyond the
  limit on the number of its indexed declarations is an error (`E_LIMIT`).
- The compiler never accepts a part of a program to stay within a limit. A
  rejected program produces no executable.
- A limit holds for the whole program. The checker checks every body, even
  one that no call reaches, and each of these checks counts.
- The diagnostic points to the construct that exceeds the limit. For a
  nesting limit this is the token that is nested too deeply. For a count or
  a budget it is the declaration, the function or the statement that exceeds
  it. A diagnostic for a limit on the inputs as a whole has no place, as
  [Diagnostics](diagnostics.md#diagnostics-without-a-place-of-their-own)
  describes.

This expression stands inside 64 pairs of parentheses, one more than the
nesting limit admits there:

```vast
{{#include ../../examples/reject/limits/nested-parentheses.vast}}
```

```text
{{#include ../../examples/reject/limits/nested-parentheses.stderr}}
```

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

- The compiler decides the source limits before the checker runs. It
  rejects a program beyond one without checking it.
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
- The limits do not bound the number of functions of a program or the length
  of a chain of calls between functions. The input limits bound both.
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

## Limits that reject nothing

Some bounds of the compiler change what it does for a program and reject no
program.

Rules:

- The compilation of reverse passes has budgets. A reverse pass beyond one
  keeps the [runtime reverse pass](../appendix/glossary.md#runtime-reverse-pass):
  the compiler compiles less of the pass and rejects nothing.
  [Reverse-pass primitives](smooth-declarations.md#reverse-pass-primitives)
  and [Appendix D](../appendix/limits.md) describe these budgets.
- A diagnostic of a resource program has a largest number of notes. The
  search for the cell that such a diagnostic names has a bound.
  [Diagnostics of resource programs](../storage/resource-programs.md#diagnostics)
  describes both. Neither bound changes which programs the compiler accepts.
