# Storage and resource programs

The values of the earlier chapters are pure: a number, a pair or a point
occupies no memory that a program can name. A matrix needs a buffer. This
chapter introduces
[*resource functions*](../appendix/glossary.md#resource-function), which
allocate buffers, lend parts
of them, write and read their cells and free them. Each of these steps is a
statement of the source, and the compiler checks every one before it
generates code. A program allocates and copies cells only where it writes a
statement that does so. This is how the language approaches its performance
goal, the C/C++-class target that
[Fast like C](../storage-ownership.md#fast-like-c) states.

The chapter reads one program of two packages,
[`examples/packages/storage`](https://github.com/MGYamada/Vastitas/tree/main/examples/packages/storage).
The package `buffers` is a library of resource functions, and the package
`app` calls them. Resource functions exist only in
[packages](creating-a-package.md), so the commands name a manifest. Run them from the
repository root:

```sh
target/debug/vastitas check --manifest-path examples/packages/storage/app/Vastitas.toml
target/debug/vastitas build --manifest-path examples/packages/storage/app/Vastitas.toml -o target/storage-example
./target/storage-example
```

The program prints `42`.

## Resource functions

A resource function is declared with `resource fn`. Its body is a list of statements followed by a `value`
block, which computes the result of the function with ordinary expressions.
The library declares three resource functions:

```vast
{{#include ../../examples/packages/storage/buffers/src/operations/mod.vast}}
```

`make` allocates a buffer, writes it and hands it to its caller. Read it
statement by statement:

1. `allocate data: F64[8];` allocates a buffer of eight
   [*cells*](../appendix/glossary.md#cell) and binds `data`, the
   [*owner*](../appendix/glossary.md#owner) of that
   [*allocation*](../appendix/glossary.md#allocation). A cell of `F64` holds
   one binary64 floating-point number. The cells hold no value yet.
2. `borrow output = write(data, layout(8, 2, 2, 4, false));` lends a part of
   the buffer for writing. The part is a
   [*view*](../appendix/glossary.md#view), a rectangle of cells, and the
   binding `output` is a [*loan*](../appendix/glossary.md#storage-loan) of
   it.
3. `fill(output, f64_bits(4613937818241073152));` writes one number to every
   cell of the view. `f64_bits` gives the 64 bits of the number, and these
   are the bits of 3. [Payloads](#payloads) shows a form that is easier to
   read.
4. `release(output);` ends the loan.
5. `value { () }` computes the result, the unit value.

The first line of `make` declares an
[*owned result*](../appendix/glossary.md#owned-result) after `returns`: the
function hands the owner `data` to its caller. `Owned<F64, 8>` is the type of
an owner of eight `F64` cells. The words `initialized [layout(…)]` tell the
caller which cells hold a value.

## Layouts

`layout(offset, rows, columns, leading, transposed)` describes a view as a
matrix that the buffer stores column by column. `offset` is the byte at which
the view starts. `leading` is the number of cells from one stored column to
the next. A cell of `F64` takes 8 bytes, so the cell in stored row `i` and
stored column `j` starts at byte `offset + (i + j × leading) × 8`. Rows and
columns count from 0.

The view `layout(8, 2, 2, 4, false)` of `make` has two rows and two columns
in a buffer of eight cells:

```text
cell   0      1      2      3      4      5      6      7
byte   0      8      16     24     32     40     48     56
view          (0,0)  (1,0)                (0,1)  (1,1)
```

The four other cells are padding. `make` does not write them, and the
contract `initialized [layout(8, 2, 2, 4, false)]` does not cover them.

With `transposed` equal to `true`, the rows of the view are the stored
columns. No cell moves.

## Parameters

`inspect` takes a loan: `Read<F64, 2, 2>` is the type of a loan that permits
reading a view of `F64` cells with two rows and two columns. `Write` and
`ReadWrite` are the two other loan types. The statement
`expect(input, 0, 0, p);` is a
[*run-time check*](../appendix/glossary.md#run-time-check). When the program
runs, it stops unless the cell in row 0 and column 0 holds the bits of `p`.

`round_trip` takes an owner and hands it back. Its body has no statements:
the owned result names the parameter. The parameter states that the cells of
the view are initialized, and so does the result.

## Calling resource functions

The package `app` imports the three functions. Its entry point is a resource
function `main` without parameters:

```vast
{{#include ../../examples/packages/storage/app/src/main.vast}}
```

- `call make() -> (data);` calls `make` and binds its owned result to the
  owner `data`.
- `borrow input = read(data, layout(8, 2, 2, 4, false));` lends the view for
  reading. A `read` loan needs initialized cells, and the contract of `make`
  promises them.
- `call inspect(input) -> ();` passes the loan. The callee sees the view of
  the caller, with its offset and its padding. The loan of the caller gives
  no access until the call returns.
- `call round_trip(data) -> (returned);` hands the owner `data` to the
  callee. The binding `data` ends here, and the owned result gets the name
  `returned`.
- `drop(returned);` frees the buffer.

The `value` block sees no owner and no loan. It computes the result from
scalars with the constructs of the earlier chapters: here a
[generic](dispatch.md) and a [lambda](function-values.md). `answer(40)`
selects the method for `Int` and gives 41, and `increment` adds one.

Only a `call` statement calls a resource function. A pure function cannot
call one, and neither can a `value` block.

Other statements act on owners and loans in the same style. `move d -> e;`
hands an allocation to another owner. `store(v, i, j, p);` writes one cell,
`copy(a, b);` copies the cells of one view to another, and `transpose(v);`
exchanges the rows and columns of a loan.
[Resource statements](../storage/resource-programs.md#resource-statements)
lists every statement.

## Owners and loans

The checker follows every owner and every loan through each resource
function. It accepts a function only when three things hold on every path:
each read finds initialized cells, each buffer is freed once, and no writer
shares cells with another loan.

### A read needs initialized cells

This program writes one column of a view and then borrows both columns for
reading:

```vast
{{#include ../../examples/reject/packages/uninitialized-read/main.vast}}
```

```text
{{#include ../../examples/reject/packages/uninitialized-read.stderr}}
```

The diagnostic points to the `borrow` and names a cell that no statement
wrote: row 0 and column 1 of the view, which occupies bytes 16 to 23 of the
allocation. Its two notes name the function and the allocation.

### An owner ends once

A call that takes an owner ends it, and so do `move` and `drop`. A statement
that names the owner afterwards is an error:

```vast
{{#include ../../examples/reject/packages/moved-owner/main.vast}}
```

```text
{{#include ../../examples/reject/packages/moved-owner.stderr}}
```

The opposite mistake is an error too. At the end of a function, every owner
must have ended: the function dropped it, moved it, handed it to a call or
returned it as an owned result. A program therefore frees each buffer once.
An owner cannot end while a loan of its allocation is live, so a function
releases its loans first.

### A writer shares no cells

Two loans whose views may overlap must both be `read` loans. This program
borrows a view for writing and then borrows one of its columns from the same
owner:

```vast
{{#include ../../examples/reject/packages/overlapping-writers/main.vast}}
```

```text
{{#include ../../examples/reject/packages/overlapping-writers.stderr}}
```

To write a part of a view, a program borrows from the loan instead of from
the owner. `borrow column = write(whole, layout(0, 2, 1, 2, false));` makes
`column` a [*child*](../appendix/glossary.md#child) of `whole`. While the
child is live, its parent gives no access, and the program releases the
child first. With that statement in place of the second `borrow`, the
compiler accepts the program.

The checker compares two views by the bytes from the first cell of each to
its last. It accepts two writers of two columns of a matrix. It rejects two
writers of two rows, although they share no cell, because the cells of the
rows alternate in the buffer.
[Resource statements](../storage/resource-programs.md#resource-statements)
states these rules.

## Payloads

A [*payload*](../appendix/glossary.md#payload) is the value of one cell.
`f64(x)` denotes the binary64 number `x`, and `complex(x, y)` the complex
number with the real part `x` and the imaginary part `y`, for a cell of
`Complex<F64>`. The number is a decimal or a hexadecimal literal:
`f64(3)`, `f64(-0.25)` and `f64(0x1.8p1)` are payloads, and the last one is
1.5 times 2, which is 3.

The compiler never rounds a payload. A number that binary64 only
approximates is an error:

```vast
{{#include ../../examples/reject/packages/inexact-payload/main.vast}}
```

```text
{{#include ../../examples/reject/packages/inexact-payload.stderr}}
```

The message names the two binary64 numbers next to one tenth.

`f64_bits(n)` and `complex_bits(m, n)` give the 64 bits of each number as an
unsigned integer. A program writes a negative zero, an infinity or a NaN in
this form. `f64_bits(4613937818241073152)` in `make` and `f64(3)` are the
same payload.

Payloads exist only in resource statements. A pure expression has no
floating-point numbers and no arithmetic on them.

## Scalars, calls and branches

A resource function also computes scalars, passes them to other resource
functions and chooses between two lists of statements.
[`examples/packages/resource-values`](https://github.com/MGYamada/Vastitas/tree/main/examples/packages/resource-values)
does all three:

```vast
{{#include ../../examples/packages/resource-values/src/main.vast}}
```

- `let input: Nat = value { … };` computes a scalar with ordinary
  expressions and binds it. A `value` block sees the scalar parameters and
  the earlier scalar bindings.
- `let selected: Bool = call choose(flag) -> (data);` binds the result of
  `choose` and its owned result. The arguments of a call are names of
  bindings, so `main` binds `seed` before it passes 41 to `finish`.
- `if flag { … } else { … }` runs one of its two
  [*arms*](../appendix/glossary.md#arm). The checker checks both arms, and
  both must leave the same owners and loans live. A cell counts as
  initialized after the branch only when both arms write it. Both arms of
  `choose` fill `output`, so `choose` can return `data` as initialized.

The integers are the unbounded integers of the earlier chapters. The
difference in the second line of `main` is a `Nat`, which is 0 where the
result would be negative, so `flag` is `true`. The commands at the start of
this chapter build and run the program with the manifest
`examples/packages/resource-values/Vastitas.toml`, and it prints `42`.

## Sizes that the program computes

The statements above fix every size in the source. The statements with the
prefix `runtime_` take their sizes from scalars. Such a size is an
[*extent*](../appendix/glossary.md#extent): a literal, or a `Nat` or `Int`
binding. This function of
[`examples/packages/runtime-extents`](https://github.com/MGYamada/Vastitas/tree/main/examples/packages/runtime-extents)
allocates a table whose numbers of rows and columns are parameters:

```vast
{{#include ../../examples/packages/runtime-extents/main.vast:table}}
```

- `runtime_allocate` allocates `capacity` cells and fixes the one layout of
  the allocation: its rows, its columns, the `leading` of a layout and the
  transposition flag.
- `runtime_borrow output = write(data);` lends that whole view. It takes no
  layout.
- The other `runtime_` statements have the meaning of the statements without
  the prefix.

The compiler cannot decide whether `capacity` cells hold the table, or
whether the cell in row 1 and column 2 lies in it. The executable checks
these conditions when the program runs, before the statement that needs
them. A condition that fails stops the program, as a failing `expect` does.
The compiler decides a condition itself when every extent in it is a
literal.

`main` calls the function with two sizes in one executable:

```vast
{{#include ../../examples/packages/runtime-extents/main.vast:main}}
```

Built with its manifest, the program prints `42`.
[Runtime extents](../storage/resource-programs.md#runtime-extents) gives the
conditions and the restrictions of these statements. One of them is that a
`runtime_` statement cannot stand in a branch.

> **What is checked.** The checker follows owners, loans, layouts and the
> initialization of each cell on every path through every resource function,
> including a function that no call reaches. The compiler generates code
> only for a program that passes. An executable checks the allocations,
> views and sizes of an operation before the first write of that operation.
> It also makes the run-time checks of `expect` and of the conditions on
> extents. The [proofs](../language/guarantees.md#storage) cover the model
> of storage that the checker keeps. In that model an accepted access lies
> in its allocation, and an accepted read finds initialized cells. Two
> loans that give access, of which one writes, do not overlap; a loan with
> a live child gives no access.
> No theorem states that the memory of an executable agrees with this
> model; tests exercise it. The performance target is an aim of the design.
> [Performance evidence and acceptance](../storage-ownership.md#performance-evidence-and-acceptance)
> states what a measurement must show, and that acceptance is open.

## See also

- [Resource programs](../storage/resource-programs.md): the statements of
  this chapter, their rules and their diagnostics.
  [Resource functions](../storage/resource-programs.md#resource-functions),
  [Storage types](../storage/resource-programs.md#storage-types) and
  [Resource statements](../storage/resource-programs.md#resource-statements)
  give the rules on owners, loans, layouts and initialization.
- [Payloads](../storage/resource-programs.md#payloads): the numbers that a
  cell can hold and how a program writes them.
- [Scalar values and calls](../storage/resource-programs.md#scalar-values-and-calls):
  scalar bindings, calls and branches.
- [Runtime extents](../storage/resource-programs.md#runtime-extents): the
  `runtime_` statements and their conditions.
- [Running a resource program](../storage/resource-programs.md#running-a-resource-program):
  what an executable does when a run-time check fails.
  [Diagnostics and the CLI](diagnostics-and-cli.md#after-the-build) shows
  such a failure.
- [Storage and ownership](../storage-ownership.md): the model of storage
  behind these rules, and the performance contract.
- [Storage](../language/guarantees.md#storage) and
  [Run-time checks](../language/guarantees.md#run-time-checks) in
  Guarantees: what an accepted resource program can rely on.
- [Resource checking](../internals/resource-checking.md): how the compiler
  checks resource programs, and what is proved about its checks.
