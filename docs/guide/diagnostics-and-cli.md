# Diagnostics and the CLI

The earlier chapters use two commands and show the reports of the compiler
one at a time. This chapter gathers them. It describes the commands, shows
how to read what the compiler reports, and says what can still fail when a
built program runs. It ends with what a successful check means, and it names
the Reference chapters that state each of these things in full.

## The commands

```text
vastitas check INPUT.vast [--lib LIBRARY.vast]...
vastitas build INPUT.vast [--lib LIBRARY.vast]... -o OUTPUT
vastitas check --manifest-path Vastitas.toml
vastitas build --manifest-path Vastitas.toml -o OUTPUT [--openblas-prefix PREFIX] [--native-cc COMPILER]
```

- `check` checks a program. `build` checks it in the same way and then
  generates an executable. `build` needs an entry point, a function `main`.
  `check` also accepts a library without one.
- The first two forms are [flat mode](../appendix/glossary.md#flat-mode):
  one entry file, and one `--lib` option for each library file. The other
  two are [manifest mode](../appendix/glossary.md#manifest-mode): the
  manifest of a [package](stdlib.md). One command cannot use both modes.
- Modules, imports, `pub`, `indexed` declarations, edit authority and
  resource functions exist only in packages. In flat mode the compiler
  rejects such a declaration, and the diagnostic says to use a manifest.
- `--openblas-prefix` and `--native-cc` belong to the build of a program
  that multiplies matrices, as
  [the chapter on numerical maps](numerical.md#building-a-numerical-program)
  explains.

A command that succeeds writes one line to standard output, `checked INPUT`
or `built OUTPUT`, and exits with status 0. The compiler has no warnings: it
accepts a program or it rejects it.

`vastitas --help` prints the usage, and `vastitas --version` prints the
version of the compiler. A further command, `audit-lean`, rechecks exported
Lean proofs and checks no program; [Appendix A](cli.md) describes it.

## Reading a diagnostic

A [*diagnostic*](../appendix/glossary.md#diagnostic) is the report that the
compiler writes for a program that it rejects. The declared result of this
function is `Int`, and its body is a Boolean:

```vast
{{#include ../../examples/reject/types/bool-result.vast}}
```

```sh
target/debug/vastitas check examples/reject/types/bool-result.vast
```

```text
{{#include ../../examples/reject/types/bool-result.stderr}}
```

The line has the form `FILE:LINE:COLUMN: CODE: message`:

- The [*place*](../appendix/glossary.md#place) names the file, the line and
  the column of the first character of the construct that is wrong: here the
  expression `true`. Lines and columns count from 1.
- The [*code*](../appendix/glossary.md#code) names the kind of the error.
  `E_TYPE` reports a value of the wrong type in every construct. The
  Reference gives the code of each rule that a program can break.
- The message explains the error. The Reference specifies the code of an
  error and not the text of its message, which can differ between versions
  of the compiler.

The compiler writes diagnostics to standard error and exits with status 1.

A diagnostic can have [*notes*](../appendix/glossary.md#note), further lines
that belong to it. In this function the operands of `+` have different
types:

```vast
{{#include ../../examples/reject/expressions/mixed-integers.vast}}
```

```text
{{#include ../../examples/reject/expressions/mixed-integers.stderr}}
```

A note whose message begins with `help:` proposes a correction. Other notes
point to related places. The diagnostics of the chapters on
[storage](storage.md#owners-and-loans) and on
[numerical maps](numerical.md#equal-dimensions-are-not-enough) name the
allocation, the loan, the space or the basis of an error. Each note points
to the statement that introduced it.

## One run, one or more diagnostics

The compiler works in phases, and a run reports the diagnostics of the first
phase that finds an error. It reads and parses the files first. In flat mode
it then resolves the names of the whole program, and this phase reports
every error that it finds:

```vast
{{#include ../../examples/reject/diagnostics/several-names.vast}}
```

```text
{{#include ../../examples/reject/diagnostics/several-names.stderr}}
```

The checker comes next. It checks types, dispatch, edit authority and
resource functions, and it reports one diagnostic, with its notes. In
manifest mode the checker also resolves the names, so every run of a package
reports one diagnostic. A program with several errors can therefore take
several runs.

The checker does not visit the functions of a program in the order of the
source. Its diagnostic is not always the error that comes first in a file.

## Diagnostics of packages and of commands

In manifest mode, a place names the absolute path of the source file. The
examples of this book show such a path without the part up to the root of
the repository.

Some errors belong to no position in a source file. Their diagnostic has
the form `CODE: message`. A file that the compiler cannot read is an example
(`E_INPUT`), and so is a kernel that is not built (`E_BACKEND`). A
diagnostic for the text of a manifest names the manifest and quotes the
line:

```toml
{{#include ../../examples/reject/packages/unknown-manifest-key/Vastitas.toml}}
```

```text
{{#include ../../examples/reject/packages/unknown-manifest-key.stderr}}
```

A few diagnostics of the checker have no place of their own. They have
line 1 and column 1 of the first input: the entry file, or the manifest of
the package. The function `main` of this package has a parameter:

```vast
{{#include ../../examples/reject/packages/entry-signature/main.vast}}
```

```text
{{#include ../../examples/reject/packages/entry-signature.stderr}}
```

The place does not say that the first character of the manifest is wrong.
[Diagnostics without a place of their own](../language/diagnostics.md#diagnostics-without-a-place-of-their-own)
lists these cases.

## From a code to its chapter

The codes form classes by the construct whose rules they report. The table
names the chapter of this guide that teaches each construct.

| Codes | The compiler reports | Chapter |
| --- | --- | --- |
| `E_LEX`, `E_PARSE`, `E_UNSUPPORTED` | Text that forms no program, and syntax that the mode of the command does not have | [Values and functions](values-and-functions.md), [The commands](#the-commands) |
| `E_NAME`, `E_DUPLICATE`, `E_SHADOW`, `E_RESERVED`, `E_VISIBILITY` | A name that nothing declares, that repeats, that the language reserves or that is not visible | [Values and functions](values-and-functions.md), [modules](modules-and-authority.md) |
| `E_TYPE`, `E_ARITY`, `E_RECURSION`, `E_MAIN` | A value or a call that its types do not permit, a cycle of calls and an invalid entry point | [Values and functions](values-and-functions.md), [control flow and pairs](control-flow-and-pairs.md) |
| `E_ENDPOINT` and the other codes of object identity | An object in the place of another object | [Indexed declarations](indexed-geometry.md) |
| `E_CAPTURE`, `E_STATIC_CALL` | A lambda that uses a binding from outside, and a call of a function value without one target | [Function values](function-values.md) |
| Codes that begin with `E_DISPATCH_` or `E_CONTRACT_` | A generic without one best method, and an invalid abstract type or abstract method | [Dispatch](dispatch.md) |
| `E_OWNER`, `E_BORROW` | An edit of a generic that its owner did not permit | [Edit authority](modules-and-authority.md) |
| Codes that begin with `E_AFFINE_`, `E_SMOOTH`, `E_METRIC` | An invalid declaration of geometry | [Presented affine geometry](affine-geometry.md), [smooth geometry](smooth-geometry.md) |
| Codes that begin with `E_RESOURCE_` | A resource function that breaks a rule on owners, loans, initialization or payloads | [Storage](storage.md) |
| Codes that begin with `E_NUMERICAL_` or `E_TENSOR`, `E_NETWORK` | A numerical statement whose spaces, bases, metrics or ports do not fit | [Numerical maps](numerical.md) |
| Codes that begin with `E_RUNTIME_` or `E_NATIVE_` | A rule on sizes that a program computes, and a check that fails when the program runs | [Storage](storage.md#sizes-that-the-program-computes), [After the build](#after-the-build) |
| `E_LIMIT` | A program beyond a limit of the compiler | [Limits](#limits) |
| `E_USAGE`, `E_INPUT`, `E_MANIFEST`, `E_OUTPUT`, `E_BACKEND`, `E_BUILD` | A command line, a file, a manifest, an output path, a kernel or a build that the compiler cannot use | [The commands](#the-commands), [packages](stdlib.md), [installation](installation.md) |

[Classes of codes](../language/diagnostics.md#classes-of-codes) gives each
class with the Reference chapters that hold its rules, and
[Appendix B](../appendix/diagnostics.md) lists every code.

## Limits

The compiler has fixed bounds on the size of a program and on the work of
checking it. A program beyond such a
[*limit*](../appendix/glossary.md#limit) is an error. This expression stands
inside 64 pairs of parentheses, one more than the compiler admits:

```vast
{{#include ../../examples/reject/limits/nested-parentheses.vast}}
```

```text
{{#include ../../examples/reject/limits/nested-parentheses.stderr}}
```

The limits keep every check finite. They count nesting, numbers of
declarations, sizes and units of work, and never time, so a program is
within the limits or beyond them on every machine. No option changes a
limit. The values of `Nat` and `Int` have no limit.
[Limits](../language/limits.md) gives the rules of all limits, and
[Appendix D](../appendix/limits.md) lists their values.

## Kernel, inputs and outputs

The compiler has two parts: a
[frontend](../appendix/glossary.md#frontend), which reads the files, and a
[kernel](../appendix/glossary.md#kernel), which checks the program. Both
commands need a built kernel, and a command fails when the kernel is missing
or was built from other sources than the compiler (`E_BACKEND`). No command
accepts a program on the result of the frontend alone.
[Installation](installation.md) shows how to build the kernel, and
[Appendix A](cli.md) describes the variables `VASTITAS_KERNEL_ROOT` and
`VASTITAS_KERNEL`, which select one.

`build` protects files. It refuses an output path that names one of its
inputs, and after a build that fails, an existing output file is as it was.
Compilation never runs the generated program. A signal that interrupts the
compiler ends it with the status 128 plus the number of the signal.

[Appendix A](cli.md) states the full contract of the commands, including
the sizes of the inputs, the handling of signals and concurrent builds.

## After the build

An executable runs the program and prints the value of `main`. A program
that the compiler accepts can still stop when it runs, because some checks
need values that only the run has. The `expect` statement of
[the storage chapter](storage.md#parameters) is such a
[*run-time check*](../appendix/glossary.md#run-time-check). This program
writes 3 to two cells and expects 4 in one of them:

```vast
{{#include ../../examples/packages/failed-expect/main.vast}}
```

The compiler accepts the program and builds it. The executable writes one
line to standard error and exits with status 1:

```text
{{#include ../../examples/packages/failed-expect.stderr}}
```

This [*run-time diagnostic*](../appendix/glossary.md#run-time-diagnostic)
has a code and a message, and no place. The message names the cell, the
payload that the cell holds and the payload that the statement expects. The
words `uncaught exception:` begin every run-time diagnostic.

A program that stops in this way prints no result. The writes that it
completed before it stopped are not undone, and it frees its allocations.

An executable makes two other kinds of run-time checks. It checks the
conditions on [sizes that the program computes](storage.md#sizes-that-the-program-computes),
and it checks the allocations, the views and the sizes of an operation
before the first write of that operation.
[Run-time diagnostics](../language/diagnostics.md#run-time-diagnostics)
gives their form, and
[Appendix B](../appendix/diagnostics.md#native-runtime) lists their codes.

## What a successful check means

The compiler [*accepts*](../appendix/glossary.md#accept) a program when
`vastitas check` reports no diagnostic.
[Guarantees](../language/guarantees.md) states what every accepted program
can rely on. Each of its sections says what backs its rules, with the status
words Implemented, Tested and Proved of the
[Introduction](../index.md#what-exists-today). Among the guarantees are
these:

- The compiler generates an executable only from a program that the checker
  accepts, and the checker checks the whole program first, including a
  function that no call reaches.
- The evaluation of every function ends. The language has no loops, and a
  cycle of calls is an error.
- `Nat` and `Int` are unbounded and their operations never overflow or
  round.
- Nothing is implicit: no conversion between `Nat` and `Int`, no allocation,
  no copy, no conjugation and no metric enters unless the program writes
  it.
- Objects, spaces, bases and allocations have nominal identity. Equal
  dimensions never make two of them the same.
- A resource function reads a cell only after a statement wrote it, and a
  program frees every allocation once.
- Two runs of one command on the same files report the same diagnostics.

Other properties are outside acceptance, and
[What is not guaranteed](../language/guarantees.md#what-is-not-guaranteed)
lists them. Acceptance does not say that a program computes what its author
intends. The results of floating-point operations and of native libraries
are outside every check. No theorem states that the executable computes
what the checked program denotes; tests exercise this. No guarantee bounds
the time or the memory of a check or of a run. Performance is an aim of the
design, the C/C++-class target of
[Fast like C](../storage-ownership.md#fast-like-c), and not a property that
acceptance gives a program.

## See also

- [Diagnostics](../language/diagnostics.md): the form of a diagnostic, its
  place, the number and the order of the diagnostics of a run, the exit
  status, run-time diagnostics and the classes of codes.
- [Limits](../language/limits.md): the kinds of limits, what has no limit,
  and limits at run time.
- [Guarantees](../language/guarantees.md): what an accepted program can rely
  on, with the evidence for each guarantee, and what is not guaranteed.
- [Programs](../language/programs.md): flat mode, manifest mode and the
  entry point.
- [Running a resource program](../storage/resource-programs.md#running-a-resource-program):
  the rules of a program that stops at run time.
- [Appendix A](cli.md): the commands, their options and their environment.
- [Appendix B](../appendix/diagnostics.md): every code, by the component
  that reports it.
- [Appendix D](../appendix/limits.md): the values of the limits.
