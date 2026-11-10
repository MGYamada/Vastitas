# Diagnostics

A **diagnostic** is the report that the compiler writes for a program that it
rejects, or for a command that it cannot carry out. Every diagnostic has a
**code**, which names the kind of the error, and a message, which explains
it. Most diagnostics have a **place**, a position in a source file, and some
have **notes**, further lines that point to related places. This chapter gives
the form of a diagnostic, its place, the number and the order of the
diagnostics of one run, and the exit status of the compiler. It holds what is
common to all constructs, for the commands `vastitas check` and
`vastitas build`. The chapter of each construct says which code a broken rule
has, and [Appendix B](../appendix/diagnostics.md) lists every code.

## Diagnostic lines

A diagnostic has one of these forms:

```text
FILE:LINE:COLUMN: CODE: message
FILE:LINE:COLUMN: note: message
MANIFEST: E_MANIFEST: message
CODE: message
```

| Form | Meaning |
| --- | --- |
| `FILE:LINE:COLUMN: CODE: message` | A diagnostic with a [place](#places) |
| `FILE:LINE:COLUMN: note: message` | A note of the diagnostic above it, with a place of its own |
| `MANIFEST: E_MANIFEST: message` | A **manifest diagnostic**: an error in the text of the manifest `MANIFEST` |
| `CODE: message` | A diagnostic without a place, about the command, an input as a whole or the build |

Rules:

- The compiler writes every diagnostic to standard error. A command that fails
  writes nothing to standard output.
- A command that succeeds writes no diagnostic: the compiler has no warnings.
  `check` writes the line `checked INPUT` to standard output, and `build` the
  line `built OUTPUT`. `INPUT` is the entry file or the manifest, and `OUTPUT`
  the output file, each as the command names it.
- A code begins with `E_` and consists of capital letters, digits and `_`.
  The word `note` is not a code.
- A diagnostic with a place and each of its notes take one line.
- A note belongs to the diagnostic above it. A note whose message begins with
  `help:` proposes a correction.
- The message of a manifest diagnostic for invalid TOML takes several lines.
  It quotes the line of the manifest, marks the error in it, and ends with an
  empty line.
- The message of a diagnostic without a place can continue on further lines.
  The usage of the command follows the `E_USAGE` of an invalid command line.
  Advice or the output of the build tools can follow `E_BACKEND` and
  `E_BUILD`.

In this program the operands of `+` have different types. The diagnostic has
one note:

```vast
{{#include ../../examples/reject/expressions/mixed-integers.vast}}
```

```text
{{#include ../../examples/reject/expressions/mixed-integers.stderr}}
```

This manifest has a key that a manifest does not have:

```toml
{{#include ../../examples/reject/packages/unknown-manifest-key/Vastitas.toml}}
```

```text
{{#include ../../examples/reject/packages/unknown-manifest-key.stderr}}
```

## Places

A place names a file, a line of the file and a column of the line. It is the
first character of the construct that the diagnostic is about, such as an
expression of the wrong type or a declaration with a repeated name. The place
of a note is the first character of a related construct, such as the
construction that introduced an identity.

Rules:

- `LINE` and `COLUMN` count from 1. A column counts the characters of the
  line, as Unicode scalar values. A character of several bytes counts as one,
  and so does a tab.
- In [flat mode](programs.md#flat-mode), `FILE` is the path of the entry file
  or of the library, as the command names it. Each file counts its own lines,
  and a diagnostic in a library names the library.
- In [manifest mode](programs.md#manifest-mode), `FILE` is the absolute path
  of the source file, with symbolic links resolved, whatever path the command
  gives. A diagnostic in an inline module names the file that holds the
  module. `MANIFEST` in a manifest diagnostic is the absolute path of the
  manifest.
- Where a reader may expect another place, the chapter of the construct says
  which construct a diagnostic points to. Examples are
  [Static targets](../stage1b.md#static-targets) and the
  [diagnostics of resource programs](../storage/resource-programs.md#diagnostics).

The examples of this book show an absolute path without its part up to the
root of the repository. In this package `main` calls a private function of a
module:

```vast
{{#include ../../examples/reject/packages/private-function/main.vast}}
```

```text
{{#include ../../examples/reject/packages/private-function.stderr}}
```

## Diagnostics without a place of their own

Some errors belong to no position in a source file. A program can lack an
entry point, or an input file can be too large.

Rules:

- A diagnostic about the command, about an input as a whole or about the
  build has the form `CODE: message`. Examples are a file that the compiler
  cannot read (`E_INPUT`), a cycle of package dependencies (`E_CYCLE`), a
  [limit](limits.md) on the inputs (`E_LIMIT`) and an unusable output path
  (`E_OUTPUT`).
- A diagnostic of the checker without a place of its own has the place
  `FILE:1:1`. `FILE` is the first input of the program: the entry file in
  flat mode, and the [root manifest](../packages.md#the-package-graph) in
  manifest mode. This place does not say that the first character of that
  file is wrong.
- The compiler reports two errors of the entry point at this place
  (`E_MAIN`). One is a program without an entry point under `vastitas build`.
  The other is a function `main` with another signature than
  [The entry point](programs.md#the-entry-point) gives. The compiler reports
  a generic named `main`, and a resource function `main` with another result
  type, at their declarations.
- The compiler reports an invalid
  [geometry compatibility export](../packages.md#geometry-compatibility-exports)
  at this place. It reports an invalid
  [function type](types.md#function-types) there too, in the programs that
  the rule of function types names.

The function `main` of this package has a parameter. The diagnostic names the
manifest of the package, not the function:

```vast
{{#include ../../examples/reject/packages/entry-signature/main.vast}}
```

```text
{{#include ../../examples/reject/packages/entry-signature.stderr}}
```

> **Implementation note.** The request that the kernel checks holds a
> position for each construct of a source file and no position in a manifest.
> The driver maps a position that the kernel returns to its file, line and
> column. It shows a diagnostic that the kernel returns without a position at
> the start of the first file that it read.

## Names and text in diagnostics

Rules:

- A message names a declaration by its name or by its path
  `package::module::name`. The first component of the path is the name that
  the manifest of the declaring package gives it, even when the source reaches
  the package through a dependency alias.
- A message names a parameter as the source spells it.
- The compiler does not write every character of a path, or of text that
  comes from a manifest, as it is. It writes a control character, white space
  other than U+0020, or a character with the Unicode
  `Default_Ignorable_Code_Point` property as its code point in angle brackets.
  A file name that holds the escape character appears as `x<U+001B>[2J.vast`,
  for example.
- The rule covers every path and file name in a diagnostic. It covers the
  message of a diagnostic with a place and of its notes, including the
  package name that begins the path of a declaration.
- In a manifest diagnostic the rule covers the line that a TOML error quotes
  and the keys that its message names. In a native build it covers the names
  that the compiler reads from the kernel root and from the generated program.
- The line `checked INPUT` or `built OUTPUT` of a successful command writes
  its path by the same rule.
- A path that is not valid UTF-8 appears with U+FFFD in place of each invalid
  sequence.
- [Source text](lexical-structure.md#source-text) gives the errors that
  report a character of a source file. Their messages name a character that
  the rule would replace by its code point alone, such as `U+001B`. They name
  another character in backticks, followed by its code point.

The rule keeps a name or a path from starting a line of its own and from
sending a control sequence to a terminal. The compiler writes the output of
the build tools that follows `E_BUILD` as the tools give it.

> **Implementation note.** The driver formats every path with one function. A
> TOML error keeps the layout of the `toml` crate, and its carets stay under
> the place that they mark in the quoted line. The message of a TOML error
> keeps its line breaks when the manifest holds no backslash and no
> multi-line string. In any other manifest a line feed of the message may
> come from the manifest, and the driver writes each one as `<U+000A>`.

## Number and order

The compiler works in phases, and a run reports the diagnostics of the first
phase that finds an error:

1. the command line and, for `build`, the output path;
2. reading and parsing the manifests and the source files;
3. in flat mode, the names of the whole program;
4. the checker, which checks the whole program;
5. for `build`, the native build.

Rules:

- A command that rejects a program reports at least one diagnostic.
- Phases 1, 2, 4 and 5 stop at their first error and report one diagnostic.
  The diagnostic of the checker can have notes.
- In flat mode the compiler reads every file and then parses the entry file
  and the libraries, in the order of the command. In manifest mode it reads
  and parses the packages that a package depends on before the modules of
  that package.
- Phase 3 reports every error of names and scopes that it finds. It reports
  the items whose names repeat first. The errors inside functions follow, in
  the order of the functions and then of the methods that hold them. One
  cycle of calls (`E_RECURSION`) comes last. These diagnostics are not sorted
  by place.
- Manifest mode has no phase 3. The checker resolves the names of a package
  and reports one diagnostic.
- The checker does not visit the items of a program in the order of the
  source. Its diagnostic is therefore not always the error that comes first
  in a file. For example, it reports an ambiguity of a generic before a type
  error in a function that stands above the generic. It reports an error in a
  function that `main` calls before an error in a function that stands
  between `main` and that function.
- A program with several errors can take several runs: after a correction the
  next run can report another error.
- The notes of a diagnostic follow it in the order that the checker gives
  them. [Diagnostics of resource programs](../storage/resource-programs.md#diagnostics)
  gives the largest number of notes.

This program has three errors of names, and one run reports them all:

```vast
{{#include ../../examples/reject/diagnostics/several-names.vast}}
```

```text
{{#include ../../examples/reject/diagnostics/several-names.stderr}}
```

> **Implementation note.** The kernel returns one diagnostic for a rejected
> request. The frontend reports the errors of phases 1 to 3 itself, and the
> kernel checks the rules of phase 3 again. When the kernel comes from other
> sources than the compiler, the driver adds a note without a place after the
> diagnostic, as [Appendix A](../guide/cli.md) describes.

## Exit status

| Outcome of `check` or `build` | Exit status |
| --- | --- |
| The command succeeds | 0 |
| The compiler rejects the program or cannot carry out the command | 1 |
| A signal interrupts the compiler, which reports `E_INTERRUPTED` | 128 plus the number of the signal |

`vastitas --help` and `vastitas --version` write to standard output and exit
with status 0. [Appendix A](../guide/cli.md) names the signals that interrupt
the compiler.

## Run-time diagnostics

An executable that fails a run-time check writes a **run-time diagnostic**: a
line of standard error that holds a code and a message. It has no place.
[Running a resource program](../storage/resource-programs.md#running-a-resource-program)
gives the rules, and [Guarantees](guarantees.md#run-time-checks) says which
checks an executable makes.

Rules:

- A run-time diagnostic has a code that begins with `E_NATIVE_` or
  `E_RUNTIME_`. [Appendix B](../appendix/diagnostics.md#native-runtime) lists
  the messages.
- An executable that stops with a run-time diagnostic writes nothing to
  standard output and exits with an unsuccessful status.
- An executable that ends without one prints its result and exits with
  status 0, as [The entry point](programs.md#the-entry-point) says.

> **Implementation note.** The line begins with `uncaught exception: `, as in
> `uncaught exception: E_RUNTIME_EXTENT: extent is negative`, and the exit
> status is 1.

## Codes

The code of a diagnostic says which kind of rule the program breaks. A rule
of the Reference gives the code of its error with the words of
[Notation](notation.md#rules).

Rules:

- The Reference specifies the code of every error and, where a chapter says
  so, its place.
- The Reference does not specify the text of a message or of a note. The text
  explains the error to a reader, and it can differ between versions of the
  compiler. The tests of the repository compare the diagnostics that this
  book shows with the output of the compiler.
- One code serves many rules. `E_TYPE` reports a value of the wrong type in
  every construct, and the message says which types are involved.
- One rule can have different codes in flat mode and in manifest mode. The
  rule then gives both.

## Classes of codes

The codes form classes by the construct whose rules they report. Each class
has its rules in the chapters of the last column, and
[Appendix B](../appendix/diagnostics.md) lists the codes of each class.

| Class | Codes | Reports | Rules |
| --- | --- | --- | --- |
| Parse | `E_LEX`, `E_PARSE`, `E_UNSUPPORTED` | Text that forms no program, and syntax that the language or the mode of the command does not have | [Lexical structure](lexical-structure.md), [Items](items.md#kinds-of-items) and every Syntax block |
| Names | `E_NAME`, `E_DUPLICATE`, `E_RESERVED`, `E_SHADOW`, `E_VISIBILITY`, `E_CYCLE` | A name that nothing declares, that repeats, that the language reserves or that is not visible, and a cycle of modules, imports or packages | [Names and paths](names-and-paths.md), [Items](items.md#names-of-items), [Scopes of bindings](statements.md#scopes-of-bindings), [Modules](modules.md) |
| Types | `E_TYPE`, `E_ARITY`, `E_OPERATOR`, `E_MAIN`, `E_RECURSION` and the codes of object identity, such as `E_ENDPOINT` | A value, a call or an operator that its types do not permit, an invalid entry point and a cycle of calls | [Types](types.md), [Expressions](expressions.md), [Functions](functions.md), [Geometric types](geometric-types.md), [Programs](programs.md#the-entry-point) |
| Capture | `E_CAPTURE`, `E_STATIC_CALL` | A lambda that uses a binding from outside, and a call of a function value without one target | [Function values](../stage1b.md) |
| Dispatch | The codes that begin with `E_DISPATCH_` or `E_CONTRACT_`, `E_CAPABILITY`, `E_HIERARCHY` | A generic without one best method at a key, and invalid abstract types and abstract methods | [Generics and dispatch](../stage1a.md) |
| Authority | `E_OWNER`, `E_BORROW`, `E_ASSEMBLY`, `E_IMPACT`, `E_PROVENANCE` | An edit of a generic that its owner did not permit, and an invalid assembly | [Edit authority](edit-authority.md) |
| Declarations | The codes that begin with `E_AFFINE_`, `E_SMOOTH`, `E_METRIC` | An invalid `indexed` declaration of geometry | [Indexed declarations](../indexed-source.md), [Presented affine declarations](../affine-geometry.md), [Smooth affine declarations](smooth-declarations.md) |
| Resources | The codes that begin with `E_RESOURCE_` | A resource function that breaks a rule on owners, loans, access, initialization or payloads | [Resource programs](../storage/resource-programs.md) |
| Numerical | The codes that begin with `E_NUMERICAL_` or `E_TENSOR`, `E_NETWORK` | A numerical statement whose spaces, bases, metrics or ports do not fit | [Numerical maps](../linalg/maps-and-gemm.md) and the two chapters after it |
| Runtime | The codes that begin with `E_RUNTIME_` or `E_NATIVE_` | A rule on runtime extents that the compiler decides, and a [run-time diagnostic](#run-time-diagnostics) of an executable | [Runtime extents](../storage/resource-programs.md#runtime-extents), [Running a resource program](../storage/resource-programs.md#running-a-resource-program) |
| Limits | `E_LIMIT`, `E_RESOURCE_LIMIT` | A program beyond a limit of the compiler | [Limits](limits.md) |
| Protocol | `E_PROTOCOL`, `E_ARGUMENT`, `E_CODEGEN` and the codes that begin with `E_INTERNAL_` | A request of the [wire protocol](../appendix/glossary.md#wire-protocol) that breaks a rule of the protocol, and a failed audit of the checker's own result | [Wire protocols](../protocol.md), [Verification boundaries](../verification.md) |
| Input and output | `E_USAGE`, `E_INPUT`, `E_MANIFEST`, `E_LIBRARY`, `E_OUTPUT`, `E_INTERRUPTED` | A command line, an input file, a manifest or an output path that the compiler cannot use, and an interrupted run | [Programs](programs.md), [Packages](../packages.md), [Appendix A](../guide/cli.md) |
| Build | `E_BACKEND`, `E_BUILD` | A kernel or a native build that is missing, does not match the compiler or fails | [Appendix A](../guide/cli.md) |

Rules:

- A code of the classes Input and output and Build reports a property of the
  command and of its environment, not of the program.
- The rules of the Reference give a code of the class Protocol for a source
  program only where the chapter of a construct says so.
- A code of the class Runtime with the prefix `E_NATIVE_` appears only in a
  run-time diagnostic.
