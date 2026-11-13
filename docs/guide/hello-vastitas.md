# Hello, Vastitas

This section writes the smallest program, checks it, builds it and runs it.
It then shows what the compiler prints for a program that it rejects.

## The smallest program

A program that you can run has an
[*entry point*](../appendix/glossary.md#entry-point): the function `main`,
which takes no arguments and returns an `Int`. Running the program computes
that integer.
[`examples/book/programs/hello.vast`](https://github.com/MGYamada/Vastitas/blob/main/examples/book/programs/hello.vast)
holds the smallest program:

```vast
{{#include ../../examples/book/programs/hello.vast}}
```

`fn` declares a function, and `main` is its name. The empty parentheses say
that it takes no arguments, and `-> Int` says that it returns an integer.
The braces hold the body. The body ends with the expression `42`, and the
value of that expression is the result of the function. A function has no
`return` statement, and no semicolon follows the result.

The language has no strings and no input or output. A program tells you one
thing, the integer that `main` returns, and the executable prints it.

## `check` and `build`

Run the commands of this book from the root of the repository.
`vastitas check` checks a program:

```sh
target/debug/vastitas check examples/book/programs/hello.vast
```

```text
checked examples/book/programs/hello.vast
```

The [frontend](../appendix/glossary.md#frontend) reads the file and sends
the program to the [kernel](../appendix/glossary.md#kernel). The kernel
checks every function of the program. `check` writes no file.

`vastitas build` checks the program in the same way. It then builds an
executable for your machine and writes it to the path after `-o`:

```sh
target/debug/vastitas build examples/book/programs/hello.vast -o target/hello
./target/hello
```

```text
built target/hello
42
```

The first line comes from the compiler and the second from the program. The
executable prints the integer that `main` returns and exits with status 0.

The two commands differ in what they need and in what they leave behind:

- `check` accepts a file without `main`, such as a file that only holds
  functions for other files. `build` needs the entry point.
- `build` writes the executable only when the whole build succeeds. A build
  that fails leaves an existing file at the output path as it was.
- Neither command runs the program.

## When the compiler says no

In
[`examples/reject/types/bool-result.vast`](https://github.com/MGYamada/Vastitas/blob/main/examples/reject/types/bool-result.vast)
`main` promises an `Int`, and its body is the Boolean `true`:

```vast
{{#include ../../examples/reject/types/bool-result.vast}}
```

```sh
target/debug/vastitas check examples/reject/types/bool-result.vast
```

The compiler prints one
[*diagnostic*](../appendix/glossary.md#diagnostic) and exits with status 1:

```text
{{#include ../../examples/reject/types/bool-result.stderr}}
```

A diagnostic names the file, the line and the column of the mistake, and
then gives a code and a message. Here the mistake is at line 1, column 20,
where `true` begins. The code `E_TYPE` names the kind of rule that the
program breaks, and the message says what the rule expects there. `build`
reports the same diagnostic and writes no executable.
[Chapter 13](diagnostics-and-cli.md) explains how to read diagnostics.

## A program with geometry

Integers alone do not show what Vastitas is for.
[`examples/pointed.vast`](https://github.com/MGYamada/Vastitas/blob/main/examples/pointed.vast)
is a preview of the geometry that later chapters teach:

```vast
{{#include ../../examples/pointed.vast}}
```

```sh
target/debug/vastitas build examples/pointed.vast -o target/pointed
./target/pointed
```

The executable prints `42`. The program builds an affine space of dimension
3 with its origin and passes the two around as one value. The type
`Point<X, Base(QQ)>` of a point names the object `X` that the point lies on.
The compiler follows that object through every call. It accepts
`preserve(X, x)` because `x` is a point of `X`, and it rejects a point of
another object, even an object of the same dimension.

You do not need to read this program yet.
[Chapter 7](indexed-geometry.md) explains objects, points and the constructs
`pack` and `unpack`.

> **What is checked.** No command accepts a program on the word of the
> frontend alone: a missing kernel, a rejected program and a failed native
> build are each an error. The kernel checks every function before it
> generates code, including a function that `main` never calls.
> [Guarantees](../language/guarantees.md#check-before-generating) states
> these rules and says what backs them.

## See also

- [Programs](../language/programs.md): source files, the two ways to give
  the compiler a program, and
  [the entry point](../language/programs.md#the-entry-point).
- [Functions](../language/functions.md) and
  [Block expressions](../language/expressions.md#block-expressions): the
  form of `main` and of its body.
- [Diagnostics](../language/diagnostics.md): the form of a diagnostic, and
  [the exit status](../language/diagnostics.md#exit-status) of the compiler.
- [Appendix A](cli.md): the commands in full.
