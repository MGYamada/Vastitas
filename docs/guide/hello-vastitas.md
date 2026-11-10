# Hello, Vastitas

## The smallest program

Every executable program has a function `main` that returns an `Int`.
[`examples/book/programs/hello.vast`](https://github.com/MGYamada/Vastitas/blob/main/examples/book/programs/hello.vast)
holds the smallest one:

```vast
{{#include ../../examples/book/programs/hello.vast}}
```

A block ends with its result expression, written without a semicolon. Compile
the program from the repository root:

```sh
mkdir -p target
target/debug/vastitas check examples/book/programs/hello.vast
target/debug/vastitas build examples/book/programs/hello.vast -o target/hello
./target/hello
```

The program prints `42`. The generated entry point prints the integer that
`main` returns and exits successfully. The language itself has no strings or
I/O; printing the result is the entry point's job, not a language feature.

## `check` and `build`

The two commands share the same front half:

- `vastitas check FILE` parses and resolves the source in Rust, then sends it to
  the Lean kernel for independent checking. It needs neither a C compiler nor a
  `main` function, so it also checks libraries.
- `vastitas build FILE -o OUTPUT` also requires `fn main() -> Int`. It emits Lean
  into a temporary Lake project and builds a native executable for the host.

`build` installs the output only after native compilation succeeds. A failed
build leaves an existing output file untouched. Compilation never runs the
generated program.

## A program with geometry

[`examples/pointed.vast`](https://github.com/MGYamada/Vastitas/blob/main/examples/pointed.vast)
is a little larger. It constructs a geometric object, returns it together with a
point on it, and checks that the point still belongs to that object:

```vast
{{#include ../../examples/pointed.vast}}
```

```sh
target/debug/vastitas check examples/pointed.vast
target/debug/vastitas build examples/pointed.vast -o target/pointed
./target/pointed
```

The executable prints `42`. When `main` opens the package with `unpack`, the
checker still knows which object `x` belongs to. The type `Point<X, Base(QQ)>`
names that object, so `preserve(X, x)` type-checks and a point from any other
object would not. [Chapter 7](indexed-geometry.md) explains objects, points and
packages.

## When the checker says no

In
[`examples/reject/types/bool-result.vast`](https://github.com/MGYamada/Vastitas/blob/main/examples/reject/types/bool-result.vast)
the declared result is `Int` but the body returns a Boolean:

```vast
{{#include ../../examples/reject/types/bool-result.vast}}
```

```sh
target/debug/vastitas check examples/reject/types/bool-result.vast
```

The process exits unsuccessfully and prints one diagnostic:

```text
{{#include ../../examples/reject/types/bool-result.stderr}}
```

Source diagnostics have the form `FILE:LINE:COLUMN: CODE: message`.
[Chapter 12](diagnostics-and-cli.md) explains how to read them.

> **What is checked.** A missing backend, a protocol mismatch, a semantic error
> or a failed native build is an error; there is no frontend-only fallback.
> The checker's nesting and work budgets are listed in
> [Compiler limits](../appendix/limits.md). The full command contract is in the
> [CLI reference](cli.md), and the
> proofs about the checked core are in
> [Verification boundaries](../verification.md#stage-0-source-correspondence-and-type-safety).
