# Hello, Vastitas

## The smallest program

Every executable program has a function `main` that returns an `Int`:

```vast
fn main() -> Int {
    42
}
```

A block ends with its result expression, written without a semicolon. Save the
program and compile it from the repository root:

```sh
mkdir -p target
printf '%s\n' 'fn main() -> Int {' '    42' '}' > target/hello.vast
target/debug/vastitas check target/hello.vast
target/debug/vastitas build target/hello.vast -o target/hello
./target/hello
```

The program prints `42`. The generated entrypoint prints the integer that
`main` returns and exits successfully. The language itself has no strings or
I/O; printing the result is the entrypoint's job, not a language feature.

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
// Construct an object and return its associated point without losing identity.
fn make_origin(n: Nat) -> Pointed<Scheme, QQ> {
    let X = Affine(QQ, n);
    pack { scheme: X, point: origin(X) }
}

fn preserve(X: Scheme, p: Point<X, Base(QQ)>) -> Point<X, Base(QQ)> {
    apply(compose(id(X), id(X)), p)
}

fn main() -> Int {
    let problem = make_origin(3);
    unpack problem as { scheme: X, point: x };
    let y: Point<X, Base(QQ)> = preserve(X, x);
    let repacked = pack { scheme: X, point: y };
    unpack repacked as { scheme: Y, point: z };
    let checked_again = apply(id(Y), z);
    if dimension(Y) == 3 { 42 } else { 0 }
}
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

Here the declared result is `Int` but the body returns a Boolean:

```sh
printf '%s\n' 'fn main() -> Int { true }' > target/manual-bad.vast
target/debug/vastitas check target/manual-bad.vast
```

The process exits unsuccessfully and reports `E_TYPE`. Source diagnostics have
the form `FILE:LINE:COLUMN: CODE: message`. [Chapter 12](diagnostics-and-cli.md)
explains how to read them.

> **What is checked.** A missing backend, a protocol mismatch, a semantic error
> or a failed native build is an error; there is no frontend-only fallback.
> The checker's nesting and work budgets are listed in
> [Compiler limits](../appendix/limits.md). The full command contract is in the
> [core language reference](../stage0.md#compiler-behavior-and-limits), and the
> proofs about the checked core are in
> [Verification boundaries](../verification.md#stage-0-source-correspondence-and-type-safety).
