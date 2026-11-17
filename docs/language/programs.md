# Programs

A **program** is the set of source files that the compiler checks together, its
compilation unit. A program comes from one of two inputs:

- **Flat mode**: an entry file and the library files that `--lib` names, as in
  `vastitas check app.vast --lib lib.vast`.
- **Manifest mode**: a package manifest, as in
  `vastitas check --manifest-path Vastitas.toml`. The manifest names the root
  source file and the packages it depends on. [Packages](../packages.md)
  describes manifests and modules.

`vastitas check` checks a program. `vastitas build` checks it and then builds a
native executable from its entry point. [Appendix A](../guide/cli.md) describes
the commands.

## Source files

> **Syntax**
>
> ```text
> SourceFile -> Item*
> ```

A source file is a sequence of [items](items.md).

Rules:

- The compiler parses each file on its own. An item must end in the file where
  it begins. An item that reaches the end of its file is an error (`E_PARSE`).
- Items are declared at the top level of a file or of a
  [module](modules.md). A `let` binding outside a function is an error
  (`E_PARSE`).

## Flat mode

In flat mode the entry file and its libraries form one namespace. Every
function of every file is visible in every other file, in both directions.
Flat mode has no modules, imports or visibility; [Items](items.md#kinds-of-items)
lists the items that it accepts.

Rules:

- Each input must name a file whose name ends in `.vast`. Another input is an
  error (`E_INPUT`). The compiler does not expand a directory.
- A library path is relative to the working directory of the command.
- Each file must be supplied once. A file supplied twice, even as both the
  entry file and a library, is an error (`E_INPUT`).
- The items of all files share one namespace, so the rule of
  [Names of items](items.md#names-of-items) on equal names applies across
  files.
- A library must not define `main`. A function `main` in a library is an
  error (`E_LIBRARY`) when no other file defines one.
- When two files define a function `main`, such as the entry file and a
  library, the rule on equal names reports the second one
  (`E_DUPLICATE`), and the compiler reports no `E_LIBRARY`.
- A program contains only the files that the command names. The compiler
  loads no library without a `--lib` option.
- Flat mode and `--manifest-path` must not be combined. Both together are an
  error (`E_USAGE`).

The standard library supplies flat libraries for exact arithmetic, such as
`stdlib/src/arithmetic/int.vast`, which its
[README](https://github.com/MGYamada/Vastitas/blob/main/stdlib/README.md)
lists. This program calls `int_add` from that library:

```vast
{{#include ../../examples/book/stdlib/stdlib-arithmetic.vast}}
```

```sh
target/debug/vastitas build examples/book/stdlib/stdlib-arithmetic.vast \
  --lib stdlib/src/arithmetic/int.vast \
  --lib stdlib/src/arithmetic/nat.vast -o target/stdlib-arithmetic
```

The executable writes `int_abs(int_neg(answer)) = 42` and
`nat_sub(nat_add(2, 3), 8) = 0`, and exits with status 0.

## Manifest mode

In manifest mode the manifest names a root source file, and the
[modules](modules.md) of each package form a tree under it. The **root
package** is the package of the manifest that the command names. Names are
visible across modules through `use` imports and `pub` visibility.
[Packages](../packages.md) gives the rules of manifests and of the package
graph.

Rules:

- A program contains only the packages that its manifests name.
- Neither mode has an implicit prelude: the compiler adds no library and no
  import to a program.

## The entry point

The **entry point** of a program is the function `main` of its entry file in
flat mode, or of the root module of its root package in manifest mode. An
executable evaluates `main` and exits with the **exit status** of its result:
the `Int` result modulo 256, which is never negative, as in C and POSIX. The
executable writes nothing for the result. A program returns 0 on success. The
only other output of a program is the lines of
[`show!`](#showing-values-with-show), on standard error. The compiler checks every function of a
program, whether or not `main` calls it, before it generates any code.

Rules:

- The entry point must have the signature `fn main() -> Int`. Another
  signature is an error (`E_MAIN`). In manifest mode, a function named `main`
  in another module is an ordinary function.
- A [generic](../stage1a.md#generic-declarations) named `main` is an error (`E_MAIN`)
  in flat mode and in the root module of the root package.
- `vastitas build` requires an entry point. A program without one is an error
  (`E_MAIN`). `vastitas check` accepts a program without an entry point, such
  as a library.
- In manifest mode the entry point may also be a resource function
  `resource fn main() -> Int`, under the rules of
  [Resource functions](../storage/resource-programs.md#resource-functions).
  Its `Int` result is the exit status in the same way.
- The exit status of the result `r` is the remainder of `r` divided by 256
  that lies in 0 to 255: 300 gives 44, and −1 gives 255.
- An error at run time, such as a failed `expect`, stops the executable with
  a message on standard error and a nonzero exit status.

In this program `main` returns `0` when the subtraction stops at zero, after
it shows the difference:

```vast
{{#include ../../examples/book/expressions/saturating-subtraction.vast}}
```

The executable writes `n - 5 = 0` and exits with status 0.

## Showing values with `show!`

> **Syntax**
>
> ```text
> ShowStatement -> `let` IDENTIFIER ( `:` Type )? `=` `show` `!` `(` Expression `)` `;`
> ```

`let x = show!(e);` at the top level of the body of `main` is a
[`let` statement](statements.md#let-statements) that binds `x` to the value of
`e`, and the executable writes the **label** of `e`, ` = `, the value and a line
feed on standard error when it binds `x`. The label is the source text of `e`,
with each run of whitespace replaced by one space and without leading or
trailing whitespace. `show!` is built into the compiler: it has no
declaration and no other form.

Rules:

- `show!` may stand only as the whole initializer of a `let` statement at the
  top level of the body of the entry point `fn main`. `show!` anywhere else,
  such as in another function, in a nested block, in a function expression, in
  an argument, in an operand or as the result of `main`, is an error
  (`E_UNSUPPORTED`).
- `show!` in a resource entry point `resource fn main` is an error
  (`E_UNSUPPORTED`).
- Any other macro invocation `name!(…)` is an error (`E_UNSUPPORTED`). There are
  no user macros.
- The value must have type `Int`, `Nat`, `Bool`, `Unit` or `Pair<T>`. A value of
  another type, including a function value or an object, is an error
  (`E_TYPE`), and the message names the type.
- `Int` and `Nat` values are written in decimal, `Bool` values as `true` or
  `false`, the `Unit` value as `()`, and a `Pair<T>` as `(a, b)`.
- The executable writes the lines in the order of the `let` statements, and
  evaluates each shown expression once. The binding has the value and the type
  of the expression, as without `show!`.
- The lines go to standard error, and the executable writes nothing to
  standard output. Standard output stays free for the output of the program.
- The label is presentation only. It never decides whether a program is
  accepted.
- `vastitas check` checks `show!` like the rest of the program and writes no
  line of it.
- A flat program that uses `show!` may use the legacy geometry of flat mode,
  such as `Scheme`, `Point`, `pack` or `Affine`, as a flat program without
  it does. A value of such a type is not shown (`E_TYPE`). In manifest mode,
  a package program that uses `show!` has geometry only from a
  `geometry_compat` export or an `indexed` profile, as in
  [Indexed declarations](../indexed-source.md). Such a program that uses a
  legacy form such as `Affine(QQ, 2)` without a `geometry_compat` export is an
  error at the legacy form (`E_TYPE`), with a note that names `show!` as the
  cause.

```vast
{{#include ../../examples/book/functions/calls.vast}}
```

The executable writes `add_twice(2, 20) = 42` and exits with status 0.

> **Implementation note.** A program that uses `show!` is sent to the kernel
> with an `observations` field on `main`
> ([The wire protocol](../protocol.md#observations-of-show)); a flat program
> becomes the root module of one package. The kernel checks the observations again: only the entry point
> has them, each names a top-level `let` of its body in order, and each value
> has a displayable type. Core stays pure: the observations are metadata of the
> entry point, and only code generation sequences the writes.
