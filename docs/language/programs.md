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
{{#include ../../examples/stdlib-arithmetic.vast}}
```

```sh
target/debug/vastitas build examples/stdlib-arithmetic.vast \
  --lib stdlib/src/arithmetic/int.vast \
  --lib stdlib/src/arithmetic/nat.vast -o target/stdlib-arithmetic
```

The executable prints `42`.

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
executable evaluates `main`, prints the resulting integer in decimal followed
by a line feed, and exits with status 0. The language has no other input or
output. The compiler checks every function of a program, whether or not `main`
calls it, before it generates any code.

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

`main` in this program returns `-42`, so the executable prints `-42`:

```vast
{{#include ../../examples/book/expressions/saturating-subtraction.vast}}
```
