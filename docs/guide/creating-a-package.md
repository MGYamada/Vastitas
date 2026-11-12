# Creating a package

A single file is enough for a first program. A
[*package*](../appendix/glossary.md#package) is a directory that holds a
program or a library: a description of the package and its source files.
Packages can use one another, and the features of later chapters that
organize a larger program exist only in packages. This section creates a
package, builds it and gives it a dependency.

## A package of one file

The package
[`examples/packages/hello`](https://github.com/MGYamada/Vastitas/tree/main/examples/packages/hello)
has two files:

```text
hello/
├── Vastitas.toml
└── src/
    └── main.vast
```

No command creates a package. Make the directory and write both files.
`Vastitas.toml` is the [*manifest*](../appendix/glossary.md#manifest), the
file that describes the package:

```toml
{{#include ../../examples/packages/hello/Vastitas.toml}}
```

The table `[package]` has three keys, and a manifest needs all three:

- `name` is the name of the package.
- `version` is its version, in the form of Semantic Versioning, such as
  `0.1.0`.
- `root` is the root source file, the file where the compiler starts
  reading. Its path starts at the directory of the manifest.

The root source file holds the program of the previous section:

```vast
{{#include ../../examples/packages/hello/src/main.vast}}
```

## Checking and building a package

The option `--manifest-path` names the manifest:

```sh
target/debug/vastitas check --manifest-path examples/packages/hello/Vastitas.toml
target/debug/vastitas build --manifest-path examples/packages/hello/Vastitas.toml -o target/hello-package
./target/hello-package
```

```text
checked examples/packages/hello/Vastitas.toml
built target/hello-package
42
```

The compiler does not search for a manifest, so every command on a package
names its manifest. A command that names a manifest runs in
[*manifest mode*](../appendix/glossary.md#manifest-mode). A command that
names a source file, as in the previous section, runs in
[*flat mode*](../appendix/glossary.md#flat-mode). One command cannot do
both.

## A library package

A package without `main` is a library: it holds functions for other packages.
[`examples/packages/dependency/answers`](https://github.com/MGYamada/Vastitas/tree/main/examples/packages/dependency/answers)
is one. Its manifest names `src/lib.vast` as the root, and that file holds
one function:

```vast
{{#include ../../examples/packages/dependency/answers/src/lib.vast}}
```

`pub` makes the function [*public*](../appendix/glossary.md#public), so
that other packages can name it. A function without `pub` is
[*private*](../appendix/glossary.md#private). `check` accepts a library,
and `build` does not, because a library has no entry point:

```sh
target/debug/vastitas check --manifest-path examples/packages/dependency/answers/Vastitas.toml
```

## Depending on a package

[`examples/packages/dependency/ask`](https://github.com/MGYamada/Vastitas/tree/main/examples/packages/dependency/ask)
is a program that uses the library. Its manifest has a second table:

```toml
{{#include ../../examples/packages/dependency/ask/Vastitas.toml}}
```

Each line of `[dependencies]` declares one dependency. The name on the left,
here `answers`, is the
[*dependency alias*](../appendix/glossary.md#dependency-alias): the name
that this package gives to the other one. It need not be the `name` of that
package. `path` is the directory of the other manifest, and it starts at the
directory of this manifest.

The root source file imports the function and calls it:

```vast
{{#include ../../examples/packages/dependency/ask/src/main.vast}}
```

`answers::answer` is a [*path*](../appendix/glossary.md#path): the dependency
alias, then the name of a public function of that package's root file.
`use` imports the function, so that the rest of the file can write `answer`
alone. `answer()` is a call: the name of a function and its arguments in
parentheses, of which this function has none.

```sh
target/debug/vastitas build --manifest-path examples/packages/dependency/ask/Vastitas.toml -o target/ask
./target/ask
```

The executable prints `42`. The compiler reads the manifest of `ask`, follows
its dependencies and checks every package that it reaches. It checks all of
each package, including functions that the program never calls.

`pub` and `use` belong to packages. A program in flat mode has neither, and
the compiler rejects them there with a message that points you to a package.

## When a package is rejected

A function that another package uses must be public. In
[`examples/reject/packages/private-dependency`](https://github.com/MGYamada/Vastitas/tree/main/examples/reject/packages/private-dependency)
the library forgets `pub`:

```vast
{{#include ../../examples/reject/packages/private-dependency/answers/lib.vast}}
```

The program is the one above:

```vast
{{#include ../../examples/reject/packages/private-dependency/main.vast}}
```

```sh
target/debug/vastitas check --manifest-path examples/reject/packages/private-dependency/Vastitas.toml
```

```text
{{#include ../../examples/reject/packages/private-dependency.stderr}}
```

The diagnostic points to the `use` declaration, the place where the program
names the private function. For a package, the compiler prints the absolute
path of the file. The book shows such a path from the root of the
repository.

A mistake in a manifest has a diagnostic of another form. This manifest has
a key that the compiler does not know:

```toml
{{#include ../../examples/reject/packages/unknown-manifest-key/Vastitas.toml}}
```

```sh
target/debug/vastitas check --manifest-path examples/reject/packages/unknown-manifest-key/Vastitas.toml
```

```text
{{#include ../../examples/reject/packages/unknown-manifest-key.stderr}}
```

The first line names the manifest and gives the code `E_MANIFEST`. The lines
after it show the place in the file and the keys that `[package]` accepts.

## What a package does not do

A dependency is always a directory on your machine. The compiler has no
registry of packages, downloads nothing and compares no versions. It also
keeps nothing between two commands: each command reads and checks every
package again.

A package can hold more than one source file.
[Chapter 6](modules-and-authority.md) divides a package into modules and
explains paths, imports and visibility in full.

## See also

- [Packages](../packages.md): [manifests](../packages.md#manifests),
  [the package graph](../packages.md#the-package-graph) and
  [the commands](../packages.md#commands).
- [Programs](../language/programs.md): flat mode, manifest mode and the
  entry point of a package.
- [`use` declarations](../language/modules.md#use-declarations),
  [Resolution](../language/names-and-paths.md#resolution) and
  [Visibility](../language/names-and-paths.md#visibility): the rules of
  imports, of a path that begins with a dependency alias, of `pub` and of
  private items.
- [Kinds of items](../language/items.md#kinds-of-items): the items that
  exist only in a package.
- [Calls](../language/functions.md#calls): the rules of a call.
- [Diagnostics](../language/diagnostics.md): the form of a diagnostic of a
  manifest.
