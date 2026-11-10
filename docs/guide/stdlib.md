# The standard library

The [*standard library*](../appendix/glossary.md#standard-library) is the
package in the directory
[`stdlib`](https://github.com/MGYamada/Vastitas/tree/main/stdlib) of the
repository. It is written in Vastitas, and the compiler checks it like every
other package. No program receives it automatically: a program names the
library as a dependency, or names its files on the command line.
<a id="a-manifest"></a>[Creating a package](creating-a-package.md) explains
manifests and dependencies.

## What the library holds

The library keeps its declarations in
[*modules*](../appendix/glossary.md#module), named parts of a package, which
[Chapter 6](modules-and-authority.md) explains. A path such as
`std::arithmetic::integers` names a module through the modules that hold it.

| Module | Content | Chapter |
| --- | --- | --- |
| `std::arithmetic` | Functions on `Int` and on `Nat`, and generic functions over both | This section, and [Chapter 4](dispatch.md) |
| `std::geometry` | Objects, points and morphisms, presented affine geometry, smooth geometry and metrics | Chapters [7](indexed-geometry.md), [8](affine-geometry.md) and [9](smooth-geometry.md) |
| `std::differential` | Pullbacks and differentials of smooth maps | [Chapter 9](smooth-geometry.md) |

The name `std` is the dependency alias that the examples of this book give
to the library.

## Using the standard library

The package
[`examples/packages/stdlib-arithmetic`](https://github.com/MGYamada/Vastitas/tree/main/examples/packages/stdlib-arithmetic)
depends on the library:

```toml
{{#include ../../examples/packages/stdlib-arithmetic/Vastitas.toml}}
```

The path leads from the directory of this manifest to the directory
`stdlib`.

One step comes before the first use. A script generates the source files of
the library's package from the library's sources:

```sh
python3 scripts/build_stdlib_package.py
```

Run the script once in a checkout or in an unpacked crate, and again after
you change the sources of the library. Without the generated file, the
compiler reports that it cannot read a file of the library.

The program calls two functions of the module `std::arithmetic::integers`:

```vast
{{#include ../../examples/packages/stdlib-arithmetic/main.vast}}
```

Each `use` names one function by its path: the alias `std`, the modules
`arithmetic` and `integers`, and the function. `int_sub(8, 50)` is the
difference `-42`, and `int_abs` returns its absolute value.

```sh
target/debug/vastitas build --manifest-path examples/packages/stdlib-arithmetic/Vastitas.toml -o target/stdlib-arithmetic
./target/stdlib-arithmetic
```

The executable prints `42`. The compiler checks the whole library with the
program, as it checks every dependency.

## Flat mode with `--lib`

The arithmetic files of the library also work without a package. In flat
mode, the option `--lib` adds a file to the program. A file that is added in
this way is a library of the program.
[`examples/book/programs/flat-library.vast`](https://github.com/MGYamada/Vastitas/blob/main/examples/book/programs/flat-library.vast)
is the program above without its `use` declarations:

```vast
{{#include ../../examples/book/programs/flat-library.vast}}
```

```sh
target/debug/vastitas build examples/book/programs/flat-library.vast \
  --lib stdlib/src/arithmetic/int.vast -o target/flat-library
./target/flat-library
```

The executable prints `42`. In flat mode every function of every file is
visible in every other file, so the program calls `int_sub` without an
import. The program holds only the files that the command names. Without
the option, the compiler does not know `int_sub`.

`--lib` may appear several times, and `check` takes it too. The entry file
holds `main`, and a library does not. This mode needs no generated file.

| File | Functions |
| --- | --- |
| [`stdlib/src/arithmetic/int.vast`](https://github.com/MGYamada/Vastitas/blob/main/stdlib/src/arithmetic/int.vast) | `int_add`, `int_sub`, `int_mul`, `int_neg`, `int_abs`, `int_min`, `int_max` |
| [`stdlib/src/arithmetic/nat.vast`](https://github.com/MGYamada/Vastitas/blob/main/stdlib/src/arithmetic/nat.vast) | `nat_add`, `nat_sub`, `nat_mul`, `nat_min`, `nat_max`, `nat_to_int` |

In a package the same functions are in the modules
`std::arithmetic::integers` and `std::arithmetic::naturals`.
[Chapter 2](values-and-functions.md) explains the two integer types `Int`
and `Nat`.

## See also

- [Flat mode](../language/programs.md#flat-mode): the rules of `--lib` and
  of the files of a flat program.
- [Packages](../packages.md): manifests, dependencies and the commands.
- [Names and paths](../language/names-and-paths.md): paths such as
  `std::arithmetic::integers::int_sub`.
- [The standard library's README](https://github.com/MGYamada/Vastitas/blob/main/stdlib/README.md):
  its modules and functions.
- [The geometry library](https://github.com/MGYamada/Vastitas/blob/main/stdlib/src/geometry/README.md):
  the modules under `std::geometry`.
