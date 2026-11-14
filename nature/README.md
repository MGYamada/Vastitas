# Vastitas `nature`

The `nature` package, `vastitas_nature`, holds the physical interpretations
of the mathematical objects of the standard library `std`: declared
identifications, conventions and hypotheses that give a `std` object its
meaning in the world
([ADR 0002](https://github.com/MGYamada/Vastitas/blob/main/docs/adr/0002-nature-dimension.md)).
It owns no mathematics. Every value and law that it uses is that of a `std`
object, and a check that it adds is a consistency check of an
interpretation, not a mathematical result.

## API reference

[`docs/`](docs/README.md) has one page for each public module: its package
and source, what it is for, every exported name with its contract, the
tested examples that use it, and the sections of the book and the
specifications that hold its rules and proofs.
`python3 scripts/library_docs.py` checks that each page lists exactly the
exports of its module.

| Module | Page |
| --- | --- |
| `nature` | [The package root](docs/README.md#the-package-root) |
| `nature::dimension` | [`dimension.md`](docs/dimension.md) |

## The boundary with `std`

- `nature` depends on `std`. Its manifest names the standard library at
  `../stdlib`, as applications do.
- `std` never depends on `nature`. No manifest under `stdlib/` depends on a
  package outside `stdlib/`, and no manifest under `nature/` depends on a
  package outside `stdlib/` and `nature/`. `scripts/check_boundaries.py`
  checks both rules.
- A `nature` declaration never changes the validity or the generated code of
  a `std` declaration or of a binding.

## Source layout

The sources follow the layout of `stdlib/`: they live under `src/`, with a
directory per module and `mod.vast` as its entrypoint. The package root
[`src/mod.vast`](src/mod.vast) declares the modules, and
[`src/dimension/mod.vast`](src/dimension/mod.vast) is `nature::dimension`.
The API reference lives under [`docs/`](docs/README.md). A module of
`nature` is a module of the one package `vastitas_nature`, not a package of
its own as the libraries of `stdlib/src/` are: such a package would have to
be exposed under its name by a dependency alias or by `use … as`, and the
name `dimension` is reserved for both.

## Use

Generate the standard-library package once from the repository root, then
depend on both packages by path:

```sh
python3 scripts/build_stdlib_package.py
```

```toml
[dependencies]
std = { path = "../Vastitas/stdlib" }
nature = { path = "../Vastitas/nature" }
```

The application and `nature` then reach one `std` package, because a package
is identified by the canonical location of its manifest. A copy of the
standard library at another location is another package, and a `nature`
package that depends on a copy does not accept the objects of the original.
The [page of `nature::dimension`](docs/dimension.md#use) lists the tested
packages that depend on both, and the book says
[how a program imports the module](https://github.com/MGYamada/Vastitas/blob/main/docs/language/physical-dimensions.md#the-library-naturedimension).
