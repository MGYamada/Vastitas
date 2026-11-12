# Packages, modules and edit authority

A package holds its declarations in modules. This chapter divides a package
into modules and names declarations of other modules and of other packages by
paths. It then controls with `pub` which
declarations other modules see. The chapter ends with the rule on who may add
methods to a generic.

Modules, paths and `pub` exist only in a package, which a command reads from
its manifest with `--manifest-path`.

## Modules

The root source file of a package is its *root module*. A `mod`
declaration makes a child module. An *inline module* has its items between
braces, as in
[`examples/packages/inline-module/main.vast`](https://github.com/MGYamada/Vastitas/blob/main/examples/packages/inline-module/main.vast):

```vast
{{#include ../../examples/packages/inline-module/main.vast}}
```

`math` is a child of the root module. The `use` declaration binds the name
`next` in the root module to the function `increment` of `math`.

```sh
target/debug/vastitas check --manifest-path examples/packages/inline-module/Vastitas.toml
target/debug/vastitas build --manifest-path examples/packages/inline-module/Vastitas.toml -o target/inline-module
./target/inline-module
```

The program prints `42`.

A *file module* has its items in a file of its own. The package
[`examples/packages/module-paths`](https://github.com/MGYamada/Vastitas/tree/main/examples/packages/module-paths)
has three source files:

```text
examples/packages/module-paths/
├── Vastitas.toml
└── src/
    ├── main.vast
    ├── shapes.vast
    └── shapes/
        └── area.vast
```

The root module is `src/main.vast`:

```vast
{{#include ../../examples/packages/module-paths/src/main.vast}}
```

`mod shapes;` declares the module `shapes` and loads `src/shapes.vast`:

```vast
{{#include ../../examples/packages/module-paths/src/shapes.vast}}
```

`pub mod area;` declares a child of `shapes`. Its
[*logical path*](../appendix/glossary.md#logical-path) is `shapes::area`:
the names of the modules from the root module down to it. The compiler finds
the file of a module from its logical path, in the directory of the root
source file. For `shapes::area` the file is `src/shapes/area.vast`:

```vast
{{#include ../../examples/packages/module-paths/src/shapes/area.vast}}
```

A module can also keep its file in a directory of its own name: the file of
`shapes` is `src/shapes.vast` or `src/shapes/mod.vast`. One of the two files
must exist, and not both.
[Module declarations](../language/modules.md#module-declarations) gives the
rules.

```sh
target/debug/vastitas build --manifest-path examples/packages/module-paths/Vastitas.toml -o target/module-paths
./target/module-paths
```

The program prints `42`.

## Paths

A path names a declaration through the modules that hold it. The package
`module-paths` begins its paths in four ways:

| Path | Written in | Begins at |
| --- | --- | --- |
| `shapes::square` | The root module | The module `shapes`, a declaration of the current module |
| `self::unit` | The root module | The current module |
| `super::scale` | `shapes::area` | The parent of the current module |
| `package::unit` | `shapes` | The root module of the package |

A [*bare name*](../appendix/glossary.md#bare-name), a name without `::`,
resolves in the current module: among its declarations, the names that its
`use` declarations bind, the bindings in scope and the built-in functions.
The names of a parent module are not in scope in a child. `shapes::area`
therefore writes `super::scale()`. A bare `scale()` there is an unknown name.

A path can also begin at another package. The manifest of
[`examples/packages/demo`](https://github.com/MGYamada/Vastitas/tree/main/examples/packages/demo)
declares the package `arithmetic` as a dependency under the alias
`arithmetic`, and its root module begins two paths with that alias:

```vast
{{#include ../../examples/packages/demo/src/main.vast}}
```

`arithmetic::increment` begins at the root module of the dependency. The
inline module `pipeline` has a `use` of its own, because the names of the
root module are not in scope in it. Only the dependencies that the manifest
of a package declares have aliases in that package. A dependency of a
dependency has none. In `main`, `package` is an ordinary binding: the word
begins a path only before `::`. This program prints `42` too.

## Imports

`use p;` binds the last name of the path `p` in the current module, and
`use p as n;` binds the name `n`. The order of the declarations in a module
does not matter: a function may use a name that a later `use` binds. A `use`
names one declaration, and there are no wildcard imports.
[`use` declarations](../language/modules.md#use-declarations) and
[Resolution](../language/names-and-paths.md#resolution) give the rules.

## Visibility

A declaration without `pub` is private: its own module and the modules below
it see it. In `module-paths`, `scale` is
private in `shapes`, and the child `shapes::area` calls it. `unit` is private
in the root module, so every module of the package can name it as
`package::unit`.

A declaration with `pub` is public: every module that can reach its module
sees it. A path from outside needs
`pub` at each step, on each module that it passes through and on the
declaration that it names:

```vast
{{#include ../../examples/reject/packages/private-function/main.vast}}
```

```text
{{#include ../../examples/reject/packages/private-function.stderr}}
```

A `pub use` declaration is a
[*reexport*](../appendix/glossary.md#reexport): it makes a public
declaration of another module visible through the current module. It cannot
reexport a private declaration. The library package
[`examples/packages/arithmetic`](https://github.com/MGYamada/Vastitas/tree/main/examples/packages/arithmetic),
which `demo` depends on, keeps its declarations in the module `scalar`:

```vast
{{#include ../../examples/packages/arithmetic/src/scalar.vast}}
```

Its root module reexports two of them:

```vast
{{#include ../../examples/packages/arithmetic/src/lib.vast}}
```

`scalar` is a private module. Another package names the function as
`arithmetic::increment`, through the reexport. The path
`arithmetic::scalar::increment` is an error there, because it passes through
the private module. [Visibility](../language/names-and-paths.md#visibility)
gives the rules.

## Owners

Every declaration has an [*owner*](../appendix/glossary.md#owner): its
package, the logical path of its module and its name. A path, an alias or a
reexport names the declaration and does not make another one. In `demo`,
`next` and `arithmetic::increment` are the same function, the one that the
module `scalar` of `arithmetic` declares. Both branches of the `if` in its
`main` are therefore one definition, and the `if` has one static target.

Two declarations with the same name in different modules are different
declarations, with different owners.

## Edit authority

An import lets a module call a generic. It does not let the module add a
method. [*Edit authority*](../appendix/glossary.md#edit-authority) is the
right to add methods to a generic, and the module that defines the generic
holds it:

```vast
{{#include ../../examples/reject/packages/foreign-method/main.vast}}
```

```text
{{#include ../../examples/reject/packages/foreign-method.stderr}}
```

The generic `size` belongs to the module `scalar`, and the second method is
in the root module. A child of the defining module has no edit authority
either, and neither `pub` nor a path gives it. The members of an abstract
type follow the same rule: only the module that defines an abstract type
places scalar types in it with `subtype`.
[Owners](../language/edit-authority.md#owners) gives the rules.

The rule keeps the methods of a generic in one module. An import therefore
never changes which method a call selects.

A module can still let another module, or another package, add methods. It
states this permission in a declaration of its own, and the program applies
it in one place. The next chapter,
[Edit authority across packages](edit-authority.md), shows how.

> **What is checked.** The checker resolves every path and assigns every
> owner itself, from the package, the module and the name of each
> declaration. It rejects a path through a private declaration and a method
> outside the defining module. The
> [proofs](../verification.md#package-namespace-acceptance) are about the
> records of this resolution. Each reference that the checker records
> resolves again, through the checker's own resolver, to the recorded
> declaration. An alias names the declaration itself. The generic of each
> method is a declaration of the method's own module. No theorem ties these
> records to the names in the source of a program, and none covers the
> reading of manifests and source files. Tests cover the diagnostics and native execution.

## See also

- [Modules](../language/modules.md): `mod` and `use` declarations, the files
  of modules and reexports.
- [Names and paths](../language/names-and-paths.md): how a path resolves, and
  [Visibility](../language/names-and-paths.md#visibility).
- [Packages](../packages.md): manifests, dependency aliases and the package
  graph.
- [Owners](../language/edit-authority.md#owners): owners and the module that
  may add methods.
- [Abstract types](../stage1a.md#abstract-types): which module may declare
  the members of an abstract type.
