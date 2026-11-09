# Packages

A **package** is a directory with a manifest, `Vastitas.toml`, a root source
file and the [modules](language/modules.md) under it. In
[manifest mode](language/programs.md#manifest-mode) the compiler checks the
package of one manifest together with every package that it depends on.

## Manifests

A manifest is a TOML file. This one declares the package `demo`, which depends
on the package in `../arithmetic` under the alias `arithmetic`:

```toml
{{#include ../examples/packages/demo/Vastitas.toml}}
```

| Table and key | Value |
| --- | --- |
| `[package]` `name` | The name of the package, a nonempty string |
| `[package]` `version` | The version of the package, in Semantic Versioning |
| `[package]` `root` | The root source file, relative to the manifest |
| `[dependencies]` *alias* `= { path = "…" }` | A dependency: the directory of its manifest, relative to the declaring manifest, under an alias |
| `[geometry_compat]` | The [geometry compatibility export](#geometry-compatibility-exports), optional |

Rules:

- The manifest file must be named `Vastitas.toml`. Another name is an error
  (`E_INPUT`).
- `name`, `version` and `root` are required. A missing key, an unknown key or
  table, and a dependency in another form than `{ path = "…" }` are errors
  (`E_MANIFEST`).
- An empty `name` is an error (`E_MANIFEST`), and so is a `version` that is not
  a Semantic Versioning version.
- `root` must name a file inside the package directory whose name ends in
  `.vast`. Another file is an error (`E_INPUT`).
- A dependency alias must be an ASCII identifier that is not a
  [reserved name](language/lexical-structure.md#reserved-names) and not `mod`,
  `use`, `pub`, `self`, `super` or `package`. Another alias is an error
  (`E_MANIFEST`).
- A dependency path must name a directory that holds a `Vastitas.toml`.
  Another path is an error (`E_INPUT`).
- A dependency alias must not collide with a declaration or a `use` of the root
  module of its package (`E_DUPLICATE`).

## The package graph

The packages that the root manifest reaches through its dependencies form the
**package graph** of the program. The identity of a package is the canonical
location of its manifest together with its name and version. One manifest that
two aliases reach is one package. Two packages with the same name and version
at different locations are different packages.

Rules:

- The package graph must not have a cycle. A cycle is an error (`E_CYCLE`).
- The depth of dependencies has a limit, which
  [Appendix D](appendix/limits.md#checker-limits) gives (`E_LIMIT`).
- Only path dependencies exist. There is no registry, no download from Git, no
  version solving, no choice of several build targets and no compilation
  cache.
- The compiler reads every input and checks every package of the graph on
  every command, including packages and declarations that the program never
  uses.

> **Implementation note.** The Rust driver loads the manifests and source files
> and sends the package graph to the Lean kernel. The kernel rebuilds the
> graph, assigns every owner and resolves every path itself; the driver
> supplies no trusted owner or target.
> [Package namespace acceptance](verification.md#package-namespace-acceptance)
> states what is proved about these checks.

## Commands

`vastitas check --manifest-path DIR/Vastitas.toml` checks the program of a
manifest, and `vastitas build --manifest-path DIR/Vastitas.toml -o OUTPUT`
builds it:

```sh
vastitas check --manifest-path examples/packages/demo/Vastitas.toml
vastitas build --manifest-path examples/packages/demo/Vastitas.toml -o target/demo
./target/demo
```

The executable prints `42`.

Rules:

- The compiler looks for no manifest of its own accord. A manifest is named
  with `--manifest-path`.
- The entry point of a build is the `main` of the root module of the root
  package, as [The entry point](language/programs.md#the-entry-point) says. A
  `main` in a dependency or in a child module, also an imported one, is not the
  entry point.

## Geometry compatibility exports

The optional `[geometry_compat]` table of a manifest maps the syntax of the
[geometric core](language/geometric-types.md), such as `Point<X, Base(QQ)>`
and `origin(X)`, to `indexed` declarations of that package, for a program in
manifest mode. Its `scheme` and `smooth` subtables map the two settings.
[Legacy geometry syntax in packages](indexed-source.md#legacy-geometry-syntax-in-packages)
gives its rules.

Rules:

- The kernel resolves every path of the table in the root module of the
  exporting package and checks every export. It trusts no owner, capability or
  validity claim from the manifest.
- A program that uses the core geometry syntax in manifest mode must have
  exactly one valid export in its package graph. Qualified indexed syntax needs
  none.

The standard library is the package of `stdlib/Vastitas.toml`. Its
[README](https://github.com/MGYamada/Vastitas/blob/main/stdlib/README.md)
lists its packages and modules.

## Moved sections

The sections of this chapter on modules, paths, visibility and edit authority
are separate chapters. These anchors keep older links working.

- <a id="manifest-and-commands"></a>Manifest and commands: [Manifests](#manifests) and [Commands](#commands).
- <a id="modules-and-paths"></a>Modules and paths: [Modules](language/modules.md) and [Names and paths](language/names-and-paths.md).
- <a id="visibility-and-ownership"></a>Visibility and ownership: [Visibility](language/names-and-paths.md#visibility) and [Owners](language/edit-authority.md#owners).
- <a id="validation-and-boundary"></a>Validation and boundary: [Package namespace acceptance](verification.md#package-namespace-acceptance).
- <a id="finite-abstract-declarations"></a>Finite abstract declarations: [Abstract types](stage1a.md#abstract-types).
- <a id="explicit-edit-authority"></a><a id="edit-borrowing"></a><a id="scoped-edit-borrowing-and-validated-assemblies"></a>Edit borrowing: [Edit authority](language/edit-authority.md).
- <a id="source-declarations"></a>Source declarations: [Grants and delegations](language/edit-authority.md#grants-and-delegations), [Contributions](language/edit-authority.md#contributions) and [Assemblies](language/edit-authority.md#assemblies).
- <a id="edit-borrowing--migrating-recipients-for-v010"></a>Migrating recipients: [Source migrations](appendix/history.md#source-migrations).
- <a id="state-and-completion"></a>State and completion: [Assemblies](language/edit-authority.md#assemblies) and [Sealing](language/edit-authority.md#sealing).
- <a id="wire-extension"></a>Wire extension: [Scoped edits and assembly](protocol.md#protocol-5-scoped-edits-and-assembly).
- <a id="edit-authority"></a><a id="nested-edit-loans-and-permanent-authority-transfer"></a>Nested loans and transfer: [Edit authority](language/edit-authority.md).
- <a id="explicit-delegation"></a>Explicit delegation: [Grants and delegations](language/edit-authority.md#grants-and-delegations).
- <a id="permanent-transfer"></a>Permanent transfer: [Transfers](language/edit-authority.md#transfers).
- <a id="completion-provenance-and-proof-boundary"></a>Completion, provenance and proof boundary: [Sealing](language/edit-authority.md#sealing) and [Edit authority acceptance](verification.md#edit-authority-acceptance-protocol-6).
- <a id="indexed-geometry-compatibility-exports"></a>Indexed geometry compatibility exports: [Geometry compatibility exports](#geometry-compatibility-exports).
