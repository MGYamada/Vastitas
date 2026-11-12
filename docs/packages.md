# Packages

A **package** is a directory with a manifest, `Vastitas.toml`, a root source
file and the [modules](language/modules.md) under it. In
[manifest mode](language/programs.md#manifest-mode) the compiler checks the
package of one manifest together with every package that it depends on. The
standard library is the package of `stdlib/Vastitas.toml`. Its
[README](https://github.com/MGYamada/Vastitas/blob/main/stdlib/README.md)
lists its packages and modules.

## Manifests

A manifest is a TOML file with these tables and keys:

| Table and key | Value |
| --- | --- |
| `[package]` `name` | The name of the package, a nonempty string |
| `[package]` `version` | The version of the package, in Semantic Versioning |
| `[package]` `root` | The root source file. A relative path starts at the directory of the manifest |
| `[dependencies]` *alias* `= { path = "…" }` | A dependency under an alias: the directory of its manifest. A relative path starts at the directory of the declaring manifest |
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
- A dependency alias must be an ASCII
  [identifier](language/lexical-structure.md#identifiers) that is not a
  [reserved name](language/lexical-structure.md#reserved-names) and not
  `package`. Another alias, such as a keyword, is an error (`E_MANIFEST`).
- A dependency path must name a directory that holds a `Vastitas.toml`.
  Another path is an error (`E_INPUT`).
- Every module of a package may begin a path with a dependency alias of the
  package. An alias must not collide with a declaration or a `use` of any
  module of its package (`E_DUPLICATE`).

This manifest declares the package `demo`, which depends on the package in
`../arithmetic` under the alias `arithmetic`:

```toml
{{#include ../examples/packages/demo/Vastitas.toml}}
```

## The package graph

The manifest that a command names is the **root manifest**, and its package is
the [root package](language/programs.md#manifest-mode). The packages that the
root manifest reaches through its dependencies form the
**package graph** of the program. The identity of a package is the canonical
location of its manifest together with its name and version. One manifest that
two aliases reach is one package. Two packages with the same name and version
at different locations are different packages.

Rules:

- The package graph must not have a cycle. A cycle is an error (`E_CYCLE`).
- The depth of dependencies has a limit, which
  [Appendix D](appendix/limits.md#inputs) gives (`E_LIMIT`).
- Only path dependencies exist. There is no registry, no download from Git, no
  version solving, no choice of several build targets and no compilation
  cache.
- The compiler reads every input and checks every package of the graph on
  every command, including packages and declarations that the program never
  uses.

> **Implementation note.** The frontend loads the manifests and source files
> and sends the package graph to the Lean kernel. The kernel rebuilds the
> graph, assigns every owner and resolves every path itself; the frontend
> supplies no trusted owner or target.
> [Package namespace acceptance](verification.md#package-namespace-acceptance)
> states what is proved about these checks.

## Commands

`vastitas check --manifest-path DIR/Vastitas.toml` checks the program of a
manifest, and `vastitas build --manifest-path DIR/Vastitas.toml -o OUTPUT`
builds it.

Rules:

- `--manifest-path` must name the root manifest. The compiler searches for no
  manifest.
- [The entry point](language/programs.md#the-entry-point) gives the entry
  point of a build. A `main` of a dependency is not the entry point, even
  when a `use` of the root module imports it.

```sh
vastitas check --manifest-path examples/packages/demo/Vastitas.toml
vastitas build --manifest-path examples/packages/demo/Vastitas.toml -o target/demo
./target/demo
```

The executable prints `42`.

## Geometry compatibility exports

The optional `[geometry_compat]` table of a manifest maps the syntax of the
[geometric core](language/geometric-types.md), such as `Point<X, Base(QQ)>`
and `origin(X)`, to `indexed` declarations, for a program in manifest mode.
Its `scheme` and `smooth` subtables map the two settings. Each path of the
table is resolved in the root module of the exporting package, so it may name
a declaration of a dependency.
[Core geometry syntax](indexed-source.md#core-geometry-syntax) gives the
entries of the table and the meaning of the core syntax under an export.

Rules:

- A program whose package graph holds no `indexed` declaration, resource
  function, grant, delegation, transfer or export uses the built-in geometric
  core, as in flat mode.
- Every other program must have exactly one export in its package graph to
  use the syntax of the geometric core. With no export or with several, that
  syntax is an error (`E_TYPE`). The `unpack` statement with `scheme` and
  `point` is the exception: it needs no export, as
  [Opening](indexed-source.md#opening) says.
- The compiler checks every export, even one that no program uses. An invalid
  export is an error (`E_TYPE`), and a path of the table that names nothing is
  an error (`E_NAME`).
- The compiler reports an invalid export, and a path of the table that it
  cannot resolve, at the root manifest, even for the export of a dependency.
  The message names the package of the export, the manifest that declares it,
  and the entry of the table, such as `scheme.origin`.
- Qualified `indexed` syntax needs no export.

> **Implementation note.** The kernel resolves every path of the table and
> checks every export itself. It trusts no owner, capability or validity claim
> from the manifest. The request that the kernel receives holds no position
> in a manifest, so the kernel names the manifest in the message.

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
- <a id="edit-borrowing--migrating-recipients-for-v010"></a><a id="migrating-recipients-for-v010"></a>Migrating recipients: [Source migrations](appendix/history.md#source-migrations).
- <a id="state-and-completion"></a>State and completion: [Assemblies](language/edit-authority.md#assemblies) and [Sealing](language/edit-authority.md#sealing).
- <a id="wire-extension"></a>Wire extension: [Scoped edits and assembly](protocol.md#protocol-5-scoped-edits-and-assembly).
- <a id="edit-authority"></a><a id="nested-edit-loans-and-permanent-authority-transfer"></a>Nested loans and transfer: [Edit authority](language/edit-authority.md).
- <a id="explicit-delegation"></a>Explicit delegation: [Grants and delegations](language/edit-authority.md#grants-and-delegations).
- <a id="permanent-transfer"></a>Permanent transfer: [Transfers](language/edit-authority.md#transfers).
- <a id="completion-provenance-and-proof-boundary"></a>Completion, provenance and proof boundary: [Sealing](language/edit-authority.md#sealing) and [Edit authority acceptance](verification.md#edit-authority-acceptance-protocol-6).
- <a id="indexed-geometry-compatibility-exports"></a>Indexed geometry compatibility exports: [Geometry compatibility exports](#geometry-compatibility-exports).
