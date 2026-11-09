# Modules

A **module** is a namespace of [items](items.md) in a package. The root source
file of a package is its **root module**, and `mod` declarations make child
modules, which form a tree. `use` declarations bind names of other modules in a
module. Modules exist only in [manifest mode](programs.md#manifest-mode).

## Module declarations

> **Syntax**
>
> ```text
> ModuleDeclaration -> `mod` ModuleName `;` | `mod` ModuleName `{` Item* `}`
> ModuleName -> IDENTIFIER | `generic`
> ```

`mod m { … }` declares an **inline module** whose items are inside the
braces. `mod m;` declares a **file module**, whose items are in a file of its
own. Each module has a **logical path**, the names of the modules from the root
module down to it. The file of a file module depends only on its logical path:
for the logical path `math::exact`, the file is `math/exact.vast` or
`math/exact/mod.vast`, relative to the directory of the root source file. It is
the same file whether `math` is inline, in `math.vast` or in `math/mod.vast`.

Rules:

- Items and `use` declarations occur only at the top level of a source file or
  of an inline module. A `use` or `mod` inside a function body is an error
  (`E_PARSE`).
- Exactly one of the two files of a file module must exist. Both files, or
  neither, are an error (`E_INPUT`).
- A file whose name matches the module name only when case is ignored is an
  error (`E_INPUT`). Module names are case sensitive on every file system.
- A module file must lie inside the package directory, after `..` and symbolic
  links are resolved, and its name must end in `.vast`. Another file is an
  error (`E_INPUT`).
- A module file must not load itself through a chain of `mod` declarations,
  also through a symbolic or hard link. Such a chain is an error (`E_CYCLE`).
- Two child modules of one module with the same name are an error
  (`E_DUPLICATE`). A module name must not be a
  [reserved name](lexical-structure.md#reserved-names) (`E_RESERVED`).
- One file that two `mod` declarations load at different logical paths makes
  two modules. Their declarations are different declarations.
- The depth of module nesting and the number of modules have limits, which
  [Appendix D](../appendix/limits.md#input-limits) lists (`E_LIMIT`).

[`examples/packages/arithmetic`](https://github.com/MGYamada/Vastitas/tree/main/examples/packages/arithmetic)
keeps part of its library in the file module `scalar`. Its root module,
`src/lib.vast`, declares the module and exports two of its functions:

```vast
{{#include ../../examples/packages/arithmetic/src/lib.vast}}
```

`src/scalar.vast` holds the items of `scalar`:

```vast
{{#include ../../examples/packages/arithmetic/src/scalar.vast}}
```

## `use` declarations

> **Syntax**
>
> ```text
> UseDeclaration -> `use` Path ( `as` IDENTIFIER )? `;`
> ```

`use p;` binds the last segment of the [path](names-and-paths.md) `p` in the
current module, and `use p as n;` binds `n`. The name then denotes the
declaration that `p` names: a module, a function, a resource function, a
generic, an abstract type, an `indexed` declaration, a grant, a delegation, a
transfer or a contribution. `pub use` also makes the name public, so that other
modules may name the declaration through the current module. This is a
**reexport**.

Rules:

- A name that `use` binds keeps the identity of its declaration. It grants no
  [edit authority](edit-authority.md) over that declaration.
- The name that `use` binds must not collide with another name of the module,
  as [Names of items](items.md#names-of-items) says. Without `as`, the last
  segment must not be a [reserved name](lexical-structure.md#reserved-names)
  (`E_RESERVED`), apart from the names that an `indexed` declaration may use.
- A `pub use` must reexport a public declaration. A private one is an error
  (`E_VISIBILITY`). The path to it may pass through private modules that the
  reexporting module can see.
- A `use` must not depend on itself through other `use` declarations. A cycle
  of imports or reexports is an error (`E_CYCLE`).
- There are no wildcard imports. `use a::*;` is an error (`E_PARSE`).
- The compiler checks every `use` declaration, also one that no expression
  uses.

An inline module and a `use` with an alias:

```vast
{{#include ../../examples/packages/inline-module/main.vast}}
```

The executable prints `42`.
