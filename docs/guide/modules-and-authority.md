# Packages, modules and edit authority

[Chapter 1](stdlib.md) introduced manifests. This chapter covers what happens
inside and between packages: modules, paths and visibility, and the rule that
decides who may add methods to a generic.

## Modules

A module is either inline or a file. In
[`examples/packages/inline-module`](https://github.com/MGYamada/Vastitas/tree/main/examples/packages/inline-module)
an inline module declares a public function, and the root imports it under
another name:

```vast
{{#include ../../examples/packages/inline-module/main.vast}}
```

`mod math;` without a body loads `math.vast` or `math/mod.vast` (having both is
an error). Paths follow the **logical** module path from the root source
directory: a child `mod exact;` of `math` loads `math/exact.vast` or
`math/exact/mod.vast`. Source files cannot escape their package directory.

[`examples/packages/arithmetic`](https://github.com/MGYamada/Vastitas/tree/main/examples/packages/arithmetic)
splits its library across a file module and reexports from the root:

```vast
// src/lib.vast
mod scalar;
pub use scalar::increment;
pub use scalar::add;

pub fn invoke(f: Fn<Int, Int>, x: Int) -> Int { f(x) }
```

```vast
// src/scalar.vast
pub generic add(left, right) { domain (Int, Int); }
method add(left: Int, right: Int) -> Int { left + right }
pub fn increment(x: Int) -> Int { add(x, 1) }
```

## Paths and imports

- `package::` starts at the current package root, `self::` at the current
  module and `super::` at its parent.
- A direct dependency alias may begin a path. Transitive dependencies are not
  imported implicitly.
- Bare names resolve in the current module's declarations, imports and local
  bindings. Parent names need an explicit path.
- `use` imports a module, function or generic, optionally renamed with `as`.
  There are no wildcard imports, and order never changes resolution.

## Visibility and ownership

Declarations are private by default: visible in their module and its
descendants. Other scopes need `pub` on every path edge they traverse. `pub use`
reexports a public declaration; it cannot reexport a private one.

Every function has an **owner**: its package, logical module path and name.
Aliases, reexports, file names and read order never create or transfer
ownership. Two functions with the same short name in different modules are
different functions.

## Edit authority

Imports permit calls only. Methods may be added to a generic only in the exact
module that defines it. A child module, `pub`, a qualified name or an import
does not grant that right.

To let another package contribute methods, the owner issues a **grant**. The
recipient declares a **contribution**, and the root package's **assembly**
borrows the grant, applies the contribution and seals the generic.
[`examples/packages/edit-borrow`](https://github.com/MGYamada/Vastitas/tree/main/examples/packages/edit-borrow)
has three packages. The library owns `choose` and grants the `(Int, Int)`
region to the package named `edit_addon`:

```vast
// lib/main.vast (package edit_base)
pub generic choose(x, y) { domain (Int, Int); }
method choose(x: Number, y: Number) -> Int { 0 }

pub grant integers : choose to edit_addon {
  domain (Int, Int);
}
```

The add-on contributes a more specific method:

```vast
// addon/main.vast (package edit_addon)
pub contribution sum : base::choose {
  method base::choose(x: Int, y: Int) -> Int { x + y }
}
```

The application's root module coordinates the edit, in
[`app/main.vast`](https://github.com/MGYamada/Vastitas/blob/main/examples/packages/edit-borrow/app/main.vast)
(package `edit_app`):

```vast
{{#include ../../examples/packages/edit-borrow/app/main.vast}}
```

```sh
target/debug/vastitas check --manifest-path examples/packages/edit-borrow/app/Vastitas.toml
```

The recipient in `to edit_addon` is a manifest `[package] name`, not a
dependency alias. A loan is exclusive. Every borrowed generic must be returned
and every edited generic sealed. Sealing checks the final method table: no
ambiguity, full domain coverage and winning methods only inside each grant's
region.

Further delegation moves authority on: a borrower can reborrow a nested loan,
and an owner can permanently transfer edit authority without changing the
function's identity. Both are described in
[Nested edit loans and permanent authority transfer](../packages.md#edit-authority).

> **What is checked.** Lean rebuilds the package graph and assigns every owner
> itself; the frontend supplies no trusted owner or target. The full rules and
> the proof boundary are in
> [Path packages and logical modules](../packages.md#validation-and-boundary) and
> [Scoped edit borrowing](../packages.md#edit-borrowing). Acceptance proofs are in
> [Verification boundaries](../verification.md#package-namespace-acceptance).
