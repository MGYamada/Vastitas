# Path packages and logical modules

This is the first increment of [#52](https://github.com/MGYamada/Vastitas/issues/52),
tracked by [#56](https://github.com/MGYamada/Vastitas/issues/56). It adds path
packages, modules, unique function owners and call-only imports to Stage 1b.
The subsequent [protocol-5 increment](edit-borrowing.md) adds scoped edit borrowing and finite impact regions. Authority transfer remains deferred.

## Manifest and commands

A package has one explicit `Vastitas.toml`:

```toml
[package]
name = "demo"
version = "0.1.0"
root = "src/main.vast"

[dependencies]
arithmetic = { path = "../arithmetic" }
```

All package fields are required. Names are nonempty strings, versions use
SemVer, and root names a `.vast` file inside the package directory. Dependency
aliases are ASCII identifiers and cannot collide with declarations or imports.
Each path names a directory containing `Vastitas.toml`; paths are relative to
the declaring manifest. Unsupported manifest fields and dependency forms fail.

```sh
vastitas check --manifest-path examples/packages/demo/Vastitas.toml
vastitas build --manifest-path examples/packages/demo/Vastitas.toml -o target/demo
./target/demo
# 42
```

There is no implicit manifest search. Positional `.vast` plus explicit `--lib`
remains the protocol-2 compatibility mode; it cannot be mixed with manifest
mode. `check` needs no main. `build` requires an ordinary `fn main() -> Int`
declared in the selected package's root module. Importing another package's
main or declaring a main in a child module does not supply that entrypoint.

Only local path dependencies are supported. There is no registry, Git fetch,
version solving, multiple build targets or independent compilation cache.
Every build rereads all inputs and checks all packages, including unused ones.
Cyclic dependencies are rejected. The same canonical manifest reached through
different aliases is one package. Identity includes canonical manifest location,
name and version; equal names and versions at different locations remain distinct.

## Modules and paths

```vast
mod math {
    pub fn increment(x: Int) -> Int { x + 1 }
}
use math::increment as next;
fn main() -> Int { next(41) }
```

Declarations and imports occur at module scope only. `mod math;` loads either
`math.vast` or `math/mod.vast`; having both is an error. Paths are based on the
root source directory plus the **logical** module path. For example, a child
`mod exact;` in logical `math` loads `math/exact.vast` or
`math/exact/mod.vast`, whether `math` is inline, `math.vast`, or `math/mod.vast`.
Source files cannot escape their package directory through `..` or symlinks.
Loading cycles are detected by file identity, including hard links. Independent
uses of the same source file in different logical modules remain different owners.

- `package::` begins at the current package root; the bare local name `package`
  remains legal. `self::` starts in the current module; `super::` starts in its
  parent, and repeated `super::` walks further ancestors.
- A direct dependency alias may begin a path. Transitive dependencies are not
  implicitly imported; their package must explicitly expose the desired API.
- Bare names resolve in the current module's declarations/imports and local
  bindings. Parent names require an explicit path. Builtins remain available.
- `use` accepts a module, ordinary function or generic, optionally followed by
  `as`. No wildcard imports are implemented. Import/declaration order does not
  select an owner or change resolution.

Declaration names and local bindings obey the existing reserved-name and
shadowing rules; package mode additionally reserves `mod`, `use`, `pub`,
`self` and `super`. `generic` is also permitted as a contextual module name and
path component (for example `std::arithmetic::generic::promote`); it remains
reserved for functions, variables and import aliases. Import that module using
an explicit alias such as `use std::arithmetic::generic as arithmetic;`.
A binding cannot shadow a dependency alias. Logical module
nesting and dependency nesting are bounded to 64 in the loader; namespace
resolution has a shared 4096-member work budget and rejects exhaustion with
`E_LIMIT`, instead of expanding shared import paths indefinitely.

## Visibility and ownership

Declarations are private by default and accessible from their declaring module
and descendants. Other scopes require `pub` at every traversed path edge.
Qualified calls receive the same checks as imports. `pub use` can reexport an
accessible public declaration, including a public function reached through an
accessible private module. It cannot reexport a private target. `self` and
`super` retain the actual module visibility. Cyclic imports/reexports fail.

A function owner is the resolved package identity, logical module path and
definition name. Aliases, reexports, source filenames and read order do not
create or transfer ownership. Functions with equal short names in different
modules remain separate. Ordinary methods may be added only in the exact module
that defines the generic; protocol-5 contributions require explicit grants and
active assembly loans. Child modules, public visibility, qualified names and
imports grant no edit authority; ordinary functions cannot receive methods.
Calls may be repeated, and aliases of function values retain the same static
function target. Generics remain callable families, not function values.

## Validation and boundary

Manifest mode sends protocol 3, retaining package dependencies, modules,
visibility, imports and unresolved paths. Lean independently validates the
graph and assigns function identities; the frontend supplies no trusted owner
or target IDs. All functions, unused dependencies and all applicable method
bodies pass through the existing surface/dispatch and core audits. Capture
prohibition, exact geometry identities, recursion rejection and specialization
limits still apply. Diagnostics retain the original source file and location.
All manifests and source files participate in output collision protection,
including aliases, and the native build keeps the same cancellation/cleanup path.

The actual-checker proofs cover unique owners, reference-ledger agreement with
the actual resolver, method authority, alias preservation, and
typing/order/termination of the returned core. The reference audit reuses the
lowering resolver. The owner structure omits source-file placement and aliases;
equal owners have equal symbols by congruence. Symbol-encoding injectivity and
correspondence between ledger entries and emitted names are not proved. Actual
symbol uniqueness is checked during namespace validation. Rust file
loading/authenticity, JSON decoding, complete namespace syntax preservation
and native compilation are not proved.
See [verification](verification.md) and [protocol](protocol.md).

The foundation is available to #48 (abstract types/methods), #49 (geometric
stdlib interfaces), and #55 (`promote`), but does not implement their remaining
requirements. #37 (same-concrete-type argument constraints) is an independent
next candidate. #22–26 and #28 retain their existing design decisions. Stage 1
as a whole remains incomplete.


## Finite abstract declarations

[Abstract selectors and contracts](abstract-types.md) use protocol 4's explicit
package mode and the same owner/index/reference audit. `pub abstract type`
participates in visibility and aliases. Scalar membership is editable only by
the abstract type's exact defining module; an abstract contract is editable
only by the generic's exact defining module. Public exposure, child modules and
imports grant neither permission. Abstract parents and contract-domain selectors
may refer to visible types in other modules without editing those declarations.
Existing package sources without abstract or edit declarations still use protocol 3. New grants, contributions or an assembly select protocol 5; see [edit borrowing](edit-borrowing.md).

## Explicit edit authority

Ordinary imports remain call-only. The exact generic owner may issue a grant to
one module in the selected dependency closure; that module contributes methods
only through a root assembly with an active exclusive loan. Neither imports,
child modules nor aliases imply this permission. See [the syntax and completion
contract](edit-borrowing.md) and `examples/packages/edit-borrow/app/Vastitas.toml`.
