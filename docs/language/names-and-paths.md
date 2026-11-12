# Names and paths

A **path** names a declaration of the current module, of another module or
of another package. This
chapter defines paths, how a name resolves to a declaration, and which
declarations a module may name. Paths with `::` exist only in
[manifest mode](programs.md#manifest-mode). In flat mode every name is one
identifier in the single namespace of the program.

> **Syntax**
>
> ```text
> Path -> PathSegment ( `::` PathSegment )*
> PathSegment -> IDENTIFIER | `generic`
> ```

## Resolution

The module in which a path occurs is its **current module**. The first segment
of a path is resolved in the current module, and each later segment in the
module that the segment before it names.

| First segment | Resolves to |
| --- | --- |
| `package` | The root module of the current package |
| `self` | The current module |
| `super` | The parent of the current module. Each further `super` goes up one more level |
| A dependency alias | The root module of that dependency |
| Another name | A declaration of the current module, or a name that a `use` of the current module binds |

A name without `::`, a **bare name**, resolves among the bindings in scope, the
declarations of the current module, the names that its `use` declarations
bind, and the [built-in functions](expressions.md#built-in-functions). Only a
bare name finds a binding. The names of a parent module are not in scope in a
child module. A path through `super` or `package` reaches them.

Rules:

- A name or path segment that resolves to nothing is an error (`E_NAME`).
- Each segment before a `::` must name a module. Another declaration there is
  an error (`E_NAME`).
- A dependency alias may only begin a path. Only the direct dependencies of a
  package have aliases in it. A path that begins with a dependency of a
  dependency is an error (`E_NAME`), unless the package declares that name
  itself.
- `package`, `self` and `super` have their meaning only as the first segment
  of a path. `package` has it only before `::`. `self` and `super` also name
  their module alone, as in `use super as up;`.
- A path that is `package` alone names a declaration `package` of the current
  module. `use package as root;` in a module without such a declaration is an
  error (`E_NAME`). `use package;` is an error (`E_RESERVED`), because it
  binds the [reserved name](lexical-structure.md#reserved-names) `package`.
- A function, a parameter or a binding may be named `package`.
  [Reserved names](lexical-structure.md#reserved-names) gives the places
  where the name is reserved, and [Manifests](../packages.md#manifests)
  excludes it as a dependency alias.
- `generic` may be a segment, as in `std::arithmetic::generic::promote`. It
  remains a strict keyword, so a `use` of a module named `generic` must give
  it an alias, as in `use std::arithmetic::generic as arithmetic;`. Without
  the alias the `use` is an error (`E_RESERVED`).
- Two constructs do not take a path that begins with `generic`. A
  [path expression](expressions.md#path-expressions) must not be `generic`
  alone, and the family of an [indexed type](types.md#indexed-types) must
  not begin with `generic` (`E_PARSE`). Another path that names a
  declaration may begin with it. Its first segment then names a module
  `generic` of the current module, and without such a module the path is an
  error (`E_NAME`).
- The order of declarations and `use` declarations does not change how a name
  resolves.
- In flat mode a path with `::` is an error. Its code depends on the place:
  `E_PARSE` in an expression and in the name of a method, `E_NAME` in a
  selector, a parent or a `subtype`, and `E_UNSUPPORTED` in a type.
- Resolution has work limits, which
  [Appendix D](../appendix/limits.md#names) lists. Exceeding one is an
  error (`E_LIMIT`).

In this program the root module imports `increment` from the dependency
`arithmetic` under the name `next`, and the module `pipeline` names `invoke`
through the same dependency:

```vast
{{#include ../../examples/packages/demo/src/main.vast}}
```

The executable prints `42`. `package` is a binding here, because it does not
begin a path with `::`.

## Visibility

A declaration with `pub` is **public**. A declaration without `pub` is
**private**: it is visible in its declaring module and in the descendants of
that module. A module is a declaration of its parent, so a module is public or
private in the same way.

Rules:

- Each declaration that a path passes through outside the modules where it is
  visible must be public: every module on the path, and the declaration that
  the path names. A private one is an error (`E_VISIBILITY`).
- A call through a path gets the same checks as a `use` of that path.
- `self` and `super` do not change visibility. A path that begins with them is
  checked like any other path.
- Visibility allows naming and calling a declaration. It never allows adding
  methods to a generic, as [Edit authority](edit-authority.md) says.
- Visibility restricts paths, not values. A public function may return a
  private function of a module that it may name, as a
  [function value](../stage1b.md). A module that must not name the private
  function may call the value that it receives. Naming the private function
  there, in a call or as a value, is an error (`E_VISIBILITY`).

Here `area` is private in the module `geometry`, and `main` is outside it:

```vast
{{#include ../../examples/reject/packages/private-function/main.vast}}
```

```text
{{#include ../../examples/reject/packages/private-function.stderr}}
```
