# Statements

A **statement** binds names for the rest of a block. Statements occur only at
the beginning of a [block expression](expressions.md#block-expressions), before
its result. The language has two statements, `let` and `unpack`, and no
expression statements.

> **Syntax**
>
> ```text
> Statement -> LetStatement | UnpackStatement
> ```

## Scopes of bindings

A **binding** is a name that a statement or a parameter list introduces. A
binding is visible from the end of its statement to the end of the block that
contains the statement, including the blocks nested in it. A parameter is a
binding that is visible in the whole body of its function or lambda. The rules
of this section apply to parameters and to the names that statements bind.

Rules:

- A binding must not reuse a name that is visible at its statement: another
  parameter, or a binding of the same block or of an enclosing block. Reuse is
  an error (`E_DUPLICATE`). The language has no shadowing.
- A binding with the name of a function, a generic or an abstract type is an
  error (`E_SHADOW`). In manifest mode, so is a binding with the name of a
  module, an import or a dependency of its module, as
  [Modules and paths](names-and-paths.md) describes.
- A binding with a [reserved name](lexical-structure.md#reserved-names) is an
  error (`E_RESERVED`).
- Blocks that do not contain one another may bind the same name. The two
  branches of an `if` are such blocks.

A lambda has stricter rules for the names it binds, which
[Lambdas](../stage1b.md#syntax-and-values) gives.

In this program the two blocks bind `step` once each:

```vast
{{#include ../../examples/book/statements/bindings.vast}}
```

The executable prints `42`. A block that binds a name of its enclosing block is
an error:

```vast
{{#include ../../examples/reject/statements/nested-rebinding.vast}}
```

```text
{{#include ../../examples/reject/statements/nested-rebinding.stderr}}
```

## `let` statements

> **Syntax**
>
> ```text
> LetStatement -> `let` IDENTIFIER ( `:` Type )? `=` Expression `;`
> ```

`let x = e;` evaluates `e` once and binds `x` to its value. With a type
annotation, `let x: T = e;` also states the type of `x`.

Rules:

- With an annotation, the expression must have the annotated type. Another type
  is an error (`E_TYPE`). The annotation is the expected type of the
  expression, which decides the type of an
  [integer literal](expressions.md#literal-expressions).
- Without an annotation, the binding has the type of its expression.
- The binding begins after its expression, so the expression cannot refer to
  the name that the statement binds. Such a reference is an unknown name
  (`E_NAME`).
- `let mut` is an error (`E_UNSUPPORTED`). Bindings are immutable.

```vast
let n: Nat = 2;
let total = n * 3;
```

Here `total` has type `Nat`, the type of `n * 3`.

## `unpack` statements

> **Syntax**
>
> ```text
> UnpackStatement -> `unpack` Expression `as` `{` UnpackFields `}` `;`
> UnpackFields -> `scheme` `:` IDENTIFIER `,` `point` `:` IDENTIFIER `,`?
>     | `witness` `:` IDENTIFIER `,` `fields` `:` `[` UnpackFieldNames? `]` `,`?
> UnpackFieldNames -> IDENTIFIER ( `,` IDENTIFIER )* `,`?
> ```

`unpack e as { scheme: X, point: p };` opens the
[existential package](geometric-types.md#existential-packages) that `e`
evaluates to. It binds `X` to a fresh object and `p` to the point of the
existential package on `X`.

The second form, with `witness` and `fields`, opens an existential package of
an [indexed profile](../appendix/glossary.md#profile) in manifest mode. It
binds the witness object and then every field, in order. [Indexed source](../indexed-source.md#declarations-and-source-example)
gives its rules.

Rules:

- The expression must have the type of an existential package. Another type is
  an error (`E_TYPE`).
- The fields must appear as `scheme`, then `point`. Another order or another
  field name is an error (`E_PARSE`).
- In flat mode, the `witness` form is an error (`E_PARSE`).
- The names that an `unpack` statement binds follow the rules of
  [Scopes of bindings](#scopes-of-bindings).
