# Resource programs

A **resource function** combines pure computation with explicit operations on
storage: it allocates buffers, lends views of them, writes and reads cells, and
frees them. The checker follows every owner and every loan through the body.
It rejects a program whose statements could read an unwritten cell, write
through two overlapping views, or leave an allocation that is not freed once.
Resource functions exist only in
[manifest mode](../language/programs.md#manifest-mode). A **resource
program** is a program that declares a resource function.
[Storage and ownership](../storage-ownership.md) states the model behind these
rules, and the sections of that chapter link the rules of this one.

## Resource functions

> **Syntax**
>
> ```text
> ResourceFunction -> `resource` `fn` IDENTIFIER `(` ResourceParameters? `)`
>     ( `returns` `(` ResourceResults? `)` )? `->` Type
>     `{` ResourceStatement* `value` BlockExpression `}`
> ResourceParameters -> ResourceParameter ( `,` ResourceParameter )* `,`?
> ResourceParameter -> IDENTIFIER `:`
>     ( ScalarType | OwnedType | BorrowedType | RuntimeParameterType | NumericalParameterType )
> ResourceResults -> ResourceResult ( `,` ResourceResult )* `,`?
> ResourceResult -> IDENTIFIER `:` ( OwnedType | NumericalResultType )
> ```

A resource function has parameters, optional **owned results** after
`returns`, and a result type. Its body is a list of
[resource statements](#resource-statements) followed by a `value` block, a
[block expression](../language/expressions.md#block-expressions) that computes
the result. An owned result names an owner of the body, which the function
hands to its caller. [Storage types](#storage-types) defines owners and loans.
An owner or a loan is **live** from the parameter or the statement that
binds it to the statement that ends it: a `move`, a `drop` or a call that
takes an owner, and the `release` of a loan.

Rules:

- The name of a resource function follows
  [Names of items](../language/items.md#names-of-items).
- The name of a resource function must not stand as a value, and a function,
  a method, a lambda and a `value` block must not call a resource function
  (`E_TYPE`). Only a `call` statement calls one.
- A `method` declaration must not name a resource function (`E_OWNER`). A
  resource function is no generic and has no methods.
- A resource function must not call itself, directly or through other resource
  functions (`E_RESOURCE_RECURSION`).
- The result type must be a scalar type or a pair type. Otherwise it is an
  error (`E_TYPE`). The `value` block must have that type (`E_TYPE`).
- The `value` block sees the scalar parameters and the scalar bindings of the
  body. An owner, a loan or another resource binding there is an error
  (`E_NAME`).
- Every owned result must name a binding of the body (`E_RESOURCE_NAME`).
  That binding must be a live owner that meets the type of the result
  (`E_RESOURCE_TYPE`), and no loan of it may be live at the end of the body
  (`E_RESOURCE_ESCAPE`). Two owned results must not name one binding
  (`E_RESOURCE_TYPE`).
- At the end of the body, every other owner must have been dropped, moved or
  handed to a call (`E_RESOURCE_ESCAPE`). A body must not release a borrowed
  parameter (`E_RESOURCE_LOAN`).
- The checker checks every resource function of the program, even one that no
  call reaches. It checks a function once on its own and once more at every
  call, with the views that the caller passes.
- The statements of all resource functions of a program have a limit, and so
  have their `value` blocks.
  [Appendix D](../appendix/limits.md#resource-functions) gives both. The
  statements of both arms of an `if` count as statements. The `value` block
  that ends a function counts as a `value` block and not as a statement. A
  program beyond a limit is an error (`E_RESOURCE_LIMIT`), reported at a
  function.
- A resource function named `main` in the root module of the root package is
  the [entry point](../language/programs.md#the-entry-point). It must have no
  parameters and no owned results (`E_RESOURCE_ESCAPE`), and its result type
  must be `Int` (`E_MAIN`).

The package `buffers` of
[`examples/packages/storage`](https://github.com/MGYamada/Vastitas/tree/main/examples/packages/storage)
declares three resource functions:

```vast
{{#include ../../examples/packages/storage/buffers/src/operations/mod.vast}}
```

## Storage types

> **Syntax**
>
> ```text
> OwnedType -> `Owned` `<` ElementType `,` INTEGER_LITERAL `>` ( `initialized` `[` Layouts? `]` )?
> BorrowedType -> ( `Read` | `Write` | `ReadWrite` )
>     `<` ElementType `,` INTEGER_LITERAL `,` INTEGER_LITERAL `>` `initializes`?
> ElementType -> `F64` | `Complex` `<` `F64` `>`
> Layouts -> Layout ( `,` Layout )* `,`?
> Layout -> `layout` `(` INTEGER_LITERAL `,` INTEGER_LITERAL `,` INTEGER_LITERAL `,`
>     INTEGER_LITERAL `,` ( `true` | `false` ) `)`
> ```

An **owner** is a binding that owns one **allocation**, a buffer of **cells**.
`Owned<S, n>` is the type of an owner of `n` cells of the element type `S`:
`F64`, a binary64 number, or `Complex<F64>`, a pair of them. A **view** is a
rectangle of cells of an allocation. A **loan**, a
[storage loan](../appendix/glossary.md#storage-loan), is a binding that gives
access to one view for a limited time. `Read<S, r, c>`, `Write<S, r, c>` and
`ReadWrite<S, r, c>` are the types of loans of a view with `r` rows and `c`
columns.

`layout(offset, rows, columns, leading, transposed)` describes a view of an
allocation in column-major order. `offset` is the first byte of the view in
the allocation. `rows` and `columns` count the stored rows and columns, and
`leading` is the number of cells from one stored column to the next. With
`transposed` equal to `true`, the rows of the view are the stored columns:
`layout(0, 2, 3, 2, true)` describes a view with 3 rows and 2 columns.

Rules:

- The layout of a `borrow` must lie inside its allocation. Its `leading` must
  be at least the number of stored rows and at least 1, and `rows`, `columns`
  and `leading` must not exceed 2³¹ − 1. Another layout is an error
  (`E_RESOURCE_LAYOUT`).
- The `offset` of a view that has a cell must be a multiple of the size of a
  cell, 8 bytes for `F64` and 16 for `Complex<F64>` (`E_RESOURCE_LAYOUT`).
- An owned parameter or result with `initialized [layout(…), …]` states that
  the cells of those views are initialized. An argument or result that does
  not meet the element type, the size or this contract is an error
  (`E_RESOURCE_TYPE`), and so is an invalid layout in the contract. The
  number of views of a contract has a limit, which
  [Appendix D](../appendix/limits.md#resource-functions) gives
  (`E_RESOURCE_TYPE`). Capacity and padding imply no initialization.
- The contract of an owned parameter is what the body may rely on: in the
  check of the function on its own, the cells of its views count as
  initialized and no other cell does. The checker checks the contract of an
  owned result against the body.
- A caller needs no contract to read an owned result. At a call the checker
  follows the statements of the callee, so the cells that the callee
  initialized count as initialized for the caller, with or without a
  contract.
- An argument for a borrowed parameter must be a live loan (`E_RESOURCE_LOAN`)
  with the element type and the shape of the parameter (`E_RESOURCE_TYPE`).
  The callee sees the caller's view, with its offset, padding and
  transposition.
- A loan passed to a `Read` or `ReadWrite` parameter must permit reading, and
  a loan passed to a `Write` or `ReadWrite` parameter must permit writing.
  Another loan is an error (`E_RESOURCE_ACCESS`).
- A parameter with `initializes` promises that the callee initializes every
  cell of the view. A body that leaves a cell unwritten on some path is an
  error (`E_RESOURCE_INIT`). Cells that a callee writes count as initialized
  for the caller, with or without `initializes`.
- Two arguments of one call whose views may overlap must both go to `Read`
  parameters (`E_RESOURCE_ALIAS`). Parameter names prove no separation.
- An integer in a storage type, a layout, an allocation size, a cell index or
  `f64_bits` must fit in 64 bits (`E_RESOURCE_LIMIT`). An allocation of more
  than 2⁶³ − 1 bytes is an error (`E_RESOURCE_OVERFLOW`).

## Resource statements

> **Syntax**
>
> ```text
> ResourceStatement -> StorageStatement `;` | BorrowStatement | ValueStatement
>     | ResourceCall | ResourceBranch | RuntimeStatement `;` | NumericalStatement
> StorageStatement -> `allocate` IDENTIFIER `:` ElementType `[` INTEGER_LITERAL `]`
>     | `move` IDENTIFIER `->` IDENTIFIER
>     | `drop` `(` IDENTIFIER `)`
>     | `release` `(` IDENTIFIER `)`
>     | `transpose` `(` IDENTIFIER `)`
>     | `fill` `(` IDENTIFIER `,` Payload `)`
>     | `store` `(` IDENTIFIER `,` INTEGER_LITERAL `,` INTEGER_LITERAL `,` Payload `)`
>     | `expect` `(` IDENTIFIER `,` INTEGER_LITERAL `,` INTEGER_LITERAL `,` Payload `)`
>     | `copy` `(` IDENTIFIER `,` IDENTIFIER `)`
> BorrowStatement -> `borrow` IDENTIFIER `=` AccessMode `(` IDENTIFIER ( `,` Layout )? `)` `;`
> AccessMode -> `read` | `write` | `read_write`
> ```

| Statement | Meaning |
| --- | --- |
| `allocate d: F64[8];` | Allocate 8 uninitialized cells and bind their owner `d` |
| `move d -> e;` | Hand the allocation of `d` to the owner `e`; `d` ends |
| `drop(d);` | Free the allocation of `d`; `d` ends |
| `borrow v = read(d, layout(…));` | Lend a view of the owner or loan `d` as the loan `v`; also `write` and `read_write` |
| `release(v);` | End the loan `v` |
| `transpose(v);` | Swap the rows and columns of `v`, without copying or conjugating |
| `fill(v, p);` | Write the payload `p` to every cell of `v` |
| `store(v, i, j, p);` | Write `p` to the cell in row `i` and column `j` of `v` |
| `expect(v, i, j, p);` | At run time, fail unless that cell holds the bits of `p` |
| `copy(a, b);` | Copy every cell of the view `a` to the view `b` |

A `read` loan permits reading, a `write` loan writing only, and a `read_write`
loan both. `borrow` without a layout lends the storage of an owned map, as
[Owned maps](../linalg/maps-and-gemm.md#owned-maps) describes.
[Numerical maps](../linalg/maps-and-gemm.md) and the two chapters after it
give the numerical statements.

Rules:

- A binding of a resource function is a parameter, an owner, a loan, a scalar
  binding or a result of a call. It must not reuse a name that is visible at
  its statement, even after the owner or loan of that name has ended
  (`E_DUPLICATE`). It must not have a name of the namespace of its module
  (`E_SHADOW`): the name of an item, of a child module, of an import or of a
  dependency alias, as
  [Scopes of bindings](../language/statements.md#scopes-of-bindings) says. It
  must not have a
  [reserved name](../language/lexical-structure.md#reserved-names).
- A statement that names a binding which is not in scope is an error
  (`E_RESOURCE_NAME`).
- The owner of a `move`, a `drop` or a `borrow` must be live
  (`E_RESOURCE_MOVE`), and an owned argument must be a live owner
  (`E_RESOURCE_TYPE`). An owner ends when it is moved, dropped or handed to a
  call.
- No loan of the allocation may be live at a `move`, at a `drop` or when a
  call takes the owner (`E_RESOURCE_LOAN`).
- `release`, `transpose`, `fill`, `store`, `expect` and `copy` must name live
  loans. An owner or a released loan there is an error (`E_RESOURCE_LOAN`),
  and so is a `borrow` from a released loan. `release` may also name a
  [map](../linalg/maps-and-gemm.md#maps) or a
  [vector](../linalg/transforms-and-metrics.md#vectors) in place of its loan.
- `fill`, `store`, `expect` and `copy` may name a vector in place of its
  loan. [Vectors](../linalg/transforms-and-metrics.md#vectors) gives the
  rules of a vector there. The rules of this section then hold for the loan
  of the vector.
- Every cell of the view of a `read` or `read_write` loan must be initialized
  (`E_RESOURCE_INIT`). `fill` initializes its view, `store` one cell and
  `copy` its target. A `write` loan may cover uninitialized cells.
  [Diagnostics](#diagnostics) describes the cell that the diagnostic of a
  `borrow` names.
- Stores that cover every cell of a view initialize it, within the bound on
  the initialization query that
  [Appendix D](../appendix/limits.md#resource-functions) gives. Beyond the
  bound, the `borrow` is an error (`E_RESOURCE_INIT`), although the stores
  write every cell. Fills of the stored columns of a view also initialize it.
  [Layout and initialization](checked-storage.md#storage-ir--layout-and-initialization)
  describes the records of the checker.
- Fills of the stored rows of a view with several stored columns do not
  initialize it. The cells of a stored row have gaps between them, and the
  checker does not join the fill of such a view with another fill.
- Two live loans whose views may overlap must both be `read` loans
  (`E_RESOURCE_ALIAS`). The checker compares the byte ranges from the first
  cell of each view to its last. Two stored rows of a matrix with several
  stored columns therefore overlap, and so does a view inside the padding of
  another. Loans of different allocations never overlap. The rule does not
  hold between a loan and its children, which the next rules govern.
- A loan borrowed from a loan is its **child**. The view of a child must lie
  in the view of its parent (`E_RESOURCE_REGION`); the `offset` of its layout
  still counts bytes of the allocation.
- A child must not have an access that its parent lacks: a `read` loan lends
  only `read` children, and a `write` loan only `write` children
  (`E_RESOURCE_ACCESS`).
- While a child is live, its parent gives no access, and a child must be
  released before its parent (`E_RESOURCE_LOAN`). A parent passed to a call
  while a child is live is an error (`E_RESOURCE_ALIAS`). Releasing a loan
  twice is an error (`E_RESOURCE_LOAN`).
- The loan of `fill` and of `store` and the target of `copy` must permit
  writing, and the loan of `expect` and the source of `copy` must permit
  reading (`E_RESOURCE_ACCESS`). The cell of `store` and `expect` must lie in
  the view (`E_RESOURCE_BOUNDS`).
- A payload must have the element type of its view, and the two views of
  `copy` must have the same element type and shape (`E_RESOURCE_TYPE`).
- A statement name that is no statement of this chapter or of the numerical
  chapters is an error (`E_PARSE`).

`main` of the same example receives an owner, lends it, hands it on and frees
it:

```vast
{{#include ../../examples/packages/storage/app/src/main.vast}}
```

The executable prints `42`.

## Payloads

> **Syntax**
>
> ```text
> Payload -> `f64` `(` Real `)` | `complex` `(` Real `,` Real `)`
>     | `f64_bits` `(` INTEGER_LITERAL `)`
>     | `complex_bits` `(` INTEGER_LITERAL `,` INTEGER_LITERAL `)`
> Real -> ( `+` | `-` )? ( INTEGER_LITERAL | FLOAT_LITERAL )
> ```

A **payload** is the value of one cell. `f64(x)` denotes the binary64 number
`x`, and `complex(x, y)` the complex number with real part `x` and imaginary
part `y`. `FLOAT_LITERAL` is a
[floating-point literal](../language/lexical-structure.md#other-literals): a
decimal number such as `1.5` or `125e-3`, or a hexadecimal number such as
`0x1.8p1`. The value of a hexadecimal number is its hexadecimal significand
times 2 to the decimal exponent after `p`. `0x1.8p1` is 3. `f64_bits(n)` and `complex_bits(m, n)`
give the 64 bits of each component as an unsigned integer.

Rules:

- The number in `f64` and `complex` must be a finite binary64 value, exactly.
  A number that binary64 only approximates is an error
  (`E_RESOURCE_LITERAL`), and so are overflow and underflow. Examples are
  `0.1` and the integer `9007199254740993`. The compiler never rounds a
  payload.
- The smallest positive payload is `f64(0x1p-1074)`, and the largest is
  `f64(0x1.fffffffffffffp1023)`.
- `f64` and `complex` denote positive zero for `0`. A negative zero there,
  such as `f64(-0)`, is an error (`E_RESOURCE_LITERAL`). A negative zero, an
  infinity and a NaN are written with `f64_bits` or `complex_bits`.
- An exponent must fit in a signed 64-bit integer (`E_RESOURCE_LITERAL`).
- A malformed number that the lexer reads as one floating-point token, as
  [Other literals](../language/lexical-structure.md#other-literals) describes,
  is an error in a payload (`E_RESOURCE_LITERAL`), and so is a string literal
  as the number of `f64` or `complex`.
- A number or a string literal in place of a payload, as in `fill(v, 1.5);`,
  is an error (`E_TYPE`).

[`examples/packages/payloads`](https://github.com/MGYamada/Vastitas/tree/main/examples/packages/payloads)
writes three payloads as numbers:

```vast
{{#include ../../examples/packages/payloads/main.vast:payloads}}
```

It then reads the cells back and expects the bits of the same numbers:

```vast
{{#include ../../examples/packages/payloads/main.vast:bits}}
```

The executable prints `42`.

## Scalar values and calls

> **Syntax**
>
> ```text
> ValueStatement -> `let` IDENTIFIER `:` Type `=` `value` BlockExpression `;`
>     | `let` IDENTIFIER `:` Type `=` ResourceCall
> ResourceCall -> `call` Path `(` ResourceArguments? `)` `->` `(` ResourceArguments? `)` `;`
> ResourceArguments -> IDENTIFIER ( `,` IDENTIFIER )* `,`?
> ResourceBranch -> `if` ( IDENTIFIER | `true` | `false` )
>     `{` ResourceStatement* `}` `else` `{` ResourceStatement* `}`
> ```

`let x: T = value { e };` computes the scalar `e` with ordinary expressions
and binds `x`. A `value` block may call functions, generics and lambdas, and
it may use the declarations of
[Indexed declarations](../indexed-source.md).
`call f(a, …) -> (d, …);` calls the resource function `f` with the named
bindings and binds its owned results, in order, to fresh owners.
`let x: T = call f(…) -> (…);` also binds the scalar result of `f`. `if c { … }
else { … }` runs one of two lists of statements, its **arms**, by the `Bool`
binding `c`.

Rules:

- The type of a scalar binding must be `Nat`, `Int`, `Bool` or `Unit`.
  Otherwise it is an error (`E_RESOURCE_VALUE`), even when it is a pair type.
  The `value` block must have the type of the binding (`E_TYPE`).
- A `value` block sees the scalar parameters and the earlier scalar bindings
  only (`E_NAME`).
- A binding inside a `value` block must not reuse a name of the function that
  is visible at the block: a parameter, a scalar binding, an owner or a loan
  (`E_SHADOW`).
- A lambda in a `value` block must not name a binding of the function, and
  its parameters must not have the name of one (`E_CAPTURE`).
- The callee of a call must be a resource function (`E_TYPE`). The arguments
  are names of bindings, one per parameter (`E_RESOURCE_ARITY`). A literal
  argument is an error (`E_PARSE`); bind it with `let` first.
- A scalar argument must have the type of its parameter, and the type of
  `let x: T = call …` must be the result type of the callee
  (`E_RESOURCE_VALUE`). A `let` must not bind the result of a callee whose
  result type is a pair type (`E_RESOURCE_VALUE`).
- A call without `let` discards the result of the callee, of a scalar type or
  of a pair type. The compiler checks the `value` block of the callee all the
  same, as it checks every resource function.
- The number of bindings after `->` must be the number of owned results of the
  callee (`E_RESOURCE_ARITY`).
- A call ends the owners that it hands to owned parameters, and it suspends
  the loans that it passes until it returns.
- The condition of a branch must be a `Bool` binding or a literal
  (`E_RESOURCE_VALUE`), and `else` is required (`E_PARSE`).
- The checker checks both arms of a branch, even for a literal condition.
  After the branch, both arms must leave the same owners and loans live, with
  the same transpositions (`E_RESOURCE_JOIN`). A cell counts as initialized
  after the branch only when both arms initialize it.
- A binding of an arm is not visible in the other arm or after the branch: a
  scalar binding (`E_NAME`), an owner or a loan (`E_RESOURCE_NAME`). Its name
  is free again there. An owner that an arm allocates must end in that arm
  (`E_RESOURCE_JOIN`).

[`examples/packages/resource-values`](https://github.com/MGYamada/Vastitas/tree/main/examples/packages/resource-values)
passes scalars through resource functions and branches on one:

```vast
{{#include ../../examples/packages/resource-values/src/main.vast}}
```

The executable prints `42`.

## Running a resource program

The executable of a resource program whose entry point is a resource function
runs the statements of the entry point in order and then prints the value of
its `value` block. A `call` statement runs the statements of its callee.

Rules:

- A failing `expect` or `runtime_expect` stops the program with an
  `E_NATIVE_EXPECT` message on standard error and an unsuccessful exit status.
  The message names the cell and shows the stored and the expected payload.
- A failing condition on [runtime extents](#runtime-extents) stops the program
  in the same way with an `E_RUNTIME_GUARD` message. An extent that is
  negative or above 2⁶³ − 1 stops it with an `E_RUNTIME_EXTENT` message.
- A program that stops prints no result. Writes that it completed before it
  stopped are not undone.
- The program frees its allocations when it ends, even when it stops early.

> **Implementation note.** A call that binds the result of its callee
> evaluates the `value` block of the callee after the statements of the callee
> have run. A call without `let` does not evaluate that block: the executable
> runs the statements of the callee only. The text of a failed `expect`, from
> the code `E_NATIVE_EXPECT` to the end of the line, is ASCII text of at most
> 361 bytes, and the executable builds it only after the comparison of the
> bits has failed. The generated program frees its allocations in a cleanup
> step that also runs after a failed statement. When that step fails too, the
> executable reports the failure of the cleanup and not the failure of the
> statement.

## Runtime extents

> **Syntax**
>
> ```text
> RuntimeStatement -> `runtime_allocate` IDENTIFIER `:` ElementType `[` Extent `]` RuntimeLayout
>     | `runtime_move` IDENTIFIER `->` IDENTIFIER
>     | `runtime_borrow` IDENTIFIER `=` AccessMode `(` IDENTIFIER `)`
>     | `runtime_release` `(` IDENTIFIER `)`
>     | `runtime_drop` `(` IDENTIFIER `)`
>     | `runtime_fill` `(` IDENTIFIER `,` Payload `)`
>     | `runtime_expect` `(` IDENTIFIER `,` INTEGER_LITERAL `,` INTEGER_LITERAL `,` Payload `)`
>     | RuntimeNumericalStatement
> RuntimeLayout -> `runtime_layout` `(` Extent `,` Extent `,` Extent `,` ( `true` | `false` ) `)`
> Extent -> INTEGER_LITERAL | IDENTIFIER
> ```

The statements above this section fix every size in the source. The
`runtime_` statements take sizes from scalars that the program computes. An
**extent** is a literal or an earlier `Nat` or `Int` binding.
`runtime_allocate d: F64[n] runtime_layout(rows, columns, leading, false);`
allocates `n` cells and fixes the one layout of the allocation, and
`runtime_borrow v = write(d);` lends that whole view. The owner and the loans
of such an allocation are **runtime** owners and loans; the others are
**static**. The other `runtime_` statements have the meaning of the
statements without the prefix. [Runtime maps](#runtime-maps) gives the
statements that multiply matrices of these sizes.

Rules:

- An extent must be a literal or a `Nat` or `Int` binding in scope
  (`E_RUNTIME_EXTENT`, or `E_RESOURCE_NAME` for a name that is not in scope).
  A program computes an extent in a `value` block; extents have no arithmetic
  of their own.
- An `Int` extent must not be negative when the program runs.
- `runtime_borrow` lends the whole layout of its allocation. It takes no
  layout and no offset.
- `leading` must be at least the number of rows and at least 1, even for an
  empty view. Padding stays uninitialized when every cell is written.
- The conditions on extents are capacity, layout bounds, dimensions that must
  be equal, and the cells of `runtime_expect`. The capacity and the layout of
  one `runtime_allocate` form one condition, and so do the layout and the
  cell of one `runtime_expect`. The condition on a capacity includes the
  largest size of an allocation, 2⁶³ − 1 bytes.
- The compiler decides a condition in which every extent is a literal. One
  that fails is an error (`E_RUNTIME_GUARD`), reported at the statement that
  the condition belongs to. A condition between an argument and a parameter
  of a call belongs to the `call` statement. A condition on the type of a
  parameter alone belongs to no statement and is reported at the function.
- The executable checks a condition in which some extent is a binding when
  the program runs, before the statement that needs it.
- A `runtime_` statement must name runtime bindings, an owner where the
  statement needs an owner and a loan where it needs a loan
  (`E_RUNTIME_TYPE`). A statement without the prefix must name static
  bindings (`E_RESOURCE_TYPE`, `E_RESOURCE_MOVE` or `E_RESOURCE_LOAN`, by the
  statement).
- A runtime owner must not be an owned result or an owned argument
  (`E_RESOURCE_TYPE`), and a runtime loan must not be an argument for a
  borrowed parameter (`E_RESOURCE_LOAN`).
- The rules of [Resource statements](#resource-statements) on owners, loans,
  access and initialization hold for runtime owners and loans. A violation is
  an error (`E_RUNTIME_SHAPE`).
- Every runtime loan covers its whole allocation. Two live loans of one
  allocation must therefore both be `read` loans, and a `read` or `read_write`
  loan needs an earlier write of the whole view. An empty view is no
  exception to either rule.
- At the end of a function, every runtime owner must have been dropped
  (`E_RUNTIME_CALL`).
- A `runtime_` statement must not be inside a branch, and neither may a call
  of a function that contains one, directly or through further calls
  (`E_RUNTIME_BRANCH`).
- An extent never proves that two spaces or bases are the same, and it is not
  a dispatch key.

## Runtime maps

> **Syntax**
>
> ```text
> RuntimeParameterType -> `RuntimeSpace` `<` Path `,` Extent `>`
>     | `RuntimeBasis` `<` IDENTIFIER `>`
>     | `RuntimeMap` `<` IDENTIFIER `,` IDENTIFIER `,` AccessMode `>` `initializes`?
> RuntimeNumericalStatement ->
>       `runtime_space` IDENTIFIER `=` `linear` `(` Path `,` Extent `)`
>     | `runtime_basis` IDENTIFIER `=` `basis` `(` IDENTIFIER `)`
>     | `runtime_map` IDENTIFIER `=`
>       `view` `(` IDENTIFIER `,` IDENTIFIER `,` IDENTIFIER `)`
>     | `runtime_gemm` `(` IDENTIFIER `,` IDENTIFIER `,` IDENTIFIER `,`
>       GemmMode `,` `NativeFast` GemmCoefficient* `)`
> ```

`runtime_space u = linear(I, m);` declares a space of dimension `m` over the
`indexed` implementation `I`, and `runtime_basis bu = basis(u);` a basis of
it. `runtime_map a = view(v, bs, bt);` presents the runtime loan `v` as the
matrix of a map from the space of the basis `bs` to the space of `bt`.
`runtime_gemm(a, b, out, overwrite, NativeFast);` writes the product of the
matrices `a` and `b` to `out`, times `alpha` when the statement gives one.
With `accumulate` it adds that product to `beta` times `out`.
[Matrix products](../linalg/maps-and-gemm.md#matrix-products) gives `GemmMode`
and `GemmCoefficient` and the meaning of the product. A function
receives spaces, bases and maps through parameters of the types
`RuntimeSpace<I, m>`, `RuntimeBasis<u>` and `RuntimeMap<bs, bt, access>`.

Rules:

- A parameter type must name earlier parameters only (`E_RESOURCE_NAME`).
- The path of `runtime_space u = linear(P, m)` and of `RuntimeSpace<P, m>`
  must name a linear implementation. Another `indexed` declaration there,
  such as a marker or a scalar base implementation, is an error
  (`E_RUNTIME_NUMERICAL`).
- The argument of `runtime_basis b = basis(u)` must be a runtime space
  (`E_RUNTIME_TYPE`).
- In `runtime_map m = view(v, bs, bt)`, `v` must be a runtime loan
  (`E_RUNTIME_TYPE`), and `bs` and `bt` must be runtime bases
  (`E_RUNTIME_NUMERICAL`). The cells of `v` must have the element type of the
  linear implementation of the two spaces (`E_RUNTIME_NUMERICAL`).
- A statement may use a runtime map only while the loan of the map is live.
  A map whose loan the function has released is an error
  (`E_RUNTIME_NUMERICAL`).
- The three operands of `runtime_gemm(a, b, out, …)` must be runtime maps
  (`E_RUNTIME_TYPE`). The source basis of `a` must be the target basis of
  `b`, and `out` must be a map from the source basis of `b` to the target
  basis of `a` (`E_RUNTIME_NUMERICAL`). Equal extents are not enough.
- An extent of a parameter type must be a literal or a `Nat` or `Int`
  parameter (`E_RUNTIME_EXTENT`). `RuntimeBasis<u>` must name a space
  (`E_RUNTIME_TYPE`), and `RuntimeMap<bs, bt, …>` two bases
  (`E_NUMERICAL_TYPE`).
- The arguments for these parameters must be the spaces, bases and maps of the
  caller that the parameter types relate. A basis that the caller declared
  separately is a different basis, even over a space of the same dimension
  (`E_RUNTIME_CALL`). For a map with such a basis the diagnostic names the
  argument, the parameter and both bases, as
  [Map parameters](../linalg/maps-and-gemm.md#map-parameters) describes.
- A `RuntimeMap` parameter with `initializes` promises that the body writes
  the whole view. A body that does not is an error (`E_RUNTIME_CALL`).
- The mode of `runtime_gemm` must be `overwrite` or `accumulate`
  (`E_NUMERICAL_TYPE`), and its policy `NativeFast` (`E_PARSE`). Its element
  type is `F64` or `Complex<F64>`.
- `alpha` and `beta` must be payloads of the element type of the maps
  (`E_RUNTIME_SHAPE`). A `coefficient(…)` there is an error
  (`E_RUNTIME_COEFFICIENT`), and `overwrite` takes no `beta`
  (`E_RUNTIME_SHAPE`).
- The output of `accumulate` must be an initialized `read_write` map, even
  for a `beta` of zero (`E_RUNTIME_SHAPE`).
- The `runtime_` statements multiply matrices only. Transforms, metrics,
  vectors and tensors have no statements with runtime extents.
- `runtime_gemm` is a product statement.
  [Building a numerical program](../linalg/maps-and-gemm.md#building-a-numerical-program)
  gives the rule on the option `--openblas-prefix` of `vastitas build` for a
  program whose entry point reaches one.

This function of
[`examples/packages/runtime-shapes`](https://github.com/MGYamada/Vastitas/tree/main/examples/packages/runtime-shapes)
multiplies two maps into a destination of its caller, at any three
dimensions:

```vast
{{#include ../../examples/packages/runtime-shapes/src/main.vast:multiply}}
```

Its caller `run` receives the three dimensions and a padding of the leading
dimensions. It computes the leading dimensions and the capacities in `value`
blocks:

```vast
{{#include ../../examples/packages/runtime-shapes/src/main.vast:run}}
```

It declares the spaces and bases from the dimensions:

```vast
{{#include ../../examples/packages/runtime-shapes/src/main.vast:spaces}}
```

It then allocates the storage, writes the two inputs, presents the loans as
maps and calls `multiply`:

```vast
{{#include ../../examples/packages/runtime-shapes/src/main.vast:maps}}
```

`main` of the example calls `run` at two sizes in one executable.

## Diagnostics

A **resource diagnostic** is a diagnostic for a rule of this chapter or of
the numerical chapters. [Diagnostics](../language/diagnostics.md) gives the
form of a diagnostic and of its notes, and
[Appendix B](../appendix/diagnostics.md) lists the `E_RESOURCE_` and
`E_RUNTIME_` codes.

Rules:

- A resource diagnostic points to the statement that breaks the rule. This
  holds even in an arm that the program does not select and in a function
  that no call reaches.
- A statement of a callee that breaks a rule with the views of a caller has
  its diagnostic at the statement of the callee. A note names the `call`
  statement.
- An argument that does not meet the type or the contract of its parameter
  has its diagnostic at the `call` statement.
- A failed branch join points to its `if`. A failure at the end of a body
  points to the block of the `value` that ends the body, at its `{`. Examples
  are an owner that the body leaves live and an owned result that does not
  meet its type.
- An error of the signature of a resource function points to the function.
  Examples are a contract that is not valid and an entry point with
  parameters.
- A diagnostic for the type of a scalar binding points to the type, unless
  the type is a pair type.
- The notes of the context come first. They name the function of the
  statement and then, from the callee outwards, each call that leads to the
  statement and the function of that call. For a statement or a call in an
  arm of a branch, a note names each `if` around it, from the inside out,
  before the note of its function.
- The notes on the operands follow. They name the owners, the loans and the
  other bindings of the statement, each with the place that introduced it.
- A diagnostic has at most 32 notes. For a longer chain of calls the compiler
  leaves out the notes of the outermost calls and keeps the notes on the
  operands.
- For a call argument in another basis than its parameter requires, the
  diagnostic names both bases, as
  [Map parameters](../linalg/maps-and-gemm.md#map-parameters) describes.
- The diagnostic of a `borrow` whose `read` or `read_write` view has an
  uninitialized cell (`E_RESOURCE_INIT`) names such a cell when the checker
  finds one.
- The checker searches for the cell after it has rejected the `borrow`, and
  the search has a bound, which
  [Appendix D](../appendix/limits.md#bounds-that-reject-nothing) gives. When
  the search finds no cell, the diagnostic says so and names none. This does
  not show that a cell is uninitialized: the checker also rejects a view
  whose cells are all written when it does not join the writes, as the rules
  of [Resource statements](#resource-statements) state.

The diagnostic of an uninitialized cell uses three words. The "logical" row
and column are the row and column of the cell in the view, which `store` and
`expect` take. The "physical" row and column are the stored row and the
stored column of the cell. Rows and columns count from 0. The "allocation
bytes" are the bytes of the cell, counted from the first byte of the
allocation; the range includes its first number and excludes its second. In
the view `layout(8, 3, 2, 4, true)` of cells of `F64`, logical row 0, column
2 is physical row 2, column 0 and has the allocation bytes `[24, 32)`.

In this program the view that `main` passes begins at byte 8 of its
allocation, and the layout of the `borrow` in `peek` begins at byte 0:

```vast
{{#include ../../examples/reject/packages/callee-region/main.vast}}
```

```text
{{#include ../../examples/reject/packages/callee-region.stderr}}
```

The diagnostic points to the `borrow` of the callee. Its notes name the
callee, the `call` statement, the caller and then the loan of the parameter.
