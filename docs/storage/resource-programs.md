# Resource programs

A **resource function** combines pure computation with explicit operations on
storage: it allocates buffers, lends views of them, writes and reads cells, and
frees them. The checker follows every owner and every loan through the body,
so a checked program never reads an unwritten cell, never writes through two
overlapping views and frees every allocation once. Resource functions exist
only in [manifest mode](../language/programs.md#manifest-mode).
[Storage and ownership](../storage-ownership.md) states the model behind these
rules.

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
`returns`, and a scalar result type. Its body is a list of
[resource statements](#resource-statements) followed by a `value` block, a
[block expression](../language/expressions.md#block-expressions) that computes
the scalar result. An owned result names an owner of the body, which the
function hands to its caller.

Rules:

- A resource function and a function must not have the same name in one module
  (`E_DUPLICATE`).
- A resource function is not a value, and a pure function, a method or a lambda
  cannot call one (`E_TYPE`). Resource functions are not generics and take no
  methods.
- A resource function must not call itself, directly or through other resource
  functions (`E_RESOURCE_RECURSION`).
- The `value` block must have the scalar result type (`E_TYPE`). It sees the
  scalar parameters and the scalar bindings of the body, and no owner, loan or
  other resource binding (`E_NAME`).
- Every owned result must name a live owner of the body that meets the result's
  type (`E_RESOURCE_NAME`, `E_RESOURCE_TYPE`). At the end of the body, every
  other owner must have been dropped, moved or handed to a call
  (`E_RESOURCE_ESCAPE`), and no loan of an owned result may be live
  (`E_RESOURCE_ESCAPE`).
- The checker checks every resource function of the program, also one that no
  call reaches.
- A resource function named `main` in the root module of the root package is
  the [entry point](../language/programs.md#the-entry-point). It must take no
  parameters and return no owners (`E_RESOURCE_ESCAPE`), and its result type
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

An **owner** is a binding that owns one allocation. `Owned<S, n>` is the type
of an owner of `n` elements of the element type `S`: `F64`, a binary64 number,
or `Complex<F64>`, a pair of them. A **loan** is a binding that gives access to
a rectangular **view** of an allocation for a limited time. `Read<S, r, c>`,
`Write<S, r, c>` and `ReadWrite<S, r, c>` are the types of loans of a view with
`r` rows and `c` columns.

`layout(offset, rows, columns, leading, transposed)` describes a view of an
allocation in column-major order: `offset` is its first byte, `leading` the
number of elements from one stored column to the next, and `transposed` says
whether the logical rows and columns are the stored columns and rows.

Rules:

- A layout must lie inside its allocation, `leading` must be at least the
  number of stored rows and at least 1, and `offset` must be a multiple of the
  element size, 8 bytes for `F64` and 16 for `Complex<F64>`. Another layout is
  an error (`E_RESOURCE_LAYOUT`).
- An owned parameter or result with `initialized [layout(…), …]` requires that
  the cells of those views are initialized. An argument or result that does not
  meet the element type, the size or this contract is an error
  (`E_RESOURCE_TYPE`). Capacity and padding imply no initialization.
- An argument for a borrowed parameter must be a live loan (`E_RESOURCE_LOAN`)
  with the element type and the logical shape of the parameter
  (`E_RESOURCE_TYPE`). The callee sees the caller's view, with its offset,
  padding and transposition.
- A loan passed to a `Write` or `ReadWrite` parameter must permit writing. A
  read loan is an error (`E_RESOURCE_ACCESS`).
- A parameter with `initializes` promises that the callee initializes every
  cell of the view. A body that leaves a cell unwritten on some path is an
  error (`E_RESOURCE_INIT`). After the call, the caller may read the view.
- Two arguments of one call that may overlap must both be read loans
  (`E_RESOURCE_ALIAS`). Parameter names prove no separation.
- An integer in a storage type or layout must fit in 64 bits
  (`E_RESOURCE_LIMIT`).

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
| `allocate d: F64[8];` | Allocate 8 uninitialized elements and bind their owner `d` |
| `move d -> e;` | Hand the allocation of `d` to the owner `e`; `d` ends |
| `drop(d);` | Free the allocation of `d`; `d` ends |
| `borrow v = read(d, layout(…));` | Lend a view of the owner or loan `d` as the loan `v`; also `write` and `read_write` |
| `release(v);` | End the loan `v` |
| `transpose(v);` | Swap the logical rows and columns of `v`, without copying |
| `fill(v, p);` | Write the payload `p` to every cell of `v` |
| `store(v, i, j, p);` | Write `p` to the cell in row `i` and column `j` of `v` |
| `expect(v, i, j, p);` | At run time, fail unless that cell holds the bits of `p` |
| `copy(a, b);` | Copy every cell of the view `a` to the view `b` |

`borrow` without a layout lends the storage of an owned map, as
[Numerical maps](../linalg/maps-and-gemm.md) describes, and that chapter gives
the numerical statements.

Rules:

- A resource binding must not reuse a name of the function, also after its
  owner or loan has ended (`E_DUPLICATE`). A statement that names a binding
  which is not in scope is an error (`E_RESOURCE_NAME`).
- `move`, `drop` and an owned argument require a live owner. An owner that was
  moved, dropped or handed to a call is an error (`E_RESOURCE_MOVE`). They also
  require that no loan of the allocation is live (`E_RESOURCE_LOAN`).
- A `read` or `read_write` loan requires that every cell of its view is
  initialized (`E_RESOURCE_INIT`). `fill` initializes its view and `store` one
  cell. Stores that cover every cell of a view initialize it; a `write` loan
  may cover uninitialized cells.
- Two live loans whose views may overlap must both be read loans
  (`E_RESOURCE_ALIAS`). Loans of views that the checker shows to be disjoint,
  and loans of different allocations, are compatible.
- A loan borrowed from a loan is its **child**. While a child is live, its
  parent gives no access, and a child must be released before its parent
  (`E_RESOURCE_LOAN`). Releasing a loan twice is an error (`E_RESOURCE_LOAN`).
- `fill`, `store` and the target of `copy` require a loan that permits
  writing (`E_RESOURCE_ACCESS`). The cell of `store` and `expect` must lie in
  the view (`E_RESOURCE_BOUNDS`).
- A payload must have the element type of its view, and the two views of
  `copy` must have the same element type and logical shape
  (`E_RESOURCE_TYPE`).
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
`0x1.8p1`, whose value is the hexadecimal significand times 2 to the decimal
exponent after `p`. `0x1.8p1` is 3. `f64_bits(n)` and `complex_bits(m, n)`
give the 64 bits of each component as an unsigned integer.

Rules:

- The number in `f64` and `complex` must be a finite binary64 value, exactly.
  A number that binary64 only approximates, such as `0.1`, is an error
  (`E_RESOURCE_LITERAL`), and so are overflow and underflow. The compiler never
  rounds a payload.
- `f64` and `complex` denote positive zero for `0`. A negative zero, an
  infinity and a NaN are written with `f64_bits` or `complex_bits`.
- An exponent must fit in a signed 64-bit integer (`E_RESOURCE_LITERAL`).

```vast
fill(output, f64(0x1.8p1));                      // 3.0
store(output, 0, 0, f64(-0x1p-2));               // -0.25
fill(complex_output, complex(0x1.8p0, -0x1p1));  // 1.5 - 2i
```

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
and binds `x`. A `value` block may call functions, generics and lambdas.
`call f(a, …) -> (d, …);` calls the resource function `f` with the named
bindings and binds its owned results, in order, to fresh owners.
`let x: T = call f(…) -> (…);` also binds the scalar result of `f`. `if c { … }
else { … }` runs one of two lists of statements, by the `Bool` binding `c`.

Rules:

- The type of a scalar binding must be `Nat`, `Int`, `Bool` or `Unit`, and the
  `value` block must have it (`E_TYPE`). The block sees the earlier scalar
  bindings only (`E_NAME`).
- The arguments of a call are names of bindings. A literal argument is an
  error (`E_PARSE`); bind it with `let` first.
- A scalar argument must have the type of its parameter, and the type of
  `let x: T = call …` must be the result type of the callee
  (`E_RESOURCE_VALUE`).
- The number of bindings after `->` must be the number of owned results of the
  callee (`E_RESOURCE_ARITY`).
- A call ends the owners that it hands to owned parameters, and it suspends
  the loans that it passes until it returns.
- The condition of a branch must be a `Bool` binding or a literal
  (`E_RESOURCE_VALUE`), and `else` is required (`E_PARSE`).
- The checker checks both arms of a branch, also for a literal condition. After
  the branch, both arms must leave the same owners and loans live
  (`E_RESOURCE_JOIN`). A cell counts as initialized after the branch only when
  both arms initialize it.
- A scalar binding of an arm is not visible in the other arm or after the
  branch (`E_NAME`).

[`examples/packages/resource-values`](https://github.com/MGYamada/Vastitas/tree/main/examples/packages/resource-values)
passes scalars through resource functions and branches on one:

```vast
{{#include ../../examples/packages/resource-values/src/main.vast}}
```

The executable prints `42`.

## Running a resource program

An executable runs the statements of its entry point in order and then prints
the value of its `value` block.

Rules:

- A failing `expect` stops the program with an `E_NATIVE_EXPECT` message on
  standard error and an unsuccessful exit status. The message names the cell
  and shows the stored and the expected payload.
- A program that stops prints no result. Writes that it completed before it
  stopped are not undone.
- The program frees its allocations when it ends, also when it stops early.

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
> RuntimeParameterType -> `RuntimeSpace` `<` Path `,` Extent `>`
>     | `RuntimeBasis` `<` IDENTIFIER `>`
>     | `RuntimeMap` `<` IDENTIFIER `,` IDENTIFIER `,` AccessMode `>` `initializes`?
> ```

The statements above this section fix every size in the source. The
`runtime_` statements take sizes from scalars that the program computes. An
**extent** is a literal or an earlier `Nat` or `Int` binding.
`runtime_allocate d: F64[n] runtime_layout(rows, columns, leading, false);`
allocates `n` elements and fixes the one layout of the allocation, and
`runtime_borrow v = write(d);` lends that whole view. The other statements act
as the statements without the prefix do.
[Numerical maps](../linalg/maps-and-gemm.md) gives the numerical statements
`runtime_space`, `runtime_basis`, `runtime_map` and `runtime_gemm` and the
parameter types.

Rules:

- An extent is computed in a `value` block; extents have no arithmetic of their
  own. An `Int` extent must not be negative when the program runs.
- A `runtime_borrow` lends the whole layout of its allocation. It takes no
  layout and no offset.
- `leading` must be at least the number of rows and at least 1, also for an
  empty view. Padding stays uninitialized when every cell is written.
- A condition on extents that holds for no values, or fails for literal
  extents, is an error when the program is checked (`E_RUNTIME_GUARD`). Other
  conditions on extents are checked when the program runs, before the
  statement that needs them: capacity, layout bounds, dimensions that must be
  equal, and cells of `runtime_expect`.
- An extent never proves that two spaces or bases are the same, and it is not
  a dispatch key.
- A `runtime_` statement, and a call of a function that contains one, must not
  be inside a branch.

[`examples/packages/runtime-shapes`](https://github.com/MGYamada/Vastitas/tree/main/examples/packages/runtime-shapes)
multiplies matrices at two sizes in one executable.

## Diagnostics

A resource diagnostic points to the statement that fails, also in an arm that
the program does not select. A failure inside a called function points to the
statement of the callee and names the call in a note. A failed branch join
points to its `if`. Notes name the owners and loans involved and where the
program introduced them; a diagnostic has at most 32 notes.
[Appendix B](../appendix/diagnostics.md) lists the `E_RESOURCE_` codes.

## Moved sections

These anchors keep older links working.

- <a id="resource-source"></a><a id="package-resource-functions-protocol-8"></a>Package resource functions: [Resource functions](#resource-functions).
- <a id="resource-source--explicit-source-contracts"></a><a id="explicit-source-contracts"></a>Explicit source contracts: [Storage types](#storage-types), [Resource statements](#resource-statements) and [Payloads](#payloads).
- <a id="pure-values-and-executable-boundaries"></a>Pure values and executable boundaries: [Scalar values and calls](#scalar-values-and-calls) and [Running a resource program](#running-a-resource-program).
- <a id="resource-diagnostics"></a>Resource diagnostics: [Diagnostics](#diagnostics).
- <a id="evidence-and-remaining-work"></a>Evidence and remaining work: [Resource checking](../internals/resource-checking.md#evidence-and-remaining-work).
- <a id="runtime-shapes"></a><a id="runtime-extents-and-caller-owned-maps"></a><a id="public-interface"></a>Runtime extents and caller-owned maps: [Runtime extents](#runtime-extents).
- <a id="exact-frame-and-guard-contract"></a>Frame and guard contract: [Resource checking](../internals/resource-checking.md#runtime-extent-frames-and-guards).
- <a id="proof-boundary"></a><a id="execution-costs-and-limits"></a><a id="validation"></a>Proof boundary, costs and validation: [Resource checking](../internals/resource-checking.md#runtime-extent-proof-boundary).
