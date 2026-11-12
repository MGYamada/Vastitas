# Numerical maps

A **numerical map** presents a view of storage as the matrix of a linear map
between two **spaces**, in a named **basis** of each. The statements of this
chapter declare spaces, bases and maps in a
[resource function](../storage/resource-programs.md) and multiply maps with
`gemm`. Spaces and bases have nominal identity: the compiler multiplies two
maps only when the bases between them are the same basis, and equal
dimensions prove nothing. The rules of
[Resource programs](../storage/resource-programs.md) on owners, loans, access
and initialization hold for the storage of every map.

> **Syntax**
>
> ```text
> NumericalStatement -> SpaceStatement | BasisStatement | MapStatement
>     | GemmStatement | UnpackMapStatement
>     | TransformStatement | TensorStatement | NetworkContraction | TreeContraction
> ```

[Transforms, evaluation and metrics](transforms-and-metrics.md) gives
`TransformStatement`, and
[Networks, packing and contraction trees](networks-and-packing.md) gives the
last three forms.

Rules:

- A space, a basis and a map are bindings of the resource function, under the
  naming rules of
  [Resource statements](../storage/resource-programs.md#resource-statements).
- A numerical statement that names a binding which is not in scope is an error
  (`E_RESOURCE_NAME`). A binding of another kind than the statement needs is
  an error (`E_NUMERICAL_TYPE`), unless a rule of this chapter gives another
  code.
- A space, a basis and a map are not scalars, owners or loans. A `value` block
  does not see them (`E_NAME`). A storage statement that names one is an
  error (`E_RESOURCE_LOAN`, `E_RESOURCE_MOVE` or `E_RESOURCE_TYPE`, by the
  statement), apart from the `release` of a map.
- A space, a basis or a map that an arm of a branch declares is visible in
  that arm only (`E_RESOURCE_NAME`).
- The statements of this chapter name static bindings. The `runtime_`
  statements of [Runtime maps](../storage/resource-programs.md#runtime-maps)
  name runtime bindings, and one function may contain both.

## Linear implementations

> **Syntax**
>
> ```text
> ScalarBaseImplementation -> `indexed` `implementation` IDENTIFIER
>     `(` Path `,` `scalar_base` `(` GeometricSetting `,` CoefficientKind `)` `)`
>     `capabilities` `(` Capabilities? `)` `;`
> LinearImplementation -> `indexed` `implementation` IDENTIFIER
>     `(` Path `,` `linear_descriptor` `(` Path `,` CoefficientKind `)` `)`
>     `capabilities` `(` Capabilities? `)` `;`
> GeometricSetting -> `scheme` | `smooth`
> CoefficientKind -> `real` | `complex`
> ```

A space needs a **linear implementation**, an `indexed` declaration that says
over which base and with which coefficients its spaces are. Four declarations
lead to one:

- `indexed marker K;` declares a coefficient marker.
- `indexed implementation S(K, scalar_base(setting, kind)) capabilities();`
  declares a **scalar base** implementation: the base of a geometric setting
  with real or complex coefficients.
- `indexed global B(S);` declares one base object of `S`.
- `indexed implementation L(K, linear_descriptor(B, kind)) capabilities();`
  declares a linear implementation over the base `B`.

A space of a `real` linear implementation stores `F64` cells, and a space of a
`complex` one stores `Complex<F64>` cells. These declarations create no space
and no storage. A linear implementation states no algebraic law, and it
converts no `Scheme` or `CInfScheme` value into a linear map.
[Indexed declarations](../indexed-source.md) describes markers, global
objects and the general rules of `indexed` declarations.

Rules:

- The base of `linear_descriptor(B, kind)` must be an `indexed global` of a
  scalar base implementation (`E_TYPE`).
- A `scalar_base` of the setting `smooth` must have the kind `real`
  (`E_TYPE`). A `scheme` base may have either kind.
- Over a `scheme` base, a linear implementation must have the kind and the
  marker of the implementation of its base (`E_TYPE`).
- Over a `smooth` base, a `real` linear implementation must have the marker of
  the implementation of its base, and a `complex` one must have another marker
  (`E_TYPE`).
- All implementations of one marker that state a coefficient kind must state
  the same kind, even an implementation that nothing uses (`E_TYPE`). A
  `smooth_affine` implementation counts as `real`.
- The capability list of both forms must be empty (`E_TYPE`).
  [Implementations](../indexed-source.md#implementations) gives the
  production `Capabilities`.
- A scalar base implementation and a linear implementation serve no
  `descriptor` primitive, no `global` primitive and no `point` or `morphism`
  family. [Families](../indexed-source.md#families) and
  [Primitives](../indexed-source.md#primitives) give these rules.

The compiler reports an error of these rules at the declaration that breaks
the rule. For a rule on an implementation, the message states the rule and
names the declarations by their paths. For the rule on the kinds of one
marker, the compiler reports one implementation of the marker, and the
message names another implementation whose kind differs.

The examples of this chapter use these declarations:

```vast
{{#include ../../examples/packages/numerical-declarations/src/profiles/mod.vast}}
```

## Spaces and bases

> **Syntax**
>
> ```text
> SpaceStatement -> `space` IDENTIFIER `=` ( LinearSpace | DerivedSpaceExpression ) `;`
> LinearSpace -> `linear` `(` Path `,` INTEGER_LITERAL `)`
> BasisStatement -> `basis` IDENTIFIER `=`
>     ( `basis` `(` IDENTIFIER `)` | DerivedBasisExpression ) `;`
> ```

`space u = linear(L, n);` declares a space of dimension `n` of the linear
implementation `L`. `basis b = basis(u);` declares a basis of the space `u`.
A space holds no storage, and a basis holds no vectors: a basis is the name by
which a map says what its coordinates mean.
[Transforms, evaluation and metrics](transforms-and-metrics.md) gives the
dual and conjugate spaces of `DerivedSpaceExpression` and the bases of
`DerivedBasisExpression`.

Rules:

- The path of `linear(P, n)` must name a linear implementation. Another
  `indexed` declaration is an error (`E_NUMERICAL_TYPE`), and a declaration
  that is not `indexed` is an error (`E_TYPE`). A `use` alias of the
  implementation names the same implementation.
- The dimension must be an integer literal that fits in 64 bits
  (`E_RESOURCE_LIMIT`). It may be 0. A dimension that the program computes
  needs `runtime_space`.
- The dimension times the size of a cell, 8 bytes for a real and 16 bytes for
  a complex implementation, must not exceed 2⁶³ − 1 bytes
  (`E_NUMERICAL_TYPE`).
- The argument of `basis(u)` must be a static space (`E_NUMERICAL_TYPE`).
- Every `space` statement declares a different space, even for one
  implementation and one dimension. Every `basis` statement declares a
  different basis, even for one space.
- Where a statement needs one space or one basis, another one is an error
  (`E_NUMERICAL_TYPE`).

```vast
{{#include ../../examples/packages/numerical/src/real/mod.vast:spaces}}
```

## Maps

> **Syntax**
>
> ```text
> MapStatement -> `map` IDENTIFIER `=` MapExpression `;`
> MapExpression -> `view` `(` IDENTIFIER `,` IDENTIFIER `,` IDENTIFIER `)`
>     | `view` `(` IDENTIFIER `,` IDENTIFIER `)`
>     | `owned` `(` IDENTIFIER `,` Layout `,` IDENTIFIER `,` IDENTIFIER `)`
>     | `pack` `(` IDENTIFIER `)`
>     | TransformedMapExpression
> ```

`map m = view(v, bs, bt);` presents the loan `v` as the matrix of a linear map
from the space of the basis `bs` to the space of the basis `bt`. The statement
copies nothing and reads no cell. [Owned maps](#owned-maps) gives `view` with
two arguments and `owned`, [Owned-map packages](#owned-map-packages) gives
`pack`, and [Transforms, evaluation and metrics](transforms-and-metrics.md)
gives `TransformedMapExpression`.

Rules:

- The first argument of `view(v, bs, bt)` must be a live static loan without
  a live child, and the other two must be bases (`E_NUMERICAL_TYPE`).
- The spaces of the two bases must have the same linear implementation
  (`E_NUMERICAL_TYPE`). The same declaration text in another package is
  another implementation.
- The view of the loan must have as many rows as the space of `bt` has
  dimensions and as many columns as the space of `bs`. Its element type must
  be `F64` for a real and `Complex<F64>` for a complex implementation
  (`E_NUMERICAL_TYPE`).
- A map may present a loan of any access, including a `write` loan of
  uninitialized cells, and several maps may present one loan.
- A statement may use a map only while the loan of the map is live, has no
  live child and has the layout that it had at the `map` statement
  (`E_NUMERICAL_TYPE`). Writing cells through the loan does not end the map.
- A map is not a loan. `fill`, `store`, `expect`, `copy` and `transpose`
  must name the loan, and a map there is an error (`E_RESOURCE_LOAN`). So is a
  map as the argument for a borrowed parameter.
- `release(m)` may name a map `m` in place of its loan. It ends that loan.
- A view has at most 2³¹ − 1 rows and columns, so a space of a higher
  dimension cannot be the source or the target of a map.

## Matrix products

> **Syntax**
>
> ```text
> GemmStatement -> `gemm` `(` IDENTIFIER `,` IDENTIFIER `,` IDENTIFIER `,`
>     GemmMode `,` `NativeFast` GemmCoefficient* `)` `;`
> GemmMode -> `overwrite` | `accumulate`
> GemmCoefficient -> `,` ( `alpha` | `beta` ) `=`
>     ( Payload | `coefficient` `(` IDENTIFIER `)` )
> ```

`gemm(a, b, c, mode, NativeFast);` multiplies two maps. With `b` a map from
`U` to `V` and `a` a map from `V` to `W`, it writes to `c`, a map from `U` to
`W`, the matrix of `a` after `b`. For the matrices `A`, `B` and `C` of the
three maps, `overwrite` computes `C := alpha·A·B` and ignores the old cells of
`c`, and `accumulate` computes `C := alpha·A·B + beta·C`. Each coefficient is
1 unless the statement gives one. A coefficient is a
[payload](../storage/resource-programs.md#payloads) or `coefficient(s)`, the
cell of the loan `s` when the statement runs. The statement conjugates nothing
and transposes nothing, for real and for complex maps.

`NativeFast` is the one numerical policy. It says that the native routine
computes the product in binary64 arithmetic, in the order of operations of
that routine. The result is not an exact product of real numbers.
[The GEMM contract](../storage-ownership.md#the-gemm-contract) states the
model behind the rules of this section: what a product reads and writes in
each mode, and what the adapter must check before the first write.

Rules:

- The three operands must be maps (`E_NUMERICAL_TYPE`).
- The source basis of `a` must be the target basis of `b`. The source basis
  of `c` must be the source basis of `b`, and the target basis of `c` the
  target basis of `a` (`E_NUMERICAL_TYPE`). Equal dimensions, one
  implementation or one space are not enough.
- The loans of `a` and `b` must permit reading, and the loan of `c` must
  permit writing (`E_RESOURCE_ACCESS`).
- With `overwrite`, the loan of `c` may be a `write` loan of uninitialized
  cells. The statement initializes every cell of the view of `c`.
- With `accumulate`, the loan of `c` must be a `read_write` loan, even for a
  `beta` of zero (`E_RESOURCE_GEMM`).
- The view of `c` must not be transposed (`E_RESOURCE_GEMM`). The views of
  `a` and `b` may be transposed.
- The view of `c` must share no cell with the view of `a` or of `b`
  (`E_RESOURCE_GEMM`). `a` and `b` may be one map, and their views may
  overlap.
- The mode must be `overwrite` or `accumulate` (`E_NUMERICAL_TYPE`), and the
  policy must be `NativeFast` (`E_PARSE`).
- `alpha` and `beta` may each appear once, in either order (`E_DUPLICATE`).
  Another name there is an error (`E_NUMERICAL_TYPE`).
- `overwrite` takes no `beta`, even `beta=f64(0)`
  (`E_RESOURCE_COEFFICIENT`).
- A payload coefficient must have the element type of the maps
  (`E_RESOURCE_COEFFICIENT`).
- The loan of `coefficient(s)` must be a live static loan without a live
  child (`E_RESOURCE_LOAN`) that permits reading (`E_RESOURCE_ACCESS`). Its
  view must have one row and one column and the element type of the maps, and
  it must share no cell with `c` (`E_RESOURCE_COEFFICIENT`). It may share
  cells with `a`, with `b` and with the other coefficient.
- The rules hold for a dimension of 0. A product whose output has no cell
  writes nothing. A product with an inner dimension of 0 leaves `beta·C`,
  whatever `alpha` is: zeros for `overwrite` and for a `beta` of zero.
- The executable reads a `coefficient` cell when the statement runs, before
  it writes the output. It makes every check of the statement before the
  first write. A failing check stops the program with an `E_NATIVE_` message,
  as [Running a resource program](../storage/resource-programs.md#running-a-resource-program)
  describes for `expect`.
- The compiler checks the numerical statements of both arms of a branch.
  After a branch the output of a `gemm` counts as initialized only when both
  arms write it.

This fragment of
[`examples/packages/numerical`](https://github.com/MGYamada/Vastitas/tree/main/examples/packages/numerical)
multiplies a 2×3 matrix by a 3×2 matrix into a 2×2 output:

```vast
{{#include ../../examples/packages/numerical/src/real/mod.vast:product}}
```

A coefficient scales the product, and `accumulate` adds to the output.
[`examples/packages/gemm-coefficients`](https://github.com/MGYamada/Vastitas/tree/main/examples/packages/gemm-coefficients)
multiplies the matrices (2) and (3). Its first product has a payload as
`alpha` and writes 3:

```vast
{{#include ../../examples/packages/gemm-coefficients/main.vast:overwrite}}
```

Its second product reads `alpha` from the cell of the loan `scale`, which
holds 4, and adds the product to twice the old output. The output then holds
30:

```vast
{{#include ../../examples/packages/gemm-coefficients/main.vast:accumulate}}
```

In this program `other` has the implementation and the dimension of `v`, but
it is another space:

```vast
{{#include ../../examples/reject/packages/other-space/main.vast}}
```

```text
{{#include ../../examples/reject/packages/other-space.stderr}}
```

## Map parameters

> **Syntax**
>
> ```text
> NumericalParameterType -> `Space` `<` Path `,` INTEGER_LITERAL `>`
>     | `Basis` `<` IDENTIFIER `>`
>     | ( `ReadMap` | `WriteMap` | `ReadWriteMap` )
>       `<` IDENTIFIER `,` IDENTIFIER `>` `initializes`?
>     | NumericalResultType
>     | TransformParameterType
> ```

A resource function receives spaces, bases and maps through parameters.
`Space<L, n>` is the type of a space of dimension `n` of the linear
implementation `L`. `Basis<u>` is the type of a basis of the space that the
parameter `u` receives. `ReadMap<bs, bt>`, `WriteMap<bs, bt>` and
`ReadWriteMap<bs, bt>` are the types of a map from the space of `bs` to the
space of `bt` whose loan permits reading, writing or both.
[Owned maps](#owned-maps) gives `NumericalResultType`, and
[Transforms, evaluation and metrics](transforms-and-metrics.md) gives
`TransformParameterType`.

Rules:

- The rules of [Spaces and bases](#spaces-and-bases) on the path and on the
  dimension of `linear(P, n)` hold for `Space<P, n>`. A dimension that is not
  an integer literal is an error (`E_PARSE`).
- `Basis<u>` must name an earlier space parameter, and a map type must name
  two earlier basis parameters. A name that is no earlier parameter is an
  error (`E_RESOURCE_NAME`), and an earlier parameter of another kind is an
  error (`E_NUMERICAL_TYPE`). The space and basis parameters of
  [Parameter types](transforms-and-metrics.md#parameter-types) fit too.
- The argument for `Space<P, n>` must be a static space of the implementation
  `P` and the dimension `n` (`E_NUMERICAL_TYPE`). One space may be the
  argument for two `Space` parameters.
- The argument for `Basis<u>` must be a basis of the space that is the
  argument for `u` (`E_NUMERICAL_TYPE`). Every basis of that space fits.
- The argument for a map parameter must be a map whose source basis is the
  argument for `bs` and whose target basis is the argument for `bt`
  (`E_NUMERICAL_TYPE`). Another basis of the same space does not fit. The
  diagnostic names the argument and the parameter. For the source basis, for
  the target basis or for both, it names the basis of the map and the basis
  that the parameter requires. Notes point to the declarations of those bases
  and of the parameter.
- The loan of a map passed to `ReadMap` or `ReadWriteMap` must permit
  reading, and the loan of a map passed to `WriteMap` or `ReadWriteMap` must
  permit writing (`E_RESOURCE_ACCESS`).
- A map parameter with `initializes` promises that the body initializes every
  cell of the view on every path (`E_RESOURCE_INIT`). Cells that a callee
  writes count as initialized for the caller, with or without `initializes`.
- One map may be the argument for several `ReadMap` parameters. A map passed
  to a `WriteMap` or `ReadWriteMap` parameter must not be the argument for
  another map parameter (`E_RESOURCE_ALIAS`). The rule is the rule of
  [Storage types](../storage/resource-programs.md#storage-types) on arguments
  whose views may overlap: it also holds for two maps of one loan, and for a
  map and its loan.
- In the body, a map parameter is a map, not a loan. A body must not release
  it (`E_RESOURCE_LOAN`).
- The compiler checks a function once on its own, with a different space for
  every `Space` parameter and a different basis for every `Basis` parameter,
  and once more at every call. A body that needs two parameters to be one
  space or one basis is an error (`E_NUMERICAL_TYPE`), even when every call
  passes one space for both.

This function of
[`examples/packages/linear-transforms`](https://github.com/MGYamada/Vastitas/tree/main/examples/packages/linear-transforms)
receives two spaces, a basis of each and three maps, and multiplies two of
the maps into the third:

```vast
{{#include ../../examples/packages/linear-transforms/src/main.vast:multiply}}
```

In this program `alternate_basis` is a basis of the space of `sensor_basis`,
but it is another basis:

```vast
{{#include ../../examples/reject/packages/other-basis/main.vast}}
```

```text
{{#include ../../examples/reject/packages/other-basis.stderr}}
```

## Owned maps

> **Syntax**
>
> ```text
> NumericalResultType -> `OwnedMap` `<` IDENTIFIER `,` IDENTIFIER `>`
>     | `OwnedMapTo` `<` IDENTIFIER `,` INTEGER_LITERAL `>`
> ```

An **owned map** is an owner whose allocation holds the initialized matrix of
a map between two bases, in one view. `map r = owned(d, layout(…), bs, bt);`
turns the owner `d` into the owned map `r` from the space of `bs` to the space
of `bt`; `d` ends, and nothing is allocated or copied. `borrow v = read(r);`
without a layout lends the view of that layout, also with `write` and
`read_write`. `map m = view(v, r);` presents the loan `v` as a map with the
bases of `r`. `OwnedMap<bs, bt>` is the type of an owned map as a parameter
or as an owned result.

Rules:

- In `owned(d, layout(…), bs, bt)`, `d` must be a live static owner
  (`E_NUMERICAL_TYPE`) without a live loan (`E_RESOURCE_LOAN`).
- The layout must lie in the allocation, with as many rows as the space of
  `bt` has dimensions and as many columns as the space of `bs`. The allocation
  must have the element type of the implementation (`E_NUMERICAL_TYPE`).
- Every cell of the view must be initialized (`E_RESOURCE_INIT`). Padding
  need not be.
- An owned map is an owner. The rules of
  [Resource statements](../storage/resource-programs.md#resource-statements)
  on `move`, `drop`, calls and the end of a body hold for it. `move r -> s;`
  makes `s` the owned map.
- `borrow` without a layout must name an owned map (`E_NUMERICAL_TYPE`).
  `borrow` with a layout may name one too, and it lends the view that it
  states.
- In `view(v, r)`, `r` must be an owned map, and `v` must be a live loan of
  the allocation of `r`, with the layout of `r` and without a live child
  (`E_NUMERICAL_TYPE`).
- A loan of an owned map is an ordinary loan. `view` with three arguments may
  present it in any bases that fit its shape and element type.
- An owned map is not a map: as an operand of `gemm` it is an error
  (`E_NUMERICAL_TYPE`).
- The argument for an `OwnedMap<bs, bt>` parameter must be an owned map from
  the argument for `bs` to the argument for `bt` (`E_NUMERICAL_TYPE`), without
  a live loan (`E_RESOURCE_LOAN`). The call ends the owner. For an owned map
  with another basis the diagnostic names the bases as
  [Map parameters](#map-parameters) describes.
- An `OwnedMap<bs, bt>` result must name `Basis` parameters
  (`E_RESOURCE_NAME` for a basis that the body declares). At the end of the
  body its binding must be an owned map between the arguments for those
  parameters (`E_NUMERICAL_TYPE`). For a binding with another basis, notes
  name that basis and the `Basis` parameter that the result type names. The
  caller gets an owned map between its own bases, with the allocation and the
  layout that the callee left.
- An owned map may be the argument for an `Owned<S, n>` parameter and the
  binding of an `Owned<S, n>` result. The receiver has an owner without
  bases.
- The compiler checks a function with an `OwnedMap` parameter on its own with
  an allocation that the view fills exactly. A `borrow` of the parameter with
  a layout must fit that allocation and the allocation of every caller
  (`E_RESOURCE_LAYOUT` or `E_RESOURCE_INIT`). A `borrow` without a layout
  always fits.

This function of
[`examples/packages/generative-owned-map`](https://github.com/MGYamada/Vastitas/tree/main/examples/packages/generative-owned-map)
receives an owned map, writes its cells and hands it back:

```vast
{{#include ../../examples/packages/generative-owned-map/src/real/mod.vast:update}}
```

## Owned-map packages

> **Syntax**
>
> ```text
> UnpackMapStatement -> `unpack` IDENTIFIER `as`
>     `(` IDENTIFIER `,` IDENTIFIER `,` IDENTIFIER `)` `;`
> ```

An `OwnedMap<bs, bt>` result names bases that are parameters, so it cannot
return a map into a space that the function declares itself. An **owned-map
package** can. `map p = pack(r);` turns the owned map `r` into the owned-map
package `p`: an owner that records the source basis and the dimension of the
target space, and hides the target space and its basis. `OwnedMapTo<bs, n>`
is its type. `unpack p as (w, bw, r);` opens `p`. It declares a fresh space
`w`, a fresh basis `bw` of `w` and the owned map `r` from the source basis to
`bw`, with the same allocation and layout. Neither statement copies a cell.
An owned-map package is not a [package](../packages.md) of source files, and
it is not an
[existential package](../language/geometric-types.md#existential-packages).

Rules:

- `pack(r)` must name an owned map (`E_NUMERICAL_PACKAGE`) without a live
  loan (`E_RESOURCE_LOAN`). The target space of `r` must not be a dual or a
  conjugate space (`E_NUMERICAL_PACKAGE`). `pack` ends `r`.
- An owned-map package is an owner. Only `move`, `drop`, `unpack`, an
  `OwnedMapTo` parameter and an `OwnedMapTo` result may take it. `move` makes
  its target the package. At the end of the body the package must have ended
  (`E_RESOURCE_ESCAPE`).
- Another use of an owned-map package is an error. A `borrow` with a layout,
  `owned`, `pack` and an `Owned<S, n>` parameter or result report
  `E_NUMERICAL_PACKAGE`. A `borrow` without a layout, `view`, `gemm` and an
  `OwnedMap` parameter or result report `E_NUMERICAL_TYPE`. A statement that
  needs a loan reports `E_RESOURCE_LOAN`.
- `unpack p as (w, bw, r)` must name a live owned-map package
  (`E_NUMERICAL_PACKAGE`) and three names that are not in use
  (`E_DUPLICATE`). It ends `p`.
- The space and the basis of an `unpack` differ from every other space and
  basis. This includes those of another `unpack` of the same storage after a
  second `pack`.
- The argument for an `OwnedMapTo<bs, n>` parameter must be an owned-map
  package whose source basis is the argument for `bs` and whose target space
  has the dimension `n` (`E_NUMERICAL_TYPE`). The binding of an
  `OwnedMapTo<bs, n>` result must be such a package at the end of the body
  (`E_NUMERICAL_TYPE`). For a package with another source basis the
  diagnostic names both bases, as [Map parameters](#map-parameters) and
  [Owned maps](#owned-maps) describe.
- In a branch, the names of an `unpack` are visible in its arm only
  (`E_RESOURCE_NAME`), and the owned map must end in that arm
  (`E_RESOURCE_JOIN`).

This function declares the target space itself and returns the map in an
owned-map package:

```vast
{{#include ../../examples/packages/generative-owned-map/src/real/mod.vast:create}}
```

Its caller moves the package, opens it and borrows the owned map:

```vast
{{#include ../../examples/packages/generative-owned-map/src/real/mod.vast:run}}
```

## Building a numerical program

`vastitas check` needs no numerical library. `vastitas build` links the
numerical runtime and OpenBLAS for a program whose entry point reaches a
**product statement**: `gemm`, `runtime_gemm`, `evaluate`, `hermitian`,
`hermitian_diagonal`, `contract`, `contract3`, `contract3_cached` or
`contract_tree`.

```sh
target/debug/vastitas check --manifest-path examples/packages/numerical/Vastitas.toml
target/debug/vastitas build --manifest-path examples/packages/numerical/Vastitas.toml \
  --openblas-prefix /path/to/openblas -o target/numerical-example
./target/numerical-example
```

The executable prints `42`. [Numerical builds](../guide/cli.md#numerical-builds)
gives the pinned OpenBLAS version and the way to build it.

Rules:

- `vastitas build` needs `--openblas-prefix` for a program whose entry point
  reaches a product statement: directly, through calls, or in an arm of a
  branch that the program never selects (`E_BUILD`).
- `--openblas-prefix` and `--native-cc` are errors (`E_USAGE`) for
  `vastitas check`, and for `vastitas build` of a program whose entry point
  reaches no product statement. Such a program may declare spaces, bases and
  maps, and it may use `adjoint_into` and `pack3`.
- The compiler checks every numerical statement of the program, even in a
  function that the entry point never calls.

[Numerical backend](../internals/numerical-backend.md) describes the checker,
the wire forms, the native adapter and the evidence for these statements.
